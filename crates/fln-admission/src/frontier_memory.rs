//! Linux memory headroom for both frontier phases. Every bound is expressed
//! as an effective process-RSS ceiling before the scheduler compares it with
//! retained RSS and in-flight reservations. A cgroup limit belongs to the
//! whole group, including siblings and page cache, not just this process.
//!
//! These are read-only scheduling snapshots, not resource verdicts. Missing
//! files leave the other observed bounds in force, and the scheduler still
//! allows one isolated module to try under its unchanged checking budgets.

use super::FrontierMemorySample;
use std::path::{Component, Path, PathBuf};

type ReadFile<'a> = dyn FnMut(&Path) -> Option<String> + 'a;

pub(super) fn sample(override_limit: Option<u64>) -> FrontierMemorySample {
    sample_with(override_limit, &mut |path| std::fs::read_to_string(path).ok())
}

fn sample_with(override_limit: Option<u64>, read: &mut ReadFile<'_>) -> FrontierMemorySample {
    let status = read(Path::new("/proc/self/status")).unwrap_or_default();
    let rss_bytes = proc_kb_value(&status, "VmRSS:").unwrap_or(0);
    let vm_size_bytes = proc_kb_value(&status, "VmSize:").unwrap_or(0);
    let address_space = read(Path::new("/proc/self/limits"))
        .and_then(|limits| address_space_ceiling(&limits, rss_bytes, vm_size_bytes));
    let physical = read(Path::new("/proc/meminfo")).and_then(|meminfo| {
        // MemAvailable includes reclaimable memory. MemFree alone would
        // unnecessarily serialize the frontier whenever the page cache grew.
        let available = proc_kb_value(&meminfo, "MemAvailable:")
            .map(|bytes| rss_bytes.saturating_add(bytes));
        available
            .into_iter()
            .chain(proc_kb_value(&meminfo, "MemTotal:"))
            .min()
    });
    let cgroup = read(Path::new("/proc/self/cgroup")).and_then(|membership| {
        read(Path::new("/proc/self/mountinfo"))
            .and_then(|mounts| cgroup_ceiling(&membership, &mounts, rss_bytes, read))
    });
    FrontierMemorySample {
        rss_bytes,
        // An explicit ceiling is an additional bound, never permission to
        // exceed RLIMIT_AS, container limits or available physical memory.
        limit_bytes: [override_limit, address_space, physical, cgroup]
            .into_iter()
            .flatten()
            .min(),
    }
}

fn proc_kb_value(text: &str, prefix: &str) -> Option<u64> {
    text.lines().find_map(|line| {
        let mut fields = line.strip_prefix(prefix)?.split_whitespace();
        let value = fields.next()?.parse::<u64>().ok()?;
        (fields.next()? == "kB").then_some(())?;
        value.checked_mul(1024)
    })
}

fn address_space_ceiling(limits: &str, rss_bytes: u64, vm_size_bytes: u64) -> Option<u64> {
    let max_as = limits.lines().find_map(|line| {
        line.strip_prefix("Max address space")?
            .split_whitespace()
            .next()?
            .parse::<u64>()
            .ok()
    })?;
    // Nonresident worker stacks and mapped code also count against RLIMIT_AS.
    Some(max_as.saturating_sub(vm_size_bytes.saturating_sub(rss_bytes)))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum CgroupVersion {
    V1,
    V2,
}

fn cgroup_ceiling(
    membership: &str,
    mounts: &str,
    rss_bytes: u64,
    read: &mut ReadFile<'_>,
) -> Option<u64> {
    let mut ceiling = None;
    for line in membership.lines() {
        let Some((hierarchy, rest)) = line.split_once(':') else {
            continue;
        };
        let Some((controllers, path)) = rest.split_once(':') else {
            continue;
        };
        let version = if hierarchy == "0" && controllers.is_empty() {
            CgroupVersion::V2
        } else if controllers.split(',').any(|controller| controller == "memory") {
            CgroupVersion::V1
        } else {
            continue;
        };
        let Some(member) = absolute_path(path) else {
            continue;
        };
        for mount in mounts.lines() {
            let Some((before, after)) = mount.split_once(" - ") else {
                continue;
            };
            let mut kind = after.split_whitespace();
            let filesystem = kind.next();
            let _source = kind.next();
            let options = kind.next().unwrap_or_default();
            let matches = match version {
                CgroupVersion::V2 => filesystem == Some("cgroup2"),
                CgroupVersion::V1 => {
                    filesystem == Some("cgroup")
                        && options.split(',').any(|option| option == "memory")
                }
            };
            if !matches {
                continue;
            }
            let mut fields = before.split_whitespace();
            let Some(root) = fields.nth(3).and_then(mount_path) else {
                continue;
            };
            let Some(mountpoint) = fields.next().and_then(mount_path) else {
                continue;
            };
            // A bind mount may expose only a subtree. Membership and root
            // are relative to the same cgroup namespace; never append the
            // full membership path to an already rebased mountpoint.
            let Ok(relative) = member.strip_prefix(root) else {
                continue;
            };
            let leaf = mountpoint.join(relative);
            for directory in leaf.ancestors() {
                if !directory.starts_with(&mountpoint) {
                    break;
                }
                // In legacy v1, an ancestor constrains its descendants only
                // when hierarchical accounting is enabled. V2 is always
                // hierarchical. The process's own group always applies.
                if version == CgroupVersion::V1
                    && directory != leaf
                    && read(&directory.join("memory.use_hierarchy"))
                        .is_none_or(|value| value.trim() != "1")
                {
                    continue;
                }
                let (limit_name, usage_name) = match version {
                    CgroupVersion::V1 => ("memory.limit_in_bytes", "memory.usage_in_bytes"),
                    CgroupVersion::V2 => ("memory.max", "memory.current"),
                };
                // V2's "max" and malformed/missing values supply no finite
                // bound. Still visit parents: an unlimited leaf can live
                // beneath a constrained service or container.
                let Some(limit) = read(&directory.join(limit_name))
                    .and_then(|value| value.trim().parse::<u64>().ok())
                else {
                    continue;
                };
                let usage = read(&directory.join(usage_name))
                    .and_then(|value| value.trim().parse::<u64>().ok());
                let effective = usage.map_or(limit, |used| {
                    rss_bytes.saturating_add(limit.saturating_sub(used))
                });
                ceiling = Some(ceiling.map_or(effective, |prior: u64| prior.min(effective)));
            }
        }
    }
    ceiling
}

fn absolute_path(value: &str) -> Option<PathBuf> {
    let path = Path::new(value);
    (path.is_absolute()
        && !path
            .components()
            .any(|part| matches!(part, Component::ParentDir)))
    .then(|| path.to_path_buf())
}

/// mountinfo escapes spaces, tabs, newlines and backslashes with octal bytes.
/// Decode only that specified alphabet; malformed paths cannot escape the
/// discovered mount or cause probes of unrelated filesystem locations.
fn mount_path(value: &str) -> Option<PathBuf> {
    let mut decoded = Vec::with_capacity(value.len());
    let mut bytes = value.as_bytes().iter().copied();
    while let Some(byte) = bytes.next() {
        if byte != b'\\' {
            decoded.push(byte);
            continue;
        }
        decoded.push(match (bytes.next()?, bytes.next()?, bytes.next()?) {
            (b'0', b'4', b'0') => b' ',
            (b'0', b'1', b'1') => b'\t',
            (b'0', b'1', b'2') => b'\n',
            (b'1', b'3', b'4') => b'\\',
            _ => return None,
        });
    }
    absolute_path(std::str::from_utf8(&decoded).ok()?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn fixture_sample(files: &[(&str, &str)], cap: Option<u64>) -> FrontierMemorySample {
        let files: BTreeMap<_, _> = files
            .iter()
            .map(|(path, text)| (Path::new(path), *text))
            .collect();
        sample_with(cap, &mut |path| files.get(path).map(|text| (*text).to_owned()))
    }

    #[test]
    fn host_available_memory_and_address_space_bound_an_explicit_cap() {
        let files = [
            ("/proc/self/status", "VmRSS: 100 kB\nVmSize: 300 kB\n"),
            ("/proc/self/limits", "Max address space 512000 512000 bytes\n"),
            ("/proc/meminfo", "MemTotal: 1000 kB\nMemAvailable: 150 kB\n"),
        ];
        // Available physical memory permits 250 KiB process RSS; RLIMIT_AS
        // permits 300 KiB. Neither is expanded by the explicit 900 KiB cap.
        assert_eq!(
            fixture_sample(&files, Some(900 * 1024)).limit_bytes,
            Some(250 * 1024)
        );
        assert_eq!(
            fixture_sample(&files, Some(200 * 1024)).limit_bytes,
            Some(200 * 1024)
        );
        assert_eq!(
            fixture_sample(&files[..2], None).limit_bytes,
            Some(300 * 1024)
        );
        assert_eq!(fixture_sample(&files, None).rss_bytes, 100 * 1024);
    }

    #[test]
    fn v2_uses_parent_headroom_including_sibling_usage() {
        let files = [
            ("/proc/self/status", "VmRSS: 1 kB\n"),
            ("/proc/self/cgroup", "0::/service/worker\n"),
            (
                "/proc/self/mountinfo",
                "7 1 0:1 / /sys/fs/cgroup rw - cgroup2 cgroup rw\n",
            ),
            ("/sys/fs/cgroup/service/worker/memory.max", "max\n"),
            ("/sys/fs/cgroup/service/memory.max", "10000\n"),
            ("/sys/fs/cgroup/service/memory.current", "9000\n"),
            ("/sys/fs/cgroup/memory.max", "30000\n"),
            ("/sys/fs/cgroup/memory.current", "10000\n"),
        ];
        assert_eq!(fixture_sample(&files, None).limit_bytes, Some(2024));
        assert_eq!(fixture_sample(&files, Some(50000)).limit_bytes, Some(2024));
        assert_eq!(fixture_sample(&files, Some(1500)).limit_bytes, Some(1500));
    }

    #[test]
    fn v2_uses_the_tightest_headroom_not_the_smallest_raw_limit() {
        let files = [
            ("/proc/self/status", "VmRSS: 1 kB\n"),
            ("/proc/self/cgroup", "0::/parent/leaf\n"),
            (
                "/proc/self/mountinfo",
                "7 1 0:1 / /cg rw - cgroup2 cgroup rw\n",
            ),
            ("/cg/parent/leaf/memory.max", "5000"),
            ("/cg/parent/leaf/memory.current", "2000"),
            ("/cg/parent/memory.max", "10000"),
            ("/cg/parent/memory.current", "9500"),
        ];
        assert_eq!(fixture_sample(&files, None).limit_bytes, Some(1524));
    }

    #[test]
    fn rebased_mounts_decode_escapes_and_never_read_above_the_mount() {
        let files = [
            ("/proc/self/status", "VmRSS: 1 kB\n"),
            ("/proc/self/cgroup", "0::/tenant group/worker\n"),
            (
                "/proc/self/mountinfo",
                "7 1 0:1 /tenant\\040group /mounted\\040group rw - cgroup2 cgroup rw\n",
            ),
            ("/mounted group/worker/memory.max", "5000"),
            ("/mounted group/worker/memory.current", "2000"),
            ("/mounted group/memory.max", "6000"),
            ("/mounted group/memory.current", "5500"),
            ("/memory.max", "0"),
            ("/memory.current", "0"),
        ];
        assert_eq!(fixture_sample(&files, None).limit_bytes, Some(1524));
        let mut reads = Vec::new();
        let files: BTreeMap<_, _> = files
            .iter()
            .map(|(path, text)| (Path::new(path), *text))
            .collect();
        sample_with(None, &mut |path| {
            reads.push(path.to_path_buf());
            files.get(path).map(|text| (*text).to_owned())
        });
        assert!(!reads.iter().any(|path| path == Path::new("/memory.max")));
        assert!(
            !reads
                .iter()
                .any(|path| path.starts_with("/mounted group/tenant group"))
        );
    }

    #[test]
    fn namespace_root_membership_uses_the_visible_root_limit() {
        let files = [
            ("/proc/self/status", "VmRSS: 1 kB\n"),
            ("/proc/self/cgroup", "0::/\n"),
            (
                "/proc/self/mountinfo",
                "7 1 0:1 / /container/cg rw - cgroup2 cgroup rw\n",
            ),
            ("/container/cg/memory.max", "2048"),
            ("/container/cg/memory.current", "2048"),
        ];
        assert_eq!(fixture_sample(&files, None).limit_bytes, Some(1024));
    }

    #[test]
    fn hybrid_v1_memory_uses_only_enforced_ancestors() {
        let mut files = vec![
            ("/proc/self/status", "VmRSS: 1 kB\n"),
            (
                "/proc/self/cgroup",
                "0::/unified\n2:cpu,cpuacct:/wrong\n5:memory:/jobs/worker\n",
            ),
            (
                "/proc/self/mountinfo",
                "7 1 0:1 / /cpu rw - cgroup cgroup rw,cpu,cpuacct\n8 1 0:2 / /memory rw - cgroup cgroup rw,memory\n",
            ),
            ("/memory/jobs/worker/memory.limit_in_bytes", "5000"),
            ("/memory/jobs/worker/memory.usage_in_bytes", "2000"),
            ("/memory/jobs/memory.use_hierarchy", "1"),
            ("/memory/jobs/memory.limit_in_bytes", "10000"),
            ("/memory/jobs/memory.usage_in_bytes", "9500"),
            ("/memory/memory.use_hierarchy", "0"),
            ("/memory/memory.limit_in_bytes", "100"),
            ("/memory/memory.usage_in_bytes", "0"),
        ];
        assert_eq!(fixture_sample(&files, None).limit_bytes, Some(1524));
        files[5].1 = "0";
        assert_eq!(fixture_sample(&files, None).limit_bytes, Some(4024));
    }

    #[test]
    fn malformed_or_hidden_cgroups_preserve_other_observed_bounds() {
        let files = [
            ("/proc/self/status", "VmRSS: 1 kB\n"),
            ("/proc/self/cgroup", "malformed\n0::/outside/../worker\n0::/valid\n"),
            (
                "/proc/self/mountinfo",
                "invalid\n7 1 0:1 /other /wrong rw - cgroup2 cgroup rw\n8 1 0:2 / /bad\\999 rw - cgroup2 cgroup rw\n9 1 0:3 / /cg rw - cgroup2 cgroup rw\n",
            ),
            ("/wrong/memory.max", "1"),
            ("/cg/valid/memory.max", "18446744073709551616"),
            ("/cg/memory.max", "max"),
            ("/proc/meminfo", "MemTotal: 100 kB\n"),
        ];
        assert_eq!(
            fixture_sample(&files, None).limit_bytes,
            Some(100 * 1024)
        );
        assert_eq!(fixture_sample(&[], Some(42)).limit_bytes, Some(42));
        assert_eq!(fixture_sample(&[], None).limit_bytes, None);
    }

    #[test]
    fn missing_usage_keeps_the_finite_limit_and_exhaustion_never_wraps() {
        let mut files = vec![
            ("/proc/self/status", "VmRSS: 1 kB\n"),
            ("/proc/self/cgroup", "0::/\n"),
            (
                "/proc/self/mountinfo",
                "7 1 0:1 / /cg rw - cgroup2 cgroup rw\n",
            ),
            ("/cg/memory.max", "2000"),
        ];
        assert_eq!(fixture_sample(&files, None).limit_bytes, Some(2000));
        files.push(("/cg/memory.current", "3000"));
        assert_eq!(fixture_sample(&files, None).limit_bytes, Some(1024));
        files[3].1 = "18446744073709551615";
        files[4].1 = "0";
        assert_eq!(fixture_sample(&files, None).limit_bytes, Some(u64::MAX));
    }

    #[test]
    fn malformed_proc_values_do_not_disable_valid_constraints() {
        let files = [
            (
                "/proc/self/status",
                "VmRSS: 1 bytes\nVmSize: 18446744073709551615 kB\n",
            ),
            (
                "/proc/self/limits",
                "Max address space unlimited unlimited bytes\n",
            ),
            (
                "/proc/meminfo",
                "MemTotal: 100 kB\nMemAvailable: 18446744073709551615 kB\n",
            ),
        ];
        assert_eq!(
            fixture_sample(&files, None).limit_bytes,
            Some(100 * 1024)
        );
        assert_eq!(fixture_sample(&files, None).rss_bytes, 0);
        assert!(mount_path("relative").is_none());
        assert!(mount_path("/cg/../outside").is_none());
        assert!(mount_path("/bad\\04").is_none());
        assert_eq!(
            mount_path("/a\\134b\\011c\\012d"),
            Some(PathBuf::from("/a\\b\tc\nd"))
        );
    }
}
