#!/usr/bin/env python3
from __future__ import annotations

import json, os, shutil, subprocess, sys, tempfile, unittest
from pathlib import Path

SCRIPT = Path(__file__).with_name("agent_handoff.py")
PACKAGE = Path(__file__).with_name("agent_handoff_lib")
SELECTOR = r'''
import hashlib, json
from dataclasses import dataclass
class FrontierError(Exception): pass
@dataclass(frozen=True)
class Issue:
 id:str; title:str; status:str; priority:int; issue_type:str; assignee:str|None; acceptance_criteria:str; description:str; labels:tuple; blockers:tuple
class Overlay: pass
def load_issues(path):
 raw=path.read_bytes(); out={}
 for n,line in enumerate(raw.splitlines(),1):
  if not line.strip(): continue
  try: row=json.loads(line)
  except Exception as e: raise FrontierError(f"invalid row {n}: {e}")
  i=row.get("id")
  if not isinstance(i,str) or not i: raise FrontierError(f"invalid id at row {n}")
  if i in out: raise FrontierError(f"duplicate issue id {i!r}")
  blockers=tuple(sorted(d.get("depends_on_id") for d in row.get("dependencies",[]) if d.get("type")=="blocks"))
  out[i]=Issue(i,row.get("title",i),row.get("status","open"),row.get("priority",2),row.get("issue_type","task"),row.get("assignee") or None,row.get("acceptance_criteria","accept"),row.get("description",""),tuple(sorted(row.get("labels",[]))),blockers)
 for issue in out.values():
  for blocker in issue.blockers:
   if blocker not in out: raise FrontierError(f"{issue.id} has dangling blocker {blocker!r}")
 return out,hashlib.sha256(raw).hexdigest()
def load_overlays(path,ids): return {} if path is None else {k:Overlay() for k in json.loads(path.read_text())}
def rank(issues,overlays,*,owner,strict):
 rows=[]; excluded={}
 for x in issues.values():
  if x.status=="closed": excluded["closed"]=excluded.get("closed",0)+1; continue
  if any(issues[b].status!="closed" for b in x.blockers): excluded["blocked_dependencies"]=excluded.get("blocked_dependencies",0)+1; continue
  if x.assignee and x.assignee!=owner: excluded["owned_by_other"]=excluded.get("owned_by_other",0)+1; continue
  score=(4-x.priority)*1000
  rows.append({"id":x.id,"title":x.title,"status":x.status,"priority":x.priority,"issue_type":x.issue_type,"assignee":x.assignee,"labels":list(x.labels),"critical_path_descendants":0,"direct_unlocks":0,"score":score,"score_components":{"priority":score},"unknown_hard_filter_facts":[] if strict else ["toolchain_available"],"promotion_authority":strict})
 rows.sort(key=lambda r:(-r["score"],r["id"]))
 return rows,dict(sorted(excluded.items()))
'''

def run(cmd,cwd,input_bytes=None):
 return subprocess.run(cmd,cwd=cwd,input=input_bytes,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)

class HandoffTests(unittest.TestCase):
 def repo(self,rows=None):
  root=Path(tempfile.mkdtemp(prefix="fln-handoff-")); (root/"scripts").mkdir()
  shutil.copyfile(SCRIPT,root/"scripts/agent_handoff.py"); shutil.copytree(PACKAGE,root/"scripts/agent_handoff_lib"); os.chmod(root/"scripts/agent_handoff.py",0o755)
  (root/"scripts/frontier_select.py").write_text(SELECTOR)
  (root/".beads").mkdir(); self.rows(root,rows or [self.row("low",2),self.row("high",0)])
  for path in ("AGENTS.md","README.md","COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md","SUITE.lock","AGENT_FRONTIER_PROTOCOL.md","IMPLEMENTATION_STATUS.md","CHANGELOG.md"):(root/path).write_text(path+"\n")
  (root/"evidence/frontiers").mkdir(parents=True); (root/"evidence/frontiers/one.json").write_text("{}\n")
  for cmd in (["git","init","-b","main"],["git","config","user.name","test"],["git","config","user.email","test@example.invalid"],["git","add","."],["git","commit","-m","initial\n\nBead: high"]):
   result=run(cmd,root); self.assertEqual(result.returncode,0,result.stderr.decode())
  return root
 @staticmethod
 def row(i,p,status="open",**extra): return {"id":i,"title":i,"status":status,"priority":p,"issue_type":"task","acceptance_criteria":"done",**extra}
 @staticmethod
 def rows(root,rows): (root/".beads/issues.jsonl").write_text("".join(json.dumps(x,sort_keys=True,separators=(",",":"))+"\n" for x in rows))
 @staticmethod
 def snap(root,*args): return run([sys.executable,"scripts/agent_handoff.py","snapshot",*args],root)
 def test_deterministic_snapshot_and_ready_selection(self):
  root=self.repo(); a=self.snap(root,"--strict","--selection-strict","--recent","1"); b=self.snap(root,"--strict","--selection-strict","--recent","1")
  self.assertEqual(a.returncode,0,a.stderr.decode()); self.assertEqual(a.stdout,b.stdout); d=json.loads(a.stdout)
  self.assertEqual(d["schema"],"fln.agent-handoff/1"); self.assertEqual(d["tracker"]["selected"]["id"],"high"); self.assertTrue(d["authority"]["promotion_authority"]); self.assertEqual(d["recent_commits"][0]["beads"],["high"])
 def test_strict_dirty_and_no_clobber_refusals(self):
  root=self.repo(); (root/"README.md").write_text("dirty\n"); dirty=self.snap(root,"--strict"); self.assertEqual(dirty.returncode,2); self.assertIn("clean working tree",json.loads(dirty.stderr)["reason"])
  output=root/"out.json"; output.write_text("sentinel\n"); refused=self.snap(root,"--output",str(output)); self.assertEqual(refused.returncode,2); self.assertEqual(output.read_text(),"sentinel\n")
 def test_current_and_archived_verification(self):
  root=self.repo(); snap=self.snap(root,"--strict"); self.assertEqual(snap.returncode,0,snap.stderr.decode())
  current=run([sys.executable,"scripts/agent_handoff.py","verify","-","--current"],root,snap.stdout); self.assertEqual(current.returncode,0,current.stderr.decode())
  self.rows(root,[self.row("new",1)]); run(["git","add",".beads/issues.jsonl"],root); run(["git","commit","-m","advance"],root)
  stale=run([sys.executable,"scripts/agent_handoff.py","verify","-","--current"],root,snap.stdout); self.assertEqual(stale.returncode,2)
  archived=run([sys.executable,"scripts/agent_handoff.py","verify","-"],root,snap.stdout); self.assertEqual(archived.returncode,0,archived.stderr.decode()); receipt=json.loads(archived.stdout); self.assertFalse(receipt["current_head_matches"]); self.assertFalse(receipt["current_tracker_matches"])
 def test_capsule_reuse_staleness_and_required_migration(self):
  root=self.repo(); tracked=root/"tracked.txt"; tracked.write_text("one\n"); run(["git","add","tracked.txt"],root); run(["git","commit","-m","seam"],root)
  commit=run(["git","rev-parse","HEAD"],root).stdout.decode().strip(); tree=run(["git","rev-parse","HEAD^{tree}"],root).stdout.decode().strip(); blob=run(["git","rev-parse","HEAD:tracked.txt"],root).stdout.decode().strip()
  capsule={"schema":"fln.agent-frontier/1","bead":"active","state":"in_progress","owner":"tester","anchor":{"branch":"main","commit":commit,"tree":tree,"tracked_blobs":{"tracked.txt":blob}}}
  row=self.row("active",1,"in_progress",comments=[{"created_at":"2026-09-03T00:00:00Z","text":"```json\n"+json.dumps(capsule)+"\n```"}]); self.rows(root,[row]); run(["git","add",".beads/issues.jsonl"],root); run(["git","commit","-m","capsule"],root)
  good=json.loads(self.snap(root,"--owner","tester").stdout)["capsules"]["records"][0]; self.assertEqual(good["freshness"],"reusable")
  tracked.write_text("two\n"); run(["git","add","tracked.txt"],root); run(["git","commit","-m","move"],root)
  stale=json.loads(self.snap(root,"--owner","tester").stdout)["capsules"]["records"][0]; self.assertEqual(stale["freshness"],"stale"); self.assertEqual(stale["stale_paths"],["tracked.txt"])
  missing=self.repo([self.row("active",1,"in_progress")]); refused=self.snap(missing,"--require-capsules"); self.assertEqual(refused.returncode,2); self.assertIn("missing=1",json.loads(refused.stderr)["reason"])
 def test_capsule_conflicts_block_authority_and_required_snapshot(self):
  root=self.repo(); tracked=root/"tracked.txt"; tracked.write_text("one\n"); run(["git","add","tracked.txt"],root); run(["git","commit","-m","seam"],root)
  commit=run(["git","rev-parse","HEAD"],root).stdout.decode().strip(); tree=run(["git","rev-parse","HEAD^{tree}"],root).stdout.decode().strip(); blob=run(["git","rev-parse","HEAD:tracked.txt"],root).stdout.decode().strip()
  def row(bead,owner):
   capsule={"schema":"fln.agent-frontier/1","bead":bead,"state":"in_progress","owner":owner,"anchor":{"branch":"main","commit":commit,"tree":tree,"tracked_blobs":{"tracked.txt":blob}}}
   return self.row(bead,1,"in_progress",comments=[{"created_at":"2026-09-03T00:00:00Z","text":json.dumps(capsule)}])
  self.rows(root,[row("alpha","owner-a"),row("beta","owner-b")]); run(["git","add",".beads/issues.jsonl"],root); run(["git","commit","-m","conflict"],root)
  snapshot=self.snap(root,"--owner","owner-a","--selection-strict"); self.assertEqual(snapshot.returncode,0,snapshot.stderr.decode()); document=json.loads(snapshot.stdout)
  self.assertFalse(document["authority"]["promotion_authority"]); self.assertEqual(document["capsules"]["conflicts"],[{"path":"tracked.txt","claimants":[{"bead":"alpha","owner":"owner-a"},{"bead":"beta","owner":"owner-b"}]}])
  refused=self.snap(root,"--owner","owner-a","--selection-strict","--require-capsules"); self.assertEqual(refused.returncode,2); self.assertIn("conflicts=1",json.loads(refused.stderr)["reason"])
 def test_duplicate_ids_and_keys_fail_closed(self):
  root=self.repo(); with_open=root/".beads/issues.jsonl"
  with with_open.open("a") as f: f.write(json.dumps(self.row("high",0))+"\n")
  duplicate=self.snap(root); self.assertEqual(duplicate.returncode,2); self.assertIn("duplicate issue id",json.loads(duplicate.stderr)["reason"])
  root=self.repo(); (root/".beads/issues.jsonl").write_text('{"id":"a","id":"b","title":"x","status":"open","priority":1,"issue_type":"task","acceptance_criteria":"done"}\n'); duplicate_key=self.snap(root); self.assertEqual(duplicate_key.returncode,2); self.assertIn("duplicate JSON key",json.loads(duplicate_key.stderr)["reason"])
 def test_commit_record_separator_does_not_split_log(self):
  root=self.repo(); message=b"separator-safe\n\nbody has \x1e byte\n\nBead: high\n"; committed=run(["git","commit","--allow-empty","-F","-"],root,message); self.assertEqual(committed.returncode,0,committed.stderr.decode())
  recent=json.loads(self.snap(root,"--recent","2").stdout)["recent_commits"]; self.assertEqual(recent[0]["subject"],"separator-safe"); self.assertEqual(recent[0]["beads"],["high"])

if __name__=="__main__": unittest.main()
