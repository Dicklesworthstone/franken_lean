/* Derivation program for the stdio.rs platform constants (fln-3gv slice 5a):
 * prints every constant the io.cpp decoder and handle_mk use, measured from
 * this host's own headers rather than transcribed from memory. */
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stddef.h>
#include <stdio.h>
#include <sys/file.h>
#include <sys/stat.h>
#define P(n) printf("pub(crate) const %s: c_int = %d;\n", #n, n)
int main(void) {
    P(EINTR); P(ELOOP); P(ENAMETOOLONG); P(EDESTADDRREQ); P(EBADF); P(EDOM);
    P(EINVAL); P(EILSEQ); P(ENOEXEC); P(ENOSTR); P(ENOTCONN); P(ENOTSOCK);
    P(ENOENT); P(EACCES); P(EROFS); P(ECONNABORTED); P(EFBIG); P(EPERM);
    P(EMFILE); P(ENFILE); P(ENOSPC); P(E2BIG); P(EAGAIN); P(EMLINK);
    P(EMSGSIZE); P(ENOBUFS); P(ENOLCK); P(ENOMEM); P(ENOSR); P(EISDIR);
    P(EBADMSG); P(ENOTDIR); P(ENXIO); P(EHOSTUNREACH); P(ENETUNREACH);
    P(ECHILD); P(ECONNREFUSED); P(ENODATA); P(ENOMSG); P(ESRCH); P(EEXIST);
    P(EINPROGRESS); P(EISCONN); P(EIO); P(ENOTEMPTY); P(ENOTTY);
    P(ECONNRESET); P(EIDRM); P(ENETDOWN); P(ENETRESET); P(ENOLINK); P(EPIPE);
    P(EPROTO); P(EPROTONOSUPPORT); P(EPROTOTYPE); P(ETIME); P(ETIMEDOUT);
    P(EADDRINUSE); P(EBUSY); P(EDEADLK); P(ETXTBSY); P(EADDRNOTAVAIL);
    P(EAFNOSUPPORT); P(ENODEV); P(ENOPROTOOPT); P(ENOSYS); P(EOPNOTSUPP);
    P(ERANGE); P(ESPIPE); P(EXDEV); P(EFAULT);
    P(O_RDONLY); P(O_WRONLY); P(O_RDWR); P(O_CREAT); P(O_TRUNC); P(O_EXCL);
    P(O_APPEND); P(O_CLOEXEC);
    P(SIGPIPE);
    printf("SIG_IGN=%p\n", (void *)SIG_IGN);
    /* fln-3gv slices 5d/6a: seek/flock and the fs plane's layout facts. */
    P(SEEK_SET); P(LOCK_SH); P(LOCK_EX); P(LOCK_NB); P(LOCK_UN);
    printf("pub(crate) const PATH_MAX: usize = %d;\n", PATH_MAX);
    printf(
        "pub(crate) const DIRENT_D_NAME_OFFSET: usize = %zu;\n",
        offsetof(struct dirent, d_name));
    /* fln-3gv slice 6d: the stat(2) layout facts metadata_core reads. */
    printf("pub(crate) const STAT_SIZE: usize = %zu;\n", sizeof(struct stat));
    printf("pub(crate) const STAT_ST_MODE_OFFSET: usize = %zu;\n",
           offsetof(struct stat, st_mode));
    printf("pub(crate) const STAT_ST_NLINK_OFFSET: usize = %zu;\n",
           offsetof(struct stat, st_nlink));
    printf("pub(crate) const STAT_ST_SIZE_OFFSET: usize = %zu;\n",
           offsetof(struct stat, st_size));
    printf("pub(crate) const STAT_ST_ATIM_OFFSET: usize = %zu;\n",
           offsetof(struct stat, st_atim));
    printf("pub(crate) const STAT_ST_MTIM_OFFSET: usize = %zu;\n",
           offsetof(struct stat, st_mtim));
    printf("pub(crate) const S_IFMT_MASK: u32 = %u;\n", (unsigned)S_IFMT);
    printf("pub(crate) const S_IFDIR_BITS: u32 = %u;\n", (unsigned)S_IFDIR);
    printf("pub(crate) const S_IFREG_BITS: u32 = %u;\n", (unsigned)S_IFREG);
    printf("pub(crate) const S_IFLNK_BITS: u32 = %u;\n", (unsigned)S_IFLNK);
    return 0;
}
