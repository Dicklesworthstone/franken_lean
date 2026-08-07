/* Derivation program for the fs plane's uv-error surface (fln-3gv slice 6b):
 * drives the Reference's own exported lean_decode_uv_error over every errno
 * the io.cpp decoder names, with a real filename, and prints one row per
 * input — the IO.Error variant tag, the stored osCode, and the details
 * string (libuv's uv_strerror text, which differs from glibc's strerror).
 *
 * Link it ONLY against libleanshared (the same recipe as the gauntlet's
 * probe_reference): the output is a measured contract table, mined from the
 * pin per D5/D9, never hand-transcribed.
 *
 *   gcc -O1 -DNDEBUG -Wall -Werror -I "$ELAN_TC/include" \
 *     tribunal/fixtures/c4/uv_error_extract.c \
 *     -L "$ELAN_TC/lib/lean" -lleanshared -Wl,-rpath,"$ELAN_TC/lib/lean" \
 *     -o uv_error_extract && ./uv_error_extract
 *
 * Row grammar: uvrow <ERRNO_NAME> <input(-errno)> <variant_tag> <oscode>
 *              <details>
 */
#include <errno.h>
#include <lean/lean.h>
#include <stdio.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *lean_decode_uv_error(int errnum, lean_object *fname);

static void row(const char *name, int e) {
    lean_object *fname = lean_mk_string("/tmp/fln-uv-extract-fixture");
    lean_object *err = lean_decode_uv_error(-e, fname);
    unsigned tag = lean_ptr_tag(err);
    unsigned nobjs = lean_ctor_num_objs(err);
    lean_object *details = lean_ctor_get(err, nobjs - 1);
    uint32_t code = lean_ctor_get_uint32(err, nobjs * sizeof(void *));
    printf("uvrow %s %d %u %u %s\n", name, -e, tag, code,
           lean_string_cstr(details));
    lean_dec(err);
    lean_dec(fname);
}

#define R(n) row(#n, n)

int main(void) {
    lean_initialize_runtime_module();
    R(EINTR); R(ELOOP); R(ENAMETOOLONG); R(EDESTADDRREQ); R(EBADF); R(EDOM);
    R(EINVAL); R(EILSEQ); R(ENOEXEC); R(ENOSTR); R(ENOTCONN); R(ENOTSOCK);
    R(ENOENT); R(EACCES); R(EROFS); R(ECONNABORTED); R(EFBIG); R(EPERM);
    R(EMFILE); R(ENFILE); R(ENOSPC); R(E2BIG); R(EAGAIN); R(EMLINK);
    R(EMSGSIZE); R(ENOBUFS); R(ENOLCK); R(ENOMEM); R(ENOSR); R(EISDIR);
    R(EBADMSG); R(ENOTDIR); R(ENXIO); R(EHOSTUNREACH); R(ENETUNREACH);
    R(ECHILD); R(ECONNREFUSED); R(ENODATA); R(ENOMSG); R(ESRCH); R(EEXIST);
    R(EINPROGRESS); R(EISCONN); R(EIO); R(ENOTEMPTY); R(ENOTTY);
    R(ECONNRESET); R(EIDRM); R(ENETDOWN); R(ENETRESET); R(ENOLINK); R(EPIPE);
    R(EPROTO); R(EPROTONOSUPPORT); R(EPROTOTYPE); R(ETIME); R(ETIMEDOUT);
    R(EADDRINUSE); R(EBUSY); R(EDEADLK); R(ETXTBSY); R(EADDRNOTAVAIL);
    R(EAFNOSUPPORT); R(ENODEV); R(ENOPROTOOPT); R(ENOSYS); R(EOPNOTSUPP);
    R(ERANGE); R(ESPIPE); R(EXDEV); R(EFAULT);
    return 0;
}
