"""Declare the Linux C++ runtime needed by the pinned Z3 test wheel."""
def _impl(ctx):
    if ctx.os.name.lower().startswith("linux"):
        root = ctx.os.environ.get("AYXG_NIX_LIBSTDCXX_ROOT", "")
        if not root.startswith("/nix/store/"):
            fail("AYXG_NIX_LIBSTDCXX_ROOT must name an immutable Nix output")
        library = ctx.path(root + "/lib/libstdc++.so.6")
        if not library.exists:
            fail("declared libstdc++ is missing")
        ctx.symlink(library, "libstdc++.so.6")
        ctx.file("BUILD.bazel", 'exports_files(["libstdc++.so.6"], visibility=["//visibility:public"])')
    else:
        ctx.file("BUILD.bazel", "")

_repo = repository_rule(implementation = _impl, local = True, configure = True,
                        environ = ["AYXG_NIX_LIBSTDCXX_ROOT"])
def _extension(_ctx):
    _repo(name = "ayxg_native")
native = module_extension(implementation = _extension)
