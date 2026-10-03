{
  tag = "v4.34.0";
  dontStrip = true;
  patchDarwinDylibNames = false;
  rev = "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b";
  toolchain = {
    x86_64-linux = {
      url = "https://github.com/leanprover/lean4/releases/download/v4.34.0/lean-4.34.0-linux.tar.zst";
      hash = "sha256-yqqYNWCYyF3A/LvSjh7GbznrZVGCmXK3Uv8g4ShrZGs=";
    };
    aarch64-darwin = {
      url = "https://github.com/leanprover/lean4/releases/download/v4.34.0/lean-4.34.0-darwin_aarch64.tar.zst";
      hash = "sha256-afJj+m4hu8JGa7+xr/zZJHnuJxTIg6B95UjgmaWSKTI=";
    };
  };
}
