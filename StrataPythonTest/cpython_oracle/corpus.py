"""Locate CPython's regression suite inside the CPython312Runtime dependency.

The suite is not on disk anywhere: CPython312Runtime is a thin from-source wrapper
whose `pkg.src` holds the upstream release tarball, and the *built* runtime strips
the `test` package entirely. So we read `Lib/test/*.py` straight out of the tarball.
That keeps the corpus pinned by the version set, with no network access and no
separate checkout to provision.

The tarball's patch version is discovered by globbing rather than hardcoded, because
the package revision advances under us when the version set moves.
"""
from __future__ import annotations

import glob
import os
import pathlib
import subprocess
import tarfile

_PREFIX = "Lib/test/"


def brazil_pkg_src(package: str = "CPython312Runtime") -> pathlib.Path:
    """`brazil-path '[<package>]pkg.src'`, or $CPYTHON_PKG_SRC to override."""
    override = os.environ.get("CPYTHON_PKG_SRC")
    if override:
        return pathlib.Path(override)
    out = subprocess.run(
        ["brazil-path", f"[{package}]pkg.src"],
        capture_output=True, text=True, check=True,
    )
    return pathlib.Path(out.stdout.strip())


def find_tarball(pkg_src: pathlib.Path | None = None) -> pathlib.Path:
    pkg_src = pkg_src or brazil_pkg_src()
    matches = sorted(glob.glob(str(pkg_src / "package" / "Python-3.*.tar.xz")))
    if not matches:
        raise FileNotFoundError(f"no Python-3.*.tar.xz under {pkg_src / 'package'}")
    return pathlib.Path(matches[-1])


class Corpus:
    """Read-only view of `Lib/test/` inside the tarball."""

    def __init__(self, tarball: pathlib.Path | None = None):
        self.tarball = tarball or find_tarball()
        self._tf = tarfile.open(self.tarball)
        self._index: dict[str, str] = {}
        # EVERY member, not only `.py`. The oracle chdirs into the extracted test
        # directory so a test can open its data file by relative path -- test_float
        # reads `formatfloat_testcases.txt` -- and a `.py`-only index never extracts
        # those. `files()` applies the `.py` filter where it belongs.
        for name in self._tf.getnames():
            idx = name.find(_PREFIX)
            if idx != -1:
                self._index[name[idx + len(_PREFIX):]] = name

    @property
    def version(self) -> str:
        """e.g. '3.12.12', from the tarball name."""
        return self.tarball.name[len("Python-"):-len(".tar.xz")]

    def files(self) -> list[str]:
        """The test MODULES. The index also holds their data files -- see `__init__`."""
        return sorted(n for n in self._index
                      if n.startswith("test_") and n.endswith(".py"))

    def read(self, relpath: str) -> str:
        member = self._index.get(relpath)
        if member is None:
            raise KeyError(f"{relpath} not in {self.tarball.name}")
        fh = self._tf.extractfile(member)
        assert fh is not None
        return fh.read().decode("utf-8", errors="replace")

    def extract_lib(self, dest: pathlib.Path) -> pathlib.Path:
        """Extract `Lib/test/**` under `dest`, returning the dir to put on sys.path.

        The oracle executes the pristine test file, so `from test import support`
        has to resolve. The built runtime strips the `test` package, so we supply it
        from the same tarball the sources came from -- which also guarantees the
        helpers match the file under test.

        The destination is keyed on the CPython VERSION, and it has to be. Extraction
        skips files that already exist, so with a fixed path a build directory surviving
        a version-set bump would keep serving the previous release's `test.support`
        against the new corpus -- mismatched helpers, silently. `find_tarball` globs the
        patch version precisely because it moves, so this has to move with it.
        """
        lib = dest / self.version / "Lib"
        for relpath, member in sorted(self._index.items()):
            target = lib / "test" / relpath
            if target.exists():
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            fh = self._tf.extractfile(member)
            if fh is None:
                continue
            target.write_bytes(fh.read())
        return lib

    def close(self) -> None:
        self._tf.close()

    def __enter__(self) -> "Corpus":
        return self

    def __exit__(self, *exc) -> None:
        self.close()
