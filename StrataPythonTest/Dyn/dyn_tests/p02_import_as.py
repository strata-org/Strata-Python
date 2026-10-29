# `import a.b as c` binds `c` to module `a.b`; `import a as b` binds `b` to `a`.
import os.path as osp
import json as j


def f(p):
    return osp.basename(p), j.dumps(p)
