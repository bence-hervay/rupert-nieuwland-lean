"""One helper: `ordered_map(fn, items)` is `[fn(x) for x in items]`, computed on all cores.

For the per-file passes over a solid's certificate, which for the largest solids are thousands
of modules and gigabytes of text: rewriting the pieces in the new names (`solid.certificate`) and
screening the modules (`build.screen_all`). Worker processes (fork) compute `fn` on the items and
the results come back in the items' order; the caller does everything else as before, so the
output is the serial loop's, byte for byte (`test_parallel.py`). `fn` must be pure (read, compute,
return; no writes) and picklable (a module-level function, or a `functools.partial` of one).

Failures are the serial loop's: the first failing item in order decides. A `sys.exit` inside `fn`
(SystemExit, which a worker would otherwise not report) is carried back and raised here with its
message; another exception is re-raised by the pool. With fewer than `min_items` items, or one
core, it is the plain loop.
"""
import multiprocessing
import os
import sys

SERIAL = False      # tests: the plain loop everywhere, for comparison


def _call(arg):
    fn, x = arg
    try:
        return True, fn(x)
    except SystemExit as e:
        return False, e.code


def ordered_map(fn, items, min_items=16):
    items = list(items)
    workers = os.cpu_count() or 1
    if SERIAL or workers <= 1 or len(items) < min_items:
        return [fn(x) for x in items]
    out = []
    with multiprocessing.get_context("fork").Pool(workers) as pool:
        for ok, v in pool.imap(_call, [(fn, x) for x in items], chunksize=max(1, len(items) // (8 * workers))):
            if not ok:
                sys.exit(v)
            out.append(v)
    return out
