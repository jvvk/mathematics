"""Mutation-suite entry point: run a checker so that only a failed check counts as a rejection.

    python3 -I run_check.py <checker.py>

Exit 1 on AssertionError (the checker rejected the input), 0 on success, 200 on any other exception (a crash, which
the mutation runner reports as INCONCLUSIVE rather than as a rejection)."""
import runpy
import sys
import traceback

try:
    sys.argv = sys.argv[1:]
    runpy.run_path(sys.argv[0], run_name="__main__")
except AssertionError:
    traceback.print_exc()
    sys.exit(1)
except SystemExit:
    raise
except BaseException:
    traceback.print_exc()
    sys.exit(200)
