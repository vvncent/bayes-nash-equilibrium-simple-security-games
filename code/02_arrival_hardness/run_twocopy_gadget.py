"""Artifact launcher (no check logic here): runs ../lib/twocopy_gadget.py as __main__ with the same
command-line arguments. The gadget builder lives in lib/ because other checks import it."""
import os, runpy, sys
_LIB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lib")
sys.path.insert(0, _LIB)
runpy.run_path(os.path.join(_LIB, "twocopy_gadget.py"), run_name="__main__")
