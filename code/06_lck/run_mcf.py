"""Launcher: runs lib/mcf.py as a script (artifact wrapper; no check logic here).
Named run_mcf.py so that it does not shadow lib/mcf.py, which lib/game.py imports."""
import os, runpy, sys
_LIB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lib")
sys.path.insert(0, _LIB)
runpy.run_path(os.path.join(_LIB, "mcf.py"), run_name="__main__")
