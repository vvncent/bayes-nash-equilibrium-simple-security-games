"""Negative controls and larger K for the two-copy gadget (same exact verifier).
Controls must FAIL: eps=0 (copies tie), eps=7 (b-offset exceeds the DS increment gap 6),
box U=w=4 with eps=3 (port-price difference can cancel the offset)."""
import os
import sys
import time

import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
from twocopy_gadget import gadget  # noqa: E402
from switchcheck import check, size, bits  # noqa: E402

allok = True  # artifact: exit status
print("negative controls (expect False):")
for label, kw in [("eps=0", dict(eps=0)), ("eps=7", dict(eps=7)), ("w=4", dict(w=4))]:
    g, K, U = gadget(2, **kw)
    ok, res = check(g, K, U)
    allok &= not ok  # artifact: exit status (control must not be certified)
    print(f"  m=2 K={K} {label}: certified={ok}; failing pieces={[r[0] for r in res if not r[3]][:4]}")
sys.stdout.flush()

print("larger K (expect True):")
for m in [int(a) for a in sys.argv[1:]]:
    t = time.time()
    g, K, U = gadget(m)
    ok, res = check(g, K, U)
    allok &= bool(ok)  # artifact: exit status (must be certified)
    print(f"  m={m} K={K} agents={size(g)} bits={bits(g)} certified={ok} "
          f"({time.time() - t:.1f}s); chain(K) would need {K + 2} agents")
    sys.stdout.flush()
sys.exit(0 if allok else 1)  # artifact: exit status
