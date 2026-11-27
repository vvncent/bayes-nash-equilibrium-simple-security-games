# Checks for the reductions manuscripts

The [standalone paper](../paper/traffic-matching-security-games.pdf) and [extended manuscript](../paper/equilibrium-reductions.pdf) give the proofs and their hypotheses. These scripts exercise particular constructions and examples. The [dated review](../paper/equilibrium-reductions-referee.md) records the scope of each round of checks.

Run the following from the repository root in a Python 3.12 environment. The companion scripts use `z3-solver`, SymPy and NetworkX. The versions in the verification environment were `z3-solver==5.4.1.0`, `sympy==1.14.0` and `networkx==3.6.1`.

| Construction | Command |
| --- | --- |
| Parallel roads and affine matching | `python -B round2/wardrop/check_wardrop.py` |
| Adaptive security-game queries encoded in one market | `python -B round2/check_security_adaptive_equilibrium.py` |
| Switching-flow decoder and the Cayley matrix family | `python -B paper/check_reductions_referee.py` |
| Binary Multi-Arrival, terminal-count bits | `python -B round2/check_multi_arrival_bits.py` |
| Multi-Arrival embedded in a security game | `python -B round2/check_multi_arrival_market.py` |
| Uniqueness from a supplied equilibrium | `python -B round2/check_security_equilibrium_uniqueness.py` |
| Prescribed utilities and prices on both sides of a market | `python -B round2/check_m1_bilateral_pins.py` |
| Clearing with a promised half-quota | `python -B round2/quota/verify_quota.py` |
| Ordered Boolean search with affine targets | `python -B round2/check_opdc_affine_witness_market.py` |

The remaining scripts in this directory include the market constructors, further finite checks, and modules imported by these commands. The [original book’s reproduction record](../code/REPRODUCTION.md) covers its separate suite.
