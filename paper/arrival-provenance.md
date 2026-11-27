# How ARRIVAL entered the security-game project

Reconstructed on November 25, 2026. All times below are UTC. BNE means an exact Bayes–Nash equilibrium of Conitzer’s Bayesian simple security game.

| Time in 2026 | What the record shows |
| --- | --- |
| Nov 21, 20:23 | Vincent Lin’s opening prompt supplied Conitzer’s problem PDF and asked for an agent swarm. The prompt did not mention ARRIVAL. [Problem statement](https://www.cs.cmu.edu/~conitzer/security_game_open_problem_simons.pdf) |
| Nov 21, 20:26:56 | A Codex worker searched for the complexity of fixed points of ℓ₁-nonexpansive maps on a simplex. |
| Nov 21, 21:04:43 | The main Codex session opened the full text of a paper by Daskalakis, Farina and Zhang. Its introduction names ARRIVAL as a problem reducible to ℓ₁-contraction and cites Haslebacher as reference 16. [Paper](https://arxiv.org/html/2607.23863v2) |
| Nov 21, 21:04:47 | Four seconds later, the same session searched for Sebastian Haslebacher’s ARRIVAL paper by author, title terms and norm. Haslebacher gives a contraction formulation of generalized ARRIVAL. [Haslebacher’s paper](https://arxiv.org/abs/2502.06477) |
| Nov 22, 05:43:38 | Claude Opus 5.5 in Kiro wrote the two-copy report. It stated the proposed one-resource reduction and the consequence for a polynomial-time equilibrium algorithm. |
| Nov 22, 05:45:19 | The Kiro report was pasted into a separate Claude Code conversation. At 05:49:10 Claude Opus 5.5 restated the implication there. |
| Nov 22, 06:40:26 | A referee agent returned its report on the switch construction, its composition and the conversion to a security game with one defender resource. It recorded two repairs to the proof of the composition and decoding step, including a bound on terminal capacity. |
| Nov 22, 10:02:48 | Jeonseong Kim publicly suggested to Conitzer that ARRIVAL reduces to exact BNE even with one defender resource. The post states the direction and the restriction. [Kim’s post](https://x.com/JeonseongKim/status/2124443473428537685) |
| Nov 22, 16:59:39 | GitHub records the creation of Lin’s public manuscript repository. [Repository metadata](https://api.github.com/repos/vvncent/bayes-nash-equilibrium-simple-security-games) |

## How the comparison became a reduction

Haslebacher’s formulation supplied a target for the construction. After a switch is visited \(q\) times, its two exits must receive \(\lceil q/2\rceil\) and \(\lfloor q/2\rfloor\) visits. A project note explicitly asked how to impose this split using market incentives, including when switches form a cycle.

The construction used two copies of a Disser–Skutella counting network. Each copy has a rising sequence of marginal costs. A small extra cost on the second copy interleaves the sequences, so the cheapest successive units go left, right, left, right. The construction preserves that order over the allowed range of prices at the exits. The project then connected one switch per graph vertex and used its market-to-game construction so that any exact equilibrium of the resulting one-resource game identifies the train’s destination.

## Where the wording came from

“With one defender resource” already appeared in a September 6 note on equilibrium uniqueness. On November 21 at 20:30:54, a Codex worker used those words about a different reduction, from rent division. At 21:12:41 the main Codex session also read the September abstract. [September note](https://www.cs.cmu.edu/~conitzer/gpt6interchangeability.pdf)

The monitor’s inherited transcript included the same September abstract. At 23:10 it wrote up rent-division examples in which the equilibrium prices trace a path with exponentially many bends. It tested the examples with exact arithmetic and at 23:11 read the companion auction construction. At 23:23 it described its new task as checking whether each successful update in Algorithm 3 of Li, Conitzer and Korzhyk follows a straight segment of equilibria as the defender’s budget increases. It opened *Catcher-Evader Games* and read the algorithm, its equilibrium-preservation lemma and the passage identifying the catcher’s resource budget with the security-game defender’s budget. In the project’s security-game example, the final budget is one and the coverage curve already has exponentially many bends before then. [Published algorithm](https://arxiv.org/abs/1602.01896)

At 23:24:22 the monitor’s final report described the restrictions as “With one defender resource, one target attacked per type, and only one slope-two entry,” and gave a lower bound of \(2^{h-1}\) successful Algorithm 3 calls. The main session received the report at 23:24:47. Two seconds later GPT-6.2 Astra summarized the result as holding “even with one defender resource.” At 23:55:10 it wrote the phrase into the project’s research priorities. The Kiro transcript records Claude Opus 5.5 reading that sentence on November 22 at 02:27:36.

At 03:15:08, in response to Vincent asking what to send a research agent, Kiro’s Opus proposed building the alternating switch. It wrote that this would show Conitzer’s problem was “at least as hard as ARRIVAL.” At 04:46:03 Vincent supplied the first worker’s report, which conjectured that a small network could not alternate between two exits often enough. Opus revisited that conjecture, tested two parallel copies of a counting network, and at 05:38:49 opened the market-to-game theorem specifying “exactly one defender resource.”

At 05:43:38 Kiro’s Opus used “even in games with one defender resource,” followed by “a polynomial algorithm for the game would then solve ARRIVAL.” At 05:49:10 the separate Claude Code session rephrased those clauses as “even with one defender resource” and “would then also solve ARRIVAL.” At 10:02:48 Kim used “even with just one defender resource” and “would also solve ARRIVAL in polynomial time.” Kim’s post gives no model or prompt. Its publication time is 4 hours 19 minutes after the Kiro report to the nearest minute. [Kim’s post](https://x.com/JeonseongKim/status/2124443473428537685)

These records place the project’s construction and internal review before Kim’s public suggestion. His post predates the creation of the public GitHub repository. The records do not date Kim’s private work or establish who first conceived the comparison.

This public excerpt gives the chronology reported in the project records. The reduction appears in Chapter 4 and Appendix C of [the original book](../main.pdf).
