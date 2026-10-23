# Partition quadratic stochastic operators converge to the empty body

Yitzchak Shmalo

Paper: [paper/main.pdf](paper/main.pdf) (LaTeX source `paper/main.tex`).

## Result

An F-quadratic stochastic operator acts on the simplex over the types {0, 1, ..., m}, where 0 is the
empty body: parents of the same sex, or a pair containing 0, produce 0. Rozikov and Zhamilov proved that
every such operator has the unique fixed point e_0 = (1, 0, ..., 0) and that every trajectory converges
to it exponentially fast. Problem 10 of Ganikhodzhaev, Mukhamedov and Rozikov, *Quadratic stochastic operators
and processes: results and open problems* (arXiv:0902.4207), asks whether the same holds when the two sexes are
replaced by the blocks E_1, ..., E_q of an arbitrary partition of {1, ..., m}, with same-block pairs
producing the empty body.

The answer is yes. If y = 1 - x_0 is the mass outside the empty body, every such operator V satisfies

    y(V(x)) <= (1 - 1/q) y(x)^2,

so e_0 is the unique fixed point and y(V^n(x)) <= c^(-1) (c y(x))^(2^n) with c = 1 - 1/q: convergence is
doubly exponential. For each q there are operators and trajectories along which the inequality is an
equality at every step. The requirement that pairs containing 0 produce 0 cannot be dropped: without it
the operator (x_0, x_1) -> (x_0^2 + x_1^2, 2 x_0 x_1) has a second, attracting fixed point (1/2, 1/2).

## Files

- `paper/main.pdf`, `paper/main.tex`: the paper.
- `code/checks.py`: exact rational checks of the one-step inequality on random operators, of the equality
  case and of the counterexample (`python checks.py`); `code/checks_output.txt` is its output.
- `lean/XiQSO.lean`: Lean 4 proofs (Mathlib) of the real-number deduction of the one-step inequality from
  the lower bound for the empty-body mass, of the iteration bound, and of the fixed-point step.
- `SHA256SUMS.txt`: checksums of the files above.
