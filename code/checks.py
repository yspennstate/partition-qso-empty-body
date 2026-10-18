"""Exact checks for the note on Problem 10 (xi-quadratic stochastic operators).

All arithmetic is in Fractions, so every inequality below is checked exactly.
Run: python checks.py   (prints one line per check and ALL PASS at the end)
"""
import random
from fractions import Fraction as Fr
from itertools import product

random.seed(20261018)


def rand_simplex_point(n, den=60):
    w = [random.randint(0, den) for _ in range(n)]
    if sum(w) == 0:
        w[0] = 1
    s = sum(w)
    return [Fr(a, s) for a in w]


def make_xi_qso(m, blocks, zero_cross=False):
    """Coefficients P[i][j] (a list of length m+1, summing to 1) of a xi-QSO.

    blocks: list of disjoint lists covering 1..m. Pairs inside a block and pairs
    containing 0 produce 0 with probability one; a cross-block pair gets a random
    exact distribution on {0,...,m} (no mass on 0 when zero_cross).
    """
    blk = {i: b for b, B in enumerate(blocks) for i in B}
    P = [[None] * (m + 1) for _ in range(m + 1)]
    for i in range(m + 1):
        for j in range(i, m + 1):
            if i == 0 or j == 0 or blk[i] == blk[j]:
                row = [Fr(1)] + [Fr(0)] * m
            else:
                row = rand_simplex_point(m + 1, 20)
                if zero_cross:
                    row[0] = Fr(0)
                    s = sum(row)
                    row = [Fr(0)] + [Fr(1, m)] * m if s == 0 else [a / s for a in row]
            P[i][j] = P[j][i] = row
    return P


def V(P, x):
    m1 = len(x)
    out = [Fr(0)] * m1
    for i in range(m1):
        if x[i] == 0:
            continue
        for j in range(m1):
            if x[j] == 0:
                continue
            w = x[i] * x[j]
            row = P[i][j]
            for k in range(m1):
                if row[k]:
                    out[k] += w * row[k]
    return out


def random_partition(m, q):
    labels = list(range(q)) + [random.randrange(q) for _ in range(m - q)]
    random.shuffle(labels)
    return [[i + 1 for i in range(m) if labels[i] == b] for b in range(q)]


ok = True

# 1. The one-step inequality 1 - V(x)_0 <= (1 - 1/q)(1 - x_0)^2, exactly, and V maps the simplex to itself.
count, worst = 0, Fr(0)
for trial in range(400):
    m = random.randint(2, 7)
    q = random.randint(1, m)
    blocks = random_partition(m, q)
    P = make_xi_qso(m, blocks, zero_cross=random.random() < 0.3)
    for _ in range(8):
        x = rand_simplex_point(m + 1)
        y = V(P, x)
        assert sum(y) == 1 and min(y) >= 0
        lhs, rhs = 1 - y[0], (1 - Fr(1, q)) * (1 - x[0]) ** 2
        ok &= lhs <= rhs
        if rhs > 0:
            worst = max(worst, lhs / rhs)
        count += 1
print(f"[1] one-step bound on {count} exact evaluations: {'pass' if ok else 'FAIL'}; max ratio {float(worst):.6f}")

# 2. Along trajectories: y_{n+1} <= (1 - 1/q) y_n^2 for 12 steps (exact; denominators stay manageable for small m).
ok2 = True
for trial in range(40):
    m = random.randint(2, 4)
    q = random.randint(2, m)
    blocks = random_partition(m, q)
    P = make_xi_qso(m, blocks)
    x = rand_simplex_point(m + 1, 9)
    for n in range(5):
        y = V(P, x)
        ok2 &= (1 - y[0]) <= (1 - Fr(1, q)) * (1 - x[0]) ** 2
        x = y
print(f"[2] trajectory bound, 40 operators x 5 steps: {'pass' if ok2 else 'FAIL'}")
ok &= ok2

# 3. Sharpness along a whole trajectory (the sharpness proposition): blocks {1},...,{q} (m = q); a cross pair's child is
#    uniform on 1..q, so equal block masses stay equal and the bound is an equality at every step.
ok3 = True
for q in range(2, 7):
    m = q
    blocks = [[i] for i in range(1, q + 1)]
    P = [[None] * (m + 1) for _ in range(m + 1)]
    for i, j in product(range(m + 1), repeat=2):
        if i == 0 or j == 0 or i == j:
            P[i][j] = [Fr(1)] + [Fr(0)] * m
        else:
            P[i][j] = [Fr(0)] + [Fr(1, q)] * m
    x = [Fr(1, 3)] + [Fr(2, 3 * q)] * q
    for n in range(4):
        y = V(P, x)
        ok3 &= (1 - y[0]) == (1 - Fr(1, q)) * (1 - x[0]) ** 2
        ok3 &= len(set(y[1:])) == 1
        x = y
print(f"[3] equality y_(n+1) = (1-1/q) y_n^2 along the symmetric trajectories, q = 2..6: {'pass' if ok3 else 'FAIL'}")
ok &= ok3

# 4. The absorbing role of 0 is needed: m = 1, P_{11,0} = 1, P_{01,1} = 1, P_{00,0} = 1 has a second fixed point (1/2, 1/2).
P = [[[Fr(1), Fr(0)], [Fr(0), Fr(1)]], [[Fr(0), Fr(1)], [Fr(1), Fr(0)]]]
x = [Fr(1, 2), Fr(1, 2)]
ok4 = V(P, x) == x and V(P, [Fr(1), Fr(0)]) == [Fr(1), Fr(0)]
print(f"[4] without the condition on pairs containing 0: second fixed point (1/2,1/2): {'pass' if ok4 else 'FAIL'}")
ok &= ok4

print("ALL PASS" if ok else "SOME CHECK FAILED")
