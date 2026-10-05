"""Exact Newton-polynomial certificates for small Chebyshev quadratures."""
import sympy as s
x = s.symbols('x')
for c in range(2, 10):
    e = [s.Rational(1)]
    def power(k):
        return s.Rational(c, k + 1) if k % 2 == 0 else s.S.Zero
    for k in range(1, c + 1):
        e.append(s.expand(sum((-1)**(j - 1) * e[k - j] * power(j)
                              for j in range(1, k + 1)) / k))
    poly = s.Poly(sum((-1)**k * e[k] * x**(c - k)
                      for k in range(c + 1)), x)
    factors = s.factor_list(poly)[1]
    rational_roots = s.polys.polytools.ground_roots(poly)
    print(f'c={c}: {s.factor(poly.as_expr())}')
    print('  irreducible factor degrees:', [f.degree() for f, _ in factors])
    print('  rational roots:', rational_roots)
    assert sum(rational_roots.values()) < c
