"""Exact symbolic checks for the weighted-selection research report.

Install the sole dependency with: python -m pip install sympy==1.14.0
Then run: python verify_exact.py
These checks supplement the written proof; they do not replace its geometric
or compactness arguments, and they do not verify the entire theorem in Lean.
"""
import sympy as sp


def check(label, expression):
    result = sp.factor(expression)
    if result != 0:
        raise AssertionError(f"{label}: {result}")
    print(f"PASS: {label}")


a, b, delta = sp.symbols("a b delta", real=True)
r = (1 + delta) / 2
x, y = 1 + sp.Rational(3, 10) * delta, 1 - sp.Rational(3, 10) * delta
P = x * y
Q = sp.Rational(7, 3) - sp.Rational(21, 100) * delta**2
h = P - a * y - b * x
F = (a + b)**2 + sp.Rational(4, 3) * (a + b) - delta * (a - b) - sp.Rational(7, 3) - delta**2
rhs = -sp.Rational(121, 100) * delta**2 * P - h * (Q + a*x + b*y) - a*b*(x-y)**2
check("scalar certificate B", P * F - rhs)
check("expected affine certificate", P - r*y - (1-r)*x - sp.Rational(21,100)*delta**2)
g = (a+b)/2 + (r*(1-r) + ((1-r)*a+r*b)/2)/(1+(a+b)/2)
check("regression scalar cost conversion", 4*(1+(a+b)/2)*(g-sp.Rational(5,6))-F)
check("sharp scalar example", g.subs({delta:0,a:sp.Rational(1,2),b:sp.Rational(1,2)})-sp.Rational(5,6))
check("anisotropy gap coefficient", sp.Rational(121,100)/sp.Rational(33,5)-sp.Rational(11,60))

c, d = sp.symbols("c d", real=True)
check("equality obstruction square completion", 7*c*c-2*c*d-3*d*d - (sp.Rational(22,3)*c*c-3*(d+c/3)**2))
star_dual = ((d-c)**2+4*(1-d*d))/(2*(1-c*c))
check("star dual norm equality conversion", 2*(1-c*c)*(star_dual-3)-(7*c*c-2*c*d-3*d*d-2))

t = sp.symbols("t", nonnegative=True)
f = t/2+(1+t)/(4+2*t)
check("isotropic monotonicity", sp.diff(f,t)-sp.Rational(1,2)-1/(2*(t+2)**2))
check("isotropic saturation", f.subs(t,1)-sp.Rational(5,6))

h11, h12, h22 = sp.symbols("h11 h12 h22", real=True)
H = sp.Matrix([[h11,h12],[h12,h22]])
A = H.adjugate()/sp.trace(H)
check("adjugate trace", sp.trace(A)-1)
check("determinant over trace covariance cost", sp.trace(A*H*A.T)-H.det()/sp.trace(H))

ux = sp.symbols("u0:6", real=True)
wx = sp.symbols("w0:6", real=True)
q = sp.symbols("q0:3", real=True)
u = [sp.Matrix(ux[2*i:2*i+2]) for i in range(3)]
w = [sp.Matrix(wx[2*i:2*i+2]) for i in range(3)]
gram = sp.zeros(2)
cross = sp.zeros(2)
for i in range(3):
    gram += q[i]*u[i]*u[i].T
    cross += q[i]*w[i]*u[i].T
pair_numerator = sp.zeros(2)
pair_denominator = 0
for i,j in [(0,1),(0,2),(1,2)]:
    U = sp.Matrix.hstack(u[i],u[j])
    W = sp.Matrix.hstack(w[i],w[j])
    det = U.det()
    pair_denominator += q[i]*q[j]*det**2
    pair_numerator += q[i]*q[j]*det*W*U.adjugate()
check("Cauchy-Binet pair weights", gram.det()-pair_denominator)
for i in range(2):
    for j in range(2):
        check(f"weighted-fit interpolation entry ({i},{j})", (cross*gram.adjugate()-pair_numerator)[i,j])

vertices = [sp.Matrix([1,0]),sp.Matrix([-sp.Rational(1,2),sp.sqrt(3)/2]),sp.Matrix([-sp.Rational(1,2),-sp.sqrt(3)/2])]
check("lower construction centered", sum((v[0] for v in vertices),sp.Integer(0)))
check("lower construction centered second coordinate", sum((v[1] for v in vertices),sp.Integer(0)))
for i,j in [(0,1),(0,2),(1,2)]:
    mid=(vertices[i]+vertices[j])/2
    check(f"lower construction edge midpoint ({i},{j})", mid.dot(mid)-sp.Rational(1,4))

print("All exact symbolic checks passed.")
