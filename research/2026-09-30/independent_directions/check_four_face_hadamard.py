"""Exact symbolic identities used by no_four_face_die_for_five.tex."""
import sympy as s
from itertools import combinations
H=s.Matrix([[-1,-1,-1],[-1,1,1],[1,-1,1],[1,1,-1]])
assert H.T*H==4*s.eye(3)
A=s.symbols('A0:3');B=s.symbols('B0:3');C=s.symbols('C0:3')
vecs=[H*s.Matrix([A[j],B[j],C[j]]) for j in range(3)]
triple=s.expand(sum(vecs[0][q]*vecs[1][q]*vecs[2][q] for q in range(4))/4)
wanted=-sum(C[i]*(A[j]*B[k]+B[j]*A[k]) for i in range(3) for j,k in [tuple(z for z in range(3) if z!=i)])
assert s.expand(triple-wanted)==0
b=s.symbols('b0:4')
M=s.Matrix(4,4,lambda i,j:0 if i==j else sum(b[k] for k in range(4) if k not in (i,j)))
e1=sum(b);e3=sum(s.prod(b[j] for j in S) for S in combinations(range(4),3));e4=s.prod(b)
positive=sum(b[i]**2*b[j]*b[k] for i in range(4) for j,k in combinations([z for z in range(4) if z!=i],2))
assert s.expand(e1*e3-4*e4-positive)==0
assert s.expand(M.det()+4*positive)==0
print('Hadamard orthogonality, triple moments, and determinant identity verified exactly.')
print('detM =',s.factor(M.det()))
