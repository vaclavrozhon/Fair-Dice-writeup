"""Exploratory Q2 root search of the one-pair surface (not a certificate).
The lambda-square test is evaluated at high-precision root approximations.
"""
import json,math
from pathlib import Path
from fractions import Fraction as Q
import sympy as sy
base=Path(__file__).parent
A,B,p,C=sy.symbols('A B p C');F=sy.sympify(json.loads((base/'one_reflection_surface.json').read_text())['poly'])
def v2(q):
 q=Q(q)
 if not q:return 999
 a,b=abs(q.numerator),q.denominator
 return (a&-a).bit_length()-(b&-b).bit_length()
def square(q):
 if not q:return False
 e=v2(q)
 if e%2:return False
 unit=q/2**e if e>=0 else q*2**(-e)
 return unit.numerator*pow(unit.denominator,-1,8)%8==1
def ev(cs,x,mod):
 y=0
 for c in cs:y=(y*x+c)%mod
 return y
tested=roots=good=0
for den in [2,4,8]:
 for a in range(1,2*den+1):
  for b in range(1,a):
   if math.gcd(math.gcd(a,b),den)!=1:continue
   r,s=Q(a,den),Q(b,den);aa=sy.Rational(r.numerator,r.denominator);bb=sy.Rational(s.numerator,s.denominator)
   poly=sy.Poly(F.subs({A:aa**2,B:bb**2,p:C/(den*den)}),C).clear_denoms()[1].primitive()[1]
   cs=[int(x) for x in poly.all_coeffs()]
   live=[0]
   for k in range(1,29):
    mod=2**k;half=mod//2
    live=[y for x in live for y in [x,x+half] if ev(cs,y,mod)==0]
    if not live:break
    if len(live)>20000:break
   tested+=1
   if not live:continue
   roots+=len(live)
   for c in live:
    pp=Q(c,den*den);q=Q(5,6)-pp;D=r*r*q-s*s*pp;W=Q(5,6)-4*pp*q
    if not D or not W:continue
    z1=Q(5,6)*r*(q-s*s)/D;z2=Q(5,6)*s*(r*r-pp)/D
    lam2=(Q(2,5)*(z1*z1+z2*z2)-Q(1,3))/W
    if square(lam2):
     good+=1
     print('POSSIBLE',r,s,'c',c,'precision',k,'lambda-v2',v2(lam2),flush=True)
     if good>=10:print('tested',tested,'roots',roots);raise SystemExit
 print('den',den,'tested',tested,'roots',roots,'square_candidates',good,flush=True)
