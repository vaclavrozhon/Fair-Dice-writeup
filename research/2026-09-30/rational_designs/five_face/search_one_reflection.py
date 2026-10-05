"""Exact search of one reflection pair and two odd comparison columns.

Modular filters only discard specializations with no rational projective
root.  Surviving univariate quintics are factored over Q, so the height
of the parameter p is unrestricted.  This is a bounded experiment in r,s.
"""
from pathlib import Path
import argparse, itertools, json, math, time
import numpy as np
import sympy as sy

ap = argparse.ArgumentParser()
ap.add_argument('--max-den', type=int, default=300)
ap.add_argument('--max-prime', type=int, default=151)
args = ap.parse_args()
base = Path(__file__).parent
data = json.loads((base/'one_reflection_surface.json').read_text())
A,B,p = sy.symbols('A B p')
F = sy.sympify(data['poly'])
terms = [(t['powers'],t['coef']) for t in data['terms']]
filters = []
for ell in sy.primerange(7,args.max_prime):
    aa = (np.arange(ell,dtype=np.int64)**2 % ell)[:,None,None]
    bb = (np.arange(ell,dtype=np.int64)**2 % ell)[None,:,None]
    pp = np.arange(ell,dtype=np.int64)[None,None,:]
    value = np.zeros((ell,ell,ell),dtype=np.int64)
    lead = np.zeros((ell,ell),dtype=np.int64)
    for (i,j,k),co in terms:
        ab = (np.power(aa,i)*np.power(bb,j))%ell
        # Reduce every multiplication to avoid overflow at larger primes.
        value = (value + ((co%ell)*ab%ell)*np.power(pp,k)%ell)%ell
        if k==5:
            lead = (lead + (co%ell)*ab[:,:,0])%ell
    good = np.any(value==0,axis=2) | (lead==0)
    filters.append((int(ell),good))
filters.sort(key=lambda z: np.mean(z[1]))
print('filter densities',[(ell,float(np.mean(g))) for ell,g in filters],flush=True)

def square_root(q):
    if q<0:return None
    a,b=map(int,sy.fraction(q)); x,y=math.isqrt(a),math.isqrt(b)
    return sy.Rational(x,y) if x*x==a and y*y==b else None

def test_root(r,s,root):
    h=sy.Rational(5,6); q=h-root
    R=root/r; S=q/s
    if not (0<S<R<1):return None
    D=r*r*q-s*s*root
    W=h-4*root*q
    if not D or not W:return None
    z1=h*r*(q-s*s)/D
    z2=h*s*(r*r-root)/D
    lam2=((sy.Rational(2,5)*(z1*z1+z2*z2))-sy.Rational(1,3))/W
    lam=square_root(lam2)
    if lam is None:return {'r':str(r),'s':str(s),'p':str(root),'lambda_squared':str(lam2),'square':False}
    z=sy.Matrix([-z1,-z2,0,z2,z1])
    u=sy.Matrix([q,-root,2*(root-q),-root,q])
    cols=[z+lam*u,z-lam*u,sy.Matrix([-r,-s,0,s,r]),sy.Matrix([-R,-S,0,S,R])]
    for k in range(1,5):
        for inds in itertools.combinations(range(4),k):
            moment=sum(sy.prod(cols[j][i] for j in inds) for i in range(5))/5
            assert moment==(0 if k%2 else sy.Rational(1,k+1)),(inds,moment)
    monotone=all(-1<c[0] and c[4]<1 and all(c[i]<c[i+1] for i in range(4)) for c in cols)
    return {'r':str(r),'s':str(s),'p':str(root),'lambda_squared':str(lam2),'square':True,'monotone':monotone,'columns':[[str(x) for x in c] for c in cols]}

seen=surv=0; roots=[]; start=time.time()
for den in range(1,args.max_den+1):
    for a in range(math.ceil(.65*den),den):
        for b in range(math.ceil(.15*den),min(a,math.floor(.65*den)+1)):
            if math.gcd(math.gcd(a,b),den)!=1:continue
            seen+=1
            good=True
            for ell,table in filters:
                if den%ell==0:continue
                inv=pow(den,-1,ell)
                if not table[a*inv%ell,b*inv%ell]:good=False;break
            if not good:continue
            surv+=1
            r,s=sy.Rational(a,den),sy.Rational(b,den)
            poly=sy.Poly(F.subs({A:r*r,B:s*s}),p)
            fac=sy.factor_list(poly)[1]
            for f,e in fac:
                if f.degree()!=1:continue
                root=-f.nth(0)/f.nth(1)
                result=test_root(r,s,root)
                if result:
                    roots.append(result)
                    print('ROOT',json.dumps(result),flush=True)
    if den%25==0:
        print('progress',den,seen,surv,len(roots),'seconds',round(time.time()-start,1),flush=True)
    (base/'search_one_reflection.json').write_text(json.dumps({'max_den_finished':den,'seen':seen,'survivors':surv,'roots':roots},indent=2)+'\n')
