from fractions import Fraction as F
import math
T=[(3906748086,8992695531,10515596180),(2312248264,15340997855,29471737793),(1402286665,25730180724,42934365099),(881725356,41909578246,58204231966),(578197906,65851089563,69037621310),(396324613,99481037884,78873099189),(283911191,144325727458,84856120711),(212206188,201105762729,88396082127),(165097686,269345996903,88303382125),(133347132,347089554156,85472321255),(111522114,430806704415,78899184238),(96349355,515561896511,70353471918),(85815639,595448778546,58838976615),(78667711,664241383483,44421321106),(74129565,716160577112,30462865791),(71741310,746637295669,5959622577)]
D=10**25
def series(z,m):
    S=sum(2*F(1,2*k+1)*z**(2*k+1) for k in range(m)); Tl=2*z**(2*m+1)/((2*m+1)*(1-z*z))
    return S,S+Tl
def enc(y,m=22):
    z=(y-1)/(y+1); lo,hi=series(z,m)
    L=math.floor(lo*D); H=math.ceil(hi*D)
    assert F(L,D)<=lo and hi<=F(H,D)
    return z,L,H
def fr(q): return f"({q.numerator} / {q.denominator} : ℝ)" if q.denominator!=1 else f"({q.numerator} : ℝ)"
out=[]
def lemma(name,y,m=22):
    z,L,H=enc(y,m)
    out.append(f"""set_option maxHeartbeats 4000000 in
lemma {name} : ({L} / 10 ^ 25 : ℝ) ≤ Real.log {fr(y)} ∧ Real.log {fr(y)} ≤ {H} / 10 ^ 25 := by
  have h := log_series_bounds {fr(z)} (by norm_num) (by norm_num) {m}
  rw [show (1 + {fr(z)}) / (1 - {fr(z)}) = {fr(y)} by norm_num] at h
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]
""")
    return L,H
bounds={}
bounds['two']=lemma("log2_enc",F(2))
ks=[]
for j,(a,b,c) in enumerate(T):
    v=F(b-a,4*10**12); k=0
    while v*2**k<1: k+=1
    y=v*2**k; assert 1<=y<2
    ks.append((k,y))
    bounds[j]=lemma(f"logy_enc_{j}",y)
    # Lk lemma
    out.append(f"""lemma Lk_{j} : Lk {j} = Real.log {fr(y)} - {k} * Real.log 2 := by
  have : (B {j} - A {j}) / 4 = {fr(y)} / 2 ^ {k} := by
    simp only [B, A, tb, ta, ent, table1]; norm_num
  rw [Lk, this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
""")
bounds['a']=lemma("log65_enc",F(6,5))
bounds['l']=lemma("log3720_enc",F(37,20))
open('gen/a10_lemmas.lean','w').write("\n".join(out))
# numeric sanity
import mpmath
mpmath.mp.dps=40
S=F(0);I_lo=F(0);I_hi=F(0)
L2lo,L2hi=F(bounds['two'][0],D),F(bounds['two'][1],D)
for j,(a,b,c) in enumerate(T):
    w=(S+F(c,10**12))**2-S**2; S+=F(c,10**12)
    k,y=ks[j]
    lo=F(bounds[j][0],D)-k*L2hi; hi=F(bounds[j][1],D)-k*L2lo
    I_lo+=w*lo; I_hi+=w*hi
print(float(I_lo),float(I_hi), I_lo> F(-2126593445148,10**12), I_hi< F(-2126593445147,10**12))
print(ks)
