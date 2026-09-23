from mpmath import mp, mpf, log, sqrt, atan, pi
mp.dps=25
T=[(3906748086,8992695531,10515596180),(2312248264,15340997855,29471737793),(1402286665,25730180724,42934365099),(881725356,41909578246,58204231966),(578197906,65851089563,69037621310),(396324613,99481037884,78873099189),(283911191,144325727458,84856120711),(212206188,201105762729,88396082127),(165097686,269345996903,88303382125),(133347132,347089554156,85472321255),(111522114,430806704415,78899184238),(96349355,515561896511,70353471918),(85815639,595448778546,58838976615),(78667711,664241383483,44421321106),(74129565,716160577112,30462865791),(71741310,746637295669,5959622577)]
T=[(mpf(a)/10**12,mpf(b)/10**12,mpf(c)/10**12) for a,b,c in T]
al=mpf(3)/40
def Uw(a,b,t):
    if a<=t<=b: return log((b-a)/4)
    return log((abs(t-(a+b)/2)+sqrt((t-a)*(t-b)))/2)
def Icl(t,c):  # ∫_0^c log(t+u^2)
    if t==0: return 2*c*log(c)-2*c
    return c*log(t+c*c)-2*c+2*sqrt(t)*atan(c/sqrt(t))
def B(l,r):
    U=sum(c*max(Uw(a,b,l),Uw(a,b,r)) for a,b,c in T)
    V=2*pi*sqrt(l)+Icl(l,1)-6*Icl(r,al)
    return 2*U-V
M0=mpf(-1329)/200; target=M0-mpf('0.0002')
# greedy: from l, find largest r (by bisection over dyadic steps) with B<=target
import sys
pts=[mpf(0)]; l=mpf(0)
if 1: pass
bps=sorted([x for a,b,c in T for x in (a,b)])
while False:
    step=mpf(2)-l
    while B(l,l+step)>target: step/=2
    # extend by doubling-ish search
    r=min(l+step,mpf(2))
    pts.append(r); l=r
print(len(pts)-1)
import pickle
print([float(p) for p in pts[:10]], [float(p) for p in pts[-5:]])
def F(t): 
    U=sum(c*Uw(a,b,t) for a,b,c in T); return 2*U-(2*pi*sqrt(t)+Icl(t,1)-6*Icl(t,al))
for t in ['0','1e-6','1e-4','1e-3','0.01','0.05','0.07','0.1','0.3','0.5','0.62','0.8','1','1.5','2']:
    print(t, float(F(mpf(t))))
