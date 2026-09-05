"""Exact interval-AD feasibility only; derivative/bridge not Lean-verified.

Bounded to 2047 box evaluations, sequential, with outward rounding after
each operation. No generated Lean files and no proof authority.
"""
from fractions import Fraction as F
import json
import sys
import evaluate_lr_upper_k_fast_points as exact
from types import SimpleNamespace

def rounded(value, bits=24):
    d=2**bits
    lo,hi=value.lower*d,value.upper*d
    return exact.Enclosure(F(lo.numerator//lo.denominator,d),
                           F(-((-hi.numerator)//hi.denominator),d))

def auto_sqrt(fuel, value):
    assert 0 <= value.lower <= value.upper
    def bracket(x):
        lo,hi=F(0),max(F(1),x)
        for _ in range(fuel):
            mid=(lo+hi)/2
            if mid*mid <= x: lo=mid
            else: hi=mid
        return lo,hi
    return exact.Enclosure(bracket(value.lower)[0],bracket(value.upper)[1])

def sqrt_check(value, root, positive_lower=False):
    return (0 <= value.lower <= value.upper and 0 <= root.lower <= root.upper
            and root.lower**2 <= value.lower and value.upper <= root.upper**2
            and (not positive_lower or root.lower > 0))

def log_check(value, cert):
    def endpoint(x,c):
        return 1 <= c.mantissa < 2 and x == F(2)**c.exponent*c.mantissa
    return (0 < value.lower <= value.upper and
            endpoint(value.lower,cert.lower) and endpoint(value.upper,cert.upper))

def inverse_positive(a):
    assert a.lower > 0
    return exact.Enclosure(1/a.upper,1/a.lower)

m=SimpleNamespace(I=exact.Enclosure,point=lambda x:exact.point(F(x)),
    add=exact.add,sub=exact.sub,mul=exact.mul,neg=exact.neg,scale=exact.scale,
    inv_positive=inverse_positive,auto_sqrt=auto_sqrt,sqrt_check=sqrt_check,
    auto_log=exact.auto_log_interval_certificate,log_check=log_check,
    log_eval=exact.log_interval_enclosure)

def natural_q(value):
    root=auto_sqrt(20,m.sub(m.point(1),value))
    lower=m.scale(F(1,2),m.sub(m.point(1),root))
    upper=m.scale(F(1,2),m.add(m.point(1),root))
    lc,uc=m.auto_log(16,lower),m.auto_log(16,upper)
    assert sqrt_check(m.sub(m.point(1),value),root,positive_lower=True)
    assert log_check(lower,lc) and log_check(upper,uc)
    ll,ul=m.log_eval(8,lc),m.log_eval(8,uc)
    q=m.neg(m.add(m.mul(lower,ll),m.mul(upper,ul)))
    qp=m.scale(F(1,4),m.mul(m.sub(ul,ll),inverse_positive(root)))
    return rounded(q),rounded(qp),(root,lc,uc)

p=SimpleNamespace(rounded=rounded,natural_q=natural_q)

def rd(i): return p.rounded(i, 32)
def add(a,b): return rd(m.add(a,b))
def mul(a,b):
    products=[a.lower*b.lower,a.lower*b.upper,a.upper*b.lower,a.upper*b.upper]
    return rd(m.I(min(products),max(products)))
def inv(a):
    assert a.lower > 0
    return rd(m.inv_positive(a))

class D:
    def __init__(self, v, dk=None, dc=None):
        self.v = v if isinstance(v,m.I) else m.point(v)
        self.d = (dk or m.point(0), dc or m.point(0))
    def __add__(self,o):
        o = lift(o)
        return D(add(self.v,o.v),*(add(a,b) for a,b in zip(self.d,o.d)))
    __radd__ = __add__
    def __neg__(self): return D(m.neg(self.v),*(m.neg(a) for a in self.d))
    def __sub__(self,o): return self+-lift(o)
    def __rsub__(self,o): return lift(o)+-self
    def __mul__(self,o):
        o=lift(o)
        return D(mul(self.v,o.v),*(add(mul(a,o.v),mul(self.v,b)) for a,b in zip(self.d,o.d)))
    __rmul__ = __mul__
    def inverse(self):
        v=inv(self.v)
        return D(v,*(m.neg(mul(mul(v,v),a)) for a in self.d))
    def __truediv__(self,o): return self*lift(o).inverse()
    def __rtruediv__(self,o): return lift(o)*self.inverse()

def lift(x): return x if isinstance(x,D) else D(x)
def compose(x,v,slope): return D(rd(v),*(mul(slope,a) for a in x.d))
def log(x):
    x=lift(x)
    cert=m.auto_log(16,x.v)
    assert m.log_check(x.v,cert)
    return compose(x,m.log_eval(8,cert),inv(x.v))
def sqrt(x):
    v=m.auto_sqrt(20,x.v)
    assert m.sqrt_check(x.v,v,positive_lower=True)
    return compose(x,v,inv(m.scale(2,v)))
def qpair(x):
    q,qp,_=p.natural_q(x.v)
    # Q''(t) = (2*t*Q'(t)-1)/(4*t*(1-t)).
    numerator=m.sub(m.scale(2,mul(x.v,qp)),m.point(1))
    denominator=m.scale(4,mul(x.v,m.sub(m.point(1),x.v)))
    qpp=mul(numerator,inv(denominator))
    return compose(x,q,qp),compose(x,qp,qpp)

def target(kl,kh,cl,ch):
    k=D(m.I(kl,kh),m.point(1),m.point(0))
    chi=D(m.I(cl,ch),m.point(0),m.point(1))
    s=D(F(1,16)); e=s*k; y=chi*e; x=1-y
    v=sqrt((1-e)/x)
    qs,qps=qpair(s); qe,_=qpair(e); qy,_=qpair(y)
    qbe,qpbe=qpair(s+(1-s)*e); qby,qpby=qpair(s+(1-s)*y)
    w=qs-s*qps
    shared=qby+qbe/v-s*(1-y)*qpby-s*(1-e)*qpbe/v
    c=shared-qy-qe/v-4*v*x/(1+v)*w
    g=(1+1/v)*(log(1+v)-log(2))-log(v)
    psi=g+shared-4/(1+v)*w
    b=log(1+v)-F(1,2)*log(s+(1-s)*e)
    yy=1+1/k-s
    d=F(1,2)*log((1+yy)/2)+(yy-1)/(3*yy+1)
    return b*c+d*psi

def lower(box):
    kl,kh,cl,ch=box; km=(kl+kh)/2; cm=(cl+ch)/2
    whole=target(*box); center=target(km,km,cm,cm)
    bound=center.v.lower
    costs=[max(abs(slope.lower),abs(slope.upper))*width
           for slope,width in zip(whole.d,((kh-kl)/2,(ch-cl)/2))]
    return bound-sum(costs),costs

def self_test():
    # Independent floating-point formula and finite differences are diagnostic
    # only. They are never used to accept a box.
    import math
    def direct(k,chi):
        s=1/16; e=s*k; y=chi*e; x=1-y
        v=math.sqrt((1-e)/x)
        def q(t):
            r=math.sqrt(1-t); a=(1-r)/2; b=(1+r)/2
            return -a*math.log(a)-b*math.log(b)
        def qp(t):
            r=math.sqrt(1-t)
            return math.log((1+r)/(1-r))/(4*r)
        w=q(s)-s*qp(s)
        def a(t): return q(s+(1-s)*t)-s*(1-t)*qp(s+(1-s)*t)-w
        ay,ae=a(y),a(e)
        kap=(1-v)**2/(v*(1+v)); delta=(1-v*x)/(1+v)
        g=(1+1/v)*(math.log(1+v)-math.log(2))-math.log(v)
        c=ay-q(y)+(ae-q(e))/v+(kap+4*delta)*w
        psi=g+ay+ae/v+kap*w
        b=math.log(1+v)-math.log(s+(1-s)*e)/2
        yy=(s+(1-s)*e)/e
        d=math.log((1+yy)/2)/2+(yy-1)/(3*yy+1)
        return b*c+d*psi
    for k in (F(2),F(3),F(4)):
        for chi in (F(1,4),F(3,8),F(1,2)):
            result=target(k,k,chi,chi)
            value=direct(float(k),float(chi))
            assert float(result.v.lower)<=value<=float(result.v.upper)
            eps=1e-5
            slopes=((direct(float(k)+eps,float(chi))-direct(float(k)-eps,float(chi)))/(2*eps),
                    (direct(float(k),float(chi)+eps)-direct(float(k),float(chi)-eps))/(2*eps))
            for enclosure,slope in zip(result.d,slopes):
                assert float(enclosure.lower)-1e-8<=slope<=float(enclosure.upper)+1e-8
    print(json.dumps({'diagnosticTests':'9 independent values and 18 finite-difference slopes passed'}),flush=True)

if __name__=='__main__':
    if '--self-test' in sys.argv: self_test()
    pending=[(F(2),F(4),F(1,4),F(1,2))]
    leaves=0; tested=0; minimum=None; max_pending=1
    accepted=[]
    while pending and tested < 2047:
        box=pending.pop(); tested+=1
        try: margin,costs=lower(box)
        except AssertionError: margin,costs=F(-1),None
        if margin>0:
            leaves+=1
            accepted.append((box,margin))
            minimum=margin if minimum is None else min(minimum,margin)
        else:
            kl,kh,cl,ch=box
            split_k = costs[0]>=costs[1] if costs and '--smart' in sys.argv else kh-kl>=8*(ch-cl)
            if split_k:
                mid=(kl+kh)/2
                pending.extend([(kl,mid,cl,ch),(mid,kh,cl,ch)])
            else:
                mid=(cl+ch)/2
                pending.extend([(kl,kh,cl,mid),(kl,kh,mid,ch)])
        max_pending=max(max_pending,len(pending))
        if tested%100==0:
            print(json.dumps({'tested':tested,'leaves':leaves,'pending':len(pending)}),flush=True)
    if not pending:
        assert sum((b[1]-b[0])*(b[3]-b[2]) for b,_ in accepted)==F(1,2)
        for i,(a,_) in enumerate(accepted):
            for b,_ in accepted[i+1:]:
                assert a[1]<=b[0] or b[1]<=a[0] or a[3]<=b[2] or b[3]<=a[2]
    report={'status':'exact-AD-experiment-NOT-Lean-proof','tested':tested,
        'leaves':leaves,'pending':len(pending),'completeCandidateCover':not pending,
        'maxPending':max_pending,'minLowerDiagnostic':float(minimum) if minimum else None}
    if '--export' in sys.argv:
        report['boxes']=[{'kChiBox':list(map(str,b)),'lower':str(v)} for b,v in accepted]
    print(json.dumps(report),flush=True)
