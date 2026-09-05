"""Bounded natural-interval alternative; exact arithmetic, not a proof."""
from fractions import Fraction as F
import json
import sys
import fixed16_c_only_grouped_21_probe as m

def rounded(value, bits=24):
    d = 2**bits
    lo, hi = value.lower*d, value.upper*d
    return m.I(F(lo.numerator//lo.denominator,d), F(-((-hi.numerator)//hi.denominator),d))

def natural_q(value):
    root = m.auto_sqrt(20, m.sub(m.point(1),value))
    lower = m.scale(F(1,2),m.sub(m.point(1),root))
    upper = m.scale(F(1,2),m.add(m.point(1),root))
    lc, uc = m.auto_log(16,lower), m.auto_log(16,upper)
    assert m.sqrt_check(m.sub(m.point(1),value),root,positive_lower=True)
    assert m.log_check(lower,lc) and m.log_check(upper,uc)
    ll, ul = m.log_eval(8,lc),m.log_eval(8,uc)
    q = m.neg(m.add(m.mul(lower,ll),m.mul(upper,ul)))
    qp = m.scale(F(1,4),m.div(m.sub(ul,ll),root))
    return rounded(q),rounded(qp),(root,lc,uc)

def calculate(depth):
    width=F(1,2**depth)
    box=m.Box(F(1,16),F(1,16),F(3)-width,F(3)+width,
              F(3,8)-width/8,F(3,8)+width/8)
    n=m.basic_nodes(box,20)
    s,e,y,v,x = (n[k] for k in ('s','e','y0','v','x'))
    by=m.add(s,m.mul(m.sub(m.point(1),s),y))
    inputs={'s':s,'e':e,'y':y,'be':n['be'],'by':by}
    qs={key:natural_q(value) for key,value in inputs.items()}
    w=m.sub(qs['s'][0],m.mul(s,qs['s'][1]))
    def a(key,prob):
        return m.sub(m.sub(qs[key][0],m.mul(m.mul(s,m.sub(m.point(1),prob)),qs[key][1])),w)
    ay,ae=a('by',y),a('be',e)
    cy,ce=m.sub(ay,qs['y'][0]),m.sub(ae,qs['e'][0])
    oneplus=m.add(m.point(1),v)
    kappa=m.div(m.mul(m.sub(m.point(1),v),m.sub(m.point(1),v)),m.mul(v,oneplus))
    delta=m.div(m.sub(m.point(1),m.mul(v,x)),oneplus)
    g0,ok=m.g0_interval(8,16,v)
    assert ok
    g0=rounded(g0)
    psi=m.add(m.add(m.add(g0,ay),m.div(ae,v)),m.mul(kappa,w))
    c=m.add(m.add(cy,m.div(ce,v)),m.mul(m.add(kappa,m.scale(F(4),delta)),w))
    bounds={'c':m.I(F(-370563,16777216),F(-91261,4194304)),
            'psi':m.I(F(1138331,4194304),F(4596343,16777216))}
    covers={key:bounds[key].lower<=value.lower and value.upper<=bounds[key].upper
            for key,value in [('c',c),('psi',psi)]}
    return inputs,qs,n,c,psi,covers

def export():
    inputs,qs,n,c,psi,covers=calculate(8)
    def frac(x): return [x.numerator,x.denominator]
    def inter(x): return [frac(x.lower),frac(x.upper)]
    def log(x):
        return [[x.lower.exponent,frac(x.lower.mantissa)],
                [x.upper.exponent,frac(x.upper.mantissa)]]
    payload={key:{'input':inter(inputs[key]),'q':inter(q),'qp':inter(qp),
             'sqrt':inter(cert[0]),'lowerLog':log(cert[1]),'upperLog':log(cert[2])}
             for key,(q,qp,cert) in qs.items()}
    print(json.dumps({'q':payload,'v':inter(n['v']),
        'c':inter(rounded(c)),'psi':inter(rounded(psi)),
        'g0':inter(rounded(m.g0_interval(8,16,n['v'])[0])),
        'logV':log(m.auto_log(16,n['v'])),
        'logOnePlus':log(m.auto_log(16,m.add(m.point(1),n['v']))),
        'logTwo':log(m.auto_log(16,m.point(2)))}))

def sharp_d1(depth):
    width=F(1,2**depth)
    k=m.I(F(3)-width,F(3)+width)
    y=m.sub(m.add(m.point(1),m.inv_positive(k)),m.point(F(1,16)))
    mean=m.scale(F(1,2),m.add(m.point(1),y))
    cert=m.auto_log(16,mean)
    assert m.log_check(mean,cert)
    return rounded(m.add(m.scale(F(1,2),m.log_eval(8,cert)),
        m.div(m.sub(y,m.point(1)),m.add(m.scale(F(3),y),m.point(1)))))

def pilot_test():
    _,_,_,c,psi,_=calculate(8)
    c,psi,d=rounded(c),rounded(psi),sharp_d1(8)
    assert c==m.I(F(-12235,524288),F(-346487,16777216))
    assert psi==m.I(F(2277261,8388608),F(4595613,16777216))
    assert d==m.I(F(1003077,8388608),F(2012899,16777216))
    b_upper=F(23117261,16777216)
    margin=b_upper*c.lower+d.lower*psi.lower
    old_margin=b_upper*c.lower+F(1985895,16777216)*psi.lower
    assert c.upper<0 and psi.lower>0 and d.lower>0 and margin>0
    assert old_margin<0  # The tighter D1 identity is essential for this route.
    print(json.dumps({'status':'exact-precheck-not-Lean-proof',
        'depth':8,'additionalSubdivisions':0,'cornerMonotonicityUsed':False,
        'positiveRoundedMargin':str(margin),
        'oldD1RoundedMargin':str(old_margin),
        'checks':'literal bounds and both margin signs passed'}))

if __name__=='__main__' and sys.argv[1:]==['export']:
    export()
elif __name__=='__main__' and sys.argv[1:]==['test']:
    pilot_test()
elif __name__=='__main__':
    for depth in (8,10,12):
        _,_,_,c,psi,covers=calculate(depth)
        print(json.dumps({'depth':depth,'covers':covers,
            'cDiagnostic':[float(c.lower),float(c.upper)],
            'psiDiagnostic':[float(psi.lower),float(psi.upper)]}),flush=True)
