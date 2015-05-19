## Calculate Silverman's upper bound on the difference betwen naive and canonical heights of points on an elliptic curve

x=var('x')
K.<a> = NumberField(x^2-x-1)

E = EllipticCurve(K,[0,a+1,a,6*a-7,10*a-15])   ## given elliptic curve

def h_inf(x):
    return (1/K.degree())*((1)*log(max(1,x.abs()))+(1)*log(max(1,x.abs(i=1))))

def h(D):
    sum=0
    for t in range(len(D.factor())):
       n_p=1
       n=D.factor()[t][0].norm()%5
       if n==0 or n==2 or n==3:
           n_p=2   
       x_v=(D.factor()[t][0].norm())^(D.factor()[t][1]/n_p)
       y=n_p*max(0,log(x_v))
       sum+=y
    sum+= max(0,log(D.abs())) + max(0,log(D.abs(i=1)))
    
    sum=.5*sum
    return float(sum)

def mu(E):
    if E.b2()==0:
        q = 0
    else:
        q = 1
    return (1/12)*h(E.discriminant()) + (1/12)*h_inf(E.j_invariant()) + (1/2)*h_inf(E.b2()/12) + (1/2)*log(q)

  
upper_bound = (1/12)*h(E.j_invariant()) + 2*mu(E) + 1.922
print upper_bound
