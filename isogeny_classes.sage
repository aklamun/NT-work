## Sage/Python code to enumerate isogeny classes of elliptic curves over cubic number fields using Billerey's algorithm

def ap(E,p):
    return E.change_ring(K.residue_field(p)).trace_of_frobenius()
x = var('x')
K.<a> = NumberField(x^3-x^2+1)      ## the cubic number field of discriminant -23
R.<x,z> = PolynomialRing(QQ,2)
primes_of_bounded_norm = []
P = Primes().first()
for j in K.primes_above(P):
    new_ind = 1
    for k in primes_of_bounded_norm:
        if j == k:
            new_ind = 0
    if new_ind:
        primes_of_bounded_norm.append(j)
for i in range(0,70):
    P = Primes().next(P)
    for j in K.primes_above(P):
        new_ind = 1
        for k in primes_of_bounded_norm:
            if j == k:
                new_ind = 0
        if new_ind:
            primes_of_bounded_norm.append(j)


@cached_function
def get_cached_stuff(K,G,prec):
    G = [u for u in G if u.multiplicative_order() == oo]
    bG = [u**12 for u in G]
    R = RealField(prec)
    C = ComplexField(prec)
    embs = list(K.embeddings(R))
    r = len(embs)
    s = len(G)+1-r
    embs.extend([psi for i,psi in enumerate(K.embeddings(C)) if \
        i >= r and 2.divides(i-r)])
    log_emb = lambda x: vector(log(abs(psi(x))) for psi in embs) \
        - log(abs(R(norm(x))))/(r+2*s)*vector([1]*(r+s))
    M = Matrix([log_emb(u) for u in bG])
    return len(G), G, M, log_emb

def canonical_model(E,G,prec=530):      ## calculate canonical model of elliptic curves
    E = E.global_minimal_model()
    K = E.base_ring()
    assert K.number_of_roots_of_unity() == 2
    ord,G,M,log_emb = get_cached_stuff(K,G,prec)
    De = log_emb(E.discriminant())
    v = M.solve_left(De, check=False)
    off = []
    for i in range(ord):
        off.append(-round(v[i]))
        if off[i] == -0.5: off[i] = 0.5
    u = prod(u**off[i] for i,u in enumerate(G))
    a1,a2,a3,a4,a6 = E.ainvs()
    a1,a2,a3,a4,a6 = u*a1,u*u*a2,u*u*u*a3,a4*u**4,a6*u**6
    P2 = K.ideal(2)
    P3 = K.ideal(3)
    a1p = a1.mod(P2)
    s = (a1p - a1)/K(2)
    sa1 = s*a1
    a2p = (a2 - sa1 - s**2).mod(P3)
    r = (a2p - a2 + sa1 + s**2)/K(3)
    ra1p = r*a1p
    a3p = (a3+ra1p).mod(P2)
    t = r*s + (a3p - a3 - ra1p)/K(2)
    a4p = a4 - s*a3 + 2*r*a2 - (t+r*s)*a1 + 3*r**2 - 2*s*t
    a6p = a6 + r*a4 + r**2*a2 + r**3 - t*a3 - t**2 - r*t*a1
    return  EllipticCurve(K, [a1p, a2p, a3p, a4p, a6p])


def billereyprimes(E):
    ## 1st step
    calc = abs(6*K.discriminant()*E.discriminant().norm())
    fact = calc.factor()
    S_1 = []
    for i in range(0,len(fact)):
        S_1.append(fact[i][0])
    ## 2nd step
    P = Primes().first()
    new_ind = 1
    for i in range(0,len(S_1)):
        if P == S_1[i]:
            new_ind = 0
    if new_ind == 0:
        while new_ind == 0:
            P = Primes().next(P)
            new_ind = 1
            for i in range(0,len(S_1)):
                if P == S_1[i]:
                    new_ind = 0
    L0 = P
    ## now compute B_L0
    if len(K.primes_above(L0)) == 2:
        idfact = K.ideal(L0).factor()
        q1 = idfact[0][0]
        v1 = idfact[0][1]
        q2 = idfact[1][0]
        v2 = idfact[1][1]
        Pq1(x) = x^2 - ap(E,q1)*x + q1.norm()
        Pq2(x) = x^2 - ap(E,q2)*x + q2.norm()
        ## now calculate Pq^(12v). note P^(r)(x^r) = (P*psi_r)(x)
        psi(x) = x^(12*v1)-1
        Pq1ast(x) = R(Pq1(z)).resultant(R(expand(psi(x/z)*z^(12*v1))),z)
        Pq1ast(x) = Pq1ast(x^(1/12))
        psi(x) = x^(12*v2)-1
        Pq2ast(x) = R(Pq2(z)).resultant(R(expand(psi(x/z)*z^(12*v1))),z)
        Pq2ast(x) = Pq2ast(x^(1/12))
        ## now compute PLstar
        PLstar(x) = R(Pq1ast(z)).resultant(R(expand(Pq2ast(x/z)*z^(Pq2ast(x).degree(x)))),z)
        ## now calculate B_L0 (note only need to sum over k=0,1 since integer part of d/2 is 1)
        k = var('k')
        terms = [PLstar(L0^(12*k)) for k in (0,1)];
        B_L0 = prod(terms)
    if len(K.primes_above(L0)) != 2:
        B_L0 = 0
    
    ## now compute B_L1
    ind = 0
    while ind == 0:
        new_ind = 0
        while new_ind == 0:
            P = Primes().next(P)
            new_ind = 1
            for i in range(0,len(S_1)):
                if P == S_1[i]:
                    new_ind = 0
        L1 = P
        if len(K.primes_above(L1)) == 2:
            idfact = K.ideal(L1).factor()
            q1 = idfact[0][0]
            v1 = idfact[0][1]
            q2 = idfact[1][0]
            v2 = idfact[1][1]
            Pq1(x) = x^2 - ap(E,q1)*x + q1.norm()
            Pq2(x) = x^2 - ap(E,q2)*x + q2.norm()
            ## now calculate Pq^(12v). note P^(r)(x^r) = (P*psi_r)(x)
            psi(x) = x^(12*v1)-1
            Pq1ast(x) = R(Pq1(z)).resultant(R(expand(psi(x/z)*z^(12*v1))),z)
            Pq1ast(x) = Pq1ast(x^(1/12))
            psi(x) = x^(12*v2)-1
            Pq2ast(x) = R(Pq2(z)).resultant(R(expand(psi(x/z)*z^(12*v1))),z)
            Pq2ast(x) = Pq2ast(x^(1/12))
            ## now compute PLstar
            PLstar(x) = R(Pq1ast(z)).resultant(R(expand(Pq2ast(x/z)*z^(Pq2ast(x).degree(x)))),z)
            ## now calculate B_L1 (note only need to sum over k=0,1 since integer part of d/2 is 1)
            k = var('k')
            terms = [PLstar(L1^(12*k)) for k in (0,1)];
            B_L1 = prod(terms)
        if len(K.primes_above(L1)) != 2:
            B_L1 = 0
        if B_L1 != 0:
            ind = 1
    
    ## now compute B_L2
    ind = 0
    while ind == 0:
        new_ind = 0
        while new_ind == 0:
            P = Primes().next(P)
            new_ind = 1
            for i in range(0,len(S_1)):
                if P == S_1[i]:
                    new_ind = 0
        L2 = P
        if len(K.primes_above(L2)) == 2:
            idfact = K.ideal(L2).factor()
            q1 = idfact[0][0]
            v1 = idfact[0][1]
            q2 = idfact[1][0]
            v2 = idfact[1][1]
            Pq1(x) = x^2 - ap(E,q1)*x + q1.norm()
            Pq2(x) = x^2 - ap(E,q2)*x + q2.norm()
            ## now calculate Pq^(12v). note P^(r)(x^r) = (P*psi_r)(x)
            psi(x) = x^(12*v1)-1
            Pq1ast(x) = R(Pq1(z)).resultant(R(expand(psi(x/z)*z^(12*v1))),z)
            Pq1ast(x) = Pq1ast(x^(1/12))
            psi(x) = x^(12*v2)-1
            Pq2ast(x) = R(Pq2(z)).resultant(R(expand(psi(x/z)*z^(12*v1))),z)
            Pq2ast(x) = Pq2ast(x^(1/12))
            ## now compute PLstar
            PLstar(x) = R(Pq1ast(z)).resultant(R(expand(Pq2ast(x/z)*z^(Pq2ast(x).degree(x)))),z)
            ## now calculate B_L2 (note only need to sum over k=0,1 since integer part of d/2 is 1)
            k = var('k')
            terms = [PLstar(L2^(12*k)) for k in (0,1)];
            B_L2 = prod(terms)
        if len(K.primes_above(L2)) != 2:
            B_L2 = 0
        if B_L2 != 0:
            ind = 1
    
    ## now compute B_L3
    ind = 0
    while ind == 0:
        new_ind = 0
        while new_ind == 0:
            P = Primes().next(P)
            new_ind = 1
            for i in range(0,len(S_1)):
                if P == S_1[i]:
                    new_ind = 0
        L3 = P
        if len(K.primes_above(L3)) == 2:
            idfact = K.ideal(L3).factor()
            q1 = idfact[0][0]
            v1 = idfact[0][1]
            q2 = idfact[1][0]
            v2 = idfact[1][1]
            Pq1(x) = x^2 - ap(E,q1)*x + q1.norm()
            Pq2(x) = x^2 - ap(E,q2)*x + q2.norm()
            ## now calculate Pq^(12v). note P^(r)(x^r) = (P*psi_r)(x)
            psi(x) = x^(12*v1)-1
            Pq1ast(x) = R(Pq1(z)).resultant(R(expand(psi(x/z)*z^(12*v1))),z)
            Pq1ast(x) = Pq1ast(x^(1/12))
            psi(x) = x^(12*v2)-1
            Pq2ast(x) = R(Pq2(z)).resultant(R(expand(psi(x/z)*z^(12*v1))),z)
            Pq2ast(x) = Pq2ast(x^(1/12))
            ## now compute PLstar
            PLstar(x) = R(Pq1ast(z)).resultant(R(expand(Pq2ast(x/z)*z^(Pq2ast(x).degree(x)))),z)
            ## now calculate B_L3 (note only need to sum over k=0,1 since integer part of d/2 is 1)
            k = var('k')
            terms = [PLstar(L3^(12*k)) for k in (0,1)];
            B_L3 = prod(terms)
        if len(K.primes_above(L3)) != 2:
            B_L3 = 0
        if B_L3 != 0:
            ind = 1
    ## 3rd step
    g = GCD(GCD(GCD(B_L0,B_L1),B_L2),B_L3)
    fact = factor(ZZ(g))
    S_2 = []
    for i in range(0,len(fact)):
        S_2.append(fact[i][0])
    S = []
    for i in range(0,len(S_1)):
        S.append(S_1[i])
    for i in range(0,len(S_2)):
        new_ind = 1
        for j in range(0,len(S)):
            if S_2[i] == S[j]:
                new_ind = 0
        if new_ind:
            S.append(S_2[i])
    S.sort()
    Ri = ZZ['X']; X = Ri.gen()
    disc = E.discriminant()
    vprimes = []
    w = []
    for i in range(0,100):
        p = primes_of_bounded_norm[i]
        if not p.divides(disc):
            vprimes.append(p)
            f = X^2 - ap(E,p)*X + p.norm()
            w.append(f)
    r = []
    for ell in S:
        new_ind = 1
        k = GF(ell)
        for i in range(0,len(vprimes)):
            q = vprimes[i]
            if not q.divides(disc) and not q.divides(ell):
                f = w[i]
                if f.change_ring(k).is_irreducible():
                    new_ind = 0
        if new_ind:
            r.append(ell)
    return r


def p_isogenous_curves(E, p, B=1000):
    E = E.change_ring(K)
    N = E.conductor()
    
    if p in [2,3,5,7,13]:
        return [canonical_model(S.codomain(),(-1,a)) for S in E.isogenies_prime_degree(p)]
        
    E = E.short_weierstrass_model()
    dp = E.division_polynomial(p).change_ring(K)
    v = []
    for f in [f for f in divisors(dp) if f.degree() == (p-1)/2]:
        try:
            G = E.isogeny(f).codomain()
            # some G need not actually be correct, because the checking
            # of validity of isogenies is broken.
            if G.conductor() == N:
                v.append(G)
        except ValueError:
            pass
    v = [canonical_model(G.change_ring(K),(-1,a)) for G in v]
    return v

def isogeny_class(E,S):            # Returns isogeny class and adjacency matrix
    E = E.change_ring(K)
    curve_list = [E]
    i = 0
    Adj = matrix(50)
    ins = 1
    P = S
    while i < len(curve_list):
        for p in P:
            for Ep in p_isogenous_curves(curve_list[i],p):
                bool = True
                for G in curve_list:
                    if Ep.is_isomorphic(G):
                        bool = False
                        Adj[i,curve_list.index(G)]=p         #if a curve in the isogeny class computation is isom
                        Adj[curve_list.index(G),i]=p         #to a curve already in the list, we want a line
                if bool:
                    curve_list.append(Ep)
                    Adj[i,ins]=p
                    Adj[ins,i]=p
                    ins += 1
        i+=1  
    Adj = Adj.submatrix(nrows=len(curve_list),ncols=len(curve_list))
    isog_class = []
    for j in range(0,len(curve_list)):
        ainv = canonical_model(curve_list[j],(-1,a),6500).a_invariants()
        ainvs = [ainv[0],ainv[1],ainv[2],ainv[3],ainv[4]]
        isog_class.append(ainvs)
    return (isog_class, Adj)


Edb = ([a-1,-a^2-1,a^2-a,a^2,0],[0,-a,-a-1,-a^2-a,0],[-a^2+a-1,-a^2+1,a-1,-1,-a^2],[-a^2,-1,-a^2+1,a+1,0])   ## given list of elliptic curves


%time
all_isog_classes = []
lprimes = []
for i in range(0,len(Edb)):        ## enumerate isogeny classes of given elliptic curves
    E = EllipticCurve(K,Edb[i])
    S = billereyprimes(E)
    lprimes.append(S)
    isog = isogeny_class(E,S)
    all_isog_classes.append(isog)

all_S = []
for i in range(0,len(lprimes)):
    for j in range(0,len(lprimes[i])):
        l = lprimes[i][j]
        new_ind = 1
        for k in all_S:
            if k == l:
                new_ind = 0
        if new_ind:
            all_S.append(l)
all_S.sort()

all_S
