-- Aluffi's M2 package CSM that 
-- e.g. computes Chern classes of the tangent bundle of subschemes of P^n
-- availabe at M2 homepage
load "CSM.m2"
load "chernpolynomials.m2"

-- 1) an example where the implementation works

R = QQ[x,y,z]

I = ideal(x^2 + y^2 + z^2)
var = Proj(R/I)

CSM I
-- result 2H^2 + 2H, where H is the hyperplane class in A_*(P^n)
chernPolynomial(tangentSheaf var)
-- result t + 1, where t is the hyperplane class in A_*(var), 
-- CSM actually computes the pushforward to P^n of the Chern class. 
-- As deg(var)=2, this result hence agrees with existing implementations
chernPolyOfVariety(var)
-- result t + 1

--examination of the resolutions used
M = module tangentSheaf var
-- it is already free, so we have a finite resolution
Mlifted = cokernel( lift(presentation M, R) )
-- a resolution of this module is used in chernPolynomial
-- even this one is free
N =  Hom(I/I^2, R/I)
betti res N
-- also the normal bundle is free


-- 2) an example where it partly works

R = QQ[x,y,z,w]

I = ideal(x^2 + y^2 + z^2 + w^2)
var = Proj(R/I)

CSM I
-- result 4H^3 + 4H^2 + 2H
chernPolynomial(tangentSheaf var)
-- result -8t^3 + 8t^2 - 4t + 1
chernPolyOfVariety(var)
-- result 2t^2 + 2t + 1
-- as deg(var)=2, this result agrees with existing implementations

--examination of the resolutions used
M = module tangentSheaf var
betti res(M, LengthLimit=>20)
-- does not seem to have a finite resolution
Mlifted = cokernel( lift(presentation M, R) )
betti res(Mlifted, LengthLimit=>20)
-- but this one has (by the Hilbert syzygy theorem)
N =  Hom(I/I^2, R/I)
betti res(N, LengthLimit=>20)
-- the normal bundle is free


-- 3) an example where nothing works

R = QQ[x,y,z,w]

twistedCubic = minors(2,matrix{{x,y,z},{y,z,w}})
var = Proj(R/twistedCubic)

CSM twistedCubic
--result 2H^3 + 3H^2
chernPolynomial(tangentSheaf var)
-- result 6t^3 + 3t^2 + 1
chernPolyOfVariety(var)
-- result 4t + 1

--examination of the resolutions used
M = module tangentSheaf var
betti res(M, LengthLimit=>14)
-- does not seem to have a finite resolution
Mlifted = cokernel( lift(presentation M, R) )
betti res(Mlifted, LengthLimit=>20)
-- but this one has (by the Hilbert syzygy theorem)
N =  Hom(twistedCubic/twistedCubic^2, R/twistedCubic)
betti res(N, LengthLimit=>14)
-- the normal bundle does not seem to have a finite resolution either

