-- One of the examples of a Stewart-Gough platform.
-- This one is not reduced.
  restart
  debug needsPackage "PD"
  needsPackage "UnitTestsPD"
  R = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  I = ideal(r^2-3,e_1*g_1+e_2*g_2+e_3*g_3+e_4*g_4, (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2-r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2+r*e_2*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2+r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2-r*e_2*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2)
  time C = minprimes I
  radI = intersect C;
  -- this is correct - 17 components
  checkMinimalPrimes(I,C)
  -- playing with factoring the generators of the GB of I
  
  time C1 = facGB ideal gens gb I
  C' = flatten (C1 / minprimes);
  -- Fails.  There are only 12 components when splitting using facGB.
  checkMinimalPrimes(I,C')
  
  Igb = flatten entries gens gb I
  (fac,facs) = findElementThatFactors Igb  
  time I1 = I : facs#0
  time I2 = I : I1
  
  (fac,facs) = findElementThatFactors I1_*  
  time I11 = I1 : facs#0
  time I12 = I1 : I11
  time minprimes I11;
  
  time C1 = minprimes I1;
  time C2 = minprimes I2;
  
  
  -- on 11/13, 16.75 seconds on Frank's office machine
  time C = minprimes(I)
  D
  D / (j -> time splitTower(j,opts));
  badSplitTower = D#4;  
  netList badSplitTower_*
  
  -- building bad split tower ideal
  restart
  debug needsPackage "PD"
  R = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  (S,SF) = makeFiberRings {e_4,g_1}
  use SF
  use coefficientRing SF
  badIdeal = ideal(r^2-3,g_4^4+((4*e_4^2+3*g_1^2)/3)*g_4^2+(4*e_4^4+18*e_4^2*g_1^2)/9,g_3+((-1)/(4*e_4*g_1))*g_4^3*r+((-2*e_4^2-3*g_1^2)/(12*e_4*g_1))*g_4*r,g_2^2+(9/8)*g_4^2+(2*e_4^2+9*g_1^2)/8,e_3+((-1)/(4*g_1))*g_4^2*r+((-2*e_4^2-3*g_1^2)/(12*g_1))*r,e_2+(9/(4*e_4^3+18*e_4*g_1^2))*g_2*g_4^3+((12*e_4^2+9*g_1^2)/(4*e_4^3+18*e_4*g_1^2))*g_2*g_4,e_1+(3/(4*e_4*g_1))*g_4^3+((2*e_4^2+3*g_1^2)/(4*e_4*g_1))*g_4)
  time splitTower badIdeal
     
  -- the time in the previous example is being spent on
  -- computing ideal gens gb (S.cache#"StoSF" G + J)
  -- the point of this example is factoring J_2 over the field
  -- extension given by J_0 and J_1 *quickly*
  G = (219136/3)*g_2*g_4^3*e_4^3*g_1-217600*g_2*g_4^3*e_4^2*g_1^2-49664*g_2*g_4^3*e_4^2-18496*g_2*g_4^3*e_4*g_1^3+456960*g_2*g_4^3*e_4*g_1+124032*g_2*g_4^3*g_1^2-39168*g_2*g_4^3-(59392/3)*g_2*g_4^2*r*e_4^4+33280*g_2*g_4^2*r*e_4^3*g_1+(1071104/3)*g_2*g_4^2*r*e_4^2*g_1^2-48128*g_2*g_4^2*r*e_4^2+48960*g_2*g_4^2*r*e_4*g_1^3-115200*g_2*g_4^2*r*e_4*g_1-9248*g_2*g_4^2*r*g_1^4-13056*g_2*g_4^2*r*g_1^2+(438272/9)*g_2*g_4*e_4^5*g_1-(87040/3)*g_2*g_4*e_4^4*g_1^2-(99328/3)*g_2*g_4*e_4^4+(620416/3)*g_2*g_4*e_4^3*g_1^3+143872*g_2*g_4*e_4^3*g_1-130560*g_2*g_4*e_4^2*g_1^4-232448*g_2*g_4*e_4^2*g_1^2-26112*g_2*g_4*e_4^2-55488*g_2*g_4*e_4*g_1^5+321024*g_2*g_4*e_4*g_1^3-23040*g_2*g_4*e_4*g_1+145248*g_2*g_4*g_1^4-19584*g_2*g_4*g_1^2-(118784/9)*g_2*r*e_4^6+(7168/9)*g_2*r*e_4^5*g_1-(38912/3)*g_2*r*e_4^4*g_1^2-(96256/3)*g_2*r*e_4^4+(47744/3)*g_2*r*e_4^3*g_1^3-17408*g_2*r*e_4^3*g_1+208896*g_2*r*e_4^2*g_1^4-144384*g_2*r*e_4^2*g_1^2+55488*g_2*r*e_4*g_1^5-78336*g_2*r*e_4*g_1^3-(48128/3)*g_4^3*r*e_4^4-(564736/3)*g_4^3*r*e_4^3*g_1-12544*g_4^3*r*e_4^2*g_1^2+44544*g_4^3*r*e_4^2+161296*g_4^3*r*e_4*g_1^3-101760*g_4^3*r*e_4*g_1+41616*g_4^3*r*g_1^4-58752*g_4^3*r*g_1^2-(174080/3)*g_4^2*e_4^5*g_1-(547840/3)*g_4^2*e_4^4*g_1^2+80384*g_4^2*e_4^4+282880*g_4^2*e_4^3*g_1^3+207232*g_4^2*e_4^3*g_1+46240*g_4^2*e_4^2*g_1^4-617472*g_4^2*e_4^2*g_1^2+11520*g_4^2*e_4^2-196656*g_4^2*e_4*g_1^3+48960*g_4^2*e_4*g_1-(96256/9)*g_4*r*e_4^6-(951296/9)*g_4*r*e_4^5*g_1-(173056/3)*g_4*r*e_4^4*g_1^2+29696*g_4*r*e_4^4-(1313248/3)*g_4*r*e_4^3*g_1^3-19712*g_4*r*e_4^3*g_1-33760*g_4*r*e_4^2*g_1^4+120576*g_4*r*e_4^2*g_1^2+170544*g_4*r*e_4*g_1^5-88704*g_4*r*e_4*g_1^3+41616*g_4*r*g_1^6-58752*g_4*r*g_1^4-(348160/9)*e_4^7*g_1-(219136/3)*e_4^6*g_1^2+(160768/3)*e_4^6-130560*e_4^5*g_1^3+(315136/3)*e_4^5*g_1-310208*e_4^4*g_1^4+134144*e_4^4*g_1^2+7680*e_4^4+195840*e_4^3*g_1^5+424288*e_4^3*g_1^3+6528*e_4^3*g_1+83232*e_4^2*g_1^6-481536*e_4^2*g_1^4+34560*e_4^2*g_1^2-217872*e_4*g_1^5+29376*e_4*g_1^3
  J = ideal(r^2-3,g_4^4+((4*e_4^2+3*g_1^2)/3)*g_4^2+(4*e_4^4+18*e_4^2*g_1^2)/9,g_2^2+(9/8)*g_4^2+(2*e_4^2+9*g_1^2)/8) 
  coeffs = coefficients(G,Variables=>{g_2})
  coeff1 = first flatten entries last coeffs
  K = ideal (J_0,J_1,g_2,e_1,e_2,e_3,g_3)
  Kmons = matrix basis comodule K
  N = last coefficients((Kmons*coeff1) % K, Monomials=>Kmons) 
  coeff2 = (Kmons*N^(-1))_0_0
  (coeff1*coeff2) % K
  myFac = g_2 + (G*coeff2) % K
  J_2 // myFac

-- Looking into using char series to factor towers.  
time splitIdeal(I, Strategy=>({strat1, IndependentSet},infinity), Verbosity=>2);  -- BUG
time splitIdeal(I, Strategy=>{strat1, (IndependentSet, infinity)}, Verbosity=>2);  -- 
time minprimes(I, Verbosity=>2)

debug Core
splitLexGB2 = method()
splitLexGB2(Ideal, Ring) := (I,SF) -> (
    -- variables should be in order used by rawCharSeries.
    sup := support I;
    Rlex := (coefficientRing ring I)[support I, MonomialOrder=>Lex];
    Ilex := sub(I, Rlex);
    time C := rawCharSeries raw gens Ilex;
    C = C/(c -> map(Rlex, c));
    select(for c in C list time ideal gens gb sub(c, SF), i -> i != 1)
    )
M = gens L

splitLexGB2(L, ring f)
return; continue;
L

gens ring L
R = QQ[a,b,c]
I = ideal"a3-3, b3-3"
rawCharSeries raw gens I
map(R, last oo)
gens gb oo

R = ZZ/5[a,b,c]
I = ideal"a5-c2, b5-c2"
minprimes(I, Verbosity=>2)
rawCharSeries raw gens I

