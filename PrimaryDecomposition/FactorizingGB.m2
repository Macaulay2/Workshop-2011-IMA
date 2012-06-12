newPackage(
        "FactorizingGB",
        Version => "0.1",
        Date => "",
        Authors => {{Name => "",
                  Email => "",
                  HomePage => ""}},
        Headline => "Factorizing Groebner Basis",
        DebuggingMode => true
        )

export {facGB, 
     minAss, 
     -- the following will not be exported
     facGB0, 
     findElementThatFactors, 
     removeRedundants,
     factors, 
     simplifyIdeal, 
     saturateIdeals}

simplifyIdeal = method()
simplifyIdeal Ideal := (originalI) -> (
     -- input: ideal I in a polynomial ring R
     -- output: (J, phi), J is an ideal in the same ring
     --                   phi : R --> R
     -- such that the only generators of J which are linear in a variable are themselves 
     -- variables, and phi J == I
     I := originalI;
     R := ring I;
     H := new MutableList from gens R;
     for x in gens R do (
	  k := position(I_*, f -> first degree diff(x,f) == 0);
	  if k === null then continue;
	  c := leadCoefficient diff(x,I_k);
	  g := I_k - c*x;  
	  -- at this point f = I_k = c*x + g, and g does not involve x.
	  --  (and c is a constant)
	  p := - 1/c * g;
	  I = ideal(x) + ideal compress sub(gens I, x=>p);
	  H#(index x) = x - p;
	  );
     (ideal compress gens I, map(R,R,toList H))
     )

minAss = (I) -> (
  time facD1 := first facGB I;
  time sortedFacD1 := sort apply(facD1, pair -> (
    flatten entries gens gb first pair, last pair ) );
  sortedFacD1 = sortedFacD1/(pair -> (ideal pair#0, pair#1)); 
  time irredFacD1 := removeRedundants sortedFacD1; 
  time irredFacD2 := removeRedundants irredFacD1;
  irredFacD2 / first
  )

factors = (F) -> (
     facs := factor F;
     facs = apply(#facs, i -> (facs#i#1, (1/leadCoefficient facs#i#0) * facs#i#0 ));
     select(facs, (n,f) -> # support f =!= 0))

findElementThatFactors = method()
findElementThatFactors(Ideal, Set) := (I, nonzeros) -> (
    for f in I_* do (
      facs := factors f;
      if #facs > 1 or (#facs == 1 and facs#0#0 > 1) then return (f,facs/last);
	  );
    (null, {})
    )

facGB0 = method()
facGB0(Ideal, Set) := (I, nonzeros) -> (
    -- returns a pair (P:List, L:List)
    --  where : P is a list of ideals, that have no factorization left.
    --  and     L is a list of (J:ideal, nonz: nonzeros), 
    --  where J is an ideal containing I, and nonz is a set of monic polynomials, which 
    --  are not in the resulting min primes
    (f, facs) := findElementThatFactors(I, nonzeros); -- chooses a generator of I that factors
    if #facs == 0 then ( 
        --<< "no elements found that factor" << endl; << "ideal is " << toString I << endl; 
        return ((I, nonzeros), {})
        );
    prev := set{};
    L := for g in toList(set facs - nonzeros) list (
          --if member(g, nonzeros) then continue;
          J := trim(ideal(g) + I);
          J = trim ideal apply(J_*, f -> (
              product toList (set ((factors f)/last) - nonzeros)
          ));
          result := (J, nonzeros + prev);
          prev = prev + set{g};
          if numgens J === 1 and J_0 == 1 then continue else result
    );
    ({}, L)
)

facGB = method(Options=>{Limit=>infinity})
facGB Ideal := opts -> (J) -> (
    C := {};
    L := {(J,set{})};
    i := 0;
    while i < opts.Limit and #L > 0 do (
        L2 := flatten for j in L list (
            (C1,L1) := facGB0 j;
            if C1 =!= {} then C = append(C, C1);
            L1
        );
        L = L2;
        << "number: " << (i, #C, #L) << endl;
        --<< "C = " << netList C << endl;
        --<< "L = " << netList L << endl;
        i = i+1;
    );
    (C, L)     
)

saturateIdeals = (L) -> (
     -- L is a list of pairs (Ideal,sepSet)
     -- where sepSet is a set of monic polynomials
     result := apply(L, pair -> (
         myI := first pair;
       	 mySep := toList last pair;
       	 satI := myI;	   
       	 for s in mySep do satI = ideal gens gb trim saturate(satI, s);
         (satI, last pair)
     ));
     select(result, pair -> pair#0 != 1)
     )

removeRedundants = (L) -> (
     -- L is a list of pairs (Ideal,sepSet)
     -- where sepSet is a set of monic polynomials
   H := partition(pair -> codim pair#0, L);
   codims := sort keys H;
   goodComps := {};
   compsToCheck := flatten for c in codims list H#c;
   for p in compsToCheck do (
       if all(goodComps, pair -> not isSubset(pair#0, p#0)) then (
            -- << codim p#0 << " " << flush;
            satI := p#0;
            for s in toList p#1 do satI = ideal gens gb trim saturate(satI, s);
            goodComps = append( goodComps, (satI, {}));
	     )
	 );
   goodComps
   )

beginDocumentation()

doc ///
Key
  FactorizingGB
Headline
  Factorizing Groebner Basis
Description
  Text
  Example
Caveat
SeeAlso
///

end

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///

TEST ///
  R1 = QQ[d, f, j, k, m, r, t, A, D, G, I, K];
  I1 = ideal ( I*K-K^2, r*G-G^2, A*D-D^2, j^2-j*t, d*f-f^2, d*f*j*k - m*r, A*D - G*I*K);
  p1 = minAss I1;
  p1 = sort apply(p1, P -> flatten entries gens gb P );
  D1 = decompose I1;
  D1 = sort apply(D1, i -> flatten entries gens gb i );  
  assert(p1 === D1)
///

TEST ///
  R1 = QQ[a..M]
  I1 = ideal(I*K-K^2,-k*s+K,-I*L+J,o*J*K-J^2,B*H*L-H^2,-i*B+H,r*G-G^2,-l*F+G,-A*L+E,o*D*E-E^2, A*D-D^2,-v*F+D,-r*s+D,b*C*L-C^2,-b*i+C,k*z-z^2,-e*F+z,-t*L+x,i*j*x-x^2,m*w-w^2,-k*M+w,- s*y+v,-j^2+j*t,-y*F+r,-i*k+r,-m*L+q,i*q*w-q^2,-y*M+p,-e*i+l,-r*M+j,-p*F+j,h*i*n-h^2,-c* i+h,-d*L+g,f*g*o-g^2,d*f-f^2,-s*F+f,-B*L+b,a*u*L-a^2,-o*u+a);
  p1 = time minAss I1;
  p1 = sort apply(p1, P -> flatten entries gens gb P );
  load "newGTZ.m2"
  D1 = singularMinAss I1;  
  D1 = sort apply(D1, i -> flatten entries gens gb i );  
  assert(p1 === D1)

  -- up to radical same ideal but naivley generated
  I2 = ideal(j*r*M-j^2,-r^2*M^2+j*r*M,v*D*F-D^2,-v^2*F^2+v*D*F,s*v*y-v^2,-s^2*y^2+s*v*y,p *y*M-p^2,-y^2*M^2+p*y*M,a*o*u-a^2,-o^2*u^2+a*o*u,i*B*H-H^2,-i^2*B^2+i*B*H,o*D*E-E^ 2,o*J*K-J^2,f*g*o-g^2,i*j*x-x^2,i*q*w-q^2,-y^2*F^2+r*y*F,r*y*F-r^2,r*G-G^2,k*z-z^2 ,j*p*F-j^2,-p^2*F^2+j*p*F,i*k*r-r^2,-i^2*k^2+i*k*r,b*C*L-C^2,b*B*L-b^2,-B^2*L^2+b* B*L,A*D-D^2,I*K-K^2,d*f-f^2,-j^2+j*t,m*w-w^2,-s^2*F^2+f*s*F,a*u*L-a^2,l*F*G-G^2,B* H*L-H^2,-l^2*F^2+l*F*G,e*i*l-l^2,h*i*n-h^2,-e^2*i^2+e*i*l,c*h*i-h^2,-c^2*i^2+c*h*i ,e*z*F-z^2,-e^2*F^2+e*z*F,b*i*C-C^2,-b^2*i^2+b*i*C,A*E*L-E^2,-A^2*L^2+A*E*L,I*J*L- J^2,-I^2*L^2+I*J*L,d*g*L-g^2,-d^2*L^2+d*g*L,t*x*L-x^2,-t^2*L^2+t*x*L,m*q*L-q^2,-m^ 2*L^2+m*q*L,r*s*D-D^2,-r^2*s^2+r*s*D,k*s*K-K^2,-k^2*s^2+k*s*K,f*s*F-f^2,k*w*M-w^2 ,-k^2*M^2+k*w*M);
  p2 = time minAss I2;
  p2 = sort apply(p2, P -> flatten entries gens gb P );
  assert(p1 === p2)
///

TEST ///
  R1 = QQ[a..M, MonomialSize=>8]
  I1 = ideal(I*K-K^2,-k*s+K,-I*L+J,o*J*K-J^2,B*H*L-H^2,-i*B+H,r*G-G^2,-l*F+G,-A*L+E,o*D*E-E^2, A*D-D^2,-v*F+D,-r*s+D,b*C*L-C^2,-b*i+C,k*z-z^2,-e*F+z,-t*L+x,i*j*x-x^2,m*w-w^2,-k*M+w,- s*y+v,-j^2+j*t,-y*F+r,-i*k+r,-m*L+q,i*q*w-q^2,-y*M+p,-e*i+l,-r*M+j,-p*F+j,h*i*n-h^2,-c* i+h,-d*L+g,f*g*o-g^2,d*f-f^2,-s*F+f,-B*L+b,a*u*L-a^2,-o*u+a);
  time (J1,phi) = simplifyIdeal I1;
  time D1 = minAss J1;

  time D2 = D1/(I -> phi I);
  time D3 = minAss I1;

  p2 = sort apply(D2, P -> flatten entries gens gb P );
  p3 = sort apply(D3, P -> flatten entries gens gb P );
  p2 === p3
  
  J1' = ideal select(J1_*, f -> first degree f > 1 or size f > 1)
  R2 = QQ[support J1', MonomialSize=>8]
  J1' = sub(J1', R2)
  time D1' = minAss J1';
  apply(D1', i -> time decompose i)
  time (D1'' = D1'/decompose);
///


TEST ///
  --R2 = ZZ/32003[d, f, j, k, m, r, t, A, D, G, I, K]
  R2 = QQ[d, f, j, k, m, r, t, A, D, G, I, K]
  I2 = ideal ( I*K-K^2, r*G-G^2, A*D-D^2, j^2-j*t, d*f-f^2, d*f*j*k - m*r, A*D - G*I*K)
  p = minAss I2
  p = sort apply(p, P -> flatten entries gens gb P )

  facD1 = first facGB(I2)
  facD1 = facD1 / first 
  facD1 = sort apply(facD1, i -> flatten entries gens gb i )  

  time D1 = decompose I2;
  D1 = sort apply(D1, i -> flatten entries gens gb i )  
  facD1 === D1
///


end


restart
load "FactorizingGB.m2"
load "siphon-example.m2"

time facD1 = first facGB(I1);
--time facD1 = first facGB(I1 + ideal product gens R1);
time sortedFacD1 = sort apply(facD1, pair -> (
  flatten entries gens gb first pair, last pair ) );
time sortedFacD1 = sortedFacD1/(pair -> (ideal pair#0, pair#1));

time irredFacD1 = removeRedundants sortedFacD1;
time satIdeals = saturateIdeals irredFacD1;
netList satIdeals

time L1 = apply(satIdeals, pair -> first facGB first pair );
K1 = flatten L1 
K2 = K1 / first 
-- check if every ideal contains a monomial, because we did not add x1...xn
--into the original ideal
I2 := first select(K2, I -> (
   I_* / size // min > 1
))

flatten apply (K2, I-> select(I_*, g -> size g  == 1 ) ) 

loadPackage "newGTZ"
singularMinAss (I2 + ideal product gens R1)


-- I + prod gens, ideal with 134 minimal primes
-- J naively generated ideal with rad J is (supposed) to equal rad I
-- is rad I == rad J
-- is I+prod gens ideal with 134 min primes? (singular can compute that)
-- for each prime, is (J+prod) contained in prime?




  
I1 = last K2

loadPackage "newGTZ"
loadPackage("newGTZ", Reload => true)


singRes = K2 / singularMinAss;
singRes / length
all (K2, singRes, (ours, theirs) -> ours == first theirs ) 


singRes = 
singularMinAss I1
singularMinAss (I1 + ideal product gens R1) 



mySep = toList last last sortedFacD1
myI = ideal first last sortedFacD1
facGB myI

satI = myI
for s in mySep do (
  satI = saturate(satI, s) )
facGB satI;

satI == myI


facD1 = facD1 / first 
facD1 = sort apply(facD1, i -> flatten entries gens gb i )  
facD1 = facD1 / ideal;

facD1 / codim // tally 
--C26 = select(facD1, i -> codim i == 26 );
--C27 = select(facD1, i -> codim i == 27 );
-- is one in c26 contained in c27? 

-- facD1 / codim // tally
Cgood = select(facD1, i -> codim i == 26 );
for i from 27 to 34 do (
  nextC := select(facD1, j -> codim j == i );
  badPositions = set flatten apply( Cgood, i -> positions( nextC, j ->  (
    -- where i is contained in j
    isSubset(i,j)
    ))
   );
  goodPositions = set (0..(#nextC-1) ) - badPositions;
  Cgood = join(Cgood, nextC _ (toList goodPositions ) );
  << (i, #Cgood) << endl;
)

Cgood / decompose; 

unique facD1


time D1 = decompose I2;

D1 = sort apply(D1, i -> flatten entries gens gb i )  
facD1 === D1

findElementThatFactors(I1, set {})
factor I_0

-- facGB(ideal I) --> return a set of GB's s.t. the radical of I is the intersection of '
--                    the radicals of all the GB ideals.

facGB0(I, nonzeroElems)
factor J_0

L1 = facGB0(J, set{})
L2 = flatten apply(L1, facGB0)
L3 = flatten apply(L2, facGB0)
L8/last
L5/(x -> numgens x#0)
L4 = flatten apply(L3, facGB0);
L5 = flatten apply(L4, facGB0);
#L5
L6 = flatten apply(L5, facGB0);
L7 = flatten apply(L6, facGB0);
L8 = flatten apply(L7, facGB0);
L9 = flatten apply(L8, facGB0);
L10 = flatten apply(L9, facGB0);
L11 = flatten apply(L10, facGB0);


(C1,L1) = facGB0(J, set{}, {})
L2 = flatten apply(L1, facGB0)
L3 = flatten apply(L2, facGB0)
L8/last
L5/(x -> numgens x#0)
L4 = flatten apply(L3, facGB0);
L5 = flatten apply(L4, facGB0);
#L5
L6 = flatten apply(L5, facGB0);
L7 = flatten apply(L6, facGB0);
L8 = flatten apply(L7, facGB0);
L9 = flatten apply(L8, facGB0);
L10 = flatten apply(L9, facGB0);
L11 = flatten apply(L10, facGB0);

time facGB J;
C = oo#0;
#C
C1 = C/(f -> (
	  s := product f#1;
	  if s == 1 then f#0 else saturate(f#0, s)
	  )
     )

C1 = C/(f -> (decompose f#0, f#1))

	  s := product f#1;
	  if s == 1 then f#0 else(f#0, s)
	  )
     )
-- try myPD:
gbTrace=3
gens gb I;
myPD(I, Strategy=>{GeneralPosition}, Verbosity=>2)

J = minimalPresentation(I)
L = ideal(J_*/(f -> (factorize f)/last//product))
myPD(L, Strategy=>{GeneralPosition}, Verbosity=>2)

-- Create a ring in variables a..zA--Z
J1 = J
R1 = (coefficientRing R)[vars(0..numgens R - 1), MonomialSize=>8]
J1 = sub(J1,vars R1)
needsPackage "ExampleIdeals"
"siphon-example.sing" <<  toSingular R1 << endl << toSingular J1 << endl << close
