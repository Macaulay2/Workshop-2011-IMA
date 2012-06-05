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

export {findElementThatFactors, facGB, factors, facGB0}

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
          if member(g, nonzeros) then continue;
          J := trim(ideal(g) + I);
          J = trim ideal apply(J_*, f -> (
              product toList (set ((factors f)/last) - nonzeros)
          ));
          if numgens J === 1 and J_0 == 1 then continue;
          result := (J, nonzeros + prev);
          prev = prev + set{g};
          result
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
  --R2 = ZZ/32003[d, f, j, k, m, r, t, A, D, G, I, K]
  R2 = QQ[d, f, j, k, m, r, t, A, D, G, I, K]
  I2 = ideal ( I*K-K^2, r*G-G^2, A*D-D^2, j^2-j*t, d*f-f^2, d*f*j*k - m*r, A*D - G*I*K)

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

facD1 = first facGB(I1)
sortedFacD1 = sort apply(facD1, pair -> (
  flatten entries gens gb first pair, last pair ) )  

satIdeals = apply(sortedFacD1, pair -> (
  myI := ideal first pair;
  mySep := toList last pair;
  satI := myI;
  for s in mySep do (
    satI = saturate(satI, s) );
  << codim satI << "  " << flush ;
  satI
  ));


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
