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

export {}

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
     (f, {})
     )

facGB0 = method()
facGB0(Ideal, Set) := (I, nonzeros) -> (
     -- returns a pair (P:List, L:List)
     --  where : P is a list of ideals, that have no factorization left.
     --  and     L is a list of (J:ideal, nonz: nonzeros), 
     --    where J is an ideal containing I, and nonz is a set of monic polynomials, which are not in the resulting min primes
     (f, facs) := findElementThatFactors(I, nonzeros); -- chooses a generator of I that factors
     if #facs == 0 then ( 
	  --<< "no elements found that factor" << endl; << "ideal is " << toString I << endl; 
	  return ((I, nonzeros), {})
	  );
     prev := set{};
     ({}, for g in toList(set facs - nonzeros) list (
	  if member(g, nonzeros) then continue;
	  J := trim(ideal(g) + I);
	  J = trim ideal apply(J_*, f -> (
		    product toList (set ((factors f)/last) - nonzeros)
	       ));
          if numgens J === 1 and J_0 == 1 then continue;
	  result := (J, nonzeros + prev);
	  prev = prev + set{g};
	  result
	  ))
     )

facGB = method(Options=>{Limit=>infinity})
facGB Ideal := opts -> (J) -> (
     C = {};
     L = {(J,set{})};
     i := 0;
     while i < opts.Limit and #L > 0 do (
     	  L2 := flatten for j in L list (
     	       (C1,L1) = facGB0 j;
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


end


restart
load "FactorizingGB.m2"
load "siphon-example.m2"

findElementThatFactors(I1, {})
factor I_0

-- facGB(ideal I) --> return a set of GB's s.t. the radical of I is the intersection of 
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
