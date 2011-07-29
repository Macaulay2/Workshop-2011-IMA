
chernPolynomial=method()

-- first, computing the chern polynomial of an ideal I 
-- (alright, computing the chern polynomial of R/I)
-- using Hartshorne corollary II.5.18 that any coherent sheaf on a projective variety can be written as a quotient of a sheaf E that's sum of twisted structure sheaves
-- THIS IS DONE


chernPolynomial(Ideal):=(I)->(
     n:= # gens ring I;
  --   t:= local t;
  --   t:= getSymbol "t";
     chernPolyRing=(coefficientRing ring I)[t]/(t^n); -- I wanted to make this local but then division doesn't work
     B:=betti res I;
     maxdegree := max apply(keys B, last); -- reading off max "diagonal" (degree) from Betti table 
     mindegree := min apply(keys B, last); -- reading off min "diagonal"
     if (mindegree == maxdegree) then (
	  polyn := (1+maxdegree*t)^((pairs B)#0#1*(-1)^mindegree);
     	  polyn
	  )
     else (
     	  keysbydegree := apply(toList(mindegree..maxdegree), d->select(keys B, k -> last k ===d));
     	  powerlist := apply(keysbydegree,k->sum(apply(k,i->B#i))); -- summing up diagonals
     	  powerpairs := apply(toList(mindegree..maxdegree), d->{1+d*t,(-1)^(d+1)*powerlist_(d-mindegree)}); 
  --     	  powerlist := apply(keysbydegree,k->sum(apply(k,i->B#i))); -- summing up diagonals
  --   	  powerpairs := apply(toList(mindegree..maxdegree), d->{1+d*t,(-1)^(d+1)*powerlist_(d-mindegree)}); 
     	  polyn:=1;
     	  for p in powerpairs do (
	       polyn= polyn*(first p)^(last p)
	       );
     	  polyn)
     )

-- chernPolynomial of a chain complex: THIS IS DONE -- CHECK SIGN OR INCLUDE WARNING

chernPolynomial(ChainComplex):=(C)->(
     n:= # gens ring C;
  --   t:= local t;
     chernPolyRing=(coefficientRing ring C)[t]/(t^n); -- I wanted to make this local but then division doesn't work
     B:=betti C;
     maxdegree := max apply(keys B, last); -- reading off max "diagonal" (degree) from Betti table 
     mindegree := min apply(keys B, last); -- reading off min "diagonal"
     if (mindegree == maxdegree) then (
	  polyn := (1+maxdegree*t)^((-1)^((keys B)#0#0)*((pairs B)#0#1));
     	  polyn
	  )
     else (
     	  keysbydegree := apply(toList(mindegree..maxdegree), d->select(keys B, k -> last k ===d));
     	  powerlist := apply(keysbydegree,k->sum(apply(k,i->B#i))); -- summing up diagonals
     	  powerpairs := apply(toList(mindegree..maxdegree), d->{1+d*t,(-1)^(d+1)*powerlist_(d-mindegree)}); 
--     	  powerlist := apply(keysbydegree,k->sum(apply(k,i->(-1)^(1+first i)*B#i))); -- summing up diagonals
--     	  powerpairs := apply(toList(mindegree..maxdegree), d->{1+d*t,powerlist_(d)}); 
     	  polyn:=1;
     	  for p in powerpairs do (
	       polyn= polyn*(first p)^(last p)
	       );
     	  polyn)
     )

-- Trying to take the information off the betti table: I am unsure about the ring here
-- NOT DONE ****

--chernPolynomial(BettiTally):=(B)->(
--     n:= # gens ring I;
  --   t:= local t;
  -- need another way to get ring here:
--     chernPolyRing=(coefficientRing ring B)[t]/(t^n); -- I wanted to make this local but then division doesn't work
--     maxdegree := max apply(keys B, last); -- reading off max "diagonal" (degree) from Betti table 
--     mindegree := min apply(keys B, last); -- reading off min "diagonal"
--     if (mindegree == maxdegree) then (
--	  polyn := (1+maxdegree*t)^((-1)^((keys B)#0#0)*((pairs B)#0#1));
--     	  polyn
--	  )
--     else (
--     	  keysbydegree := apply(toList(mindegree..maxdegree), d->select(keys B, k -> last k ===d));
--     	  powerlist := apply(keysbydegree,k->sum(apply(k,i->B#i))); -- summing up diagonals
 --    	  powerpairs := apply(toList(mindegree..maxdegree), d->{1+d*t,(-1)^(d+1)*powerlist_(d-mindegree)}); 
--     	  polyn:=1;
--     	  for p in powerpairs do (
--	       polyn= polyn*(first p)^(last p)
--	       );
--     	  polyn)
--     )

-- Chern polynomial of a module
chernPolynomial(Module):=(M)->(
     n:= # gens ring M;
  --   t:= local t;
     chernPolyRing=(coefficientRing ring M)[t]/(t^n); -- I wanted to make this local but then division doesn't work
     B:=betti res M;
     maxdegree := max apply(keys B, last); -- reading off max "diagonal" (degree) from Betti table 
     mindegree := min apply(keys B, last); -- reading off min "diagonal"
     if (mindegree == maxdegree) then (
	  polyn := (1+maxdegree*t)^((-1)^((keys B)#0#0)*((pairs B)#0#1));
     	  polyn
	  )
     else (
     	  keysbydegree := apply(toList(mindegree..maxdegree), d->select(keys B, k -> last k ===d));
     	  powerlist := apply(keysbydegree,k->sum(apply(k,i->B#i))); -- summing up diagonals
     	  powerpairs := apply(toList(mindegree..maxdegree), d->{1+d*t,(-1)^(d+1)*powerlist_(d-mindegree)}); 
--     	  powerlist := apply(keysbydegree,k->sum(apply(k,i->(-1)^(1+first i)*B#i))); -- summing up diagonals
--     	  powerpairs := apply(toList(mindegree..maxdegree), d->{1+d*t,powerlist_(d)}); 
     	  polyn:=1;
     	  for p in powerpairs do (
	       polyn= polyn*(first p)^(last p)
	       );
     	  polyn)
     )

-- Chern polynomial of a coherent sheaf: be careful as signs of degrees in betti table
-- are not exactly obvious;
-- generators in degree -d correspond to sheaves OO(d)

chernPolynomial(CoherentSheaf):=(S)->(
     n:= # gens ring S;
--     t:= local t;
     chernPolyRing=(coefficientRing ring S)[t]/(t^n); -- I wanted to make this local but then division doesn't work
     modOfSheaf := module S;
     liftOfMod := lift(presentation modOfSheaf, ring ideal ring module S);
     newModOfSheaf := coker liftOfMod;
     B:=betti res newModOfSheaf;
     maxdegree := max apply(keys B, last); -- reading off max "diagonal" (degree) from Betti table 
     mindegree := min apply(keys B, last); -- reading off min "diagonal"
     if (mindegree == maxdegree) then (
	  polyn := (1-maxdegree*t)^((-1)^((keys B)#0#0)*((pairs B)#0#1));
     	  polyn
	  )
     else (
     	  keysbydegree := apply(toList(mindegree..maxdegree), d->select(keys B, k -> last k ===d));
     	  powerlist := apply(keysbydegree,k->sum(apply(k,i->B#i))); -- summing up diagonals
     	  powerpairs := apply(toList(mindegree..maxdegree), d->{1-d*t,(-1)^(d+1)*powerlist_(d-mindegree)}); 
---     	  powerlist := apply(keysbydegree,k->sum(apply(k,i->(-1)^(1+first i)*B#i))); -- summing up diagonals
---     	  powerpairs := apply(toList(mindegree..maxdegree), d->{1-d*t,powerlist_(d)}); 
     	  polyn:=1;
     	  for p in powerpairs do (
	       polyn= polyn*(first p)^(last p)
	       );
     	  polyn)
     )


-- input Betti table -- is this well-defined, or do we need the dimension of the ambient space as 
-- an additional input? what about the ring, as well?

chernPolyOfVariety = method()
-- now the chern polynomial of the tangent sheaf of a variety, automatically
-- however, this does not work. Something is wrong in tangentSheaf, as it should work
-- seems our resolution of tangentSheaf is not entirely correct.
-- I can't pin down the error
--chernPolynomialOfVariety(ProjectiveVariety):=(P)->(
--     S := tangentSheaf P;
--     polyOfVar := chernPolynomial S;
--     polyOfVar
--     )


chernPolyOfVariety(ProjectiveVariety):=(P)->(
     n := dim P+1;
     chernPRing = (coefficientRing ring P)[t]/t^n;
     ambring := ring ambient P;
     tanProj := tangentSheaf ambient P;
     toppoly := chernPolynomial tanProj;
     idealofvar := ideal P;
     normalbdl := Hom(idealofvar/idealofvar^2, ambring/idealofvar);
     bottompoly := chernPolynomial sheaf normalbdl;
     m := map(chernPRing, ring bottompoly);
     p := map(chernPRing, ring toppoly);
     newtoppoly := p toppoly;
     newbottompoly := m bottompoly;
     newtoppoly//newbottompoly
     )
    

--input the ideal of a projective variety and get chern poly of tangent sheaf
chernPolynomialOfVariety(Ideal):=(I)->(
     var := Proj(ring I /I);
     tanSheaf := tangentSheaf var;
     polyOfVar := chernPolynomial tanSheaf;
     polyOfVar
     )

-- now taking the output of hilbertSeries to a Chern polynomial

hilbertToChernPoly = method()

hilbertToChernPoly(Divide) :=(D)->(
n := D#1#0#1;
S = QQ[t]/(t^n);
termsOfHilb := terms numerator D;
numberOfTerms := #termsOfHilb;
coeffOfHilb := termsOfHilb/leadCoefficient;
exponentsOfHilb := termsOfHilb/exponents;
betterExponents := apply(exponentsOfHilb, i-> flatten i);
pairsagain:=apply(toList(0..numberOfTerms-1), d->{1-betterExponents#d#0 * t, coeffOfHilb#d});
polynagain :=1;
for p in pairsagain do (
	       polynagain= polynagain*(first p)^(last p)
	       );
     polynagain
     )

end;


document {
     Key => key,
     Headline => "Chern polynomial of an ideal", -- not needed for overviews
     Usage => "chernPolynomial I",
     BaseFunction => "chernPolynomial", -- usually not needed
     Inputs => {
          "I" an ideal
          },
     Consequences => {
          effects
          },
     Outputs => {
          a polynomial in the quotient ring 
          },
     "Use chernPolynomial to get the Chern polynomial of an ideal.",
     EXAMPLE lines \/\/\/
                m2code
                m2code
                m2code
          \/\/\/,
     "There can be explanatory prose here in the form of a hypertext list.",
     Caveat => {"warning"},
     SeeAlso => {"other things"},
     Subnodes => {
          "subheading a",
          TO "node 1", 
          TO "node 2",
          "subheading b",
          TO "node 3", 
          ...
          },
     }
