loadPackage "SpaceCurvesMultiplierIdeals"
debug SpaceCurvesMultiplierIdeals

R = QQ[x,y,z];
I = affineMonomialCurveIdeal(R,{2,3,4})
gens gb I


-- From Thomas Kahle's package Binomials.m2
isPureDifference = I -> (
     ge := flatten entries gens I;
     for g in ge do (
	  coeffs := sort flatten entries (coefficients g)#1;
     	  if coeffs == {1} then continue;
	  if coeffs == { -1} then continue;
	  if coeffs == { -1 , 1} then continue;
	  return false;
	  );
     return true;
     )

findExponents = I -> (
     if not isPureDifference I then error "expected a pure difference ideal";
     grobnerBasis := flatten entries gens gb I;
     M := map(ZZ^0,ZZ^3,{});     
     for i in grobnerBasis do (
     	  u := exponents i;
     	  M = M || matrix{u_0-u_1}
	  );
     K := ker M
     if rank K =!= 1 then error "check ideal defines a curve";
     
     );

K = findExponents I
rank K
findExponents ideal(x+y)

isPureDifference I
g = x-y-z
sort flatten entries (coefficients g)#1