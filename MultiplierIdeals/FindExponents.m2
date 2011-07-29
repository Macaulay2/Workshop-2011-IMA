restart
loadPackage "SpaceCurvesMultiplierIdeals"
debug SpaceCurvesMultiplierIdeals

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
     );


findExponents = I -> (
     if not isPureDifference I then error "expected a pure difference ideal";
     R  := ring I;
     KK := coefficientRing R;
     grobnerBasis := flatten entries gens gb I;
     M := map(ZZ^0,ZZ^(numgens R),{});
     for i in grobnerBasis do (
     	  u := exponents i;
     	  M = M || matrix{u_0-u_1};
	  );
     KM := ker M;
     if rank KM =!= 1 then error "check ideal defines a curve";
     exps := apply(flatten entries gens KM, i -> abs i);
     t = getSymbol("t");
     if ( ker map(KK[t],R,apply(exps, i->t^i)) =!= I ) then error "incomplete generators of curve ideal";
     return exps;
     );

nn = {3,4,5}; K = findExponents affineMonomialCurveIdeal(QQ[x_1..x_(#nn)],nn)

I = affineMonomialCurveIdeal(QQ[x_1..x_3],{3,4,5})
J = ideal(I_0,I_1)
findExponents(J)
J == affineMonomialCurveIdeal(ring J, findExponents(J))


