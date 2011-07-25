installPackage "MonomialMultiplierIdeals"
viewHelp MonomialMultiplierIdeals

R = QQ[x,y];
I = monomialIdeal(y^2,x^3);
monomialMultiplierIdeal(I,5/6)

-- End functionality:
-- input: sequence of integers and a real number
-- output: multiplier ideal

-- Intermediate functionality (we need):
-- Symbolic power of I
-- term ideal of the monomial ideal
-- some intersection of the lattice points. 

KK = ZZ/101
R = KK[x,y,z,w]
I = monomialCurveIdeal(R,{2,3,4})

-- term ideal is just the ideal of the terms of the gens... right?
termIdeal = I -> ideal flatten apply(flatten entries gens I, i -> terms i);

termIdeal I

code methods leadTerm
