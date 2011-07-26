-- End functionality:
-- input: ring, sequence of integers, and a real number
-- output: multiplier ideal

-- Intermediate functionality (we need):
-- Symbolic power of I.
-- term ideal of the monomial ideal. DONE!
-- some intersection of the lattice points. 

-- This implementation is based on the algorithm given in
-- H.M. Thompson's paper: "Multiplier Ideals of Monomial Space
-- Curves."


loadPackage("Normaliz", Reload=>true);
loadPackage("MonomialMultiplierIdeals", Reload=>true);



-- the code for affineMonomialCurveIdeal is based off of the code for
-- monomialCurveideal

affineMonomialCurveIdeal = (S, a) -> (
     -- check that S is a polynomial ring over a field
     n := # a;
     if not all(a, i -> instance(i,ZZ) and i >= 1)
     then error "expected positive integers";
     t := symbol t;
     k := coefficientRing S;
     M1 := monoid [t];
     M2 := monoid [Variables=>n];
     R1 := k M1;
     R2 := k M2;
     t = R1_0;
     mm := matrix table(1, n, (j,i) -> t^(a#i));
     j := generators kernel map(R1, R2, mm);
     ideal substitute(j, submatrix(vars S, {0..n-1}))
     );

ord = (mm,p) -> (
     R := ring p;
     KK := coefficientRing R;
     A := KK[gens R,Degrees=>mm];
     min flatten apply(terms p, i -> degree sub(i,A))
     );


sortedff = (R,nn) -> (
     KK := coefficientRing R;
     L := sort apply(flatten entries gens affineMonomialCurveIdeal(R,nn), i -> {ord(nn,i), i});
     apply(L, i-> last i)     
     );


exceptionalDivisorValuation = (nn,mm,p) -> (
     R := ring p;
     ff := sortedff(R,nn);
     n := 0;
     while p % ff_0 == 0 do (p = p//ff_0; n = n+1;);
     n*ord(mm,ff_1) + ord(mm,p)
     );

km = (mm,ff) -> sum mm -1 + ord(mm, ff_1) - ord(mm, ff_0);




--
-- The code below was copied directy from Zach Teitler's Pacakage
-- MonomialMultiplierIdeas.m2
-- 

intmat2monomIdeal = method();
intmat2monomIdeal ( Matrix, Ring ) := (M,R) -> (
  if ( numColumns M > numgens R ) then (
    error("intmat2monomIdeal: Not enough generators in ring.");
  );
  
  genList := apply( 0..< numRows M ,
                    i -> R_(flatten entries M^{i}) );
  
  return monomialIdeal genList;
);
-- only include rows whose last entry is d; and ignore last column
intmat2monomIdeal ( Matrix, Ring, ZZ ) := (M,R,d) -> intmat2monomIdeal(M,R,d,numColumns(M)-1);
-- only include rows with entry 'd' in column 'c'; and ignore column 'c'
intmat2monomIdeal ( Matrix, Ring, ZZ, ZZ ) := (M,R,d,c) -> (
  if ( numColumns M > 1 + numgens R ) then (
    error("intmat2monomIdeal: Not enough generators in ring.");
  );
  
  rowList := select( 0 ..< numRows M , i -> (M_(i,c) == d) ) ;
  columnList := delete( c , toList(0 ..< numColumns M) );
  
  M1 := submatrix(M,rowList,columnList);
  
  return intmat2monomIdeal(M1,R);
);

--
-- The code above was copied directy from Zach Teitler's Pacakage
-- MonomialMultiplierIdeas.m2
-- 

monomialValuationIdeal = (R,mm,val) -> (
     M := (matrix{mm}|matrix{{-val}}) || id_(ZZ^(#mm+1));
     normalizOutput := normaliz(M,4);
     M2 := normalizOutput#"gen";
     intmat2monomIdeal(M2,R,1)
     );


exceptionalDivisorValuationIdeal = (R,ff,mm,val) -> (
     maxpow := ceiling(val / ord(mm,ff_1));
     sum apply(splice{0..maxpow}, i -> ideal(ff_1^(maxpow-i))*monomialValuationIdeal(R,mm,i))
     );

termIdeal = I -> monomialIdeal flatten apply(flatten entries gens I, i -> terms i);

-- here we wish to compute the symbolic power I^(floor t). We'll use
-- the saturate command, but in the future there may be a better
-- option.

symbolicPowerCurveIdeal = (I,t) -> saturate(I^(floor t));

end

restart
load "bart.m2"
KK = ZZ/101;
R = KK[x,y,z];	    
nn = {3,4,5};
ff = sortedff(R,nn);
I = affineMonomialCurveIdeal(R,nn)
mm = {1,1,1};
exceptionalDivisorValuation(nn,mm,x^2+y^2+z^2)
exceptionalDivisorValuationIdeal(R,ff,mm,4)

uu = {(exponents(ff_0))_0, (exponents(ff_1))_0}
vv = {(exponents(ff_0))_1, (exponents(ff_1))_1}

(normaliz(matrix{uu_0 - vv_0},5))#"gen"
Guu_1 = (normaliz(matrix{uu_0 - vv_0} || matrix{vv_0 - uu_0} || matrix{uu_1 - vv_1} || id_(ZZ^3),4))#"gen"
Gvv_1 = (normaliz(matrix{uu_0 - vv_0} || matrix{vv_0 - uu_0} || matrix{vv_1 - uu_1} || id_(ZZ^3),4))#"gen"
rho_u = transpose matrix {uu_1-uu_0} -- defining eqn of the ray (not rho from the paper)
rho_v = transpose matrix {vv_1-vv_0} -- defining eqn of the ray (not rho from the paper)

T = (Guu_1||Gvv_1)*(rho_u|rho_v)
rows = toList select(0..<numRows T, i -> all(0..<numColumns T, j -> T_(i,j) > 0))
unique apply(rows, i -> flatten entries (Guu_1||Gvv_1)^{i})

-- intersect(Ideal,Ideal,Ideal) etc
