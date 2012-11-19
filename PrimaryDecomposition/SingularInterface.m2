newPackage(
        "SingularInterface",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "",
        DebuggingMode => true
        )

export {
    toSingular, -- monomial order, ring, polynomial, ideal, matrix, list, what else?
    toSingularMO,
    wallTime,
    wallTiming
    }

wallTime = Command (() -> value get "!date +%s")
wallTiming = f -> (
    a := wallTime(); 
    r := f(); 
    b := wallTime();  
    << "wall time : " << b-a << " seconds" << endl;
    r);

-- Code here

-----------------------------------------------
-- Translation to Singular --------------------
-----------------------------------------------
-- ring variable name translation
--   ring variable with no subscript, and no 's:  same
--   ring variable with complicated subscripts need to be mapped
--   I think that even doubly indexed variables can't be done?
--   
toSingular = method()
toSingularMO = method() -- monomial order

toSingular Ideal := (I) -> (
     g := concatenate between(",\n   ", apply(numgens I, i -> replace(///[\*\^]///,"",toString I_i)));
     "ideal i = " | g | ";\n"
     )
toSingular(Ring,String) := (R,name) -> (
     -- note: R is assumed to be a polynomial ring.  Variables alowed: single letters, 
     -- letters indexed by a single non-negative integer.
     kk := coefficientRing R;
     p := char kk;
     a := "ring "|name|" = "|p|",(";
     b := concatenate between(",", (gens R)/toString);
     c := "),dp;\n";
     a | b | c
     )
toSingular(Ring) := (R) -> toSingular(R,"R1")
toSingular(Ideal,String) := (I,name) -> (
     a := "ideal "|name|" = \n";
     g := concatenate between(",\n   ", apply(numgens I, i -> toString I_i));
     a | g | ";\n"
     )
toSingular (Ideal, String) := (I,str) -> (
     a := "ideal " | str | " = \n";
     g := concatenate between(",\n   ", apply(numgens I, i -> toString I_i));
     a | g | ";\n"
     )
variableNameToSingular = method()
variableNameToSingular String := (s) -> (
    -- variables names can be: usual M2 identifiers, except _ is allowed, ' is allowed
    -- note: x_i is a variable, but is treated just like a string.
    -- indexed variables: x(1), x(2), not: x[2], x(1,3).
    --   NOT: x(a), where a is a symbol
    -- multi-indices: x(1)(2)(3)
    -- SO:
    -- translate x_i to x(i)
    -- translate x_(i,j) to x(i)(j)
    --   NOTE: in Singular, you can use e.g. x_(1,3), but it means x_(1)
    --   and so on: each entry of the Sequence becomes another set of parens.
    -- translate x_a to what?  It doesn't work in Singular
    -- So: translate _ to (...)
    --     x_hasjdahd to x(hasjdahd)
    --     x_(sada,dsfs) to x(sada)(dsfs)  i.e.: , --> )(
    --
    )

--------------------------------------------------
-- Link to Singular primary decomposition --------
--------------------------------------------------
minAssGTZStr = ///
LIB "primdec.lib";
list L=minAssGTZ(I1);
L;
link fil=":a @FILE@";
for (int idx=1; idx<=size(L); idx++) {
    write(fil, L[idx]);
  }
///
  
singularMinAss = method()
singularMinAss Ideal := (I) -> (
     -- checks: I is an ideal in a poly ring.
     -- poly ring has variables usable by Singular
     -- monomial order translates OK.
     -- coeff ring is QQ or ZZ/p.  Perhaps allow others later?
     --
     -- Step 1: Create the ring and ideal for singular
     outfile := "foo-sing.answer";
     ringStr := toSingular(ring I, "R1");
     idealStr := toSingular(I, "I1");
     primdec := replace("@FILE@", outfile, minAssGTZStr);
     "foo.sing" << ringStr << endl << idealStr << endl << primdec << endl << close;
     -- Step 2: Append code for prim decomp
     -- Step 3: run Singular (from path)
     if fileExists outfile then removeFile outfile;
     result := get "!Singular <foo.sing";
     -- Step 5: translate output to M2 list of lists of ideals
     apply(lines get outfile, f -> value("ideal\""|f|"\""))
     )
--------------------------------------------------
primdecStr = ///
LIB "primdec.lib";
list L=primdecGTZ(I1);
L;
link fil=":a @FILE@";
for (int idx=1; idx<=size(L); idx++) {
  for (int jdx=1; jdx<=size(L[idx]); jdx++) {
    write(fil, L[idx][jdx]);
  }}
///
  
singularPD = method()
singularPD Ideal := (I) -> (
     -- checks: I is an ideal in a poly ring.
     -- poly ring has variables usable by Singular
     -- monomial order translates OK.
     -- coeff ring is QQ or ZZ/p.  Perhaps allow others later?
     --
     -- Step 1: Create the ring and ideal for singular
     outfile := "foo-sing.answer";
     ringStr := toSingular ring I;
     idealStr := toSingular I;
     primdec := replace("@FILE@", outfile, primdecStr);
     "foo.sing" << ringStr << endl << idealStr << endl << primdec << endl << close;
     -- Step 2: Append code for prim decomp
     -- Step 3: run Singular (from path)
     if fileExists outfile then removeFile outfile;
     result := get "!Singular <foo.sing";
     -- Step 5: translate output to M2 list of lists of ideals
     answer := apply(lines get outfile, f -> value("ideal\""|f|"\""));
     pack(2,answer)
     )

beginDocumentation()

end

TEST ///
restart
loadPackage "SingularInterface"

  R = ZZ/32003[a..d]
  s = toSingular(R, "R1")
  ans = "ring R1 = 32003,(a,b,c,d),dp;\n"
  assert (s === ans)
///

TEST ///
restart
loadPackage "PD"
debug loadPackage "SingularInterface"

  R = ZZ/32003[a,b,c,h]
  I = ideal(a+b+c,a*b+b*c+a*c,a*b*c-h^3)
  singularMinAss I

  R = QQ[a,b,c,h]
  I = ideal(a+b+c,a*b+b*c+a*c,a*b*c-h^3)
  D = singularMinAss I

  C = minprimes I
  C1 = C/(i -> flatten entries gens gb i)//set
  D1 = D/(i -> flatten entries gens gb i)//set
  assert(C1 === D1)
///

TEST ///
  restart
  needsPackage "PD"
  debug needsPackage "SingularInterface"
  Q = ZZ/32003[a,b,c,d]
  -- 3 random cubics in R
  I = ideal(-840*a^3-7687*a^2*b+9625*a*b^2-3820*b^3-10392*a^2*c-13100*a*b*c-11362*b^2*c-7463*a*c^2-11288*b*c^2+1417*c^3-14802*a^2*d-7804*a*b*d+5834*b^2*d-10186*a*c*d-11900*b*c*
     d+5062*c^2*d+14848*a*d^2+1270*b*d^2+4670*c*d^2+14589*d^3,6046*a^3-1565*a^2*b-10455*a*b^2+13719*b^3+9618*a^2*c+4969*a*b*c+14049*b^2*c+7621*a*c^2-15861*b*c^2-11905*c^3-
     13456*a^2*d+2029*a*b*d+8067*b^2*d-10420*a*c*d-14441*b*c*d-13965*c^2*d-3634*a*d^2-4035*b*d^2+350*c*d^2-8942*d^3,-12512*a^3-11973*a^2*b-8963*a*b^2-12001*b^3-10663*a^2*c-
     7202*a*b*c+9856*b^2*c-7955*a*c^2-8818*b*c^2+398*c^3+4259*a^2*d+13332*a*b*d+1576*b^2*d+3008*a*c*d+2588*b*c*d-6135*c^2*d-5311*a*d^2+6731*b*d^2-13991*c*d^2-9315*d^3)
  time C1 = minprimes I;
  D1 = singularMinAss I;
  C2 = C1/(i -> flatten entries gens gb i)//set
  D2 = D1/(i -> flatten entries gens gb i)//set
  assert(C2 === D2)
///

TEST ///
  restart
  debug needsPackage "PD"
  debug needsPackage "SingularInterface"
  R = QQ[a,b,c,d,f,g,h,k,l,s,t,u,v,w,x,y,z]
  I = ideal"
    -ab-ad+2ah,
    ad-bd-cf-2ah+2bh+2ck,
    ab-ad-2bh+2dh-2ck+2fk+2gl,
    ac-2cs-at+2bt,
    ac-cs-2at+bt,
    -d-3s+4u,
    -f-3t+4v,
    -g+4w,
    -a+2x,
    -b2-c2+2bx+2cy,
    -d2-f2-g2+2dx+2fy+2gz"

    time J = first simplifyIdeal I
    time birationalSplit I
///

TEST ///
  restart
  debug needsPackage "PD"
  debug needsPackage "SingularInterface"
  R = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  I = ideal(r^2-3,e_1*g_1+e_2*g_2+e_3*g_3+e_4*g_4, (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2-r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2+r*e_2*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2+r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2-r*e_2*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2)
  time C1 = birationalSplit I;
  time C2 = flatten (C1/(m -> (C := decompose m#0; apply(C, i -> (i, m#1, m#2)))));
  
  -- for each: find ideal itself
  time C3 = apply(C2, m -> (I1 := ideal(m#1 / last) + m#0; g := product (m#2); if g == 1 then I1 else saturate(I1, g)));
  time C4 = selectMinimalIdeals C3;
  #C4
///

TEST ///
  restart
  debug needsPackage "PD"
  debug needsPackage "SingularInterface"
  R = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  I = ideal(r^2-3,e_1*g_1+e_2*g_2+e_3*g_3+e_4*g_4, (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2-r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2+r*e_2*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2+r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2-r*e_2*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2)
  R1 = QQ[vars(0..numgens R-1)]
  I1 = sub(I, vars R1)
  time C1 = minprimes I1; -- 17.7 sec
  D1 = singularMinAss I1; -- at 45 minutes, was using 650 MB.,  3hr19m using 1.68 GB, killed after 3hr30m

doc ///
Key
  SingularInterface
Headline
Description
  Text
  Example
Caveat
SeeAlso
///

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
loadPackage "SingularInterface"


R = QQ[a..d]
toSingular R

R = ZZ/32003[w,x,y,z]
toSingular R

x = symbol x
R = ZZ/32003[x_1..x_4]
toSingular R -- not correct yet
