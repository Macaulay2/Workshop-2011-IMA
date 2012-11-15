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
    toSingularMO
    }

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
