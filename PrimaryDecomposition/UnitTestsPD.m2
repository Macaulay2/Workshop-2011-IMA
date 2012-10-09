
newPackage(
        "UnitTestsPD",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "Short tests for basic correctness of PD.m2",
        DebuggingMode => true
        )

export {}

-- radicalContainment
TEST ///
    debug needsPackage "PD"
    R = ZZ/32003[a..f]
    F = map(R,R,symmetricPower(2,matrix{{a,b,c}}))
    I = ker F
    J = I^2
    G = I_0
    assert radicalContainment(G,J)
    assert not radicalContainment(G-a^2,J)
    assert (radicalContainment(I, I^2) === null)
///

TEST ///
    debug needsPackage "PD"
    R = (frac(QQ[a,b]))[x,y,z]
    F = 15 * a * (a*x-y-1/a)^2 * (1/b * x * z - a * y)^2
    assert(set factors F === set {(2, a^2*x-a*y-1), (2, x*z - a*b*y)})
    assert ( vars coefficientRing ring numerator F == 0 ) 

    G = a * (a*x-y-1/a)^2 * (1/b * x * z - a * y)^2
    assert( set factors F === set factors G)
///

TEST ///
    debug loadPackage "PD"
    R = ZZ/32003[a..d]
    I = monomialCurveIdeal(R,{1,3,4})
    J = I + ideal(a^5-b^5)
    assert(findNonMemberIndex(I,J) == -1)-- which (index of)  element of I is not in J
    assert(findNonMemberIndex(J,I) == 4) -- J_4 is not in I
    assert(selectMinimalIdeals {I,J} === {I})
    assert(selectMinimalIdeals {J,I} === {I})
///

TEST ///
  debug loadPackage "PD"
  R = ZZ/32003[a,b,c,d,e,f,g,h]
  (S,SF) = makeFiberRings {c}
  assert ( first sort gens S == c ) 
  assert ( not member(c, gens SF) ) 
  use SF
  F = 1/c
  assert ( F*c == 1 ) 
///

TEST ///
  debug loadPackage "PD"
  R = ZZ/32003[a,x]
  I = ideal( a*x + a^2 )
  (S,SF) = makeFiberRings {a}
  IS = sub(I,S)
  assert( ( ideal 1_SF === ideal first minimalizeOverFrac(IS, SF) ) )
  assert( ( IS  ===  ideal last minimalizeOverFrac(IS, SF) ) )
///

TEST ///
  debug loadPackage "PD"
  R = ZZ/32003[a,x]
  I = ideal( a*x + a^2 )
  (S,SF) = makeFiberRings {a,x}
  IS = sub(I,S)

///

-- for Mike: can we do "assert error" ? 
TEST ///
  debug loadPackage "PD"
  R = ZZ/32003[a,x]
  I = ideal( a*x + a^2 )
  --(S,SF) = makeFiberRings {}
///

end 

-- 

restart
loadPackage "UnitTestsPD"
check "UnitTestsPD"


