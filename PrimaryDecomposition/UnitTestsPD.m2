
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
  assert( ( ideal(x+sub(a,SF))  === ideal first minimalizeOverFrac(IS, SF) ) )
  assert( ( ideal(sub(a,S))  === ideal last minimalizeOverFrac(IS, SF) ) )
///

TEST ///
  debug loadPackage "PD"
  R = ZZ/32003[a,x]
  I = ideal( a*x + a^2 )
  (S,SF) = makeFiberRings {a,x}
  IS = sub(I,S)
  assert( ( ideal 1_SF === ideal first minimalizeOverFrac(IS, SF) ) )
  assert( ( IS  ===  ideal last minimalizeOverFrac(IS, SF) ) )
///


-- for Mike: can we do "assert error" ? 
TEST ///
  debug loadPackage "PD"
  R = ZZ/32003[a,x]
  I = ideal( a*x + a^2 )
///
  --(S,SF) = makeFiberRings {}

TEST ///
  debug loadPackage "PD"
  R = QQ[a,b,c,d,e,h]
  (S,SF) = makeFiberRings {c}
  use SF
  C = sub(c, coefficientRing SF) 
  I = ideal(h^4+C*h^3+6*C^2*h^2-4*C^3*h+C^4,e+(1/(11*C^2))*h^3+((-2)/(11*C))*h^2+(1/11)*h+(4*C)/11,d+((-3)/(11*C^2))*h^3+(6/(11*C))*h^2+((-3)/11)*h+(-C)/11,b+(1/(11*C^2))*h^3+((-2)/(11*C))*h^2+(1/11)*h+(4* C)/11,a+(1/(11*C^2))*h^3+((-2)/(11*C))*h^2+(1/11)*h+(4*C)/11)
  use S
  J = ideal(d+3*e+c,b-e,a-e,e*h+3*e*c-h^2+h*c+c^2,e^2+3*e*c+c^2)
  assert( J == contractToPolynomialRing I )
///

TEST ///
  debug loadPackage "PD"
  R = QQ[a,b,c,d,e,h]
  J = ideal(d+3*e+c,b-e,a-e,e*h+3*e*c-h^2+h*c+c^2,e^2+3*e*c+c^2)
  assert( independentSets J == {h}) 
  assert( extendIdeal J == ideal(e^4+h*e^3+h^2*e^2+h^3*e+h^4,d+(1/(h))*e^2+2*e+h,c+((-1)/(h))*e^2+e-h,b-e,a-e))
  -- this is passing for now, but it would not work if we were to change the order of left and right hand side in assertion 
///

end 

-- 

restart
loadPackage "UnitTestsPD"
check "UnitTestsPD"


