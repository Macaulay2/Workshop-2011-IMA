
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
    factors F
    numerator F 

    F = a * (a*x-y-1/a)^2 * (1/b * x * z - a * y)^2
    factors F 
    numerator F 
///

end 

-- 

restart
loadPackage "UnitTestsPD"
check "UnitTestsPD"


