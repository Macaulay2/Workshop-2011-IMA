-- Example of Allen Knutson
--   problem: compute the minimal primes of this ideal
nonPappas = (kk) -> (
    Gr := Grassmannian(2,8,CoefficientRing => kk);
    use ring Gr;
    P := Gr + ideal {p_(0,1,2), p_(3,6,8),  -- the two lines with 3 points on them
        p_(0,3,4), p_(0,6,7),		-- the two lines touching 0
        p_(1,3,5), p_(1,7,8),		-- the two lines touching 1
        p_(2,4,8), p_(2,5,6)};		-- the two lines touching 2
    P = trim P;
    P)

end

restart
load "example-nonpappas.m2"
I = nonPappas QQ
I = nonPappas (ZZ/32003)
o3_0
o3_1
