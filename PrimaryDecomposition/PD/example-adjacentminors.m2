adjacentMinorsIdeal = method(Options=>{CoefficientRing=>QQ})
adjacentMinorsIdeal(ZZ, ZZ, ZZ) := opts -> (K,M,N) -> (
    kk := opts.CoefficientRing;
    R := kk[vars(0..M*N-1)];
    Mat := genericMatrix(R,M,N);
    rowchoices := for i from 0 to M-K list toList(i..i+K-1);
    colchoices := for i from 0 to N-K list toList(i..i+K-1);
    ideal flatten (
      for r in rowchoices list 
      for c in colchoices list 
        det(submatrix(Mat, r, c))
        )
    )

end

restart
load "PD/example-adjacentminors.m2"
needsPackage "PD"
I = adjacentMinorsIdeal(2,3,3,CoefficientRing=>ZZ/32003)
minprimes I
primaryDecomposition I
intersect oo == I

-- some possible ones to try (see recent paper by Kawazoe and Noro)
-- in the paper, the examples are done over QQ
I = adjacentMinorsIdeal(2,3,5,CoefficientRing=>ZZ/32003)
time minprimes I
I = adjacentMinorsIdeal(2,3,6,CoefficientRing=>ZZ/32003)
time minprimes I
I = adjacentMinorsIdeal(2,3,7,CoefficientRing=>ZZ/32003)
time minprimes I
I = adjacentMinorsIdeal(2,3,8,CoefficientRing=>ZZ/32003)
  -- 7 Dec 2012:
  time minprimesViaBirationalSplit I;
     -- used 22.6325 seconds
  time minprimes I;
  time decompose I;  -- killed after short period of time
  
I = adjacentMinorsIdeal(2,3,9,CoefficientRing=>ZZ/32003)
time minprimes I
I = adjacentMinorsIdeal(2,3,10,CoefficientRing=>ZZ/32003)
time minprimes I

I = adjacentMinorsIdeal(2,4,4,CoefficientRing=>ZZ/32003)
time minprimes I
time decompose I
I = adjacentMinorsIdeal(2,4,5,CoefficientRing=>ZZ/32003)
time minprimes I
adjacentMinorsIdeal(2,4,6,CoefficientRing=>ZZ/32003)
time minprimes I
adjacentMinorsIdeal(2,4,7,CoefficientRing=>ZZ/32003)
time minprimes I

adjacentMinorsIdeal(2,5,5,CoefficientRing=>ZZ/32003)
time minprimes I

