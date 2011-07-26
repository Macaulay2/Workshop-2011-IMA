restart;
load "QuillenSuslin.m2"

-- For a Laurent polynomial, this method returns a list of lists
-- {{i,coeff(var^i)}} of degrees of the given variable that appear
-- in f and also the corresponding coefficients.
laurentCoeffList = method()
laurentCoeffList(RingElement,RingElement) := (f,var) -> (
     local coeff; local coeffDenom; local coeffList; local degreeList;
     local denom; local denomDeg; local num;
     f = sub(f,frac ring f);
     num = numerator(f);
     denom = denominator(f);
     denomDeg = degVar(denom,var);
     coeffDenom = denom*(var^(-denomDeg)); -- Get rid of the variable from the denominator.
     coeff = coefficients(num,Variables => {var});
     degreeList = apply(reverse flatten entries (coeff)#0, i -> degVar(i,var) - denomDeg);
     coeffList = apply(reverse flatten entries transpose (coeff)#1, i -> i*(coeffDenom)^-1);
     return apply(#degreeList, i -> {degreeList#i,coeffList#i});
)

laurentNormalize = method()
laurentNormalize(Matrix,RingElement) := (f,var) -> (
     varList = flatten entries vars ring f;     
     f = sub(f,frac ring f);
     usedVars = unique support f_(0,0); -- Need to use 'unique support' since for a rational function, the 'support' command returns the concatenation of the support of the numerator and the support of the denominator.
     if not isSubset({var},usedVars) then error "Error: Expected the given variable to be in the support of the first polynomial.";
     if numcols f < 2 then error "Error: Expected the given row to have at least 2 columns.";
     -- TODO: Possible optimization here.  May want to move polynomial with least number of terms or that needs the least
     -- value of l to the front.
     
     -- The following code creates a list of lists where each interior list is the degree vector of a term of
     -- the Laurent polynomial f_(0,0).
     numTerms = terms numerator f_(0,0);
     denom = denominator(f_(0,0));
     denomDegSeq = apply(#numTerms, i -> apply(varList, j -> degVar(denom,j)));
     numDegSeq = apply(numTerms, i -> apply(varList, j -> degVar(i,j)));
     degSeqList = numDegSeq - denomDegSeq;
     lVector = matrix{apply(#usedVars, i -> 1)};
     dotList = apply(degSeqList, i -> (matrix{i}*transpose lVector)_(0,0)); -- Create a list of the dot product of the current lVector with each degree vector.
     l = 1;
     while dotList != unique dotList do (
	  l = l+1;
	  lVector = matrix{apply(#usedVars, i -> l^i)};
	  dotList = apply(degSeqList, i -> (matrix{i}*transpose lVector)_(0,0)); -- Create a list of the dot product of the current lVector with each degree vector.
     );
     -- Once we exit the while loop, the terms of f_(0,0) will have all distinct powers of var with Laurent monomial coefficients.
     -- Now we construct the appropriate change of variables.
     subList = flatten entries vars ring f;
     invSubList = flatten entries vars ring f;
     j = 1;
     scan(subList, i -> if member(i,usedVars) and i != var then (
	  i = i*var^(l^j);
     	  j = j+1;
     ));
     j = 1;
     scan(invSubList, i -> if member(i,usedVars) and i != var then (
	  i = i*var^(-l^j);
     	  j = j+1;
     ));
     subs1 = matrix{subList};
     invSubs1 = matrix{invSubList};
     print(subs1,invSubs1);
     f2 = sub(f,subs1); -- Now each term of f2_(0,0) has a unique power of var.
     print f2;
     minCoeff = (laurentCoeffList(f2_(0,0),var))#0; -- Get the smallest power of var occuring in f2_(0,0) and also its coefficient.
     D = mutableIdentity(ring f,numcols f);
     -- Need numcols f >= 2 here.
     D_(0,0) = (minCoeff#1 * var^(minCoeff#0))^-1;
     D_(1,1) = minCoeff#1 * var^(minCoeff#0);
     print D;
     f3 = f2*matrix(D); -- Now f3_(0,0) has constant term 1 in var and only positive powers of var. (ie. it's a polynomial in var whose coefficients are Laurent polynomials in the other variables.)
     print f3;
     -- Since the constant term of f3_(0,0) is 1, we can use elementary column operations to make all other polynomials have strictly positive degree in var.
     E = matrix mutableIdentity(ring f,numcols f);
     scan(1..(numcols f - 1), i -> (
	  leastDegTerm = (laurentCoeffList(f3_(0,i),var))#0;
	  while leastDegTerm#0 < 1 do (
	       Etemp = mutableIdentity(ring f,numcols f);
	       Etemp_(0,i) = -leastDegTerm#1 * var^(leastDegTerm#0); -- Make an elementary matrix to kill the lowest degree term in f3_(0,i).
	       Etemp = matrix Etemp;
	       f3 = f3*Etemp;
     	       print f3;
	       E = E*Etemp;
	       leastDegTerm = (laurentCoeffList(f3_(0,i),var))#0;
	  );
     ));
     -- After this scan, every entry of f3 except the first has strictly positive degree in var.	       
     -- Now we construct the invertible change of variables which makes f3 become a matrix of polynomials.
     usedVars = delete(var,usedVars);
     if #usedVars > 0 then (
     	  minSolList = {};
     	  scan(drop(laurentCoeffList(f3_(0,0),var),1), i -> 
	       minSolList = minSolList|apply(usedVars, j -> -(((laurentCoeffList(i#1,j))#0)#0)/(i#0))
     	  );
          print minSolList;
     	  scan(1..(numcols f - 1), i ->
	       scan(laurentCoeffList(f3_(0,i),var), j ->
	       	    minSolList = minSolList|apply(usedVars, k -> -(((laurentCoeffList(j#1,k))#0)#0)/(j#0))
	      )
     	  );
          print minSolList;
     	  minExp = max(ceiling max minSolList,0);
     ) else minExp = 0;
     print minExp;
     subMatrix = vars ring f;
     subs2 = sub(subMatrix,{var => var*(product usedVars)^minExp});
     invSubs2 = sub(subMatrix,{var => var*(product usedVars)^-minExp});
     subs = sub(subs1,subs2);
     invSubs = sub(invSubs2,invSubs1);
     return(sub(matrix(D)*E,invSubs1),subs,invSubs);
)

dot = method()
dot(List,List) := (u,v) -> (
     return ((matrix{u})*(transpose matrix{v}))_(0,0);
)

S = frac(QQ[x,y,z])
f = x^-5*y^-1*z^-4 + x^2*y^-2*z
g = x^-3*y^2*z^-3 + x^-2*y^-1*z^2
M = matrix{{f,g}}
(U,subs,invSubs) = laurentNormalize(M,x)
sub(M*U,subs)

-- ====================================================================
-- Examples from Fabianska's website
-- ====================================================================

-- Example 1:
R = frac(QQ[x])
f = matrix{{x^-1+1+x,2*x^-2+1,1-x}}
(U,subs,invSubs) = laurentNormalize(f,x)
g = sub(f*U,subs) -- Same output as Fabianska's method.
isUnimodular(sub(g,last R.baseRings))

-- Example 3:
R = frac(QQ[x,y])
f = matrix{{1/y+x/y+x,x/y^2+1+y+x*y}}
(U,subs,invSubs) = laurentNormalize(f,x)
g = sub(f*U,subs) -- Better than output of Fabianska's method.
isUnimodular(sub(g,last R.baseRings))
-- Note: last R.baseRings gives the underlying ring of the fraction field.

-- Example 4:
R = frac(QQ[x,y])
f = matrix{{y/x^2+1+y/x,1+y/x,x-x*y}}
(U,subs,invSubs) = laurentNormalize(f,x)
g = sub(f*U,subs) -- Same output as Fabianska's method.
sub(g,invSubs) == f*U
isUnimodular(sub(g,last R.baseRings))

-- Example 6:
R = frac(QQ[x,y])
f = matrix{{x^2*y+x,1+y,x-x*y}}
(U,subs,invSubs) = laurentNormalize(f,x)
g = sub(f*U,subs) -- Same output as Fabianska's method.
sub(g,invSubs) == f*U
isUnimodular(sub(g,last R.baseRings))




g = sub(f,frac S)

laurentCoeffList(f,x)
f = x^-5*y^2*z^-6+x^-4*y*z^-3+x^-1*y^2*z^-5+y^2*z+x^2*y^2*z^-2
laurentCoeffList(f,x)
degreeSeqList(f)

f = sub(x^2*y+y^5*x+4,R)
