restart;
load "QuillenSuslin.m2"

-- For a Laurent polynomial, this method returns a list of lists
-- {{i,coeff(var^i)}} of degrees of the given variable that appear
-- in f and also the corresponding coefficients.
laurentCoeffList = method()
laurentCoeffList(RingElement,RingElement) := (f,var) -> (
     local coeff; local coeffDenom; local coeffList; local degreeList;
     local denom; local denomDeg; local num; local R;
     
     R = frac((coefficientRing ring f)[flatten entries vars ring f]);
     f = sub(f,R);
     var = sub(var,R);
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
     local D; local degSeqList; local denom; local denomDegSeq;
     local dotList; local E; local Etemp; local f2; local f3; local j;
     local invSubList; local invSubs; local invSubs1; local invSubs2;
     local l; local leastDegTerm; local lVector; local minCoeff;
     local minExp; local minSolList; local numDegSeq; local numTerms;
     local R; local S; local subList; local subMatrix; local subs;
     local subs1; local subs2; local usedVars; local varList;
     
     R = ring f;
     S = frac((coefficientRing ring f)[flatten entries vars ring f]);
     f = sub(f,S);
     var = sub(var,S);
     varList = flatten entries vars S;
     usedVars = unique support f_(0,0); -- Need to use 'unique support' since for a rational function, the 'support' command returns the concatenation of the support of the numerator and the support of the denominator.
     if not member(var,usedVars) then error "Error: Expected the given variable to be in the support of the first polynomial.";
     if numcols f < 2 then error "Error: Expected the given row to have at least 2 columns.";
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
     f2 = sub(f,subs1); -- Now each term of f2_(0,0) has a unique power of var.
     minCoeff = (laurentCoeffList(f2_(0,0),var))#0; -- Get the smallest power of var occuring in f2_(0,0) and also its coefficient.
     D = mutableIdentity(ring f,numcols f);
     -- Need numcols f >= 2 here.
     D_(0,0) = (sub(minCoeff#1,S) * var^(minCoeff#0))^-1;
     D_(1,1) = (sub(minCoeff#1,S) * var^(minCoeff#0));
     f3 = f2*matrix(D); -- Now f3_(0,0) has constant term 1 in var and only positive powers of var. (ie. it's a polynomial in var whose coefficients are Laurent polynomials in the other variables.)
     -- Since the constant term of f3_(0,0) is 1, we can use elementary column operations to make all other polynomials have strictly positive degree in var.
     E = matrix mutableIdentity(ring f,numcols f);
     scan(1..(numcols f - 1), i -> (
	  leastDegTerm = (laurentCoeffList(f3_(0,i),var))#0;
	  while leastDegTerm#0 < 1 do (
	       Etemp = mutableIdentity(ring f,numcols f);
	       Etemp_(0,i) = -sub(leastDegTerm#1,S) * var^(leastDegTerm#0); -- Make an elementary matrix to kill the lowest degree term in f3_(0,i).
	       Etemp = matrix Etemp;
	       f3 = f3*Etemp;
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
          scan(1..(numcols f - 1), i ->
	       scan(laurentCoeffList(f3_(0,i),var), j ->
	       	    minSolList = minSolList|apply(usedVars, k -> -(((laurentCoeffList(j#1,k))#0)#0)/(j#0))
	      )
     	  );
          minExp = max(ceiling max minSolList,0);
     ) else minExp = 0;
     subMatrix = vars ring f;
     subs2 = sub(subMatrix,{var => var*(product usedVars)^minExp});
     invSubs2 = sub(subMatrix,{var => var*(product usedVars)^-minExp});
     subs = sub(subs1,subs2);
     invSubs = sub(invSubs2,invSubs1);
     return(sub(sub(matrix(D)*E,invSubs1),R),sub(subs,R),sub(invSubs,R));
)


parkAlgorithm = method()
parkAlgorithm(Matrix) := f -> (
     local cols; local E; local NList; local invSubList; local R;
     local rows; local S; local T; local temp; local tempInvSub;
     local tempN; local tempSub; local tempU; local U; local UList;
     local V; local varList;
     
     R = ring f;
     S = frac((coefficientRing R)[flatten entries vars R]);
     T = (coefficientRing R)[flatten entries vars R];
     varList = flatten entries vars S;
     f = sub(f,S);
     rows = numrows f;
     cols = numcols f;
     -- First handle the case where f has only 1 column (and hence only 1 row since we are assuming rows <= cols).
     -- The matrix is unimodular over the Laurent polynomial ring if and only if the entry is a unit (Laurent monomial).
     if cols == 1 then (
	  if #(terms numerator f) == 1 then return matrix{{(f_(0,0))^-1}} else error "Error: The given matrix is not unimodular.";
     );
     NList = {};
     UList = {};
     invSubList = {};
     scan(rows, i -> (
	  temp = submatrix(f,{i},toList(i..(cols-1)));
          (tempN,tempSub,tempInvSub) = laurentNormalize(temp,first varList);
     	  
     -- TODO: Possible optimization.  May want to choose the 'best' variable
     -- to normalize with respect to at each inductive step of the algorithm.
     
          NList = NList|{map(R^i,R^i,1_R)++sub(tempN,R)};
     	  invSubList = invSubList|{sub(tempInvSub,S)};
     	  temp = sub(sub(temp*tempN,tempSub),T); -- Now temp is a polynomial row vector which is unimodular if and only if the first row of f is.
     	  if not isUnimodular temp then error "The given matrix was not unimodular over the Laurent polynomial ring.";
     	  tempU = map(R^i,R^i,1_R)++sub(qsAlgorithm temp,R);
     	  UList = UList|{tempU};
     	  f = f*sub(NList#i,S)*sub(UList#i,tempInvSub); -- Now the i-th row of f has 1 on the diagonal and 0's to the right of the diagonal.
     ));
     U = map(R^cols,R^cols,1_R);
     scan(#NList, i -> U = U*(sub(NList#i,R))*sub(sub(UList#i,invSubList#i),R)); 
     if rows == 1 then return U; -- If f only has 1 row then f*U = [1 0 ... 0].
     V = prune image f;
     E = (gens V // map(R^rows,R^cols,f))|(map(R^rows,R^(cols-rows),0_R)||map(R^(cols-rows)));
     return U*E;
)


completeMatrixLaurent = method()
completeMatrixLaurent(Matrix) := f -> (
     local R;
     R = ring f;
     return sub(inverse sub(parkAlgorithm f,frac((coefficientRing R)[flatten entries vars R])),R);
)

end

dot = method()
dot(List,List) := (u,v) -> (
     return ((matrix{u})*(transpose matrix{v}))_(0,0);
)

restart;
loadPackage "QuillenSuslin"

R = QQ[x,y,z,Inverses => true,MonomialOrder => Lex]
f = x^-5*y^-1*z^-4 + x^2*y^-2*z + x+x^-6+x^10
g = sub(f,frac(QQ[x,y,z]))

coefficients(f,Variables => {x})
L = laurentCoeffList(f,x)

g = x^-3*y^2*z^-3 + x^-2*y^-1*z^2
M = matrix{{f,g}}
(U,subs,invSubs) = laurentNormalize(M,x)
sub(M*U,subs)

-- ====================================================================
-- Examples from Fabianska's website
-- ====================================================================
restart;
loadPackage "QuillenSuslin"

-- Example 1:
R = QQ[x,Inverses => true,MonomialOrder => Lex]
f = matrix{{x^-1+1+x,2*x^-2+1,1-x}}
(U,subs,invSubs) = laurentNormalize(f,x)
g = sub(f*U,subs) -- Same output as Fabianska's method.
isUnimodular(sub(g,QQ[x]))
U = parkAlgorithm f
det U
f*U
C = completeMatrixLaurent f
det C


-- Example 3:
R = QQ[x,y,Inverses => true,MonomialOrder => Lex]
describe R
f = matrix{{1*y^-1+x*y^-1+x,x*y^-2+1+y+x*y}}
(U,subs,invSubs) = laurentNormalize(f,x)
g = sub(f*U,subs) -- Same output as Fabianska's method.
isUnimodular(sub(g,QQ[x,y])) -- This is supposed to be 'false'.

-- Example 4:
R = QQ[x,y,Inverses => true,MonomialOrder => Lex]
f = matrix{{y*x^-2+1+y*x^-1,1+y*x^-1,x-x*y}}
(U,subs,invSubs) = laurentNormalize(f,x)
g = sub(f*U,subs) -- Same output as Fabianska's method.
isUnimodular(sub(g,QQ[x]))
U = parkAlgorithm f
det U
f*U
C = completeMatrixLaurent f
det C


-- Example 6:
R = QQ[x,y,Inverses => true,MonomialOrder => Lex]
f = matrix{{x^2*y+x,1+y,x-x*y}}
(U,subs,invSubs) = laurentNormalize(f,x)
g = sub(f*U,subs) -- Same output as Fabianska's method.
isUnimodular(sub(g,QQ[x]))
U = parkAlgorithm f
det U
f*U
C = completeMatrixLaurent f
det C


-- Trying general algorithm with 2 rows:
restart
loadPackage "QuillenSuslin"
R = QQ[x,Inverses => true,MonomialOrder => Lex]
f = matrix{{3*x^-1-2-2*x+2*x^2, 3*x^-1-2*x,2*x},{6*x^-1+25-23*x-16*x^2+20*x^3, 6*x^-1+29-4*x-20*x^2,2+4*x+20*x^2}}
U = parkAlgorithm f
det U
f*U
C = completeMatrixLaurent f
det C


-- Worked out example.
f1 = submatrix(f,{0},)
(N1,s1,i1) = laurentNormalize(f1,x)
g1 = sub(f1*N1,s1)
isUnimodular(sub(g1,QQ[x]))
U1 = sub(qsAlgorithm(sub(g1,QQ[x])),R)
h1 = f*N1*sub(U1,i1)
f2 = submatrix'(h1,{0},{0})
ring (support f2_(0,0))#0
ring x
(N2,s2,i2) = laurentNormalize(f2,sub(x,R))
g2 = sub(f2*N2,s2)
isUnimodular(sub(g2,QQ[x]))
U2 = qsAlgorithm(sub(g2,QQ[x]))
N2 = map(R^1,R^1,1_R)++N2
U2 = map(R^1,R^1,1_R)++sub(U2,R)
h2 = f*N1*sub(U1,i1)*N2*sub(U2,i2)
-- Now use elementary column operations to clear out nonzero entries under the main diagonal.
E1 = mutableIdentity(R,3)
E1_(1,0) = -h2_(1,0)
E1 = matrix E1
h2*E1

-- So the matrix solving the unimodular matrix problem for f is
N1*sub(U1,i1)*N2*sub(U2,i2)*E1

g = sub(f,frac S)

laurentCoeffList(f,x)
f = x^-5*y^2*z^-6+x^-4*y*z^-3+x^-1*y^2*z^-5+y^2*z+x^2*y^2*z^-2
laurentCoeffList(f,x)
degreeSeqList(f)

f = sub(x^2*y+y^5*x+4,R)
