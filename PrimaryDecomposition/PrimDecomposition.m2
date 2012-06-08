newPackage(
        "PrimDecomposition",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "",
        DebuggingMode => true
        )

export {primdec, minAssPrimes, "Indeps", "Intersect", "FacGB",
     getIndependentSets,
     makeFiberRings
     }

-------------------------
simplifyIdeal = method()
simplifyIdeal Ideal := (I) -> (
     -- returns a pair (I', phi),
     -- where phi : R --> R, and
     -- phi(I') = I, and all variables which occured only linearly have been replaced with variables.
     )

isContainedInRadical = method()

primDecomp = method(Options => {Strategy=>null})
  -- return type: list of {primary,prime}

minAssPrimes = method(Options => {FacGB => false, Strategy=>null})
  -- return type: list of {prime}
  -- the list is the irredundant set of minimal primes.
minAssPrimes Ideal := opts -> (I) -> (
     -- step 1: handle special case: I == 0
     -- (also: check ring, and either put it into the correct form, or give error if can't)
     minAssFcn := if opts.Strategy === GTZ then minAssGTZ else minAssSL;
     P0 := ring I;
     -- define a new ring P, in grevlex, same number of vars
     -- bring I into P.
     -- parse input options
     
     (I', map1) := simplifyIdeal I;
     gb I';  -- if map1 != identity, then we need to compute this here
     if I' == 1 then return {I'};
     if dim I' == 0 then (
	  -- use Moeller-H. algorithm
	  -- create a lex order ring
	  -- if vdim(I')  
	  return result;
	  );
     if not opts.FacGB then (
	  result = minAssFcn(I');
	  result = removeRedundants(result);
	  return (map1 result);
     	  );
     comps := facGB I';
     result = comp/minAssFcn//removeRedundants;
     map1 result);

minAssSL = (I) -> (
     local pd;
     result := {};
     P := ideal(1_(ring I));
     while (
	  pd = minAssSLIteration(I,P);
	  pd =!= null
     ) do (
	  P = intersect(P, pd#1);
	  result = join(result, pd#0);
	  );
     result
     )

minAssGTZ = (I) -> ()

minAssSLIteration = method()
minAssSLIteration(Ideal, Ideal) := (I,P) -> (
     -- input: ideal I
     --        ideal P, which is the intersection of some components of I
     -- output: (components, P')
     --   where components is a list of different minimal components of I (from those in P)
     --   and P' is the intersection of these components
     k := position(P_*, f -> not isContainedInRadical(f, I));
     if k =!= null then return null;
     J := saturate(I, P_k);
     -- now compute some of the components of J
     newDecompStep(J, Indeps=>1, Intersect=>true, Strategy=>2)
     )


-- questions:
--  1. what are seri, peek?
--  2. 
newDecompStep = method(Options=>{Indeps=>1, Intersect=>true, Strategy=>2})
newDecompStep Ideal := opts -> (I) -> (
{*     
     R := ring I;
     if isHomogeneous I then (
	  if dim I === 0 then return ({ideal vars ring I}, ideal vars ring I);
	  hf := poincare I;
	  );
     if I == 0 then return ({I}, I);
     -- 
     R1 := newRing(ring I, MonomialOrder=>Lex);
     J := sub(I, R1);
     -- also compute the reduced GB of J:
     --   if R1 === R, then already done
     --   if not, but J is homog, then use the hilbert function to compute GB
     --     else, just compute GB
     gbJ := computeLexGB J;
     -- step: gbJ --> (fried, gbJ), where 
     --   fried consists of the elements with linear lead term
     --   and gbJ consists of all the rest
     fried := for f in gbJ list if deg(leadMonomial f) == 1 then ...
     if #fried == numgens ring I then return ({I}, I);
     if #fried > 0 then (
	  -- create a lex polynomial ring with just the variables not
	  -- occuring as lead terms of 'fried'
	  -- then map gbJ to this ring, and recurse
	  -- then map these back, and return this result
	  return ...
	  );
     if I == 1 then return (....);
     -- handle the case when R1 has 1 variable:
     if numgens R1 then (
	  -- factor the generator of gbJ
	  -- create the PD from this factorization, and return
	  );
     -- the zero-dimensional case
     if dim J == 0 then (
	  result := newZeroDecomp(J, ser, Strategy=>opts.Strategy);
	  return (cleanPrimary result, J);
	  );
     -- now find a maximal indep set
     --
     -- in @Phelp (same ring as R, except with grevlex, if R was not weighted, grevlex)
     -- compute a GB of I, call it jwork
     --
     -- 
*}
     )

makeFiberRings = method()
makeFiberRings(List) := (baseVars) -> (
   -- This function takes an ideal I and a list of variables baseVars as input
   -- and returns a pair of matrices (mons, cs) where mons are the monomials in the ideal
   -- of lead terms of a gb of I, and cs are the coefficients, but with respect to
   -- a product order kk[fiberVars][baseVars].  See example below for behavior
   if #baseVars == 0 then error "expected at least one variable in the base";
   R := ring baseVars#0;
   if any(baseVars, x -> ring x =!= R) then error "expected all base variables to have the same ring";
   allVars := set gens R;
   fiberVars := rsort toList(allVars - set baseVars);
   baseVars = rsort baseVars;
   RU := (coefficientRing R) monoid([fiberVars,baseVars,MonomialOrder=>Lex]);
	     --MonomialOrder=>{#fiberVars,#baseVars}]);
   KK := frac((coefficientRing R)[baseVars]);
   KR := KK[fiberVars, MonomialOrder=>Lex];
   (RU, KR)
   )

getIndependentSets = method(Options => options independentSets)
getIndependentSets(Ideal) := opts -> (I) -> (
     indeps := independentSets(I, Limit=>opts.Limit);
     -- for each element, create two rings:
     --  product order ring
     --  frac field ring
     indeps
     )



beginDocumentation()

doc ///
Key
  PrimDecomposition
Headline
  looking at singular algorithms
Description
  Text
  Example
Caveat
SeeAlso
///

end

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

restart
loadPackage "PrimDecomposition"

R1 = QQ[a..M, MonomialSize => 8]
I1 = ideal(K,J,I,E,D,A,v,s,r-G,q-t,o,m-w,l-y,k-z,j-t,i-L,g,f,d,c-n,b-H,a,G*M-t,z*M-w,y*M-p, H*L-C,B*L-H,z*L-G,w*L-t,t*L-x,n*L-h,e*L-y,B*G-z*H,y*F-G,p*F-t,e*F-z,B*C-H^2,z*C-G*H,w* C-t*H,t*C-x*H,n*C-h*H,e*C-y*H,y*B-e*H,x*B-t*H,t*B-w*H,h*B-n*H,y*z-e*G,x*z-t*G,t*z-w*G, h*z-n*G,w*y-p*z,t*y-p*G,e*x-p*G,t^2-w*x,n*t-h*w,h*t-n*x,e*t-p*z,e*h-n*y,e*H*M-p*B,p*G* L-x*y,p*C*G-x*y*H,p*z*B-e*w*H,p*z^2-e*w*G,n*x*y-h*p*G,h^2*w-n^2*x)
indeps = getIndependentSets I1
#indeps
makeFiberRings(support indeps#0)
indeps / (makeFiberRings @@ support)
