-- -*- coding: utf-8 -*-


-----------------------------------------------------------------
-- Preamble
-----------------------------------------------------------------

newPackage(
	"characteristicClasses",
    	Version => "0.1", 
    	Date => "July 25, 2011",
    	Authors => {{Name => "Christine Jost", 
		  Email => "jost at math.su.se", 
		  HomePage => "http://www.math.su.se/~jost"}},
    	Headline => "Degrees of Chern and Segre classes",
    	DebuggingMode => true
    	)


----------------------------------------------------------------
-- Exported functions
----------------------------------------------------------------

-- The package provides the following functions:
-- segreClass:     computes Segre classes of closed subschemes of P^k, or rather the pushforward 
--                 of the total Segre class to the Chow ring of the ambient space
-- segreClassList: does the same as segreClass, but returns a list with coefficients instead of a 
--                 polynomial
-- chernClass:     computes Chern classes of closed subschemes of P^k, or rather the pushforward 
--                 of the total Chern class to the Chow ring of the ambient space
-- chernlassList:  does the same as chernClass, but returns a list with coefficients instead of a 
--                 polynomial
export {segreClass, chernClass, segreClassList, chernClassList}



-- The computation of the Segre classes is done by the internal function internalSegreClassList, which 
-- returns a list with the degrees of the Segre Classes and the dimension of the ambient space. The 
-- human-readable output as a polynomial in the Chow ring ZZ[H]/H^(k+1) of the ambient space P^k is
-- produced by the internal function output.
-- The user can choose to give the input as a homogeneous ideal in a polynomial ring or as a projective
-- variety. Furthermore, the user can give the symbol used for the Chow ring ZZ[H]/H^(k+1) as an 
-- optional input. The default symbol is H for hyperplane class.
segreClass = method(TypicalValue => RingElement);
segreClass (Ideal, Symbol) := (I,hyperplaneClass) -> (
     (segreList, ambientDim) := internalSegreClassList I;
     return output (segreList, ambientDim, hyperplaneClass)
     )
segreClass Ideal := I -> (     
     H := symbol H;
     return segreClass (I, H)
     )
segreClass (ProjectiveVariety,Symbol) := (projectiveVar,hyperplaneClass) -> (
     I := projectiveVar.ring.ideal;
     return segreClass(I, hyperplaneClass)
     )
segreClass ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return segreClass I
     )

segreClassList = method(TypicalValue => List);
segreClassList Ideal := I -> (
     (segreList, ambientDim) := internalSegreClassList I;
     return segreList
     )
segreClassList ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return segreClassList I
     )

-- Analogously to the computation of the Segre classes, the computation of the Chern classes is done by 
-- the internal function internalChernClassList, which returns a list with the degrees of the Chern 
-- Classes and the dimension of the ambient space. The human-readable output as a polynomial in the Chow ring 
-- ZZ[H]/H^(k+1) of the ambient space P^k is produced by the internal function output.
-- The user can choose to give the input as a homogeneous ideal in a polynomial ring or as a projective
-- variety. Furthermore, the user can give the symbol used for the Chow ring ZZ[H]/H^(k+1) as an 
-- optional input. The default symbol is H for hyperplane class.
chernClass = method(TypicalValue => RingElement);
chernClass (Ideal, Symbol) := (I,hyperplaneClass) -> (
     (chernList, ambientDim) := internalChernClassList I;
     return output (chernList, ambientDim, hyperplaneClass)
     )
chernClass Ideal := I -> (  
     H := symbol H;   
     return chernClass (I, H)
     )
chernClass (ProjectiveVariety,Symbol) := (projectiveVar, hyperplaneClass) -> (
     I := projectiveVar.ring.ideal;
     return chernClass(I, hyperplaneClass)
     )
chernClass ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return chernClass I
     )

 
chernClassList = method(TypicalValue => List);
chernClassList Ideal := I -> (
     (chernList, ambientDim) := internalChernClassList I;
     return chernList
     )
chernClassList ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return chernClassList I
     )




----------------------------------------------
-- Internal functions
----------------------------------------------



-- The functions internalSegreClassList and internalChernClassList call other internal functions 
-- which do the actual work. 
internalSegreClassList = I -> (
     -- check that the input is a homogeneous ideal in a polynomial ring over a field
     checkUserInput I;
     -- trim the ideal and make it an ideal over a ring only used internally
     localI := prepare I;
     -- compute the Segre classes
     return internalSegre localI;
     )
internalChernClassList = I -> (
     -- check that the input is a homogeneous ideal in a polynomial ring over a field
     checkUserInput I;
     -- trim the ideal and make it an ideal over a ring only used internally
     localI := prepare I;
     -- compute the Chern classes
     return internalChern localI;
     )

-- The function internalSegre is the main function in this package which does the actual computation of the 
-- Segre classes. It uses the algorithm described in [1].
-- Notation: This algorithm computes the degrees of the Segre classes s_0(Z,P^k), ..., s_n(Z,P^k) of an
-- n-dimensional closed subscheme Z of P^k. The subscheme Z is given by a homogeneous ideal I in the 
-- polynomial ring R.
-- Input:  I, a homogeneous ideal in a polynomial ring over a field
-- Output: segreList, a list containing the degrees of the Segre classes of Proj(R/I) = Z
--         ambientDim, the dimension k of the ambient space Proj(R)=P^k 
internalSegre = I -> (
    
     -- Obtain:
     -- the ring R 
     -- the dimension of the ambient space and
     -- the dimension n of Z
     R := ring I;
     ambientDim := dim Proj R;
     dimension := dim Proj(R/I) ;
     
     -- take care of the special cases I = (0) and I = (1)
     if I == ideal(0_R) then (
	  segreList := for i from 0 to dimension list if i==0 then 1 else 0;
	  return (segreList,ambientDim);
	  );
     if I == ideal(1_R) then (
	  segreList = {};
	  return (segreList,ambientDim);
	  ); 
        
     -- For the nonspecial cases, obtain:
     -- a list of the generators of I sorted by degree
     -- the maximal degree of the generators of I and
     -- a generator of I with minimal degree     
     
     gensI := flatten entries sort gens I;
     maxDeg := first max degrees I; 
     minDegGen := first gensI;
     
     -- initialize segreList as an empty list
     segreList= {};
    
     -- Pick random elements in I of degree maxdeg, as many as the dimension of the ambient space, store in the list f.
     f := for i from 1 to ambientDim list sum( gensI, g -> g * random(maxDeg - first(degree(g)), R) );      
     
     -- The for loop computes the degrees of the Segre classes of Z
     for d from (ambientDim - dimension) to ambientDim do (
	  
	  -- Obtain the ideal J of the intersection of d hypersurfaces containing Z, where d = comdimension of Z, ..., dimension of the ambient space.
	  J := ideal(take(f,d));
	  
	  -- Compute the residual of Z in the intersection of the d hypersurfaces, using saturation. Compute the degree of the residual. 
	  -- Remark: Instead of saturating with the ideal I of the scheme Z, we saturate with a hypersurface containing Z of minimal degree.
	  --         This gives the same result with sufficiently high probability and speeds up calculations considerably.
	  residual := saturate(J,minDegGen);
	  -- Take care of the special case where the residual is the irrelevant ideal when computing the degree
	  residualDeg := if residual != ideal vars R then degree residual else 0;
	  
     	  -- Using the degree of the residual, compute the degree of the pth Segre class, where p = d - codimension of Z.
	  p := d - (ambientDim - dimension);
	  degSegreClass := maxDeg^d - residualDeg - sum( 0..(p-1), i -> binomial(d,p-i)*maxDeg^(p-i)*segreList_i );
	  
	  segreList = append(segreList, degSegreClass);
	    
	  );
     
     return (segreList, ambientDim);
     
     )


-- The function internalChern calls internalSegre to compute the Segre classes of the given subscheme of P^k. From these it computes the
-- Chern-Fulton classes using a simple formula (see e.g. [1]). The Chern-Fulton classes are identical to the Chern classes if the scheme 
-- is a smooth variety.
-- Input:  I, a homogeneous ideal in a polynomial ring over a field
-- Output: chernList, a list containing the degrees of the Chern classes of Proj(R/I)
--         ambientDim, the dimension k of the ambient space Proj(R)=P^k 
internalChern = I -> (
     
     -- Obtain:
     -- the ring R
     -- the dimension of the ambient space and
     -- the dimension n of Z
     R := ring I;
     ambientDim := dim Proj R;
     dimension := dim Proj(R/I) ;

     -- take care of the special cases I = (0) and I = (1) 
     if I == ideal(0_R) then (
	  chernList := apply(0..dimension, i-> binomial(dimension, i));
	  return (chernList,ambientDim);
	  );
     if I == ideal(1_R) then (
	  chernList = {};
	  return (chernList,ambientDim);
	  ); 

     (segreList,ambientDim) := internalSegre(I); 
     chernList = for i from 0 to dimension list sum( 0..i, p -> binomial( ambientDim + 1, i-p )*segreList_p );
     return  (chernList, ambientDim)
        
     )



-- The function checkUserInput checks that the given ideal I is a homogeneous ideal in a polynomial ring over a field.
checkUserInput = I -> (
        
     -- Is the ring a polynomial ring?
     if not isPolynomialRing ring I then error "The ideal needs to be defined over a polynomial ring.";
     
     -- Is the ideal homogeneous?
     if not isHomogeneous I then error "The ideal has to be homogeneous.";
     
     -- Is the coefficient ring a field (to make dimension command work)?
     if not isField coefficientRing ring I then error "The coefficient ring needs to be a field.";
     )


-- The function prepare does two things to prepare the later computations. Firstly, it trims the ideal I, taking away
-- nonnecessary generators. Then it creates a ring only used internally and an ideal in it isomorphic to I and returns this ideal. This 
-- step is done to avoid possible later conflicts in the choice of variables.
prepare = I -> (

     --trim I
     localI := trim I;     
     
     -- rename variables
     numGen := numgens ring localI;
     coeffRing := coefficientRing ring localI;
     z := symbol z;
     internalR := coeffRing[z_1 .. z_numGen];
     renamingMap := map(internalR, ring localI, {z_1 .. z_numGen});
     return renamingMap localI;
     )

-- The function output turns a list of degrees of characteristic classes into a polynomial in the Chow ring of the ambient space P^k.
-- This ring is generated by the hyperplane class.
-- Input:  segreList, a list {deg s_0, ..., deg s_n} of integers
--         ambientDim, the dimension k of ambient space P^k
--         hyperplaneClass, the symbol for the hyperplane class
-- Output: the polynomial (deg s_0)*hyperplaneClass^ambientDim + ... + (deg s_n)*hyperplaneClass^(ambientDim - n)
output = (segreList,ambientDim,hyperplaneClass) -> (
     -- produce the Chow ring ZZ[hyperplaneClass]/(hyperplaneClass^ambientDim+1)
     tempRing := ZZ[hyperplaneClass];
     outputRing := tempRing / ideal((tempRing_0)^(ambientDim+1));
     -- obtain the dimension n
     dimension := #segreList-1;
     -- create the polynomial (deg s_0)*hyperplaneClass^ambientDim + ... + (deg s_n)*hyperplaneClass^(ambientDim - n)
     return  sum(0..dimension, i -> segreList_i * (outputRing_0)^(ambientDim - dimension + i))
     )



----------------------------------------------
-- Documentation
---------------------------------------------



beginDocumentation()

doc ///
     Key
     	  characteristicClasses
     Headline
     	  Degrees of Chern and Segre classes
     Description
     	  Text
	       The package characteristicClasses provides commands to compute the degrees of the Chern and Segre classes of subvarieties and subschemes of projective space. 
	       Equivalently, it computes the pushforward to projective space of the Chern and Segre classes.
	       
	       Let X be an n-dimensional subscheme of projective space P^k. If X is smooth, then by definition the Chern classes of X are the Chern classes c_0(T_X), ..., c_n(T_X) of the tangent bundle T_X. The Chern classes are cycles in the Chow ring of X, i.e. linear combinations of subvarieties of X modulo rational equivalence. For a subvariety V of X, the degree of the cycle [V] is defined as the degree of the variety V. This extends linearly to linear combinations of subvarieties. Computing the degrees of the Chern classes of X is equivalent to computing the pushforward of the Chern classes to the Chow ring of P^k, which is the ring ZZ[H]/(H^{k+1}), with H the hyperplane class. Also by definition, the Segre classes of the projective scheme X are the Segre classes s_0(X,P^k), ..., s_n(X,P^k) of X in P^k. For definition of the concepts used here, see e.g. W. Fulton "Intersection Theory".
	       
	       The functions in this package can have two different kinds of output. The functions chernClass and segreClass give back the pushforward of the total Chern class to the Chow ring of P^k, whereas chernClassList and segreClassList give a list of the degrees of the Chern or Segre classes, respectively. The scheme X can be given as either a homogeneous ideal in a polynomial ring over a field, or as projective variety.
	       
	       This implementation uses the algorithm given in the  articles "Chern Numbers of Smooth Varieties via Homotopy Continuation and Intersection Theory" (Sandra Di Rocco, David Eklund, Chris Peterson, Andrew J. Sommese) and "A method to compute Segre classes" (David Eklund, Christine Jost, Chris Peterson).
	       
      
///

doc ///
     Key
     	  segreClass
	  (segreClass,Ideal)
	  (segreClass, ProjectiveVariety)
	  (segreClass, Ideal, Symbol)
	  (segreClass, ProjectiveVariety, Symbol)	  
     Headline
     	  Degrees of the Segre classes
     Usage
     	  segreClass I
	  segreClass P
     Inputs
     	  I:Ideal
	    a homogeneous ideal in a polynomial ring over a field, defining a closed subscheme X of P^k
	  P:ProjectiveVariety
	    a projective variety X
     Outputs
     	  :RingElement
	   the pushforward of the total Segre class of the scheme X to the Chow ring ZZ[H]^(H^{k+1}) of projective space P^k.
     Description
     	  Text
	       For an n-dimensional subscheme X of projective space P^k, this command computes the push-forward of the total Segre class of X in P^k to the Chow ring of P^k. The output is a polynomial in the hyperplane class, containing the degrees of the Segre classes s_0(X,P^k),...,s_n(X,P^k) as coefficients.
	  Example
	       R = QQ[x,y,z]
	       segreClass ideal (x*z - y^2)	  
	  Text
	       So the degrees of the Segre classes of the plane curve C = {x*z-y^2 = 0} are deg s_0(C,P^2) = 2 and deg s_1(X,P^2) = -4. It is also possible to provide the symbol for the hyperplane class in the Chow ring of P^k:
	  Example
	       segreClass( ideal( x*z - y^2), symbol t )  
///
     
doc ///
     Key
     	  chernClass
	  (chernClass,Ideal)
	  (chernClass, ProjectiveVariety)
	  (chernClass, Ideal, Symbol)
	  (chernClass, ProjectiveVariety, Symbol)	  
     Headline
     	  computes degrees of the Chern classes
     Usage
     	  chernClass I
	  chernClass P
     Inputs
          I:Ideal
	    a homogeneous ideal in a polynomial ring over a field, defining a projective scheme X
	  P:ProjectiveVariety
	    a projective variety X
     Outputs
     	  :RingElement
	   the pushforward of the total Chern class of the scheme X to the Chow ring ZZ[H]^(H^{k+1}) of projective space P^k.
     Description
     	  Text
	       For an n-dimensional subscheme X of projective space P^k, this command computes the push-forward of the total Chern class of X to the Chow ring of P^k. The output is a polynomial in the hyperplane class, containing the degrees of the Chern classes c_0(T_X),...,c_n(T_X) as coefficients.
	  Example
	       R = QQ[x,y,z]
	       chernClass ideal (x*z - y^2)	  
	  Text
	       So the degrees of the Chern classes of the plane curve C = {x*z-y^2 = 0} are deg s_0(C,P^2) = 2 and deg s_1(X,P^2) = 2. This agrees with the theoretical results stating that deg s_0(C,P^2) is the degree and deg s_1(C,P^2) the Euler characteristic 2-2g of C. It is also possible to provide the symbol for the hyperplane class in the Chow ring of P^k:
	  Example
	       chernClass( ideal( x*z - y^2), symbol t ) 
///

doc ///
     Key
     	  segreClassList
	  (segreClassList, Ideal)
	  (segreClassList, ProjectiveVariety)
     Headline
     	  computes degrees of the Segre classes
     Usage
     	  segreClassList I
	  segreClassList P
     Inputs
          I:Ideal
	    a homogeneous ideal in a polynomial ring over a field, defining a subscheme X of P^k
	  P:ProjectiveVariety
	    a projective variety X
     Outputs
     	  :List
	   A list \{ deg s_0(X,P^k),..., deg s_n(X,P_K) \} of the degrees of the Segre classes of X in P^k
     Description
     	  Text
	       This function does the same as the function segreClass, but provides an output that is easier to read for a computer.
///



doc ///
     Key
     	  chernClassList
	  (chernClassList, Ideal)
	  (chernClassList, ProjectiveVariety)
     Headline
     	  degrees of Chern classes
     Usage
     	  chernClassList I
	  chernClassList P
     Inputs
          I:Ideal
	    a homogeneous ideal in a polynomial ring over a field, defining a projective scheme X
	  P:ProjectiveVariety
	    a projective variety X
     Outputs
     	  :List
	   A list \{ deg c_0(T_X),..., deg c_n(T_X) \} of the degrees of the Chern classes of X
     Description
     	  Text
	       This function does the same as the function chernClass, but provides an output that is easier to read for a computer.
///
   
   
   
--------------------------------------------------------
-- Tests
--------------------------------------------------------
 

TEST ///
   R = QQ[x,y,z]
   assert( segreClassList ideal x == {1,-1} )
   assert( chernClassList ideal x == {1,2} )
 ///
 
TEST ///
   R = QQ[x,y,z]
   totalSegre = segreClass ideal x
   assert( totalSegre == (ring(totalSegre))_0 - ((ring(totalSegre))_0)^2 )
   totalChern = chernClass ideal x
   assert( totalChern == (ring(totalChern))_0 +2 * ((ring(totalChern))_0)^2 )
///



-------------------------------------------------------
-- References
------------------------------------------------------
-- [1] A method to compute Segre classes (David Eklund, Christine Jost, Chris Peterson)