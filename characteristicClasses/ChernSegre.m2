-- -*- coding: utf-8 -*-
newPackage(
	"ChernSegre",
    	Version => "0.1", 
    	Date => "July 25, 2011",
    	Authors => {{Name => "Christine Jost", 
		  Email => "jost@math.su.se", 
		  HomePage => "http://www.math.su.se/~jost"}},
    	Headline => "Degrees of Chern and Segre classes",
    	DebuggingMode => true
    	)

export {segreClass, chernClass, segreClassList, chernClassList}

-- internal commenting!!!

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


internalSegreClassList = I -> (
     checkUserInput I;
     localI := prepare I;
     return internalSegre localI;
     )


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


internalChernClassList = I -> (
     checkUserInput I;
     localI := prepare I;
     return internalChern localI;
     )






 
 
internalSegre = I -> (
    
     -- Obtain:
     -- the ring R 
     -- the dimension of the ambient space
     -- the dimension n of Z
     -- a list of the generators of I sorted by degree
     -- the maximal degree of the generators of I and
     -- a generator of I with minimal degree
     R := ring I;
     ambientDim := dim Proj R;
     dimension := dim Proj(R/I) ;
     
     s:= {};
     
     
     if I == ideal(0_R) then (
	  s = for i from 0 to dimension list if i==0 then 1 else 0;
	  return (s,ambientDim);
	  );
     if I == ideal(1_R) then (
	  s = {};
	  return (s,ambientDim);
	  );    
     
     
     
     gensI := flatten entries sort gens I;
     maxDeg := first max degrees I; 
     minDegGen := first gensI;
     

    
     -- Pick random elements in I of degree maxdeg, as many as the dimension of the ambient space, store in the list f.
     f := for i from 1 to ambientDim list sum( gensI, g -> g * random(maxDeg - first(degree(g)), R) );      
     
     -- The for loop computes the degrees of the Segre classes of Z, stores them in the list s.
     for d from (ambientDim - dimension) to ambientDim do (
	  
	  -- Obtain the ideal J of the intersection of d hypersurfaces containing Z, where d = comdimension of Z, ..., dimension of the ambient space.
	  J := ideal(take(f,d));
	  
	  -- Compute the residual of Z in the intersection of the d hypersurfaces, using saturation. Compute the degree of the residual. 
	  residual := saturate(J,minDegGen);
	  residualDeg := if residual != ideal vars R then degree residual else 0;
	  
     	  -- Using the degree of the residual, compute the degree of the pth Segre class, where p = d - codimension of Z.
	  p := d - (ambientDim - dimension);
	  degSegreClass := maxDeg^d - residualDeg - sum( 0..(p-1), i -> binomial(d,p-i)*maxDeg^(p-i)*s_i );
	  
	  s = append(s, degSegreClass);
	    
	  );
     
     return (s, ambientDim);
     
     )




internalChern = I -> (
 
     
     -- Compute the Segre classes use them to compute the Chern-Fulton classes.     
     (segreList,ambientDim) := internalSegre(I);   
     dimension := #segreList - 1;
     chernList := for i from 0 to dimension list sum( 0..i, p -> binomial( ambientDim + 1, i-p )*segreList_p );
     return  (chernList, ambientDim)
        
     )




checkUserInput = I -> (
        
     -- Is the ring a polynomial ring?
     if not isPolynomialRing ring I then error "The ideal needs to be defined over a polynomial ring.";
     
     -- Is the ideal homogeneous?
     if not isHomogeneous I then error "The ideal has to be homogeneous.";
     
     -- Is the coefficientRing a field (to make dimension command work)?
     if not isField coefficientRing ring I then error "The coefficient ring needs to be a field.";
     )



prepare = I -> (

     --trim I
     localI := trim I;     
     
     -- rename variables to avoid later collisions
     numGen := numgens ring localI;
     coeffRing := coefficientRing ring localI;
     z := symbol z;
     R := coeffRing[z_1 .. z_numGen];
     renamingMap := map(R, ring localI, {z_1 .. z_numGen});
     return renamingMap localI;
     )



output = (segreList,ambientDim,hyperplaneClass) -> (
     -- produces the ring ZZ[hyperplaneClass]/(hyperplaneClass^ambientDim+1)
     tempRing := ZZ[hyperplaneClass];
     outputRing := tempRing / ideal((tempRing_0)^(ambientDim+1));
     
     -- reserved symbol
     dimension := #segreList-1;
     return  sum(0..dimension, i -> segreList_i * (outputRing_0)^(ambientDim - dimension + i))
     )




beginDocumentation()

doc ///
     Key
     	  ChernSegre
     Headline
     	  Degrees of Chern and Segre classes
     Description
     	  Text
	       The package ChernSegre provides commands to compute the degrees of the Chern and Segre classes of subvarieties and subschemes of projective space. 
	       Equivalently, it computes the pushforward to projective space of the Chern and Segre classes.
	       
	       Let X be an n-dimensional subscheme of projective space P^k, with embedding i: X -> P^k. If X is smooth, then by definition the Chern classes of X are the Chern classes c_0(T_X), ..., c_n(T_X) of the tangent bundle T_X. The Chern classes are cycles in the Chow ring of X, i.e. linear combinations of subvarieties of X modulo rational equivalence. For a subvariety V of X, the degree of the cycle [V] is defined as the degree of the variety V. This extends linearly to linear combinations of subvarieties. Computing the degrees of the Chern classes of X is equivalent to computing the pushforward of the Chern classes to the Chow ring of P^k, which is the ring ZZ[H]/(H^{k+1}), with H the hyperplane class. Also by definition, the Segre classes of the projective scheme X are the Segre classes s_0(X,P^k), ..., s_n(X,P^k) of X in P^k. For definition of the concepts used here, see e.g. W. Fulton "Intersection Theory".
	       
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
	    a homogeneous ideal in a polynomial ring over a field, defining a subscheme X of P^k
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
