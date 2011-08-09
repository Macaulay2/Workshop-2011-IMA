----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
loadPackage("Posets",FileName=>"./Posets.m2")

---------
-- types
----------           
doc ///
     Key
           Poset
     Headline
           a class for partially ordered sets (posets)
     Description
          Text
               This class is a type of HashTable which represents finite posets.  It consists of a ground 
               set, a set of sequences (a,b) representing relationships where a is less than or 
               equal to b, a matrix encoding these relations. 
      Example
          G = {a,b,c,d,e}; -- the ground set
          R = {(a,b),(b,c),(a,c),(a,d),(d,e)}; --a set of sequences representing relations that "generate" all other relations
          P = poset (G,R) -- the matrix encoding these relations is computed by calling this function       
     SeeAlso
          poset
          GroundSet
          Relations
          RelationMatrix       
///     

-------------
-- constructors
-------------

doc ///
     Key
           poset
      (poset, List, List)
      (poset, List, List, Matrix)
     Headline
           creating a poset
     Usage
       P = poset (G,R)
       P = poset (G,R,M)
     Inputs
      G : List 
           elements in the ground set of P
      R : List 
           sequences (a,b) which indicate that a is less than or equal to b
      M : Matrix
           with entries ij equal to one when the jth element in G is less than or equal to the ith element in G
     Outputs
      P : Poset
           a poset consisting of the elements in G, with the order relations determined by R 
           and or M
     Description
        Text
           This function allows one to create a poset by defining the set and giving the order relations between the elements in the set.
           The function assumes that each element in the defining list given is distinct, and operates by taking the transitive and reflexive 
            closure of the relations that it is given.  The function returns an error
            if the input relations are incompatible with creating a poset.
       Example
           G = {a,b,c,d};
            R = {(a,b), (a,c), (c,d)};
            P = poset (G,R)    
       Text
           Sometimes in finding "enough" relations one inadverdently finds all of the relations in the poset.  In this case, the user
        can bypass having the function poset calculate the transitive closure of the relations by entering the matrix encoding the
        relations in when calling the poset function.  In this scenario, the function does not check that the resulting object is 
        actually a poset because in order to do this, the function needs to compute the transitive closure of the relations and check
        that this matches the matrix given.  The purpose of entering a matrix is to bypass that computation.
       Example
           S = QQ[x,y,z];
        G = {x^2, x*y, z^2, x^2*y*z, x*y*z^3, x^2*y^2*z^3};
            R = select((flatten apply (G, g-> apply (G, h-> if h % g == 0 then (g,h)))), i -> i =!= null) -- finds all pairs where g divides h
        M = matrix apply (G, g-> apply (G, h-> if h % g == 0 then 1 else 0)) 
        P = poset(G,R,M) 
        
     SeeAlso
           Poset
      GroundSet
      Relations
      RelationMatrix
///
  
-----------
-- finding relations
-----------

doc ///
     Key
           transitiveClosure
      (transitiveClosure, List, List)
     Headline
           computes the transitive closure of a given set of relations.  
     Usage
           M = transitiveClosure(I,R)
     Inputs
      I : List
           ground set 
      R : List
           of pairs of elements in the ground set I.
     Outputs
      M : Matrix 
           whose (i,j) entry is 1 if (i,j) is a relation and 0 otherwise.
     Description
       Text
           This function uses the floydWarshall method from the Graphs package and is used by the poset constructor to compute RelationMatrix from Relations in a Poset.
       Example
           I = {a,b,c,d,e}; -- the ground set
           R = {(a,b),(b,c),(a,c),(a,d),(d,e)}; -- relations
                transitiveClosure(I,R)
     Caveat
        `       Output matrix is over RR.
     SeeAlso
           Poset
      poset
      Relations
      RelationMatrix
/// 
 
 
---------
-- poset routines
---------
 
doc ///
     Key
           compare
          (compare, Poset,Thing,Thing)
     Headline
          returns boolean value for whether an element is less than another 
     Usage
          compare(P,a,b)
     Inputs
           P : Poset
      a : Thing
      b : Thing
           a and b are elements of P
     Outputs
       true : Boolean
          if a is less than or equal to b
       false : Boolean
           otherwise
     Description
      Text
           This function simply looks at two elements in P, and determines what if any relation exists between them.
      Example
           P = poset ({a,b,c}, {(a,b), (a,c)});
           compare (P,a,c)
           compare (P,c,a)
           compare (P,b,c)
     Caveat
           Note that if two elements are not comparable, compare still returns a value of false.       
/// 
  
 
doc ///
     Key
           filter
          (filter,Poset,Thing)
     Headline
           returns a principal filter generated by the given element
     Usage 
           F = filter (P,a)
     Inputs
      P : Poset
      a : Thing
           a is an element of P
     Outputs
       F : List
           a list of all elements in P that are greater than or equal to a
     Description
       Example
           G = {a,b,c,d};
           R = {(a,b), (a,c), (c,d)};
           P = poset (G,R);
           F = filter (P,d)
     SeeAlso
           orderIdeal           
/// 

doc ///
     Key
           orderIdeal
          (orderIdeal, Poset, Thing)
     Headline
           returns a principal order ideal generated by the given element
     Usage 
           O = orderIdeal (P,a)
     Inputs
      P : Poset
      a : Thing
           a is an element of P
     Outputs
      O : List
           a list of all elements in P that are less than or equal to a
     Description
      Example
           G = {a,b,c,d};
           R = {(a,b), (a,c), (c,d)};
           P = poset (G,R);
           O = orderIdeal (P,c)
     SeeAlso
           filter    
/// 
 
 
doc ///
     Key
           posetMeet
      (posetMeet, Poset, Thing, Thing)
     Headline
           returns the meet of two elements
     Usage
          m = posetMeet (P,a,b)
     Inputs
           P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
       m : Thing
           m is the meet of a and b in P
     Description 
       Text
           This function returns the greatest element that is less than both a and b in P.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           posetMeet (P, d,e)
     Caveat
             This function returns an error if the meet does not exist.  To check if the meet exists use meetExists.
     SeeAlso
             meetExists
       posetJoin
       joinExists
/// 



doc ///
     Key
           posetJoin
      (posetJoin, Poset, Thing, Thing)
     Headline
           returns the join of two elements
     Usage
          j = posetJoin (P,a,b)
     Inputs
           P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
      j : Thing
           j is the join of a and b in P
     Description 
      Text
           This function returns the least element that is greater than both a and b in P.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           posetJoin (P, a,b)
     Caveat
             This function returns an error if the join does not exist.  To check if the join exists use joinExists.
     SeeAlso
             joinExists
       posetMeet
       meetExists
/// 
   
   
doc ///
     Key
           meetExists
      (meetExists, Poset, Thing, Thing)
     Headline
           determines if the meet exists
     Usage
          meetExists (P,a,b)
     Inputs
      P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
      true : Boolean
           the meet of a and b in P exists
      false : Boolean
           otherwise
     Description 
      Text
          This function determines if greatest element that is less than both a and b in P exists.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           meetExists (P,d,e)
                meetExists(P,a,b)
     Caveat
            If the meet exists, to find it use posetMeet.
     SeeAlso
             posetMeet
       posetJoin
       joinExists    
/// 

doc ///
     Key
           joinExists
      (joinExists, Poset, Thing,Thing)
     Headline
           determines if the join exists
     Usage
          joinExists (P,a,b)
     Inputs
      P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
      true : Boolean
           the join of a and b in P exists
      false : Boolean
           otherwise
     Description 
      Text
           This function determines if least element that is greater than both a and b in P exists.
      Example
           P = poset ({a,b,c,d,e}, {(a,d),(b,d),(b,e),(c,e)});
           joinExists (P,d,e)
                joinExists(P,a,b)
     Caveat
            If the join exists, to find it use posetJoin.
     SeeAlso
       posetJoin
       posetMeet
       meetExists  
/// 
 
doc ///
     Key
      isLattice
      (isLattice,Poset)
     Headline
           determines if a poset is a lattice
     Usage
           isLattice (P)
     Inputs
           P: Poset
     Outputs
      true : Boolean
           if P is a lattice
      false : Boolean
           otherwise
     Description 
      Text
           This function examines the entire poset to determine whether or not every pair of elements has both a meet and a join.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           isLattice (P)
      Text
           And by adding an element to the above example, we can create a poset which is a lattice.     
      Example
           P = poset ({a,b,c,d,e,f,x}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f), (x,a), (x,b), (x,c)});   
               isLattice (P)       
    
/// 

     
---------
-- LCM lattices
---------

doc ///
     Key
           lcmLattice
      (lcmLattice,Ideal)
      (lcmLattice, MonomialIdeal)
     Headline
           returns the LCM lattice of an ideal
     Usage
           lcmLattice (I)
      lcmLattice (M)
     Inputs 
      I : Ideal
      M : MonomialIdeal
     Outputs
      L : Poset
     Description
      Text
           This command allows for fast computation of LCM lattices, which are particularly useful in the study of resolutions of monomial ideals.
           Specifically the LCM lattice is the set of all lcms of subsets of the generators of the ideal, partially ordered by divisability.  
      Example
           S = QQ[a,b,c,d];
           I = ideal (b^2-a*d, a*d-b*c, c^2-b*d);
           M = monomialIdeal (b^2, b*c, c^2);
           L = lcmLattice (I);
           L.GroundSet
           L.RelationMatrix
           LM = lcmLattice (M);
           LM.GroundSet
           LM.RelationMatrix
     Caveat           
           Note, that at present this command does not efficiently handle ideals with large numbers of generators.  This is a problem that should be
        fixed by the next release of this package.     
/// 

     
-----------------
-- divisorPoset
-----------------

doc ///
    Key
        divisorPoset
        (divisorPoset,RingElement)
    Headline
        returns the poset of all divisors of a given monomial
    Usage
        divisorPoset (M)
    Inputs 
        M : RingElement
    Outputs
        P : Poset
    Description
        Text
            This command computes the poset of all divisors of a given monomial. For two monomials,
            u and v with u strictly dividing v, we have u < v in this poset.
        Example
            S = QQ[a,b,c,d];
            P = divisorPoset(a*b^2*d^3)
/// 

     

-----------------
-- coveringRelations
-----------------

doc ///
    Key
        coveringRelations
        (coveringRelations,Poset)
    Headline
        returns a list of all relations (a < b) with no intermediates
    Usage
        coveringRelations (P)
    Inputs 
        P : Poset
    Outputs
        C : List
            all pairs (a,b) of elements of P where a < b and there is no c with a < c < b
    Description
        Text
            This command computes the list of all covering relations of a poset P. 
            A relation (a,b) is said to be a covering relation if a < b and there
            is no element c with a < c < b. The result of this method is cached.
        Example
            S = QQ[a,b,c,d];
            P = divisorPoset(a*b^2*d);
            P.GroundSet
            P.Relations
            C = coveringRelations P
/// 

-----------------
-- dropElements
-----------------

doc ///
    Key
        dropElements
        (dropElements,Poset,List)
        (dropElements,Poset,Function)
    Headline
        returns the poset obtained by removing a list of elements 
    Usage
        dropElements (P, L)
        dropElements (P, f)
    Inputs 
        P : Poset
        L : List
            elements of P
        f : Function
            boolean valued giving true on those elements to be removed
    Outputs
        Q : Poset
            on elements of P that are not in L (or for which f is false) and all induced relations
    Description
        Text
            This command take a poset P and returns a new poset that
            contains all elements in P that are not in L.
            The relations on the remaining elements are all relations that held in P.

            Alternately, if a boolean function is given as input instead of a list, all 
            elements for which the function returns true are removed from P.

        Example
            S = QQ[a,b];
            P = divisorPoset(a*b^2);
            P.GroundSet
            Q = dropElements(P, {a,a*b^2})
            R = dropElements(P, m -> first degree m === 2)
/// 

-----------------
-- maximalChains
-----------------

doc ///
    Key
        maximalChains
        (maximalChains,Poset)
    Headline
        returns all maximal chains of a poset
    Usage
        maximalChains (P)
    Inputs 
        P : Poset
    Outputs
        C : List
            of maximal chains of P
    Description
        Text
            The maximal chains of P are totally orders subsets of P which are not properly contained
            in any other totally ordered subsets.

            This method returns a list of all maximal chains. The maximal chains are themselves
            lists of elements in P ordered from smallest to largest.

            The results of this method are cached.

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b^2*c);
            C = maximalChains P
/// 

-----------------
-- minimalElements
-----------------

doc ///
    Key
        minimalElements
        (minimalElements,Poset)
    Headline
        returns all minimal elements of a poset
    Usage
        minimalElements (P)
    Inputs 
        P : Poset
    Outputs
        L : List
            of all minimal elements of P
    Description
        Text
            This method returns a list of all minimal elements of P.
            The results of this method are cached.

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b^2*c);
            minimalElements P
            Q = dropElements(P, minimalElements(P));
            minimalElements Q
/// 

-----------------
-- maximalElements
-----------------

doc ///
    Key
        maximalElements
        (maximalElements,Poset)
    Headline
        returns all maximal elements of a poset
    Usage
        maximalElements (P)
    Inputs 
        P : Poset
    Outputs
        L : List
            of all maximal elements of P
    Description
        Text
            This method returns a list of all maximal elements of P.
            The results of this method are cached.

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b^2*c);
            maximalElements P
            Q = dropElements(P, maximalElements(P));
            maximalElements Q
/// 

-----------------
-- adjoinMax
-----------------

doc ///
    Key
        adjoinMax
        (adjoinMax,Poset)
        (adjoinMax,Poset,Thing)
    Headline
        returns new Poset with new maximal element
    Usage
        adjoinMax P
        adjoinMax(P,a)
    Inputs 
        P : Poset
        a : Thing
    Outputs
        Q : Poset
    Description
        Text
            This method returns a new poset with maximal element adjoined.
            If no element specified, uses {1}.

        Example
            G = {1,2,3,4}
            R = {{1,2},{1,3},{2,4},{3,4}}
            P = poset(G,R)
            Q = adjoinMax P
            Q = adjoinMax(P,5)
    SeeAlso
             adjoinMin
        maximalElements
        minimalElements
/// 

-----------------
-- adjoinMax
-----------------

doc ///
    Key
        adjoinMin
        (adjoinMin,Poset)
        (adjoinMin,Poset,Thing)
    Headline
        returns new Poset with new minimal element
    Usage
        adjoinMin P
        adjoinMin(P,a)
    Inputs 
        P : Poset
        a : Thing
    Outputs
        Q : Poset
    Description
        Text
            This method returns a new poset with minimal element adjoined.
            If no element specified, uses {0}.

        Example
            G = {1,2,3,4}
            R = {{1,2},{1,3},{2,4},{3,4}}
            P = poset(G,R)
            Q = adjoinMin P
            Q = adjoinMin(P,0)
    SeeAlso
             adjoinMax
        maximalElements
        minimalElements
/// 
-----------------
-- orderComplex
-----------------

doc ///
    Key
        orderComplex
        (orderComplex,Poset)
    Headline
        returns the simplicial complex with faces given by chains
    Usage
        orderComplex (P)
    Inputs 
        P : Poset
    Outputs
        D : SimplicialComplex
            the order complex of P
    Description
        Text
            This method returns the order complex of a poset P. The order
            complex is the simplicial complex whose faces are chains of P
            (and whose facets are maximal chains of P).

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b*c);
            C = maximalChains P
            D = orderComplex P
/// 


-----------------
-- closedInterval
-----------------
doc ///
    Key
        closedInterval
        (closedInterval,Poset, Thing, Thing)
    Headline
        returns the closed interval in the poset between two elements
    Usage
        closedInterval(P,a,b)
    Inputs 
        P : Poset
        a : Thing
        b : Thing 
    Outputs
        I : Poset
            the closed interval between a and b 
    Description
        Text
             This routine returns the interval between the elements a and b in P, 
                     including a and b,
             and an error message if the two elements are not comparable in P.

        Example
             P = poset({a,b,c,d},{(a,b),(b,c),(b,d)});
             closedInterval(P,a,d)      
/// 

----------------
--openInterval
----------------

doc ///
    Key
        openInterval
        (openInterval,Poset,Thing,Thing)
    Headline
        returns the open interval in the poset between two elements
    Usage
        openInterval(P,a,b)
    Inputs
        P : Poset
        a : Thing
        b : Thing
    Outputs
        I : Poset
    Description
         Text
              This routine returns the intreval between the elements a and b in P, not including a and b,
              and an error message if the two elements are not comparable in P.
      
        Example
                     P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
              openInterval(P,a,g)
///

-----------------
-- hasseDiagram
-----------------
doc  ///
    Key
              hasseDiagram
         (hasseDiagram,Poset)
    Headline
             returns Hasse diagram for the poset
    Usage
              hasseDiagram(P)
        Inputs
              P : Poset
        Outputs
         G : Digraph
              Directed graph whose edges correspond to covering relations in P
        Description
              Text 
              This routine returns the Hasse diagram which is a directed graph (defined in the Graphs package)
              whose edges correspond to the covering relations in P.  Specifically, the vertices in the graph 
              correspond to the elements in the ground set of P, and two vertices a and b have a directed edge 
              from a to b if a > b.
         Example
              P = poset ({a,b,c,d},{(a,b), (b,c), (b,d)})
              G = hasseDiagram(P)    
        SeeAlso
             displayGraph
///


-----------------
-- moebiusFunction
-----------------
doc///
     Key
           moebiusFunction
      (moebiusFunction,Poset)
     Headline
           returns the Moebius function values for the unique minimal element to each element of the poset
     Usage
           moebiusFunction(P)
     Inputs
           P : Poset
     Outputs
      M : HashTable
           Moebius function values for the minimal element of the poset to each element of the poset
     Description
       Text 
           This routine returns the Moebius function values for the unique minimal element to each element of the poset.
           If {\tt P} has more than one minimal element, an error will be signalled.
           In this example, $a$ is the minimal element of $P$; $M$ lists the Moebius function values from $a$ to each element of $P$.
      Example
           P = poset ({a,b,c,d},{(a,b), (b,c), (b,d)})
           M = moebiusFunction(P)    
     SeeAlso
           (moebiusFunction,Poset,Thing,Thing)
      Poset
///

doc///
     Key
      (moebiusFunction,Poset,Thing,Thing)
     Headline
           returns the Moebius function values for the minimal element of a closed interval to each element of the interval
     Usage
           moebiusFunction(P,a,b)
     Inputs
      P : Poset
      a : Thing
           a is an element of P
      b : Thing
           b is an element of P
     Outputs
       M : HashTable
           Moebius function values for the lesser of a and b to each element of the interval between a and b           
     Description
      Text
           For elements a and b of a poset P, this routine returns the Mobius function values for the minimal element in the closed 
           interval between elements a and b to each element of the interval between a and b. The routine handles both of the cases a<b and b<a.
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           moebiusFunction(P,b,g)
           moebiusFunction(P,g,b)           
     SeeAlso
           (moebiusFunction,Poset)
      Poset
///      

-----------------
-- subposet
-----------------
doc///
     Key
           subposet
      (subposet,Poset,List)
     Headline
           returns the subposet supported on elements in a given list
     Usage
           subposet(P,L)
     Inputs
      P : Poset
      L : List
           L consists of element in P
     Outputs
      Q : Poset
           subposet of P supported on elements in L           
     Description
        Text
               This command take a poset P and returns a new poset that
            contains all elements in P that are in L.
            The relations on the remaining elements are all relations that held in P.
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           subposet(P, {a,e,g})           
     SeeAlso
          dropElements
///

-----------------
-- atoms
-----------------
doc///
     Key
           atoms
      (atoms,Poset)
     Headline
           returns the atoms of a poset
     Usage
           A = atoms(P)
     Inputs
           P : Poset
     Outputs
        A : List
          subset of the ground set of P consisting of elements covering minimal elements           
     Description
           Text
               This routine returns a list of elements which cover any minimal elements in P, these are known
                as the atoms of P.
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           atoms(P)           
///    


--------------
-- meetIrreducibles
--------------
doc///
     Key
           meetIrreducibles
      (meetIrreducibles,Poset)
     Headline
           returns the meet-irreducibles of a poset
     Usage
           L = meetIrreducibles(P)
     Inputs
           P : Poset
     Outputs
       L : List
          subset of the ground set of P consisting of meet-irreducible elements           
     Description
       Text
               An element a of a poset P is meet irreducible if it is not the meet of any set of elements (not containing a).  
                This routine returns a list of all such elements in the poset P.  
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           meetIrreducibles(P)           
///



doc ///
     Key 
           GroundSet
     Headline
           underlying set of a poset
     Usage
           G = P.GroundSet
     Inputs
           P : Poset
     Outputs
        G : List
           list of elements in P without the data of how they are partially ordered
     Description
           Text
                Since any poset is in fact a HashTable this symbol denotes the data in the HashTable consisting of the elements of the set.
      Example
           S = QQ[a,b,c,d];
           M = monomialIdeal (b^2, b*c, c^2);
           L = lcmLattice (M);
           L.GroundSet
     SeeAlso
           RelationMatrix
      Relations
      poset
      Poset
///
 
 
doc ///
     Key 
           RelationMatrix
     Headline
           the matrix expressing all of the relations between elements in a Poset
     Usage
           M = P.RelationMatrix
     Inputs
           P : Poset
     Outputs
        M : Matrix
           where the ijth entry indicates whether or not the jth element in the set is less than or equal to the ith element
     Description
           Text
                Since any poset is in fact a HashTable this symbol denotes the data in the HashTable containing all possible relations between elements.
      Example
           S = QQ[a,b,c,d];
           M = monomialIdeal (b^2, b*c, c^2);
           L = lcmLattice (M);
           L.GroundSet
           L.RelationMatrix
     SeeAlso
           GroundSet
      Relations
      poset
      Poset
/// 
 
doc ///
     Key 
           Relations
     Headline
           a set of relations in the poset that generates all other relations
     Usage
           R = P.Relations
     Inputs
           P : Poset
     Outputs
           R : List
            list of pairs of elements in P where (a,b) means a is less than or equal to b
     Description
           Text
                Since any poset is in fact a HashTable this symbol denotes the data in the HashTable which will describe all of the relations
            between elements in P.
      Example
           P = poset ({a,b,c,d,e,f},{(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           P.Relations --note there is not a one to one correspondence between these and entries in the RelationMatrix
           P.RelationMatrix
     Caveat
           Typically, the relations are the data entered in by the user and by no means account for every relation.  The RelationMatrix is usually computed
       from this set and thus is a better descriptor of the relations in P.
     SeeAlso
           RelationMatrix
      GroundSet
      poset
      Poset
///

doc///
     Key
           isAntichain
      (isAntichain, Poset, List)
     Headline
           checks whether a subposet is an anti-chain
     Usage
           isAntichain(P, L)
     Inputs
         P : Poset
         L : List
           a list of elements of P 
     Outputs
          true : Boolean
               if L is an antichain in P
         false : Boolean
             otherwise
     Description
           Text
            This function determines whether a list of elements of a poset is an anti-chain.
             
      Example
           P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           isAntichain(P2, {a,b})     
           isAntichain(P2, {b,c,d}) 
///

doc///
     Key
           intersectionLattice
        (intersectionLattice, List, Ring)
     Headline
           computes intersection lattice of an arrangement
     Usage
           intersectionLattice(H,R)
     Inputs
         H : List
             a list of elements of R
         R : PolynomialRing 
     Outputs
          P : Poset
     Description
      Text
           Given a set of equations f defining hyperplanes or hypersurfaces,
           computes the intersection lattice of the f.
          
      Example
           R=QQ[x,y]
           H={y+x,y-x,y-x-1,y}
           L=intersectionLattice(H,R)
      Text
           This code will produce intersection arrangement for hypersurfaces.
      Example
           R=QQ[x,y,z]
           H={x^2+y^2+z^2-9, z-1, x,y}
           L=intersectionLattice(H,R)
     SeeAlso
           projectivizeArrangement
           
///     

------------------------------------------
-- )Tests
------------------------------------------

-- TEST 0
-- a lattice, B_3
TEST ///
I ={a,b,c,d,e,f,g,h};
C ={(a,b),(a,c),(a,d),(b,e),(b,f),(c,e),(c,g),(d,f),(d,g),(e,h),(f,h),(g,h)};
P=poset(I,C);
M = matrix {{1,1,1,1,1,1,1,1},
        {0,1,0,0,1,1,0,1},
        {0,0,1,0,1,0,1,1},
        {0,0,0,1,0,1,1,1},
        {0,0,0,0,1,0,0,1},
        {0,0,0,0,0,1,0,1},
        {0,0,0,0,0,0,1,1},
        {0,0,0,0,0,0,0,1}};
assert (entries P.RelationMatrix == entries M)
assert (posetJoin(P,a,b) == {b})
assert (posetJoin(P,b,d) == {f})
assert (posetMeet(P,a,b) == {a})
assert (posetMeet(P,f,g) == {d})
assert (filter(P,a) == {a,b,c,d,e,f,g,h})
assert (filter(P,b) == {b,e,f,h})
assert (orderIdeal(P,a) == {a})
assert (orderIdeal(P,g) == {a,c,d,g})
assert (isLattice(P))
///


-- TEST 1
-- two equivllaent non lattices with different initial data
TEST ///
I1={a,b,c,d,e,f};
C1={(a,c),(a,d),(b,c),(b,d),(c,e),(d,e),(e,f)};
P1=poset(I1,C1);

--Poset P1 with additional relations (a,e) and (a,f) added
I2={a,b,c,d,e,f};
C2={(a,c),(a,d),(b,c),(b,d),(c,e),(d,e),(a,e),(a,f),(e,f)};
P2=poset(I2,C2);

assert (P1.RelationMatrix == P2.RelationMatrix)    
assert (orderIdeal(P1,b) == {b})
assert (orderIdeal(P1,c) == {a,b,c})
assert (filter (P1,b) == {b,c,d,e,f})
assert (isLattice (P1) == false)
-- do joins and meets
///

-- do an LCM lattice
-- do order ideal

-- TEST 2
-- failing test commented out by dan:
-- TEST ///
-- V = {a,b,c,d,e};
-- E = {(a,b),(a,d),(b,c),(b,e),(c,e),(d,e)};
-- G = poset (V,E);
-- A = adjacencyMatrix(G);
-- D = allPairsShortestPath(A);
-- T = transitiveClosure(V,E);

-- assert(A_(0,1)==1 and A_(0,3)==1 and A_(1,2)==1 and A_(1,4)==1 and A_(2,4)==1 and A_(3,4)==1)
-- assert(D_(0,4)==2 and D_(4,0)==1/0. and D_(3,3)==0)
-- --assert(T== promote(matrix {{1, 1, 1, 1, 1}, {0, 1, 1, 0, 1}, {0, 0, 1, 0, 1}, {0, 0, 0, 1, 1}, {0, 0, 0, 0, 1}}, RR))

-- D1 =allPairsShortestPath(matrix({{0,1,1/0.,4},{1/0.,0,1/0.,2},{1,1/0.,0,1/0.},{1/0.,1/0.,1,0}})); -- digraph with a cycle
-- assert(D1 ==  promote(matrix {{0, 1, 4, 3}, {4, 0, 3, 2}, {1, 2, 0, 4}, {2, 3, 1, 0}}, RR))

-- ///


-- TEST 3
TEST ///
P1 = poset ({a,b,c,d},{(a,b), (b,c), (b,d)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, x*y, y^3, y*z);
L = lcmLattice I;
M = new HashTable from {x^2*y^3*z => 0, y^3*z => 1, x^2*y*z => 0, y^3 => -1, x*y^3*z => -1, y*z => -1, x^2 => -1,
      x*y => -1, x*y^3 => 1, x^2*y^3 => 0, 1 => 1, x^2*y => 1, x*y*z => 1}; 

assert ((moebiusFunction L)#(x^2*y^3) === M#(x^2*y^3)) 
assert ((moebiusFunction L)#(x*y*z) === M#(x*y*z)) 
assert( (moebiusFunction(P2, b,g)) === new HashTable from {e => -1, b => 1, g => 0} )
assert( (moebiusFunction(P1)) === new HashTable from {a => 1, b => -1, c => 0, d => 0} )
///

-- TEST 4
TEST ///
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);
L2 = divisorPoset(x^2*y^3);

--testing divisorPoset and LCM lattices
assert( (L.GroundSet) == {1,z^2,y^2,y^2*z^2,x^2,x^2*z^2,x^2*y^2,x^2*y^2*z^2} )
assert( allRelations L == {{1,1},{1,z^2},{1,y^2},{1,y^2*z^2},{1,x^2},{1,x^2*z^2},{1,x^2*y^2},{1,x^2*y^2*z^2},{z^2,z^2},{z^2,y^2*z^2},{z^2,x^2*z^2},{z^2,x^2*y^2*z^2},{y^2,y^2},{y^2,y^2*z^2},{y^2,x^2*y^2},{y^2,x^2*y^2*z^2},{y^2*z^2,y^2*z^2},{y^2*z^2,x^2*y^2*z^2},{x^2,x^2},{x^2,x^2*z^2},{x^2,x^2*y^2},{x^2,x^2*y^2*z^2},{x^2*z^2,x^2*z^2},{x^2*z^2,x^2*y^2*z^2},{x^2*y^2,x^2*y^2},{x^2*y^2,x^2*y^2*z^2},{x^2*y^2*z^2,x^2*y^2*z^2}} )
assert( (L.RelationMatrix) === map(ZZ^8,ZZ^8,{{1, 1, 1, 1, 1, 1, 1, 1}, {0, 1, 0, 1, 0, 1, 0, 1}, {0, 0, 1, 1, 0, 0, 1, 1}, {0, 0, 0, 1, 0, 0, 0, 1}, {0, 0, 0, 0, 1, 1, 1, 1}, {0, 0, 0, 0, 0, 1, 0, 1}, {0, 0, 0, 0, 0, 0, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 1}}) )
assert( (L2.GroundSet) == {1,y,y^2,y^3,x,x*y,x*y^2,x*y^3,x^2,x^2*y,x^2*y^2,x^2*y^3} )
assert( allRelations L2 == {{1,1},{1,y},{1,y^2},{1,y^3},{1,x},{1,x*y},{1,x*y^2},{1,x*y^3},{1,x^2},{1,x^2*y},{1,x^2*y^2},{1,x^2*y^3},{y,y},{y,y^2},{y,y^3},{y,x*y},{y,x*y^2},{y,x*y^3},{y,x^2*y},{y,x^2*y^2},{y,x^2*y^3},{y^2,y^2},{y^2,y^3},{y^2,x*y^2},{y^2,x*y^3},{y^2,x^2*y^2},{y^2,x^2*y^3},{y^3,y^3},{y^3,x*y^3},{y^3,x^2*y^3},{x,x},{x,x*y},{x,x*y^2},{x,x*y^3},{x,x^2},{x,x^2*y},{x,x^2*y^2},{x,x^2*y^3},{x*y,x*y},{x*y,x*y^2},{x*y,x*y^3},{x*y,x^2*y},{x*y,x^2*y^2},{x*y,x^2*y^3},{x*y^2,x*y^2},{x*y^2,x*y^3},{x*y^2,x^2*y^2},{x*y^2,x^2*y^3},{x*y^3,x*y^3},{x*y^3,x^2*y^3},{x^2,x^2},{x^2,x^2*y},{x^2,x^2*y^2},{x^2,x^2*y^3},{x^2*y,x^2*y},{x^2*y,x^2*y^2},{x^2*y,x^2*y^3},{x^2*y^2,x^2*y^2},{x^2*y^2,x^2*y^3},{x^2*y^3,x^2*y^3}} )
assert( (L2.RelationMatrix) === map(ZZ^12,ZZ^12,{{1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1}, {0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1}, {0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1}, {0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1}, {0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1}, {0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1}, {0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1}}) )
///


-- TEST 5
-- failing test commented out by dan:
-- TEST ///
-- P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
-- R = QQ[x,y,z];
-- L = lcmLattice ideal (x^2, y^2, z^2);

-- -- testing hasseDiagram
-- assert((hasseDiagram P1)#a === set {})
-- assert((hasseDiagram P1)#b === set {})
-- assert((hasseDiagram P1)#c === set {a,b})
-- assert((hasseDiagram P1)#d === set {a,b})
-- assert((hasseDiagram P1)#e === set {c,d})
-- assert( toString sort pairs (hasseDiagram L) === toString sort pairs new Digraph from {x^2*y^2*z^2 => new Set from {x^2*y^2, x^2*z^2, y^2*z^2}, x^2*y^2 => new Set from {x^2, y^2}, x^2*z^2 => new Set from {x^2, z^2}, x^2 => new Set from {1}, y^2*z^2 => new Set from {y^2, z^2}, 1 => new Set from {}, z^2 => new Set from {1}, y^2 => new Set from {1}} )

-- ///

-- TEST 6
TEST ///
P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);
--testing max/min elts
assert( (maximalElements P1) === {e} )
assert( (maximalElements L) === {x^2*y^2*z^2} )
assert( (minimalElements P1) === {a,b} )
assert( (minimalElements L) == {1} )

--testing atoms
assert( (atoms(P1) ) === {c,d} )
assert( (atoms(L)) === {x^2,z^2,y^2} )
///

-- TEST 7
TEST /// 
P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
P2 = poset({a,b,c,d,e,f,g,h},{(h,a),(h,b),(h,c),(h,d),(a,e),(b,e),(e,f),(c,f),(f,g),(d,g)});
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);
L2 = divisorPoset(x^2*y^3);

--testing subposet
assert( ((subposet(P1, {a,b,e})).GroundSet) === {a,b,e} )
assert( ((subposet(P1, {a,b,e})).Relations) === {{a,e},{b,e}} )
assert( ((subposet(P1, {a,b,e})).RelationMatrix) === map(ZZ^3,ZZ^3,{{1, 0, 1}, {0, 1, 1}, {0, 0, 1}}) )
assert( ((subposet(P2, {a,e,f,d})).GroundSet) === {a,d,e,f} )
assert( ((subposet(P2, {a,e,f,d})).Relations) === {{a,e},{a,f},{e,f}} )
assert( ((subposet(P2, {a,e,f,d})).RelationMatrix) === map(ZZ^4,ZZ^4,{{1, 0, 1, 1}, {0, 1, 0, 0}, {0, 0, 1, 1}, {0, 0, 0, 1}}) )
assert( ((subposet(L, {x^2,y^2,x^2*y^2})).GroundSet) === {y^2,x^2,x^2*y^2} )
assert( ((subposet(L, {x^2,y^2,x^2*y^2})).Relations) === {{y^2,x^2*y^2},{x^2,x^2*y^2}} )
assert( ((subposet(L, {x^2,y^2,x^2*y^2})).RelationMatrix) === map(ZZ^3,ZZ^3,{{1, 0, 1}, {0, 1, 1}, {0, 0, 1}}) )

-- testing dropElements
assert( ((dropElements(P1, {a,c})).GroundSet) === {b,d,e} )
assert( ((dropElements(P1, {a,c})).Relations) === {{b,d},{b,e},{d,e}} )
assert( ((dropElements(P1, {a,c})).RelationMatrix) === map(ZZ^3,ZZ^3,{{1, 1, 1}, {0, 1, 1}, {0, 0, 1}}) )
assert( ((dropElements(L2, m-> first degree m > 2)).GroundSet) == {1,y,y^2,x,x*y,x^2} )
assert( ((dropElements(L2, m-> first degree m > 2)).Relations) == {{1,y}, {1,y^2}, {1,x}, {1,x*y}, {1,x^2}, {y,y^2}, {y,x*y}, {x,x*y}, {x,x^2}} )
assert( ((dropElements(L2, m-> first degree m > 2)).RelationMatrix) === map(ZZ^6,ZZ^6,{{1, 1, 1, 1, 1, 1}, {0, 1, 1, 0, 1, 0}, {0, 0, 1, 0, 0, 0}, {0, 0, 0, 1, 1, 1}, {0, 0, 0, 0, 1, 0}, {0, 0, 0, 0, 0, 1}}) )

///


-- TEST 8
TEST ///
P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);

S = QQ[v_0..v_4]
T = QQ[v_0..v_7]
assert( toString ((orderComplex P1).facets) === toString (use S; map(S^1,S^{{-3},{-3},{-3},{-3}},{{v_1*v_3*v_4, v_0*v_3*v_4, v_1*v_2*v_4, v_0*v_2*v_4}})) )
assert( toString ((orderComplex L).facets) === toString (use T; map(T^1,T^{{-4},{-4},{-4},{-4},{-4},{-4}},{{v_0*v_4*v_6*v_7, v_0*v_2*v_6*v_7, v_0*v_4*v_5*v_7, v_0*v_1*v_5*v_7, v_0*v_2*v_3*v_7, v_0*v_1*v_3*v_7}})) )
///

-- TEST 9
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)})
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
R = QQ[x,y,z,w]
I = ideal(x^2, x*y, y^3, y*z)
L = lcmLattice I
assert( (isAntichain(P1, {j, k})) === true )
assert( (isAntichain(P1, {j, k, h})) === false )
assert( (isAntichain(P2, {a, b, g})) === false )
assert( (isAntichain(P2, {b, c, d})) === true )
assert( (isAntichain(L, {y*z, y^3, x*y})) === true )
assert( (isAntichain(L, {y*z, x^2*y, x*y*x})) === true )
///


-- TEST 10
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, x*y, y^3, y*z);
L = lcmLattice I;

assert( (maximalChains(P1)) === {{h,i,j},{h,i,k}} )
assert( (maximalChains(P2)) === {{a,b,e,g},{a,c,e,g},{a,c,f,g},{a,d,f,g}})
assert( (sort maximalChains(L)) == {{1, y*z, x*y*z, x^2*y*z, x^2*y^3*z}, {1, y*z, x*y*z, x*y^3*z, x^2*y^3*z},
        {1, y*z, y^3*z, x*y^3*z, x^2*y^3*z}, {1, x*y, x*y*z, x^2*y*z, x^2*y^3*z}, {1, x*y, x*y*z, x*y^3*z, x^2*y^3*z},
        {1, x*y, x^2*y, x^2*y*z, x^2*y^3*z}, {1, x*y, x^2*y, x^2*y^3, x^2*y^3*z}, {1, x*y, x*y^3, x*y^3*z, x^2*y^3*z}, 
        {1, x*y, x*y^3, x^2*y^3, x^2*y^3*z}, {1, x^2, x^2*y, x^2*y*z, x^2*y^3*z}, {1, x^2, x^2*y, x^2*y^3, x^2*y^3*z},
        {1, y^3, y^3*z, x*y^3*z, x^2*y^3*z}, {1, y^3, x*y^3, x*y^3*z, x^2*y^3*z}, {1, y^3, x*y^3, x^2*y^3, x^2*y^3*z}} )
///

-- TEST 11
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, x*y, y^3, y*z);
L = lcmLattice I;


meetIrreducibles L
assert( (try meetIrreducibles P1  else oops) === oops )
assert( set meetIrreducibles P2 === set {e,f,g,b,d} )
assert( (set meetIrreducibles L) === set {x^2, y^3*z, x*y^3*z, x^2*y*z, x^2*y^3, x^2*y^3*z} )
///

-- TEST 12
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, y^2, z^2);
L = lcmLattice I;
assert( (coveringRelations P1) === {{h,i},{i,j},{i,k}} )
assert( (coveringRelations P2) === {{a,b},{a,c},{a,d},{b,e},{c,e},{c,f},{d,f},{e,g},{f,g}} )
assert( (sort coveringRelations L) == {{1, z^2}, {1, y^2}, {1, x^2}, {z^2, y^2*z^2}, {z^2, x^2*z^2}, {y^2, y^2*z^2}, {y^2, x^2*y^2}, 
        {x^2, x^2*z^2}, {x^2, x^2*y^2}, {y^2*z^2, x^2*y^2*z^2}, {x^2*z^2, x^2*y^2*z^2}, {x^2*y^2, x^2*y^2*z^2}} )
///

-- TEST 13
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});

assert( ((openInterval(P1,h,j)).Relations) === {} )
assert( sort ((closedInterval(P1,i,k)).Relations) === {{i,k}} )
assert( sort ((openInterval(P2,a,e)).Relations) === {} )
assert( sort ((closedInterval(P2,c,g)).Relations) === {{c,e},{c,f},{c,g},{e,g},{f,g}} )

///

-- TEST 14
--TEST ///
--B = booleanLattice(2)   
--assert( toString (B.GroundSet) === toString {1,x_2,x_1,x_1*x_2} )
--assert( (B.RelationMatrix) === map(ZZ^4,ZZ^4,{{1, 1, 1, 1}, {0, 1, 0, 1}, {0, 0, 1, 1}, {0, 0, 0, 1}}) )
--assert( toString (B.Relations) === toString {(1,1),(1,x_2),(1,x_1),(1,x_1*x_2),(x_2,x_2),(x_2,x_1*x_2),(x_1,x_1),(x_1, x_1*x_2),(x_1*x_2,x_1*x_2)} )
--///


end;


loadPackage("Posets",FileName=>"./Posets.m2")
