newPackage(
     "LRcheckergame",
     Version => "0.1",
     Date => "April 5, 2012",
     Authors =>{Name => "Abraham Martin del Campo", 
                  Email => "asanchez@math.tamu.edu", 
                  HomePage => "www.math.tamu.edu/~asanchez"},
     Headline => "an implementation of Ravi Vakil's gemetric Littlewood-Richardson rule",
     DebuggingMode => true
     )

export{
     trackHomotopy,
     verifyLength,
     partition2bracket,
     bracket2input,
     output2partition,
     output2bracket,
     bracket2partition,
     redChkrPos,
     moveRed,
     moveCheckers,
     playCheckers,
     NC,
     FFF,
     Board,
     Parent,
     Children,
     TypeOfMoveFromParent,
     printTree,
     makeLocalCoordinates,
     resolveNode,
     FlagM,
     CriticalRow,
     Polynomials,
     Solutions,
     SolutionsSuperset -- temporary
     }
-- Abraham Martin del Campo
-- 25/July/2011
-- ---------------------
-- This is a file where I implement Ravis LR-decomposition
-- ---------------------

needsPackage "NumericalAlgebraicGeometry"


-- NC means no checker in that column
NC = infinity

-- OUR FIELD
FFF = QQ

-- ---------------------
--	verifyLength	--
--								--
-- makes sure a partition l
-- that is supposed to impose
-- conditions on Gr(k,n)
-- is in fact a partition 
-- of length k (add 0s if not)
--
verifyLength = method(TypicalValue => List)
verifyLength(VisibleList, ZZ) := (l,k) ->(
     x:=new List;
     if #l <= k then (
	  x = for i to k-#l-1 list 0;
	  l | x
     ) else print("wrong size of partition")
)

--------------------------
-- Dictionaries of different notations
--
--------------------------

partition2bracket = method(TypicalValue => List)
partition2bracket(List,ZZ,ZZ) := (l, k, n) -> (
     l = verifyLength(l, k);
     brackt := for i to #l-1 list (n-k)+(i+1)-l#i
)

output2partition = method(TypicalValue => List)
output2partition(List) := redpos ->(
		n:= #redpos;
		posn := select(redpos, x->x!= NC);
		k:= #posn;
		partitn := new MutableList from k:0;
		apply(#posn, j->(
			partitn#j = n-k+j-posn#j;
		));
		reverse sort toList partitn
)

-- not using this function
bracket2input = method(TypicalValue => List)
bracket2input(List,ZZ) := (br,n) ->(
     inp := for i to n-1 list NC;
     inp = new MutableList from inp;
     apply(br, b-> inp#(b-1) = b-1);
     toList inp
)

-- not using this function either
output2bracket = method(TypicalValue=>List)
output2bracket List := outp -> (
     br := select(outp, x-> x!=NC);
     apply(br, x-> x=x+1)
) 

bracket2partition = method(TypicalValue => List)
bracket2partition(List,ZZ) := (l, n) -> (
--     l = reverse sort l;
     partitn := for i to #l-1 list (n-#l)+(i+1)-l#i 
)
---------------------
-- change this method to be between checkers
---------------------
-- input: two schubert conditions l and m
--			entered as brackets
--		  the Grassmannian G(k,n)
--
-- Output: checkboard coordinates for the 
--         red checkers
---------------------
-- example: for {2,1}*{2} in G(3,6)
--
--partition2bracket({2,1},3,6)
--partition2bracket({2},3,6)
--redChkrPos({2,4,6},{2,5,6},3,6)
--------------------
redChkrPos = method(TypicalValue => List)
redChkrPos(List,List,ZZ,ZZ) := (l,m,k,n) -> (
     -- input the Schubert conditions l and m
     -- as bracket
     -- input the Grassmannian G(k,n)
     m = reverse m;
     board := for i to n-1 list NC;
     redPos := new MutableList from board;
     apply(#l, j -> redPos#(l#j-1) = m#j-1);
     toList redPos
)
------- TEST -----
-- first, given the partitions 
-- {2,1}*{2} in G(3,6)
-- we test if the positions of the 
-- redcheckers is {NC,5,NC,4,NC,1}
------------------
-- partition2bracket({2,1},3,6)
-- partition2bracket({2},3,6)
-- redChkrPos({2,4,6},{2,5,6},3,6)
-- redChkrPos(partition2bracket({2,1},3,6),partition2bracket({2},3,6),3,6)

--####################
-- "moveRed" moves the red checkers
--
-- input:
--       blackup - Coordinates of the ascending black checker
--       blackdown - Coordinates of the descending black checker
--       redpos - List of red checker positions
--
--	output: {(repos,typeofmove,critrow)} or {(repos1,typeofmove1,critrow),(repos2,typeofmove2,critrow)}
--       redpos - Updated list (of lists) of red checker positions
--       typeofmove - {row,column,split}
--                    a tuple which tells the type of the move we had to perform from
--                    the 3x3 table of moves. This is given as a 
--                    tuple {row,column,split} where split says
--                    if you moved or not the red checkers
--                    (by 0 and 1 respectively) when there was a split
--        critrow - the critical row
moveRed = method(TypicalValue => List)
moveRed(List,List,List) := (blackup, blackdown, redposition) -> (
	------------------------------------------------
	-- We need to check first if it is a valid configuration
	-- that is why I have been having errors
	------------------------------------------------
	 n := #redposition; -- n is the size of the checkboard
	 split:=0;
     critrow := 0;
     critdiag := 0;
     g:=2; -- These are two flags to indicate in which situation we are 
     r:=2;
     indx := new List;
     redpos := new MutableList from redposition;
     -- find the "critical row"
     indx = for i to n-blackdown#0-1 list n-1-i;
     apply(indx, j -> (
	  if redpos#j === blackdown#1 then (
	       critrow = j;
	       if j == blackdown#0 then g=0 else g=1;
	  ) 
     ));
     -- find the "critical diagonal"
     indx= for i to blackdown#0-1 list i;
     indx = reverse indx;
     apply(indx, j->(
	  if blackdown#0-j+redpos#j == n then(
	       critdiag = j;
	       if blackup === {j,redpos#j} then r=0 else r=1;
	  )
     ));
     if r == 0 then (
	  redpos#(blackup#0)=redpos#(blackup#0)-1;
	  if g == 0 then redpos#(blackdown#0) = redpos#(blackdown#0)+1;
	  if g == 1 then redpos#critrow = redpos#critrow + 1;
     ) else if r == 1 then (
	  if g == 0 then(
	       redpos#critrow = redpos#critdiag;
	       redpos#critdiag = NC;
	       redpos#(blackup#0) = blackdown#1;
	  ) else if g == 1 then(
	       block := 0;
	       blockindx := for i to critrow-1-critdiag-1 list critrow-1-i;
	       apply(blockindx, b -> if redpos#critrow < redpos#b and redpos#b < redpos#critdiag then block = 1);
	       if block != 1 then (
		    -- switch the rows of the red checkers in the critical diagonal and row
		    -- then, move the left one over to the column of the ascending black
		    redpos#critrow = redpos#critdiag;
		    redpos#critdiag = NC;
		    redpos#(blackup#0) = blackdown#1;
		    split = 1;
	       );
	  );
     ) else if r == 2 and g == 0 then (
     	  redpos#(blackup#0)=redpos#critrow;
	  redpos#critrow = NC;
     );
     if split == 0 then {(toList redpos,{r,g,split})} else {(redposition,{r,g,0}), (toList redpos,{r,g,split})}
)
-- TEST THE FUNCTION HERE!!

--moveRed({0,2},{2,1},{NC,3,NC,1})
-- The output must be
-- {{NC, 3, NC, 1, 1, NC, NC, 3},1}

--moveRed({0, 3}, {1, 2}, {NC, 3, NC, 1})
--moveRed({0, 2}, {2, 1}, {NC, 3, NC, 1})
--moveRed( {1, 3}, {2, 2}, {NC, 3, NC, 1, 1, NC, NC, 3})
--moveRed({0, 1}, {3, 0}, {NC, 2, NC, 1, 1, NC, NC, 3})
--moveRed({ 1, 2}, {3, 1}, {NC, 2, NC, 1, 1, NC, NC, 3})
--moveRed({2, 3}, {3, 2}, {NC, 1, NC, 2, 1, NC, NC, 3})
--moveRed({1, 3}, {2, 2}, {1, NC, NC, 3})
--moveRed( {0, 1}, {3, 0}, {1, NC, NC, 3})
--moveRed({1, 2}, {3, 1}, {0, NC, NC, 3})
--moveRed({2, 3}, {3, 2}, {0, NC, NC, 3})

moveCheckers = method(TypicalValue => List)
moveCheckers Array := blackred -> (
     blackposition := first blackred;
     redposition := last blackred;
     n := #redposition; -- n is the size of the board
     splitcount:=0;
     copies:=0;
     -- determine the columns of the descending and ascending black checkers
     -- blackdown1 is the column to the right of the column of the lowest black checker
	 -- blackup1 is the column of the checker that is one row lower than the checker 
	 --        in blackdown1 
     blackdown1 := position(blackposition, x->x == n-1) + 1;
     if blackdown1 == n then return ({},"leaf");
     blackup1 := position(blackposition, x-> x == 1+blackposition#blackdown1);
     -- The column of the right black checker to be sorted goes from desccol 
     -- to the end of the board.
     -- Determine the rows of the next pair of black checkers to be sorted.
	 blackup2 := n-blackdown1+blackup1;
	 blackdown2 := blackup2-1; -- this is the critical row
	 listofredpositions := moveRed({blackup1,blackup2},{blackdown1,blackdown2}, redposition);
	 blackposition = new MutableList from blackposition;
	 blackposition#blackup1 = blackposition#blackup1 - 1;
	 blackposition#blackdown1 = blackposition#blackdown1 + 1;
	 (
	      apply(listofredpositions, r-> [toList blackposition, 
		   	first r, -- new redposition
		   	last r -- new type of move
		   	]), 
	      blackdown2 --return also the critical row
	      )
)
--moveCheckers({3,5,4,2,1,0},{3,NC,NC,5,NC,1})


playCheckers = method(TypicalValue => MutableHashTable)
playCheckers(List,List,ZZ,ZZ) := (partn1,partn2,k,n) -> (
     redChkrs := 
     if partn1 > partn2 then
     	  redChkrPos(partition2bracket(partn2,k,n),partition2bracket(partn1,k,n),k,n)
      else 
          redChkrPos(partition2bracket(partn1,k,n),partition2bracket(partn2,k,n),k,n)
     ;
     blackChkrs := reverse toList (0..(n-1)); --initial black positions
     playCheckers ([blackChkrs, redChkrs], "root", {})  -- returns the root of the tree
)

playCheckers (Array,Thing,List) := (board,parent,typeofmove) ->(
     self := new MutableHashTable from {
	  Board => board, 
	  Parent => parent,
	  TypeOfMoveFromParent => typeofmove
	  };
     (children,c) := moveCheckers board;
     self.CriticalRow = c;
     self.Children = apply(children, b -> playCheckers (take(b,2),self,last b));
     self
)

printTree = method()
printTree MutableHashTable := node ->(
	print peek node;
	scan(node.Children, c-> printTree c);
)

--Examples:
--verifyLength({2,1,1,1},3)
--partition2bracket({2,1},3,7)
--partition2bracket({1,1},3,7)
--partition2bracket({1},3,7)
--bracket2input({4,6,7},7)
--output2bracket({NC, NC, NC, 3, NC, 5, 6})
--bracket2partition({2,4,6},6)

--redChkrPos(partition2bracket({2,1},3,6),partition2bracket({1,1},3,6),3,6)


--playCheckers({1,1},{2,1},3,6)
--playCheckers({1,1},{2,0},2,4)
--playCheckers({1},{1},2,4)
--playCheckers({1,1},{2,1},3,6)
--playCheckers({2,1},{1,1},3,6)

-----------------
--- makeLocalCoordinates
--
-- This procedure will translate a checker 
-- board configuration into a matrix with
-- 0's 1's and variables
-----------------
-- input: an array of black and red checkers
--        in the form ( ListofPositionsBlack, ListofPositionsRed)
-- output: a matrix with local coordinates
-----------------
-- example:
-----------------

makeLocalCoordinates = method(TypicalValue => MutableMatrix)
makeLocalCoordinates Array := blackred ->(
  blackposition := first blackred;
  redposition := last blackred;
  VAR := symbol VAR;
  n := #redposition; -- n is the size of the board
  -- we find how many black checkers are in northwest to a given red
  rowsred := sort select(redposition, r->r=!=NC);
  colsred := apply(rowsred, r -> position(redposition, j-> j == r));
  E := new MutableHashTable;
    for r to #rowsred-1 do(
      E#(rowsred#r,r) = 1;
      variablerows := take(blackposition,colsred#r+1);
      variablerows = select(variablerows, b-> b< rowsred#r);
      scan(variablerows, j->(
        if member(j,rowsred) and position(redposition, i-> i == j) < colsred#r then
	  variablerows = delete(j,variablerows);
      ));
      scan(variablerows, col-> (
        E#(col,r)=VAR;
      ));
   );
   x:= symbol x;
   R:=FFF[apply(select(keys E, k-> E#k===VAR), k-> x_k)];
   X := mutableMatrix(R,n,#rowsred);
   scan(keys E, k-> X_k = if E#k === 1 then 1 else x_k);
   matrix X
)

------------------
-- resolveNode
------------------
-- A function that will be the skeleton
-- of the homotopy.
-- It first transform the Flag of the child Sch. Var
-- into a generalized flag for the parent
------------------
resolveNode = method()
resolveNode(MutableHashTable,List) := (node,remaining'conditions'and'flags) ->(
     n := #node.Board#0;
     node.Solutions = {};
     if node.Children == {} then node.FlagM = matrix mutableIdentity(FFF,n)
     else scan(node.Children, c->resolveNode(c,remaining'conditions'and'flags));
     
     -- temporary: creates a superset of solutions via a blackbox solver
     X := makeLocalCoordinates node.Board;
     node.Polynomials = makePolynomials(node.FlagM * X,remaining'conditions'and'flags);
     node.SolutionsSuperset = apply(solveSystem flatten entries node.Polynomials, s-> (map(CC,ring X,matrix s)) X);
     
     if node.Children == {} then node.Solutions = node.SolutionsSuperset;  -- should change!!! 
     
     if node.Parent =!= "root" then (
     	  r := node.Parent.CriticalRow; -- critical row: rows r and r+1 are the most important ones
	  M := node.FlagM;
	  M'':= M_{0..(r-1)} | M_{r} - M_{r+1} | M_{r}| M_{(r+2)..(n-1)};
      	  node.Parent.FlagM = M'';
	  node.Parent.Solutions = node.Parent.Solutions |  
	  if node.Solutions == {} then {} -- means: not implemented
	  else if node.TypeOfMoveFromParent#1 == 2 then (-- case (_,2)
     	       apply(node.Solutions, X->(
		    	 X'' := (X^{0..r-1}) || (-X^{r+1}) || (X^{r}+X^{r+1}) ||( X^{r+2..n-1});
		    	 normalizeAndReduce(X'',node.Parent)
	       	    	 ))
	       )
	  else if member(node.TypeOfMoveFromParent,{{2,0,0},{2,1,0},{1,1,0}}) then (-- case "STAY"
	       coordX := makeLocalCoordinates node.Board; -- local coordinates X = (x_(i,j))
	       R := ring coordX;
	       t := symbol t;
	       Rt := (coefficientRing R)[t,gens R]; -- homotopy ring
	       mapRtoRt := map(Rt,R,drop(gens Rt,1));
	       Xt := mapRtoRt coordX; --  "homotopy" X 
	       M'X' := promote(M,Rt) * (Xt^{0..r-1} || Xt^{r} + Xt^{r+1} || -t*Xt^{r} || Xt^{r+2..n-1}); -- this is V(t) = M'(t) X'(t)
	       polys := makePolynomials(M'X',remaining'conditions'and'flags);
	       startSolutions := apply(node.Solutions, X->toRawSolutions(coordX,X));
	       
	       -- track homotopy and plug in the solution together with t=1 into Xt
	       targetSolutions := trackHomotopy(polys,startSolutions);
	       apply(targetSolutions, s->( 
		    M''X'' := (map(CC,Rt,matrix{{1}}|matrix s)) Xt;
      		    X'' := inverse node.Parent.FlagM * M''X'';
		    normalizeAndReduce(X'',node.Parent)
		    ))
	       )
     	  else {} -- means: not implemented
	  );
     )

toRawSolutions = method()
toRawSolutions(Matrix,Matrix) := (coordX,X) -> (
     a := flatten entries coordX;
     b := flatten entries X;
     delete(null, apply(#a, i->if a#i == 1 or a#i == 0 then null else b#i))
     )

normalizeAndReduce = method()
normalizeAndReduce(Matrix,MutableHashTable) := (X'', father) -> (  
     k := numgens source X'';
     n := numgens target X'';
     r := father.CriticalRow;
     j := position(sort delete(NC, father.Board#1), i-> i==r+1);
     if j=!=null then(
	  X'' = mutableMatrix(X''_{0..j-1} | (1/X''_(r+1,j))*X''_{j}  | X''_{j+1..k-1}); -- X''_(r+1,j) = X_(r,j)+X_(r+1,j) = 1+X_(r+1,j), so is the first part of Ravi's mistake
	  --X''_(r,j) =-1/(1+X_(r,j)); -- error in Ravi's notes: should be -X_(r+1,j)/(1+X_(r,j))
	  --X''_(r+1,j) = 1; -- this is correct, but is also already taken care of 
	  redCheckersColumnReduce(father.Board#1, (j, n, k), X'');
	  );
     matrix X''
     )
redCheckersColumnReduce = method()
redCheckersColumnReduce(List,Sequence,MutableMatrix) := (red, jnk, X'') -> (
     redSorted := sort delete(NC,red);
     (j,n,k) := jnk; -- (moving red column, numrows X'', numcols X'')
     -- if j == 0  then 1/0; --!!!!!!!!
     for jj from j+1 to k-1 do 
     if position(red, jjj->redSorted#jj == jjj) > j then (
	  r := redSorted#j; -- crit.row + 1
	  c := X''_(r,jj)/X''_(r,j); 
	  scan(n, i->X''_(i,jj) = X''_(i,jj) - c*X''_(i,j))
	  );
     )

-----------------
-- makePolynomials
--
-- creates a zero dimensional system
-- that corresponds to a localization pattern
-- and the list of Schubert conditions
-- together with specified flags.
----------------
-- input:
--     	   MX = global coordinates for an open subset
--     	        of a checkerboard variety (or MX' in the homotopy (in Ravi's notes))
--
--     	    conds = list of pairs (l,F) where l is a Schubert condition and F is a flag
--
-- output:  a matrix of polynomials
-----------------
makePolynomials = method(TypicalValue => Matrix)
makePolynomials(Matrix, List) := (MX,conds) ->(
     R := ring MX;
     k := numgens source MX;
     n := numgens target MX;
     eqs := sum(conds, lF ->(
	       (l,F) := lF;
	       MXF:=MX|promote(F,R);
	       b := partition2bracket(l,k,n);
	       sum(#b, r->( 
			 c := b#r;
			 minors(k+c-(r+1)+1, MXF_{0..k+c-1})
			 ))
	  ));
     gens eqs
)

-- Tracks a homotopy
-- Input: 
--    H -- a list of polynomials in k[xx,t];
--    S = {{...},...,{...}} -- a list of solutions to H at t=0
-- Output: 
--    T - a list of Points that are solutions to H at t=1
trackHomotopy = method(TypicalValue=>List)
trackHomotopy (Matrix,List) := (H,S) -> (
     Rt := ring H;
     R := (coefficientRing Rt)[drop(gens Rt,1)];
     map't'0 := map(R, Rt, matrix{{0}}|vars R);
     map't'1 := map(R, Rt, matrix{{1}}|vars R);
     track(first entries map't'0 H, first entries map't'1 H, S)
     )
