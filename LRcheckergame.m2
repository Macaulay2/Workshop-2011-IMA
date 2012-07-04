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
     Fathers,
     Children,
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
FFF = RR
FFF = CC
ERROR'TOLERANCE := 0.001

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

---- this is an unused function:
---- input: redcheckers
---- output: list with the two partitions that generate
----         that redchecker board
redcheckers2partitions= method(TypicalValue=>List)
redcheckers2partitions List := redchckrs ->(
     br := sort select(redchckrs, x-> x!=NC);     
     part1:=apply(#br, i-> br#i-i);
     br2:=select(#redchckrs, i-> redchckrs#i != NC);
     part2 := apply(#br2, i-> br2#i-i);
     {rsort part1, rsort part2}
     )
----

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

playCheckers (Array,Thing,List) := (board,father,typeofmove) ->(
     self := new MutableHashTable from {
	  Board => board, 
	  Fathers => {(father,typeofmove)},
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
   R:=FFF[apply(select(sort keys E, k-> E#k===VAR), k-> x_k)];
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
     coordX := makeLocalCoordinates node.Board; -- local coordinates X = (x_(i,j))
     if numgens ring coordX == 0 then (
	  if #remaining'conditions'and'flags > 0
	  then error "invalid Schubert problem"
	  else node.Solutions = {lift(coordX,FFF)};
	  return
	  );
     black := first node.Board;
          
     if node.Children == {} then node.FlagM = matrix mutableIdentity(FFF,n)
     else scan(node.Children, c->resolveNode(c,remaining'conditions'and'flags));
     
     -- temporary: creates a superset of solutions via a blackbox solver
     all'polynomials := makePolynomials(node.FlagM * coordX, remaining'conditions'and'flags);
     polynomials := squareUpPolynomials(numgens ring coordX, all'polynomials);
     ---* this part is to time and keep track of what is the expensive part of the computation
     print("Blackbox solving cpuTime:");
     time Soluciones:=solveSystem flatten entries polynomials;
     ---*
     node.SolutionsSuperset = apply(
	  select(
	       --// After finish with the timing, remove the previous part and the next line
	       --// and uncomment the following line (deleting the line after that)
	       Soluciones,
	       --time solveSystem flatten entries polynomials, 
	       s-> norm sub(gens all'polynomials,matrix s) < ERROR'TOLERANCE * 
	       norm matrix s * 
	       norm sub(last coefficients gens all'polynomials,CC)
	       ), 
	  ss-> (map(CC,ring coordX,matrix ss)) coordX
	  ); 
     	  
     if node.Children == {} then (
	    --(Vars,Coeffs) := coefficients polynomials;
	    --rws:= numRows Coeffs - 1;
	    -- we solve the linear system
	    --Soluts:= - inverse transpose Coeffs^{0..rws-1} * transpose Coeffs^{rws};
	    --node.Solutions = {(map(CC,ring coordX,matrix sub(transpose Soluts, CC))) coordX}
	    --print(node.SolutionsSuperset);
	    --print({(map(CC,ring coordX,matrix sub(transpose Soluts, CC))) coordX});
	    node.Solutions = node.SolutionsSuperset; 
     ); -- should change!!! 
     
     scan(node.Fathers, father'movetype->(
     
     (father,movetype) := father'movetype; 
     tparents1:=cpuTime();
     if father =!= "root" then (
     	  r := father.CriticalRow; -- critical row: rows r and r+1 are the most important ones
     	  red := last father.Board;     
     	  red'sorted := sort delete(NC, red);
	  M := node.FlagM;
	  M'':= M_{0..(r-1)} | M_{r} - M_{r+1} | M_{r}| M_{(r+2)..(n-1)};
      	  father.FlagM = M'';
	  
--	  if movetype=={2,2,0} and r == 1 then 1/0;
	  parent'solutions :=  -- THIS IS WHERE THE MAIN ACTION HAPPENS
	  if node.Solutions == {} then {} -- means: not implemented
	  else if movetype#1 == 2 then (-- case (_,2)
     	       apply(node.Solutions, X->(
		    	 X'' := (X^{0..r-1}) || (-X^{r+1}) || (X^{r}+X^{r+1}) ||( X^{r+2..n-1});
			 j := position(red'sorted, i-> i==r+1);-- the column we need to normalize
		    	 if j=!=null then redCheckersColumnReduce2(normalizeColumn(X'',r+1,j),father)
			 else X''
	       	    	 ))
	       )
	  else ( -- cases STAY and SWAP require homotopy 
	       R := ring coordX;
	       t := symbol t;
	       Rt := (coefficientRing R)[t,gens R]; -- homotopy ring
	       mapRtoRt := map(Rt,R,drop(gens Rt,1));
	       Xt := mapRtoRt coordX; --  "homotopy" X 
	       local M'X'; -- homotopy in global coordinates (produced by each case)
	       
	       -- these are used only in SWAP cases
	       s := position(red'sorted, i->i==r); -- number of the first moving red checker
	       VwrtM := map(Rt^n,Rt^0,{}); -- an empty column vector

	       if member(movetype,{{2,0,0},{2,1,0},{1,1,0}}) then (-- case "STAY"
		    -- V(t) = M'(t) X'(t) .......... we write everything in terms of M
		    scan(#red'sorted, j-> VwrtM = VwrtM |
		    	 if isRedCheckerInRegionE(
			      position(red,i->i==red'sorted#j), -- column of the j-th red checker on the board
			      father) 
			 then (
		    	      --submatrix(Xt,{0..r-1},{j}) 
		    	      --|| submatrix(Xt,{r},{j}) + submatrix(Xt,{r+1},{j})
		    	      submatrix(Xt,{0..r},{j}) 
		    	      || matrix{{0_FFF}}
		    	      || submatrix(Xt, {r+2..n-1}, {j})
			      ) else (
		    	      submatrix(Xt,{0..r},{j}) 
		    	      || submatrix(Xt,{r+1},{j})-t*submatrix(Xt,{r},{j})
		    	      || submatrix(Xt, {r+2..n-1}, {j})	    
			      )
		    	 );
	       	    M'X' = promote(M,Rt) * VwrtM;
	       	    ) 
	       else if member(movetype,{{1,0,0},{1,1,1},{0,0,0},{0,1,0}}) then (-- case SWAP(middle row)		    
	       	    bigR := red'sorted#(s+1); -- row of the second moving red checker
		    rightmost'col'B := position(black, j->j==r);
		    leftmost'col'A := position(black, j->j==r+1)+1;
 		    
		    -- check if the black checker in the i'th row is in region A
		    isRegionA := i -> position(black, i'->i'==i) >= leftmost'col'A;	     
		    -- check if the black checker in the i'th row is in region B
		    isRegionB := i -> position(black, i'->i'==i) <= rightmost'col'B;
		    	       	    
		    -- V(t) = M'(t) X'(t) .......... we write everything in terms of M
		    scan(#red'sorted, j-> VwrtM = VwrtM |
		    	 if j == s then ( -- note: this part can be optimized for speed
			      transpose matrix { apply(n,i->(
					if i==r then Xt_(r+1,s+1)
					else if i==r+1 then -t*Xt_(r+1,s+1)
					else if isRegionA i then -t*Xt_(i,s+1)
					else if isRegionB i then Xt_(r+1,s+1)*Xt_(i,s)
					else 0
					)) }
			      )
			 else if j == s+1 then (
			      transpose matrix { apply(n,i->(
					if i==bigR then 1
					else if i==r+1 then Xt_(r+1,s+1)
					else if i==r then 0
					else Xt_(i,s+1)
					)) }
			      )
			 else if isRedCheckerInRegionE(
			      position(red,i->i==red'sorted#j), -- column of the j-th red checker on the board
			      father
			      ) 
			 then (
		    	      submatrix(Xt,{0..r-1},{j}) 
		    	      || submatrix(Xt,{r},{j}) + submatrix(Xt,{r+1},{j})
		    	      || matrix{{0_FFF}}
		    	      || submatrix(Xt, {r+2..n-1}, {j})
			      ) else (
		    	      submatrix(Xt,{0..r},{j}) 
		    	      || submatrix(Xt,{r+1},{j})-t*submatrix(Xt,{r},{j})
		    	      || submatrix(Xt, {r+2..n-1}, {j})	    
			      )
		    	 );
	       	    M'X' = promote(M,Rt) * VwrtM;         
		    )
	       -- implementing this case separately gives lower degree polynomials
--	       else if member(movetype,{{0,0,0},{0,1,0}}) then (-- case SWAP(top row)		    
--		    )
	       else error "an unaccounted case";
	       
	       all'polys := makePolynomials(M'X',remaining'conditions'and'flags);
	       polys := squareUpPolynomials(numgens R, all'polys);
	       startSolutions := apply(node.Solutions, X->toRawSolutions(coordX,X));
	       
	       -- track homotopy and plug in the solution together with t=1 into Xt
	       scan(startSolutions,  
		    s->assert(norm sub(polys,matrix{{0_FFF}|s}) < ERROR'TOLERANCE * 
			 norm matrix{s} * 
			 norm sub(last coefficients polys,CC))); 
	       t1:= cpuTime();
	       targetSolutions := trackHomotopy(polys,startSolutions);
	       t2:= cpuTime();
	       << node.Board << " -- track time: " << (t2-t1) << endl;
	       apply(targetSolutions, sln->( 
		    M''X'' := (map(CC,Rt,matrix{{1}}|matrix sln)) M'X';
		    X'' := inverse M'' * M''X'';
		    if not member(movetype,{ {2,0,0},{2,1,0},{1,1,0} }) -- SWAP CASE
		    then (
     			 k := numgens source X'';
			 X'' = X''_{0..s}| X''_{s}+X''_{s+1}| X''_{s+2..k-1}; -- we substitute the s+1 column for the vector w_{s+1}
		    	 redCheckersColumnReduce2(normalizeColumn(X'',r,s),father)
			 ) 
		    else --redCheckersColumnReduce2(
		    normalizeColumn(X'',r,s)
		    --,father) -- !!!
		    ))
	       );
     	  -- else {}; -- means: not implemented
	  
	  -- verify solutions
	  parentX := makeLocalCoordinates father.Board;
	  parentXlist := flatten entries parentX;
	  scan(parent'solutions, X'''->( 
		    -- check that solutions fit the parent's pattern
		    a := flatten entries X''';
		    scan(#a, i->assert(
			      (abs a#i < ERROR'TOLERANCE and parentXlist#i == 0)
			      or (abs(a#i-1) < ERROR'TOLERANCE and parentXlist#i == 1)
			      or (parentXlist#i != 0 and parentXlist#i != 1)
			      ));
		    ));
	  father.Solutions = father.Solutions | parent'solutions;
	  );
     tparents2:=cpuTime();
     << "time of computing one edge: "<< (tparents2 - tparents1) << endl;
     ));
     -- check against the blackbox solutions
     scan(node.Solutions, X->
	  assert(position(node.SolutionsSuperset, Y->norm(Y-X)<ERROR'TOLERANCE) =!= null)); 
     )

toRawSolutions = method()
toRawSolutions(Matrix,Matrix) := (coordX,X) -> (
     a := flatten entries coordX;
     b := flatten entries X;
     delete(null, apply(#a, i->if a#i == 1 or a#i == 0 then null else b#i))
     )

------------------
-- normalizeColumn
------------------
--  this function divide a specific column of a matrix
--  by a specific value
------------------
-- Input:
--     X'' - the matrix to be normalized
--     r   - the row of the elt that becomes 1
--     j - the column to be normalized
-----------------
normalizeColumn = method(TypicalValue => Matrix)
normalizeColumn(Matrix,ZZ,ZZ) := (X,r,j) -> (  
     k := numgens source X;
     if j=!=null then(
	  X = X_{0..j-1} | (1/X_(r,j))*X_{j}  | X_{j+1..k-1}; 
	  --X''_(r,j) =-1/(1+X_(r,j)); -- error in Ravi's notes: should be -X_(r+1,j)/(1+X_(r,j))
	  --X''_(r+1,j) = 1; -- this is correct, but is also already taken care of 
	  );
     matrix X
     )

-----------------
-- redCheckersColumnReduce
-----------------
-- This function reduce specific column
-- using elementary column operations
-----------------
redCheckersColumnReduce = method(TypicalValue => Matrix)
redCheckersColumnReduce(Matrix, MutableHashTable) := (X'', father) -> (
     k := numgens source X'';
     n := numgens target X'';
     red := delete(NC,last father.Board);
     redSorted := sort red;
     r := father.CriticalRow;
     j := position(redSorted, i-> i==r+1);
     if j=!=null then(
     	  X''  = mutableMatrix X'';
	  crit'col := position(red, i->i==r+1);
     	  for jj from j+1 to k-1 do 
	  -- reduce the columns for red checkers that have higher number and "see" the red checker in the row r+1
     	  if position(red, i->red#jj == i) > crit'col then ( 
	       c := X''_(r+1,jj)/X''_(r+1,j); 
	       scan(n, i->X''_(i,jj) = X''_(i,jj) - c*X''_(i,j))
	       )
	  );
     matrix X''
     )

redCheckersColumnReduceSwap = method(TypicalValue => Matrix)
redCheckersColumnReduceSwap(Matrix, MutableHashTable) := (X'', father) -> (
     k := numgens source X'';
     n := numgens target X'';
     red := delete(NC,last father.Board);
     redSorted := sort red;
     r := father.CriticalRow;
     j := position(redSorted, i-> i>=r+1);
     rowj := redSorted#j; -- the row of the lower swapped red checker (in the father)
     if j=!=null then(
     	  X''  = mutableMatrix X'';
	  for jj from j+1 to k-1 do(
	       -- reduce the columns for red checkers that have higher number and "see" the red checker in the row r+1
	       scan(n, i-> (
	       		 X''_(i,jj) = X''_(i,jj) - X''_(rowj,jj)*X''_(i,j);
	       		 ));
	       )
     	  );
     matrix X''
     )

redCheckersColumnReduce2 = method(TypicalValue => Matrix)
redCheckersColumnReduce2(Matrix, MutableHashTable) := (X'', father) -> (
     k := numgens source X'';
     n := numgens target X'';
     X''  = mutableMatrix X'';
     red := delete(NC,last father.Board);
     redSorted := sort red; -- numbers of the rows where red checkers are
     apply(#redSorted, r->( -- column r is to be reduced 
--	 -- find the redcheckers bellow that can see the current redChecker
--	 witnessReds:=select(drop(red,r), i->i>red#r);
--	 j:={};
--         scan(witnessReds, i-> j=append(j,position(redSorted, l-> l==i)));
     	 col'of'r'on'board := position(last father.Board, i->i==redSorted#r); 
	 reducers := select(0..r-1, 
	      j->position(last father.Board, i->i==redSorted#j)<col'of'r'on'board
	      );  
	 scan(reducers, j->(
	      		-- reduce the columns for red checkers that have higher number and "see" the red checker in the row r+1
			scan(n, i-> (
			     	  X''_(i,r) = X''_(i,r) - X''_(redSorted#j,r)*X''_(i,j);
			     	  ));
		   	));
	 ));
     matrix X''
     )
 
-----------------
-- makePolynomials
--
-- creates a square zero dimensional system
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
makePolynomials = method(TypicalValue => Ideal)
makePolynomials(Matrix, List) := (MX, conds) ->(
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
     eqs 
)

-- m random linear combinations of generators of the ideal
squareUpPolynomials = method()
squareUpPolynomials(ZZ,Ideal) := (m,eqs) ->  gens eqs * random(FFF^(numgens eqs), FFF^m)  

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
     map't'0 := map(R, Rt, matrix{{0_FFF}}|vars R);
     map't'1 := map(R, Rt, matrix{{1_FFF}}|vars R);
     track(first entries map't'0 H, first entries map't'1 H, S)
     )

-- Input: 
--     j = number of a red checker
--     r = critical row
--     black = black checkers on the board
isRedCheckerInRegionE = method()
isRedCheckerInRegionE(ZZ,MutableHashTable) := (i,node) -> (
     r := node.CriticalRow;
     black := first node.Board;
     e0 := position(black, b->b==r+1);
     e1 := position(black, b->b==r);
     i < e1 and i >= e0
     )