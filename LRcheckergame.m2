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
	 Board,
	 Parent,
	 Children,
	 printTree,
	makeLocalCoordinates
     }
-- Abraham Martin del Campo
-- 25/July/2011
-- ---------------------
-- This is a file where I implement Ravis LR-decomposition
-- ---------------------

-- NC means no checker in that column
NC = infinity;

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
--	output:
--       redpos - Updated list (of lists) of red checker positions
--
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
     if split == 0 then {toList redpos} else {redposition, toList redpos}
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
     if blackdown1 == n then return {};
     blackup1 := position(blackposition, x-> x == 1+blackposition#blackdown1);
     -- The column of the right black checker to be sorted goes from desccol 
     -- to the end of the board.
     -- Determine the rows of the next pair of black checkers to be sorted.
	 blackup2 := n-blackdown1+blackup1;
	 blackdown2 := blackup2-1;
	 redposition = moveRed({blackup1,blackup2},{blackdown1,blackdown2}, redposition);
	 blackposition = new MutableList from blackposition;
	 blackposition#blackup1 = blackposition#blackup1 - 1;
	 blackposition#blackdown1 = blackposition#blackdown1 + 1;
	 apply(redposition, r-> [toList blackposition, r])
)
--moveCheckers({3,5,4,2,1,0},{3,NC,NC,5,NC,1})


playCheckers = method(TypicalValue => List)
playCheckers(List,List,ZZ,ZZ) := (partn1,partn2,k,n) -> (
     redChkrs := 
     if partn1 > partn2 then
     	  redChkrPos(partition2bracket(partn2,k,n),partition2bracket(partn1,k,n),k,n)
      else 
          redChkrPos(partition2bracket(partn1,k,n),partition2bracket(partn2,k,n),k,n)
     ;
     blackChkrs := reverse toList (0..(n-1)); --initial black positions
     playCheckers ([blackChkrs, redChkrs], new MutableHashTable)  -- returns the root of the tree
)

playCheckers (Array,MutableHashTable) := (board,parent) ->(
	self := new MutableHashTable from {
	   Board => board, 
	   Parent => parent
	};
	self.Children = apply(moveCheckers board, b -> playCheckers (b,self));
	self
)

printTree = method()
printTree MutableHashTable := node ->(
	print node.Board;
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
-- output: a matrix
-----------------
-- example:
-----------------

makeLocalCoordinates = method(TypicalValue => MutableHashTable)
makeLocalCoordinates Array := blackred ->(
  blackposition := first blackred;
	redposition := last blackred;
	VAR := symbol VAR;
  n := #redposition; -- n is the size of the board
  -- we find how many black checkers are in northwest to a given red
  rowsred := sort select(redposition, r->r=!=NC);
  E := new MutableHashTable;
	for r to #rowsred-1 do(
			columnred := position(redposition, j-> j== rowsred#r); 
			E#(rowsred#r-1,r) = 1;
			variablerows := take(blackposition,columnred+1);
			variablerows = select(variablerows, b-> b< rowsred#r);			
			scan(take(rowsred,columnred-1),i-> variablerows = delete(i,variablerows));
			apply(variablerows, col-> (
			  E#(col,r)=VAR;
				)
			);
		 );
	return E
)
