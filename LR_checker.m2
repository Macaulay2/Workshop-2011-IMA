-- Abraham Martin del Campo
-- 25/July/2011
-- ##################
-- This is a file where I implement Ravi's LR-decomposition
-- ##################

-- Given two partitions, we compute the red checker and black checker position
--
-- input: two partitions, the grassmannian

restart;
---------------------
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
     if #l < k then x = for i to k-#l-1 list 0;
     l | x
)


k=3;
n=6;
-- l and m are partitions of n
l = {2,1};
m = {2};

partition2bracket = method(TypicalValue => List)
partition2bracket(List,ZZ,ZZ) := (l, k, n) -> (
     l = verifyLength(l, k);
     brackt := for i to #l-1 list (n-k)+(i+1)-l#i
)
partition2bracket(l,k,n)

bracket2partition = method(TypicalValue => List)
bracket2partition(List,ZZ) := (l, n) -> (
--     l = reverse sort l;
     partitn := for i to #l-1 list (n-#l)+(i+1)-l#i 
)
bracket2partition({2,4,6},6)

redChkrPos = method(TypicalValue => List)
redChkrPos(List,List,ZZ,ZZ) := (l,m,k,n) -> (
     -- input the Schubert conditions l and m
     --     as bracket
     -- input the Grassmannian G(k,n)
     m = reverse m;
     --redPos := new MutableHashTable from {};
     --apply(#l, j-> redPos#(l#j) = m#j);
     --redPos = new HashTable from redPos
     board = for i to n-1 list 99;
     print board;
     redPos = new MutableList from board;
--     print #redPos;
     apply(#l, j -> redPos#(l#j-1) = m#j-1);
     toList redPos
)
Red =redChkrPos(partition2bracket(l,k,n),partition2bracket(m,k,n),k,n)

--####################
-- "rtest" moves the red checkers
--
-- input:
--       blackup - Coordinates of the ascending black checker
--       blackdown - Coordinates of the descending black checker
--       redpos - List of red checker positions
--       n - Dimension of the board
--
--	output:
--       redpos - Updated list of red checker positions
--       split - "1" if a split occured, "0" otherwise
--
moveRed = method(TypicalValue => List)
moveRed(List,List,List,ZZ) := (blackup, blackdown, redposition, n) -> (
     split:=0;
     g:=2; -- I dont know yet what are these two vars for 
     r:=2;
     redpos := new MutableList from redposition;
     -- find the row where we will move the black
     indx := for i to n-blackdown#0-1 list n-1-i;
     apply(indx, j -> (
	  if redpos#j == blackdown#1 then (
	       critrow := j;
	       if j == blackdown#0 then g=0 else g=1;
	  ) 
     ));
     -- find the "critical diagonal"
     indx2:= for i to blackdown#0-1 list i;
     indx2 = reverse indx2;
     apply(indx2, j->(
	  if blackdown#0-j+redpos#j == n then(
	       critdiag = j;
	       if blackup === {j,redpos#j} then r=0 else r=1;
	  )
     ));
     if r == 0 then (
	  redpos#(blackup#0)=redpos#(blackup#0)-1;
	  if g == 0 then redpos#(blackdown#0) = redpos#(blackdown#0)+1;
	  if g == 1 then redpos#(critdiag) = redpos#(critdiag)+1;
     ) else if r == 1 then (
	  if g == 0 then(
	       redpos#(critrow)=redpos#(critdiag);
	       redpos#(critdiag)=99;
	       redpos#(blackup#0)=blackdown#1;
	  ) else if g == 1 then(
	       block := 0;
	       blokindx = for i to critdiag-critrow list critrow-1-i;
	       apply(blokindx, b -> if redpos#critrow < redpos#blokindx and redpos#blockindx < redpos#critdiag then block = 1);
	       if block != 1 then (
		    -- switch the rows of the red checkers in the critical diagonal and row
		    -- then, move the left one over to the column of the ascending black
		    switchred := drop(redpos,-1);
		    switchred#critrow = switchred#critdiag;
		    switchred#critdiag = 99;
		    switchred#(blackup#0) = blackdown#1;
		    redpos = switchred;
		    split = 1;
	       );
	  );
     ) else if r == 2 and g == 0 then (
     	  redpos#(blackup#0)=redpos#critrow;
	  redpos#critrow = 99;
     );
     redpos = new List from redpos;
     {redpos, split}
)
-- TEST THE FUNCTION HERE!!
moveRed({1,5},{0,0},{99, 5, 99, 4, 99, 1},6)
