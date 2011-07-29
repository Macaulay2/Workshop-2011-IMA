newPackage(
     "LRcheckergame",
     Version => "0.1",
     Date => "July 25, 2011",
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
     output2bracket,
     bracket2partition,
     redChkrPos,
     moveRed,
     moveCheckers,
     playCheckers
     }
-- Abraham Martin del Campo
-- 25/July/2011
-- ---------------------
-- This is a file where I implement Ravis LR-decomposition
-- ---------------------

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
     ) else "wrong partition size, you need lest boxes"
)
--verifyLength({2,1,1,1},3)


-- l and m are partitions of n
-- l = {2,1};
-- m = {1,1};

-- Dictionaries of different notation
partition2bracket = method(TypicalValue => List)
partition2bracket(List,ZZ,ZZ) := (l, k, n) -> (
     l = verifyLength(l, k);
     brackt := for i to #l-1 list (n-k)+(i+1)-l#i
)

partition2input = method(TypicalValue => List)
output2partition = method(TypicalValue => List)
--partition2bracket(l,k,n)
--partition2bracket({2,1},3,7)
--partition2bracket({1,1},3,7)
--partition2bracket({1},3,7)

--combine all these functions to make only
-- partition -> checkers and viceversa
bracket2input = method(TypicalValue => List)
bracket2input(List,ZZ) := (br,n) ->(
     inp := for i to n-1 list 99;
     inp = new MutableList from inp;
     apply(br, b-> inp#(b-1) = b-1);
     toList inp
)
--bracket2input({4,6,7},7)

output2bracket = method(TypicalValue=>List)
output2bracket List := outp -> (
     br := select(outp, x-> x!=99);
     apply(br, x-> x=x+1)
) 
--output2bracket({99, 99, 99, 3, 99, 5, 6})

bracket2partition = method(TypicalValue => List)
bracket2partition(List,ZZ) := (l, n) -> (
--     l = reverse sort l;
     partitn := for i to #l-1 list (n-#l)+(i+1)-l#i 
)
--bracket2partition({2,4,6},6)

-- change this method to be between checkers
redChkrPos = method(TypicalValue => List)
redChkrPos(List,List,ZZ,ZZ) := (l,m,k,n) -> (
     -- input the Schubert conditions l and m
     --     as bracket
     -- input the Grassmannian G(k,n)
     m = reverse m;
     board := for i to n-1 list 99;
     redPos := new MutableList from board;
     apply(#l, j -> redPos#(l#j-1) = m#j-1);
     toList redPos
)
--Red =redChkrPos(partition2bracket({2,1},3,6),partition2bracket({1,1},3,6),3,6)

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
     critrow := 0;
     critdiag := 0;
     g:=2; -- These are two flags to indicate in which situation we are 
     r:=2;
     indx := new List;
     redpos := new MutableList from redposition;
     -- find the "critical row"
     indx = for i to n-blackdown#0-1 list n-1-i;
     apply(indx, j -> (
	  if redpos#j == blackdown#1 then (
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
	       redpos#critdiag = 99;
	       redpos#(blackup#0) = blackdown#1;
	  ) else if g == 1 then(
	       block := 0;
	       blockindx := for i to critdiag-critrow list critrow-1-i;
	       apply(blockindx, b -> if redpos#critrow < redpos#blockindx and redpos#blockindx < redpos#critdiag then block = 1);
	       if block != 1 then (
		    -- switch the rows of the red checkers in the critical diagonal and row
		    -- then, move the left one over to the column of the ascending black
		    switchred := redpos;
		    switchred#critrow = switchred#critdiag;
		    switchred#critdiag = 99;
		    switchred#(blackup#0) = blackdown#1;
		    if #redpos != #switchred then print("the error is here");
		    redpos = join(redpos, switchred);
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

--moveRed({0,3},{3,2},{3,99,99,5,99,1},6) -- this should move the red
--moveRed({2,5},{3,4},{2,99,99,5,99,1},6) -- this shouldnt move the red
--moveRed({0, 2}, {4, 1}, {2, 99, 99, 5, 99, 1},6) --this one should move the red!!
--moveRed({1, 3}, {4, 2}, {1, 99, 99, 5, 99, 2},6) -- and this error is even worse!

moveCheckers = method(TypicalValue => List)
moveCheckers(List,List,ZZ) := (blackposition, redposition, n) ->(
     splitcount:=0;
     copies:=0;
     -- determine the columns of the descending and ascending black checkers
     desccol := 1 + position(blackposition, x->x == n-1);
     asccol := position(blackposition, x-> x == 1+blackposition#desccol);
     for blackdown1 from desccol to n-1 do(
	  if blackdown1 == desccol+1 then asccol=0;
	  for blackup1 from asccol to blackdown1-1 do(
	       blackup2 := n-blackdown1+blackup1;
	       blackdown2 := blackup2-1;
	       (redposition,copies) = toSequence moveRed({blackup1,blackup2},{blackdown1,blackdown2}, redposition,n);
	       blackposition = new MutableList from blackposition;
	       blackposition#blackup1 = blackposition#blackup1 - 1;
	       blackposition#blackdown1 = blackposition#blackdown1 + 1;
	       if copies == 1 then (
		    blackposition = join(blackposition,blackposition);
		    splitcount = splitcount + 1;
	       );
	  );
     );
     {toList(blackposition), toList(redposition), splitcount}
)
--moveCheckers({3,5,4,2,1,0},{3,99,99,5,99,1},6)

playCheckers = method(TypicalValue => List)
playCheckers(List,List,ZZ,ZZ) := (partn1,partn2,k,n) -> (
     reds:= new List;
     tree := new List;
     storeRed:=new List;
		 redChkrs := new List;
     splitcount := 0;
		 if partn1 > partn2 then(
		   redChkrs=redChkrPos(partition2bracket(partn2,k,n),partition2bracket(partn1,k,n),k,n);
		 ) else (
		   redChkrs=redChkrPos(partition2bracket(partn1,k,n),partition2bracket(partn2,k,n),k,n);
		 );
     -- we check for red checkers above the diagonal. If one, give a null output
     --apply(#redChkrs, i->(
	--  if i+redChkrs#i < n-1 then return({toList(n:99)})
     --));
     blackChkrs:=new List;
     counter:=0;
     blackChkrs = reverse toList (0..(n-1)); --initial black positions.
     while blackChkrs != {} do (
	  (blackChkrs, redChkrs, splitcount) = toSequence moveCheckers(blackChkrs, redChkrs, n);
	  counter = counter+1;
	  tree=join(tree,toList(splitcount:counter));
	  storeRed = join(storeRed, {take(redChkrs,n)});
    blackChkrs = drop(blackChkrs,n);
	  redChkrs = drop(redChkrs,n-1);
    );
     -- here call the function makeTree
    storeRed / output2bracket
)
--playCheckers({1,1},{2,1},3,6)
--playCheckers({1,1},{2,0},2,4)
--playCheckers({1},{1},2,4)
--playCheckers({1,1},{2,1},3,6)
--playCheckers({2,1},{1,1},3,6)

