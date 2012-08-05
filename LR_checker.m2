-- Abraham Martin del Campo
-- 25/July/2011
-- ---------------------
-- This is a file to test the implementation of numerical LR-rule
-- ---------------------

restart
setRandomSeed 0
--debug needsPackage "LRcheckergame";
debug needsPackage "NumericalSchubertCalculus";
root = playCheckers({1},{1},2,4)
resolveNode(root, {({1},random(FFF^4,FFF^4)), ({1},random(FFF^4,FFF^4))})
printTree root
peek root

root = playCheckers({2,1,0},{2,1,0},3,6)
time resolveNode(root, {({2,1,0},random(FFF^6,FFF^6))})
peek root

root = playCheckers({2,1},{2,1},3,6)
time resolveNode(root, {({2},random(FFF^6,FFF^6)), ({1},random(FFF^6,FFF^6))})
peek root

n=7; K'n=FFF^n;
root = playCheckers({2,1,0},{2,1,0},3,n)
time resolveNode(root, {({2,1,0},random(K'n,K'n)),({2,1,0},random(K'n,K'n))})
peek root
printTree root

root = playCheckers({2,1}, {2}, 3,6)
time resolveNode(root, {({2},random(FFF^6,FFF^6)), ({2},random(FFF^6,FFF^6))})
peek root
printTree root

---- there is something wrong, 
root = playCheckers({3,2,2},{2}, 3,6)
peek root
resolveNode(root, {})
restart
setRandomSeed 0
debug needsPackage "LRcheckergame";

-- we test if the resolveNode function
-- can just solve the problem when 
-- the Schubert problem consist of two
-- complementary partitions only
root = playCheckers({3,3,1},{2},3,6)
resolveNode(root,{})
peek root

root = playCheckers({3,3,1}, {2}, 3,6)
resolveNode(root, {({2,1,0},random(FFF^6,FFF^6))})

-------

movetype
startSolutions
s -- the "solutions that are wrong"
polys
norm sub(polys,matrix{{0}|s})

SolBlackBox =apply(node.SolutionsSuperset, X->toRawSolutions(coordX,X))
s2 = flatten SolBlackBox
norm sub(polys,matrix{{0}|s2})

--------------------------------------
end
moveCheckers({3,5,4,2,1,0},{3,99,99,5,99,1},6)
restart
needsPackage "LRcheckergame";
moveRed({0, 2}, {2, 1}, {99, 3, 99, 1}, 4)
-- The output must be
-- {{99, 3, 99, 1, 1, 99, 99, 3},1}
playCheckers({1},{1},2,4)

moveRed({0, 3}, {3, 2}, {99, 99, 5, 3, 99, 2}, 6)
moveRed({2,5},{3,4},{2,99,99,5,99,1},6)
-- output must be {99, 99, 5, 3, 99, 2}
playCheckers({1,1},{1,1},3,6)
playCheckers({1,1},{2,1},3,6)
playCheckers({1,1},{2,0},2,4)
playCheckers({1,1},{2,1},3,6)
playCheckers({2,1},{1,1},3,6)

Sol = playCheckers({3},{3},2,8)
#Sol
unique Sol#0
redChkrPos(partition2bracket(partn2,k,n),partition2bracket(partn1,k,n),k,n);
playCheckers({2,2},{2,2},4,8)

restart
needsPackage "LRcheckergame";
black = {3,5,4,2,1,0};
red = {3,NC,NC,5,NC,1};
makeLocalCoordinates [black,red];
peek oo

black = {6,7,8,9,11,12,13,14,10,5,4,3,2,1};
red = {}


