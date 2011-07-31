-- Abraham Martin del Campo
-- 25/July/2011
-- ---------------------
-- This is a file where I implement Ravis LR-decomposition
-- ---------------------

--moveCheckers({3,5,4,2,1,0},{3,99,99,5,99,1},6)
restart
needsPackage "LRcheckergame";
moveRed({0, 2}, {2, 1}, {99, 3, 99, 1}, 4)
-- The output must be
-- {{99, 3, 99, 1, 1, 99, 99, 3},1}
playCheckers({1},{1},2,4)

moveRed({0, 3}, {3, 2}, {99, 99, 5, 3, 99, 2}, 6)
-- output must be {99, 99, 5, 3, 99, 2}

playCheckers({1,1},{1,1},3,6)
playCheckers({1,1},{2,1},3,6)
playCheckers({1,1},{2,0},2,4)
playCheckers({1,1},{2,1},3,6)
playCheckers({2,1},{1,1},3,6)


