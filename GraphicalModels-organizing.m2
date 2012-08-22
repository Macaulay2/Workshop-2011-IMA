
----------------------------------------------------------------------
----------------------------------------------------------------------
----------------------------------------------------------------------
-- here is the list of things we are exporting:
export {bidirectedEdgesMatrix,
       Coefficients,
              conditionalIndependenceIdeal,
       covarianceMatrix,
       directedEdgesMatrix,
       discreteVanishingIdeal,
       gaussianMatrices,
       gaussianParametrization,
              gaussianVanishingIdeal,
       SimpleTreks,
       gaussianRing, 
       globalMarkov,
       hiddenMap,
       identifyParameters, 
       inverseMarginMap,
       localMarkov,
       markovMatrices, 
       markovRing,        
       marginMap, 
       pairMarkov, 
       trekIdeal, 
       trekSeparation,
       VariableName,
       sVariableName,
       kVariableName,
       lVariableName,
       pVariableName,
       undirectedEdgesMatrix
	} 

-- LIST OF METHODS (in order of appearance in the package): 
pairMarkov Digraph
localMarkov Digraph
globalMarkov Digraph
markovRing Sequence
marginMap(ZZ,Ring)
inverseMarginMap(ZZ,Ring) 
hiddenMap(ZZ,Ring)
markovMatrices(Ring,List,List) 
markovMatrices(Ring,List)
gaussianRing ZZ
gaussianRing Digraph
covarianceMatrix(Ring)
gaussianMatrices(Ring,List)
gaussianRing Graph 
undirectedEdgesMatrix Ring 
gaussianVanishingIdeal Ring
pairMarkov Graph
localMarkov Graph
globalMarkov Graph
conditionalIndependenceIdeal (Ring,List)
conditionalIndependenceIdeal (Ring,List,List)
gaussianRing MixedGraph
directedEdgesMatrix Ring 
bidirectedEdgesMatrix Ring
gaussianParametrization (Ring,MixedGraph)
identifyParameters (Ring,MixedGraph)
trekSeparation MixedGraph
trekIdeal (Ring,MixedGraph)
trekIdeal (Ring,Graph)
trekIdeal (Ring,Digraph)


-- LIST OF FUNCTIONS (in order of appearance in the package): 
bayesBall -- [internal function used by globalMarkov]
--remove redundant statements:
equivStmts  -- [internal routine used within Markov relation routines to remove redundant statements]
setit -- [internal routine used within Markov relation routines to remove redundant statements]
under -- [internal routine used within Markov relation routines to remove redundant statements]
sortdeps  -- [internal routine used within Markov relation routines to remove redundant statements]
normalizeStmt -- [internal routine used within Markov relation routines to remove redundant statements]
minimize -- [internal routine used within Markov relation routines to remove redundant statements]
removeRedundants  -- [internal routine used within Markov relation routines to remove redundant statements]
pos -- [internal routine to get position of an element in a list]
cartesian -- [internal routine] 
possibleValues -- [internal routine]
prob -- [internal routine] 
setToBinary -- [internal routine]
subsetsBetween -- [internal routine]
-- NOTE: all of the above functions/routines are actually called from another function or method in the package. Checked.


----------------------------------------------------------------------
----------------------------------------------------------------------
----------------------------------------------------------------------
----------------------------------------------------------------------


---- NOW LIST OF ALL FUNCTIONS/METHODS IN THE ORDER THEY SHOULD APPEAR IN THE PACKAGE:

--**************************--
--  INTERNAL ROUTINES        	  --
--**************************--
--*************************************--
--  Functions used by globalMarkov--
--*************************************--
bayesBall
--*************************************--
--  Functions used throughout          --
--*************************************--
cartesian
pos 
possibleValues 
prob 
setToBinary
subsetsBetween 
--***********************************************************************************--
--  Functions used within Markov relation routines to remove redundant statements    --
--***********************************************************************************--
equivStmts  
setit 
under 
sortdeps 
normalizeStmt 
minimize 
removeRedundants  

--**************************--
--  METHODS 	      	   	  --
--**************************--
--****************************************************************************************--
--  Methods for creating conditional independence statements from graphs and digraphs	  --
--****************************************************************************************--
pairMarkov Graph
pairMarkov Digraph
localMarkov Graph
localMarkov Digraph
globalMarkov Graph
globalMarkov Digraph
--**************************************************************************************************************************************--
--  Methods for creating polynomial rings that carry information about random variables and/or underlying graph, digraph or mixed graph --
--**************************************************************************************************************************************--
markovRing Sequence
gaussianRing ZZ
gaussianRing Graph 
gaussianRing Digraph
gaussianRing MixedGraph
--********************************************************************************************************************************--
--  Methods for creating matrices relevant for the graphical models (covariance matrix, matrices whose minors vanish on the model)--
--********************************************************************************************************************************--
undirectedEdgesMatrix Ring 
directedEdgesMatrix Ring 
bidirectedEdgesMatrix Ring
markovMatrices(Ring,List,List) 
markovMatrices(Ring,List)
covarianceMatrix(Ring)
gaussianMatrices(Ring,List)
--******************************************************************--
--  Methods for creating ideals that vanish for a graphical model   --
--******************************************************************--
conditionalIndependenceIdeal (Ring,List)
conditionalIndependenceIdeal (Ring,List,List)
gaussianParametrization (Ring,MixedGraph)
gaussianVanishingIdeal Ring
trekSeparation MixedGraph
trekIdeal (Ring,MixedGraph)
trekIdeal (Ring,Graph)
trekIdeal (Ring,Digraph)
--********************************************************************************************************************************--
--  Methods for manipulating polynomial maps frequently used in graphical models
--********************************************************************************************************************************--
marginMap(ZZ,Ring)
inverseMarginMap(ZZ,Ring) 
hiddenMap(ZZ,Ring)
identifyParameters (Ring,MixedGraph)
