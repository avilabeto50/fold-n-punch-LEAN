import FoldAndPunch.Geometry
import FoldAndPunch.Folding
import FoldAndPunch.Punching
import FoldAndPunch.Creases
import FoldAndPunch.FoldLemmas
import FoldAndPunch.ConfigurationLemmas
import FoldAndPunch.Pair
import FoldAndPunch.CreaseLemmas
import FoldAndPunch.PairCreases
import FoldAndPunch.PunchingLemmas
import FoldAndPunch.PairBatches
import FoldAndPunch.PairCreaseCount
import FoldAndPunch.K2
import FoldAndPunch.CreaseUnions
import FoldAndPunch.SecondFoldCreases
import FoldAndPunch.Triple
import FoldAndPunch.TripleBatches
import FoldAndPunch.K3

/-!
Convex-polygon folding and depth-limited punching.
For even n, the complete k=2 algorithm is proved safe and complete, with
at most n/2 distinct crease segments. This is a uniform linear upper bound.
Two successive folds create at most three creases; the second contributes at
most two. Any three distinct fresh vertices can be punched by the prescribed
two folds, using the exposure check to choose the second placement and punch side.
For n divisible by three, the complete k=3 iteration punches all and only
vertices in n/3 batches, with at most n geometric crease segments.
-/
