newPackage (
  "HilbertML",
  Version=>"1.0",
  Authors => {{Name => "Lily Silverstein", Email => "lsilverstein@cpp.edu"}},
  Headline => "Hilbert series computations with different pivot strategies",
  DebuggingMode => false
)


export {
    "allTreeScores",
    "generatorPivot",
    "m2pivot",
    "mostFrequentVar",
    "pivotHilbert",
    "purePowerGCD",
    "randomGCD",
    "treeScore",
    "PivotStrategy",
    "RandomQuantity",
    "PrintTree"
    }

-------------------------------
-- Methods for choosing a pivot
-------------------------------

generatorPivot = method()
generatorPivot (MonomialIdeal) := (I) -> (
    first sort(select(mingensList I, a -> #(support a)>1), MonomialOrder => RevLex)
    )

mostFrequentVar = method();
mostFrequentVar (MonomialIdeal) := I -> (
    first random commonest flatten select(apply(mingensList I, support), a -> #a>1)
    )

m2pivot = method();
m2pivot (MonomialIdeal) := I -> (
    f := mostFrequentVar I;
    candidates := select(mingensList I, mon -> #(support mon)>1 and gcd(mon, f) > 1);
    f^(degree(f, gcd(candidates)))
    )

randomGCD = method();
randomGCD (MonomialIdeal, ZZ) := (I, k) -> (
    f := mostFrequentVar I;
    candidates := select(mingensList I, mon -> #(support mon) > 1 and gcd(mon, f) > 1);
    if #candidates < k then gcd candidates else gcd(take(random candidates, k))
    )

purePowerGCD = method();
purePowerGCD (MonomialIdeal, ZZ) := (I, k) -> (
    f := mostFrequentVar I;
    candidates := select(mingensList I, mon -> #(support mon) > 1 and gcd(mon, f) > 1);
    if #candidates < k then f^(degree(f, gcd candidates)) else f^(degree(f, gcd(take(random candidates, k))))
    )

-----------------------------------------------------------------
-- Compute Hilbert series numerator with specified pivot strategy
-----------------------------------------------------------------
pivotHilbert = method(TypicalValue => Sequence, Options => {PivotStrategy => "Variable", RandomQuantity => 2, PrintTree => false});
pivotHilbert (MonomialIdeal, Thing) := o -> (I, T) -> (
    --0-base-case
    if nontrivialPowerProducts I == 0 then(
	zeroBaseCase(I, T)
	)
    --1-base-case
    else if nontrivialPowerProducts I == 1 then(
	oneBaseCase(I, T)
	)
    else(
	pivot := if o.PivotStrategy == "Variable" then m2pivot I else(
	    if o.PivotStrategy == "GCD" then randomGCD(I, o.RandomQuantity) else(
		if o.PivotStrategy == "PureGCD" then purePowerGCD(I, o.RandomQuantity) else(
		    if o.PivotStrategy == "Generator" then generatorPivot(I)
		    )
		)
	    );
	if member(pivot, mingensList I) then(
	    J1 := monomialIdeal(delete(pivot, mingensList I));
	    K1 := (J1:pivot);
	    pivotHilbert (J1, T, PivotStrategy => o.PivotStrategy, RandomQuantity => o.RandomQuantity, PrintTree => o.PrintTree) - T^(sum degree pivot) * pivotHilbert(K1, T, PivotStrategy => o.PivotStrategy, RandomQuantity => o.RandomQuantity, PrintTree => o.PrintTree)
	    )
	else(
	    J2 := (I + monomialIdeal(pivot));
	    K2 := (I:pivot);
	    pivotHilbert (J2, T, PivotStrategy => o.PivotStrategy, RandomQuantity => o.RandomQuantity, PrintTree => o.PrintTree) + T^(sum degree pivot) * pivotHilbert(K2, T, PivotStrategy => o.PivotStrategy, RandomQuantity => o.RandomQuantity, PrintTree => o.PrintTree)
	    )
	)
    )

--------------------------------------------------------------------
-- Number of base cases for a given ideal and a given pivot strategy
--------------------------------------------------------------------
treeScore = method(TypicalValue => Sequence, Options => {PivotStrategy => "Variable", RandomQuantity => 2, PrintTree => false});
treeScore (MonomialIdeal) := o -> I -> (
    if o.PrintTree then(
	<< I << endl;
	);
    if isBaseCase I then (
	if o.PrintTree then(
	    << " base case " << endl;
	    );
	1
	) 
    else (
	pivot := if o.PivotStrategy == "Variable" then m2pivot I else(
	    if o.PivotStrategy == "GCD" then randomGCD(I, o.RandomQuantity) else(
		if o.PivotStrategy == "PureGCD" then purePowerGCD(I, o.RandomQuantity) else(
		    if o.PivotStrategy == "Generator" then generatorPivot(I)
		    )
		)
	    );
	if o.PrintTree then(
	    << "pivot: " << pivot << endl;
	    );
	if member(pivot, mingensList I) then(
	    J1 := monomialIdeal(delete(pivot, mingensList I));
	    K1 := (J1:pivot);
	    treeScore (J1, PivotStrategy => o.PivotStrategy, RandomQuantity => o.RandomQuantity, PrintTree => o.PrintTree) + treeScore (K1, PivotStrategy => o.PivotStrategy, RandomQuantity => o.RandomQuantity, PrintTree => o.PrintTree)
	    )
	else(
	    J2 := (I + monomialIdeal(pivot));
	    K2 := (I:pivot);
	    treeScore (J2, PivotStrategy => o.PivotStrategy, RandomQuantity => o.RandomQuantity, PrintTree => o.PrintTree) + treeScore (K2, PivotStrategy => o.PivotStrategy, RandomQuantity => o.RandomQuantity, PrintTree => o.PrintTree)
	    )
	)
    ) 

------------------------------------------------------------------
-- Number of base cases for a given ideal and all pivot strategies
-- Input: monomial ideal
-- Output: sequence whose first element is a list with the number 
--     of base cases for every pivot considered, and whose second 
--     element is the index of the best pivot strategy 
------------------------------------------------------------------
allTreeScores = method();
allTreeScores (MonomialIdeal) := (I) -> (
    N := 10; --number of trials to average the trees over
    allTrees := {
	treeScore(I, PivotStrategy => "Generator"),
	toRR(1/N)*(sum toList(apply(1..N, i -> treeScore(I, PivotStrategy => "Variable")))),
	toRR(1/N)*(sum toList(apply(1..N, i -> treeScore(I, PivotStrategy => "M2")))),
	toRR(1/N)*(sum toList(apply(1..N, i -> treeScore(I, PivotStrategy => "PureGCD", RandomQuantity => 1)))),
	toRR(1/N)*(sum toList(apply(1..N, i -> treeScore(I, PivotStrategy => "PureGCD", RandomQuantity => 2)))),
	toRR(1/N)*(sum toList(apply(1..N, i -> treeScore(I, PivotStrategy => "PureGCD", RandomQuantity => 3)))),	
	toRR(1/N)*(sum toList(apply(1..N, i -> treeScore(I, PivotStrategy => "GCD", RandomQuantity => 2)))),
	toRR(1/N)*(sum toList(apply(1..N, i -> treeScore(I, PivotStrategy => "GCD", RandomQuantity => 3)))),
	toRR(1/N)*(sum toList(apply(1..N, i -> treeScore(I, PivotStrategy => "GCD", RandomQuantity => 4))))
	};
    allTrees   
)

----------------
-- Local Methods
----------------
mean = method();
mean (List) := (L) -> (
    sum(L)/#L
    )

variance = method();
variance (List) := (L) -> (
    m := mean L;
    sum(apply(L, i -> (i-m)^2))/#L
    )

nontrivialPowerProducts = method();
nontrivialPowerProducts (MonomialIdeal) := (I) -> (
    number(apply(mingensList I, mon -> #support mon), a -> a>1)
    )

isBaseCase = method();
isBaseCase (MonomialIdeal) := (I) -> (
    nontrivialPowerProducts I <= 1
    )

mingensList = method();
mingensList (MonomialIdeal) := (I) -> (
    flatten first entries mingens I
    )

colon := (a, b) -> (
    apply(#a, i -> max(a#i-b#i, 0))
    )

zeroBaseCase = method();
zeroBaseCase (MonomialIdeal, Thing) := (M, t) -> (
    product(apply(mingensList M, m -> 1-t^(sum degree m) ))
    )

oneBaseCase = method();
oneBaseCase (MonomialIdeal, Thing) := (K, t) -> (
    P := first select(mingensList K, m -> #support m > 1);
    mL := delete(P, mingensList K);
    product(apply(mL, m -> 1-t^(sum degree m))) - t^(sum degree P) * product(apply(mL, m -> 1-t^(sum colon(flatten exponents m, flatten exponents P))))
    )


--------
-- Tests
--------
--nontrivialPowerProducts, isBaseCase, zero- and oneBaseCase
TEST ///
R = QQ[x,y,z,w];
I = monomialIdeal(x^2*y*z^3, x*y^2*z^2, y*z*w^4, z^5*w);
assert(nontrivialPowerProducts I == 4)
assert(isBaseCase I == false)
J = monomialIdeal(x^5, y^2, z^7);
assert(nontrivialPowerProducts J == 0)
assert(isBaseCase J)
assert(zeroBaseCase(J, t) == -t^14 + t^12 + t^9 - t^5 - t^2 + 1)
K = monomialIdeal(x^5, y^2, z^7, x^4*y*z^3);
assert(nontrivialPowerProducts K == 1)
assert(isBaseCase K)
assert(oneBaseCase(K, t) == -2*t^13 + 2*t^12 - t^10 + 3*t^9 - t^8 - t^5 - t^2 + 1)
///

--purePowerGCD and generatorPivot
TEST ///
R = QQ[x,y,z,w];
I = monomialIdeal(x^2*y^3*z,y*z^2*w^2,x^2*z*w^4,x^5*w);
assert(purePowerGCD(I, 2) == 2)
assert(generatorPivot I == y*z^2*w^2)
///

--treeScore and pivotHilbert
--an example ideal used throughout Bigatti 1997
TEST ///
R = QQ[x,y,z,w];
B = monomialIdeal (x*z^3, x^2*y^2*z, x*y^3*z, x^3*y*z*w);
assert(treeScore(B, PivotStrategy => "Variable") == 5)
assert(pivotHilbert(B,t) == -t^9 + 3*t^7 - 2*t^5 - t^4 + 1)
///

--colon
TEST ///
assert(colon({0,0,7},{4,1,3}) == {0,0,4})
///


end

--
restart
needsPackage("HilbertML", FileName => "~/Desktop/MonLearning/HilbertML.m2")

