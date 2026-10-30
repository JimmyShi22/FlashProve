-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqTailToy.lean: THE SMALLNESS TEST: THE PREMISES OF `eqTail_returns`
(Johnson/Desc/K8/Honest/EqTailReturns.lean) AS ONE TEST WITH CODE, A THEOREM THAT ITS YES GIVES
THEM, AND `#guard` LINES AT THE LIBRARY's SMALL EXAMPLE (OnBytes/Model/TestTailRun.lean: one matrix
of 6 rows of cells and 2 columns, one table with three rows to an entry, 160 combinations). Lemmas
and tests; none of the library's goals.

  `freshB`, `fitsB`, `tableB`, `readB`   four of the premises as tests
  `tailReadyB before front tl funs F cs`   all seventeen
  `tailReady_of_B`    a yes gives `TailReady`, at the marks and the two numbers of segments that the
                      library's own functions yield
  `liveB tl' x`       the test on values at one read
  `behindFour`        the example behind the list's first four claims: the library's own `eqKeys`
                      and `eqCounts` run on it
What the lines show. 1 At the example all seventeen hold, the test on values holds behind the
weights' step, and the text itself returns: the law is not empty. 2 With one thing spoiled the test
says no AND the text refuses, under the name of the guard that is meant: a count of claims in front;
the batching element not drawn; a table on no matrix of the list; a mark that no read sets; a vector
shorter than its tables; an array of another kind; a table whose rows do not divide the matrix's; a
plan without a claim; a shape with two symbols to a row; a matrix's sums laid before; a shape with
another number of columns; an array without a column; a table twice in the list, so that a read is
marked twice; the vector of reads not there. 3 With a column of the drawn matrix laid to 0 the
seventeen still hold, the test on values fails and the text refuses: the one premise on values
bites.
Limits. One example, with ONE matrix: `apart` (no two matrices on one array) cannot fail there;
`sum` and `count` are not spoiled apart from `kinds` and `tile3`; `tile1` not apart from `allSet`;
of `fits` the row of cells, and of `reads` the row below 2^32, are spoiled by no line. THE TEST GOES
ONE WAY: a yes gives the premises; a no is not shown to deny them: beside each no the text itself
refuses. One thing spoiled is not always one premise broken: the table on matrix 7 and the fifth
mark also break `tile3`; rows that do not divide also turn the list of reads; the vector not there
also breaks `reads`; the table twice in the list also breaks `tile3` and `count`. Three names are
shared by several guards ("internal-f-exist": five; "internal-f-table-read": two; "weightsF:1030":
three tests in one): there the name alone does not tell which test refused; the text's order does.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqTailReturns
import OnBytes.Model.TestTailRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St eqTail)
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- No matrix's sums are laid yet. -/
def freshB (tl : HTailF2) : Bool := (List.range tl.NM).all fun mu => !(takenOf tl).getD mu true

/-- Each matrix's shape has its columns, and it has a row of cells. -/
def fitsB (tl : HTailF2) : Bool :=
  (List.range tl.NM).all fun mu =>
    (tl.shp.getD mu {}).k == (tl.mats.getD mu {}).k && decide (0 < (tl.mats.getD mu {}).m)

/-- Each table on a matrix of the list and on one of the two vectors is well made. -/
def tableB (tl : HTailF2) (funs : Array HFun) : Bool :=
  funs.toList.all fun Fn =>
    !(decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)) ||
      ((tl.ix.U.getD Fn.tree none).isSome && Fn.len != 0 &&
        (tl.mats.getD Fn.mat {}).m % Fn.len == 0 && Fn.phi.size == Fn.len)

/-- A read is ready. -/
def readB (tl : HTailF2) (F : Fork) (x : HFun × Nat) : Bool :=
  match tl.ix.U.getD x.1.tree none with
  | none => false
  | some tU =>
    colsOf F tU != 0 && decide (x.1.mat < tl.NM) && x.1.len != 0 && decide (x.2 < segs tl x.1) &&
      (!decide (0 < (tl.mats.getD x.1.mat {}).k) ||
        decide ((x.1.start + ((tl.mats.getD x.1.mat {}).k - 1) * segs tl x.1 + x.2) / colsOf F tU
          < 2 ^ 32))

/-- All seventeen premises. -/
def tailReadyB (before front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork)
    (cs : Array Claim) : Bool :=
  match marksOf tl funs, tl.tablesTile funs 0, tl.tablesTile funs 2 with
  | some rd, some s1, some s3 =>
    front + cs.size - before == 4 && F.thetaDrawnF && F.planClaimsF != 0 && oneRow tl &&
      freshB tl && fitsB tl && tableB tl funs && (readsList tl funs).all (readB tl F) &&
      (rd.all fun a => a.all id) &&
      (funs.all fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)) &&
      ((List.range F.trees.size).all fun t =>
        (tiesOnOf tl F.trees.size).getD t 0 ==
          (if (F.trees.map (·.kind)).getD t .table == .symbols then 1 else 0)) &&
      (tiesOnOf tl F.trees.size).foldl (· + ·) 0 == tl.NM &&
      (readsList tl funs).length == s1 + s3 && allDistinct tl.gtTree.toList
  | _, _, _ => false

theorem readReady_of_B {tl : HTailF2} {F : Fork} {x : HFun × Nat} (h : readB tl F x = true) :
    ∃ tU, ReadReady tl F x.1 x.2 tU := by
  unfold readB at h
  cases hU : tl.ix.U.getD x.1.tree none with
  | none => rw [hU] at h; cases h
  | some tU =>
    rw [hU] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
      decide_eq_true_eq, decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨tU, hU, h1, h2, h3, h4, fun hk => h5.resolve_left fun hn => hn hk⟩

/-- A yes gives the seventeen premises. -/
theorem tailReady_of_B {before front : Nat} {tl : HTailF2} {funs : Array HFun} {F : Fork}
    {cs : Array Claim} (h : tailReadyB before front tl funs F cs = true) :
    ∃ rd s1 s3, TailReady before front tl funs F cs rd s1 s3 := by
  unfold tailReadyB at h
  cases hm : marksOf tl funs with
  | none => rw [hm] at h; cases h
  | some rd =>
    cases h1 : tl.tablesTile funs 0 with
    | none => rw [hm, h1] at h; cases h
    | some s1 =>
      cases h3 : tl.tablesTile funs 2 with
      | none => rw [hm, h1, h3] at h; cases h
      | some s3 =>
        rw [hm, h1, h3] at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩,
          a14⟩ := h
        refine ⟨rd, s1, s3, beq_iff_eq.1 a1, a2, bne_iff_ne.1 a3, a4, fun mu hmu => ?_,
          fun mu hmu => ?_,
          fun Fn hFn hmat htree => ?_, fun x hx => readReady_of_B (List.all_eq_true.1 a8 x hx), hm,
          a9, a10, h1, h3, a11, beq_iff_eq.1 a12, beq_iff_eq.1 a13, a14⟩
        · have := List.all_eq_true.1 a5 mu (List.mem_range.2 hmu)
          simpa using this
        · have := List.all_eq_true.1 a6 mu (List.mem_range.2 hmu)
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
          exact this
        · have := List.all_eq_true.1 a7 Fn hFn
          simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Bool.and_eq_false_iff,
            Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_iff_eq,
            beq_eq_false_iff_ne, bne_iff_ne, ne_eq] at this
          rcases this with h' | h'
          · rcases h' with h' | h'
            · exact absurd hmat h'
            · rcases htree with e | e
              · exact absurd e h'.1
              · exact absurd e h'.2
          · exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

/-- The test on values at one read. -/
def liveB (tl' : HTailF2) (x : HFun × Nat) : Bool :=
  (List.range (tl'.mats.getD x.1.mat {}).k).all fun c =>
    !isZeroE ((tl'.gamV.getD x.1.mat #[]).getD c zeroE)

namespace TailToy

/-- The example's table. -/
def funs : Array HFun := TestTailRun.funs false

/-- The example behind its messages and the draw of the batching element; turn: what is spoiled. -/
def start (turnT : HTailF2 → HTailF2) (turnF : Fork → Fork) : Option (HTailF2 × Fork) :=
  TestTailRun.planned.toOption.map fun y =>
    (turnT (TestTailRun.afterMessages y.1), turnF (TestTailRun.afterDraw y.1 y.2))

/-- Behind the list's first four claims: the library's own two routines, run. front: the lookup's
own claims stand in front. -/
def behindFour (turnT : HTailF2 → HTailF2) (turnF : Fork → Fork) : Option (Nat × HTailF2 × St) :=
  (start id id).bind fun y =>
    ((eqKeys y.1 >>= eqCounts) (lookRows y.1) (y.2, #[])).toOption.map fun z =>
      (lookRows y.1, turnT z.1, (turnF z.2.1, z.2.2))

/-- What the test with code says there. -/
def ready (turnT : HTailF2 → HTailF2) (turnF : Fork → Fork) (fs : Array HFun := funs)
    (less : Nat := 0) : Option Bool :=
  (behindFour turnT turnF).map fun y => tailReadyB (y.1 - less) y.1 y.2.1 fs y.2.2.1 y.2.2.2

/-- What the text itself says there: none: it returns; some: the name under which it refuses. -/
def refusal (turnT : HTailF2 → HTailF2) (turnF : Fork → Fork) (fs : Array HFun := funs)
    (less : Nat := 0) : Option (Option String) :=
  (behindFour turnT turnF).map fun y =>
    match eqTail (y.1 - less) y.2.1 fs y.1 y.2.2 with
    | .ok _ => none
    | .error e => some e

/-- The test on values behind the weights' step, at all reads. -/
def live (turnT : HTailF2 → HTailF2) : Option Bool :=
  (behindFour turnT id).bind fun y =>
    (eqWeights y.2.1 y.1 y.2.2).toOption.map fun z => (readsList y.2.1 funs).all (liveB z.1)

-- 1 the member
#guard (behindFour id id).isSome
#guard ready id id == some true
#guard live id == some true
#guard refusal id id == some none
#guard (behindFour id id).any fun y => (readsList y.2.1 funs).length == 2
-- 2 one thing spoiled: the test says no, and the text refuses under the guard's own name
#guard ready id id funs 1 == some false && refusal id id funs 1 == some (some "internal-f-exist")
#guard ready id (fun F => { F with thetaDrawnF := false }) == some false &&
  refusal id (fun F => { F with thetaDrawnF := false }) == some (some "weightsF:1030")
#guard ready id id (funs.push { mat := 7, len := 3, tree := 2 }) == some false &&
  refusal id id (funs.push { mat := 7, len := 3, tree := 2 }) ==
    some (some "internal-t2f-functional")
#guard ready (fun t => { t with tabLen := #[0, 5] }) id == some false &&
  refusal (fun t => { t with tabLen := #[0, 5] }) id == some (some "internal-f-table-read")
#guard ready (fun t => { t with nUF := #[0, 0, 3] }) id == some false &&
  refusal (fun t => { t with nUF := #[0, 0, 3] }) id == some (some "objectsF:1086")
#guard ready id (fun F => { F with trees := F.trees.map fun X => { X with kind := .table } }) ==
    some false &&
  refusal id (fun F => { F with trees := F.trees.map fun X => { X with kind := .table } }) ==
    some (some "internal-f-exist")
#guard ready id id (funs.map fun f => { f with len := 4 }) == some false &&
  refusal id id (funs.map fun f => { f with len := 4 }) == some (some "shape-functional")
#guard ready id (fun F => { F with planClaimsF := 0 }) == some false &&
  refusal id (fun F => { F with planClaimsF := 0 }) == some (some "weightsF:1030")
#guard ready (fun t => { t with shp := t.shp.map fun s => { s with J := 2 } }) id == some false &&
  refusal (fun t => { t with shp := t.shp.map fun s => { s with J := 2 } }) id ==
    some (some "weightsF:1030")
#guard ready (fun t => { t with foldTakenF := #[true] }) id == some false &&
  refusal (fun t => { t with foldTakenF := #[true] }) id == some (some "weightsF:1031")
#guard ready (fun t => { t with shp := t.shp.map fun s => { s with k := 3 } }) id == some false &&
  refusal (fun t => { t with shp := t.shp.map fun s => { s with k := 3 } }) id ==
    some (some "linTie:940")
#guard ready id (fun F => { F with trees := F.trees.map fun X => { X with K := 0 } }) ==
    some false &&
  refusal id (fun F => { F with trees := F.trees.map fun X => { X with K := 0 } }) ==
    some (some "internal-L-row")
#guard ready id id (funs ++ funs) == some false &&
  refusal id id (funs ++ funs) == some (some "objectsF:1077")
#guard ready (fun t => { t with ix := { t.ix with U := t.ix.U.set! 2 none } }) id == some false &&
  refusal (fun t => { t with ix := { t.ix with U := t.ix.U.set! 2 none } }) id ==
    some (some "internal-t2f-unit")
-- 3 a column of the drawn matrix laid to 0: the seventeen hold; the test on values fails; the text
-- refuses under the name of the guard on values
#guard ready (fun t => { t with cfF := t.cfF.mapIdx fun i x => if i < 160 then 0 else x }) id ==
  some true
#guard live (fun t => { t with cfF := t.cfF.mapIdx fun i x => if i < 160 then 0 else x }) ==
  some false
#guard refusal (fun t => { t with cfF := t.cfF.mapIdx fun i x => if i < 160 then 0 else x }) id ==
  some (some "internal-f-table-read")

end TailToy

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.readReady_of_B
#print axioms VerifiableInference.Desc.First.K8.Honest.tailReady_of_B
