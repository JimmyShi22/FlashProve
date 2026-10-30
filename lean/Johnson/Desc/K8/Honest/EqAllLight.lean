-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/EqAllLight.lean: THE SMALLNESS TEST: THE ONE Bool OF THE WHOLE RUN OF
EQUATIONS ON SHAPES (allB, Johnson/Desc/K8/Honest/EqAllShape.lean) IN A LIGHTER FORM, FOR WHOEVER
EVALUATES IT AT A LARGE PLAN: it lays no mark. General laws: nothing is evaluated.

  allL            allB's text with the lighter test on the tail's premises (tailLightB,
                  Johnson/Desc/K8/Honest/TailLight.lean: no marks of the reads, no count of them;
                  at most two parts that hold tables) in the place of tailReadyB, at the same blank
                  records.
  **allB_of_light**   a yes of allL is a yes of allB. So every law that asks allB's yes may be
                  called with allL's.
  tableN, tableN_eq   the one test that reads a table's number of weights, on the shape's own
                  number, so that no array of zeros is built to be counted: the same Bool, by law.
  ivOf, sortedB, tileN, tileN_some   the tiling without the sort: where the tables' stretches lie
                  sorted, tablesTile's own walk over them as they lie; its return is tablesTile's.
  tailLightN, tailLight_of_N, allN, allL_of_N, **allB_of_N**   THE PAYER's FORM of the whole list's
                  Bool, with these two; its yes is allB's yes.
  eqGL, eqG_of_light   the step on the chain's shape (eqG, EqAllChain.lean) with allN in the place
                  of allB; where it returns, eqG returns the same.

It needs no law on blank records: the law "a yes of the lighter test is a yes of the test
for the seventeen" (tailReadyB_of_light, TailLightProofs.lean) holds at all records, so at these.
Limits. allL still walks every read once and sorts the tables twice; allN walks every read once and
rejects a list of tables that does not lie sorted, which allB may accept. LIGHT IS THE Bool ALONE:
eqGL's update is eqG's own (allRecU, allLedU). tailLightN still hands the blank records (t.blank;
each table with its array of zeros; ledBlank L) to readsList, readB, fb.all and tiesOnOf, among
others: that no such array is built hangs on what an evaluator leaves unforced, on no law. NOTHING
IS MEASURED IN THIS FILE; of the two remarks on Lean's kernel in its section heads the second tells
of a run outside the library, and the first ("would build") is a forecast. One direction alone.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.K8.Honest.EqAllChain
import Johnson.Desc.K8.Honest.TailLightProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Shape
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- **The lighter form of the whole list's Bool.** -/
def allL (front : Nat) (t : TailSh) (fs : List FunSh) (L : LedSh) (n : Nat) : Bool :=
  match t.heard with
  | none => false
  | some g =>
    t.funClosed && fs.length == t.funs.length && g.rows.length == lookRows t.blank &&
      Law.keysAt g.narrow (Law.EqSh.mk t.narrow L []) && openB g.leaves L &&
      tailLightB (front + n) front t.blank (fs.map FunSh.blank).toArray (ledBlank L)
        (Array.replicate (n + 4) {})

/-- **A yes of the lighter form is a yes of allB.** -/
theorem allB_of_light {front : Nat} {t : TailSh} {fs : List FunSh} {L : LedSh} {n : Nat}
    (h : allL front t fs L n = true) : allB front t fs L n = true := by
  unfold allL at h
  unfold allB
  cases hg : t.heard with
  | none =>
    rw [hg] at h
    cases h
  | some g =>
    rw [hg] at h
    dsimp only at h ⊢
    rw [Bool.and_eq_true] at h ⊢
    exact ⟨h.1, tailReadyB_of_light _ _ _ _ _ _ h.2⟩

/-! ## Sizes as numbers

At a blank table the one test that reads the weights' number asks the size of an array of zeros. At
a large plan (tables of 65,536 weights) Lean's kernel would build each such array to count it. So
that one test is written a second time, on the shape's own number, and shown to be the same. -/

/-- tableB (EqTailToy.lean) on the tables' shapes: the number of weights is read as a number. -/
def tableN (t : TailSh) (fs : List FunSh) : Bool :=
  fs.all fun f =>
    !(decide (f.mat < t.NM) && (f.tree == 0 || f.tree == 2)) ||
      ((t.ix.U.getD f.tree none).isSome && f.len != 0 &&
        (t.mats.getD f.mat {}).m % f.len == 0 && f.weights == f.len)

theorem tableN_eq (t : TailSh) (fs : List FunSh) :
    tableB t.blank (fs.map FunSh.blank).toArray = tableN t fs := by
  unfold tableB tableN
  show (fs.map FunSh.blank).all _ = _
  rw [List.all_map]
  congr 1
  funext f
  show (!(decide (f.mat < t.NM) && (f.tree == 0 || f.tree == 2)) ||
    ((t.ix.U.getD f.tree none).isSome && f.len != 0 &&
      (t.mats.getD f.mat {}).m % f.len == 0 &&
      (Array.replicate f.weights zeroE).size == f.len)) = _
  rw [Array.size_replicate]

/-! ## The tiling without the sort

HTailF2.tablesTile sorts the tables' stretches by their first entries (List.mergeSort) and walks
them. In a trial Lean's kernel ran out of memory on that sort at 31 tables. Where the stretches lie
sorted already the sort returns them as they lie. -/

/-- The stretches of the tables on vector un: first entry, entries, segments. -/
def ivOf (t : TailSh) (fs : List FunSh) (un : Nat) : List (Nat × Nat × Nat) :=
  (fs.filter fun f => f.tree == un).map fun f =>
    (f.start, (t.mats.getD f.mat {}).k * ((t.mats.getD f.mat {}).m / f.len),
      (t.mats.getD f.mat {}).m / f.len)

/-- Each member's first entry is at most each later member's. -/
def sortedB : List (Nat × Nat × Nat) → Bool
  | [] => true
  | a :: l => (l.all fun b => decide (a.1 ≤ b.1)) && sortedB l

theorem sortedB_pairwise : ∀ (l : List (Nat × Nat × Nat)), sortedB l = true →
    l.Pairwise fun a b => decide (a.1 ≤ b.1) = true
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    unfold sortedB at h
    rw [Bool.and_eq_true] at h
    exact List.pairwise_cons.2 ⟨fun b hb => List.all_eq_true.1 h.1 b hb, sortedB_pairwise l h.2⟩

/-- tablesTile's walk, at stretches that lie sorted; none where they do not. -/
def tileN (t : TailSh) (fs : List FunSh) (un : Nat) : Option Nat :=
  if sortedB (ivOf t fs un) then
    let first := t.tabFirst.getD (un / 2) 0
    let walked := (ivOf t fs un).foldl
      (fun (s : Option (Nat × Nat)) x =>
        s.bind fun (pos, segments) =>
          if x.2.1 != 0 && x.1 == pos then some (pos + x.2.1, segments + x.2.2) else none)
      (some (first, 0))
    walked.bind fun (pos, segments) =>
      if pos == first + t.tabLen.getD (un / 2) 0 &&
          ((t.ix.U.getD un none).isNone || decide (pos ≤ t.nUF.getD un 0)) then
        some segments
      else none
  else none

theorem tileN_some {t : TailSh} {fs : List FunSh} {un s : Nat} (h : tileN t fs un = some s) :
    t.blank.tablesTile (fs.map FunSh.blank).toArray un = some s := by
  unfold tileN at h
  by_cases hs : sortedB (ivOf t fs un) = true
  · rw [if_pos hs] at h
    unfold HTailF2.tablesTile
    have e : (((fs.map FunSh.blank).toArray.toList.filter fun Fn => Fn.tree == un).map fun Fn =>
        (Fn.start, (t.blank.mats.getD Fn.mat {}).k * ((t.blank.mats.getD Fn.mat {}).m / Fn.len),
          (t.blank.mats.getD Fn.mat {}).m / Fn.len)) = ivOf t fs un := by
      show (((fs.map FunSh.blank).filter fun Fn => Fn.tree == un).map _) = _
      rw [List.filter_map, List.map_map]
      rfl
    dsimp only
    rw [e, List.mergeSort_of_pairwise (sortedB_pairwise _ hs)]
    exact h
  · rw [if_neg hs] at h
    cases h

/-- tailLightB at the blank records, with tableN in the place of tableB and tileN in the place of
tablesTile. n: the number of claims on the array (allN hands in its own n + 4). -/
def tailLightN (before front : Nat) (t : TailSh) (fs : List FunSh) (L : LedSh) (n : Nat) : Bool :=
  let tb := t.blank
  let fb := (fs.map FunSh.blank).toArray
  let F := ledBlank L
  match tileN t fs 0, tileN t fs 2 with
  | some _, some _ =>
    front + n - before == 4 && F.thetaDrawnF && F.planClaimsF != 0 && oneRow tb &&
      freshB tb && fitsB tb && tableN t fs && (readsList tb fb).all (readB tb F) &&
      (fb.all fun Fn => decide (Fn.mat < tb.NM) && (Fn.tree == 0 || Fn.tree == 2)) &&
      ((List.range F.trees.size).all fun x =>
        (tiesOnOf tb F.trees.size).getD x 0 ==
          (if (F.trees.map (·.kind)).getD x .table == .symbols then 1 else 0)) &&
      (tiesOnOf tb F.trees.size).foldl (· + ·) 0 == tb.NM && allDistinct tb.gtTree.toList &&
      decide (tb.tabLen.size ≤ 2)
  | _, _ => false

theorem tailLight_of_N {before front : Nat} {t : TailSh} {fs : List FunSh} {L : LedSh} {n : Nat}
    (h : tailLightN before front t fs L n = true) :
    tailLightB before front t.blank (fs.map FunSh.blank).toArray (ledBlank L)
      (Array.replicate n {}) = true := by
  unfold tailLightN at h
  unfold tailLightB
  cases h0 : tileN t fs 0 with
  | none => rw [h0] at h; cases h
  | some s1 =>
    cases h2 : tileN t fs 2 with
    | none => rw [h0, h2] at h; cases h
    | some s3 =>
      rw [h0, h2] at h
      rw [tileN_some h0, tileN_some h2, tableN_eq, Array.size_replicate]
      exact h

/-- **The payer's form of the whole list's Bool.** -/
def allN (front : Nat) (t : TailSh) (fs : List FunSh) (L : LedSh) (n : Nat) : Bool :=
  match t.heard with
  | none => false
  | some g =>
    t.funClosed && fs.length == t.funs.length && g.rows.length == lookRows t.blank &&
      Law.keysAt g.narrow (Law.EqSh.mk t.narrow L []) && openB g.leaves L &&
      tailLightN (front + n) front t fs L (n + 4)

theorem allL_of_N {front : Nat} {t : TailSh} {fs : List FunSh} {L : LedSh} {n : Nat}
    (h : allN front t fs L n = true) : allL front t fs L n = true := by
  unfold allN at h
  unfold allL
  cases hg : t.heard with
  | none =>
    rw [hg] at h
    cases h
  | some g =>
    rw [hg] at h
    dsimp only at h ⊢
    rw [Bool.and_eq_true] at h ⊢
    exact ⟨h.1, tailLight_of_N h.2⟩

/-- **A yes of the payer's form is a yes of allB.** -/
theorem allB_of_N {front : Nat} {t : TailSh} {fs : List FunSh} {L : LedSh} {n : Nat}
    (h : allN front t fs L n = true) : allB front t fs L n = true :=
  allB_of_light (allL_of_N h)

/-- The step on the chain's shape, with the lighter Bool; the update is eqG's own. -/
def eqGL (front : Nat) (a : ChainSh) : Except String ChainSh :=
  match a.tl, a.led, a.tables with
  | some t, some L, some fs =>
    match t.heard with
    | some g =>
      if allN (L.claims + front) t fs L 0 then
        .ok ((a.setTl (allRecU (L.claims + front) 0 t fs L)).setLed (allLedU g L))
      else .error "K8.equations: the shape does not pass"
    | none => .error "K8.equations: no record is heard"
  | _, _, _ => .error "K8.equations: no link is open, or no list of tables is laid"

/-- Where the lighter step returns, eqG returns the same. -/
theorem eqG_of_light {front : Nat} {a t : ChainSh} (h : eqGL front a = .ok t) :
    eqG front a = .ok t := by
  unfold eqGL at h
  unfold eqG
  cases h1 : a.tl with
  | none => rw [h1] at h; cases h
  | some tt =>
    cases h2 : a.led with
    | none => rw [h1, h2] at h; cases h
    | some L =>
      cases h3 : a.tables with
      | none => rw [h1, h2, h3] at h; cases h
      | some fs =>
        rw [h1, h2, h3] at h
        dsimp only at h ⊢
        cases h4 : tt.heard with
        | none => rw [h4] at h; cases h
        | some g =>
          rw [h4] at h
          dsimp only at h ⊢
          by_cases hb : allN (L.claims + front) tt fs L 0 = true
          · rw [if_pos hb] at h
            rw [if_pos (allB_of_N hb)]
            exact h
          · rw [if_neg hb] at h
            cases h

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.allB_of_light
#print axioms VerifiableInference.Desc.First.K8.Honest.tableN_eq
#print axioms VerifiableInference.Desc.First.K8.Honest.sortedB_pairwise
#print axioms VerifiableInference.Desc.First.K8.Honest.tileN_some
#print axioms VerifiableInference.Desc.First.K8.Honest.tailLight_of_N
#print axioms VerifiableInference.Desc.First.K8.Honest.allL_of_N
#print axioms VerifiableInference.Desc.First.K8.Honest.allB_of_N
#print axioms VerifiableInference.Desc.First.K8.Honest.eqG_of_light
#print axioms VerifiableInference.Desc.First.K8.Honest.allL
#print axioms VerifiableInference.Desc.First.K8.Honest.tableN
#print axioms VerifiableInference.Desc.First.K8.Honest.ivOf
#print axioms VerifiableInference.Desc.First.K8.Honest.sortedB
#print axioms VerifiableInference.Desc.First.K8.Honest.tileN
#print axioms VerifiableInference.Desc.First.K8.Honest.tailLightN
#print axioms VerifiableInference.Desc.First.K8.Honest.allN
#print axioms VerifiableInference.Desc.First.K8.Honest.eqGL
