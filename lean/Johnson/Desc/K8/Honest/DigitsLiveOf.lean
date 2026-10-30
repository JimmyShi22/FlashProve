-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/DigitsLiveOf.lean: THE SMALLNESS TEST: FROM CONDITIONS ON THE VALUES THAT THE
DIGITS' LOOKUP HAS HEARD, AND A PUBLIC TEST ON ITS TWO CALLS' PIECES, TO `digitsLive`
(Johnson/Desc/K8/Honest/DigitsFew.lean). Definitions with code, statements and proofs. On plain
data: no block, no prover. Lemmas; none of the library's goals.

tl: the smallness test's data; g: what its lookup has heard (tl.heard = some g). ZZ: the digits'
array. A piece of a call is a rectangle of an array that the call's keys fill.
  **`eqOne_ne`**   the index in range, no coordinate of the point with the value 0 or 1: the single
      equality weight does not have the value 0
  `covers R t r i`, **`runsE_sum`**   the value of what a list of runs lays on an entry: the sum,
      over the runs that cover it, of the run's coefficient times its weight there
  `addMul_ents`   an entry of a + k b is one of a's, or stands at the place of one of b's
  `joinPairs tl`, `joinRuns_eq`   the two calls' pieces, each with its call's number; the first
      claim's runs are theirs
  **`digitsCover tl`**   with code, on public numbers (the pieces' array, row, first column and
      number of columns): each entry that `digitsLive` asks is covered by just one piece
  `DigitsGood tl g`   the conditions, by name: the form of the key side's end names no entry of ZZ;
      the two calls' weights are not 0; no coordinate of the two calls' points is 0 or 1; each
      piece's index is in range; each piece's table is at least as long as the piece has columns
  `four8_zero`   the claim on the key side, by its number among the four
  **`digitsLive_of`**   tl.heard = some g, `digitsCover tl` and `DigitsGood tl g`: then `digitsLive
      tl` says yes
By: K9L.four8 (Johnson/Desc/First/Batch/Law/K8Four.lean) · Fo.joinRuns, Fo.joinRun
(OnBytes/Tie/Pv/Lookup/Ends/FoTailJoin.lean) · Fo.eqOne_fold (FoTailKf.lean) · `eqTab_ne`,
`entsE_none`, `liveAt_of_val` (Johnson/Desc/K8/Honest/PlanesLiveOf.lean).
Limits. `DigitsGood` and `digitsCover` are premises: that any state's data meet them is not shown
here. Where two pieces cover one entry nothing is said: their two products are added. Nothing on any
measure.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.PlanesLiveOf
import Johnson.Desc.K8.Honest.DigitsFew
import OnBytes.Tie.Pv.Lookup.Ends.FoTailKf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc

/-- **A single equality weight is not 0.** -/
theorem eqOne_ne (z : Array E) (c : Nat) (hok : eqIndexOK z c = true)
    (h : ∀ w ∈ z.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) :
    Reading.gl.val (eqOne z c) ≠ 0 := by
  have r := Fo.eqOne_fold Reading.gl c z.toList oneE z.size
  rw [Reading.gl.one, one_mul] at r
  have key : Reading.gl.val (eqOne z c) = ∏ t ∈ Finset.range z.toList.length,
      (if c.testBit (z.size - 1 - t) then Reading.gl.val (z.toList.getD t zeroE)
        else 1 - Reading.gl.val (z.toList.getD t zeroE)) := by
    unfold eqOne
    rw [if_pos hok, ← Array.foldl_toList]
    exact r
  rw [key, Finset.prod_ne_zero_iff]
  intro t ht
  have ht' : t < z.toList.length := Finset.mem_range.1 ht
  have hm : z.toList.getD t zeroE ∈ z.toList := by
    rw [List.getD_eq_getElem _ _ ht']
    exact List.getElem_mem ht'
  obtain ⟨h0, h1⟩ := h _ hm
  split
  · exact h0
  · exact sub_ne_zero.2 (Ne.symm h1)

/-- The run covers the entry. -/
def covers (R : Run2) (t r i : Nat) : Bool :=
  decide (R.tree = t ∧ R.row = r ∧ R.first ≤ i ∧ i < R.first + R.n)

/-- **What a list of runs lays on an entry.** -/
theorem runsE_sum : ∀ (l : List Run2) (t r i : Nat),
    Reading.gl.val (runsE l t r i) =
      ((l.filter fun R => covers R t r i).map fun R =>
        Reading.gl.val R.coef * Reading.gl.val (R.w.getD (R.w0 + (i - R.first)) zeroE)).sum
  | [], _, _, _ => Reading.gl.zero
  | R :: l, t, r, i => by
    have ih := runsE_sum l t r i
    unfold runsE at ih ⊢
    rw [List.foldr_cons, List.filter_cons]
    by_cases hc : R.tree = t ∧ R.row = r ∧ R.first ≤ i ∧ i < R.first + R.n
    · rw [if_pos hc, if_pos (by unfold covers; exact decide_eq_true hc), List.map_cons,
        List.sum_cons, Reading.gl.add, Reading.gl.mul, ih]
    · rw [if_neg hc, if_neg (by unfold covers; rw [decide_eq_false hc]; exact Bool.false_ne_true)]
      exact ih

theorem push_ents (k : E) : ∀ (l : List Ent) (acc : Array Ent) (x : Ent),
    x ∈ (l.foldl (fun (a : Array Ent) y => a.push { y with coef := mulE y.coef k }) acc).toList →
      x ∈ acc.toList ∨ ∃ y ∈ l, x.tree = y.tree ∧ x.row = y.row ∧ x.idx = y.idx
  | [], _, _, h => Or.inl h
  | y :: l, acc, x, h => by
    rw [List.foldl_cons] at h
    rcases push_ents k l _ x h with h1 | ⟨z, hz, e⟩
    · rw [Array.toList_push] at h1
      rcases List.mem_append.1 h1 with h2 | h2
      · exact Or.inl h2
      · obtain rfl := List.mem_singleton.1 h2
        exact Or.inr ⟨y, List.mem_cons_self, rfl, rfl, rfl⟩
    · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, e⟩

/-- An entry of a + k b is one of a's, or stands at the place of one of b's. -/
theorem addMul_ents (a b : Aff) (k : E) (x : Ent) (h : x ∈ (Aff.addMul a b k).ents.toList) :
    x ∈ a.ents.toList ∨ ∃ y ∈ b.ents.toList, x.tree = y.tree ∧ x.row = y.row ∧ x.idx = y.idx := by
  have h' : x ∈ (b.ents.foldl (fun (l : Array Ent) y => l.push { y with coef := mulE y.coef k })
      a.ents).toList := h
  rw [← Array.foldl_toList] at h'
  exact push_ents k _ _ x h'

/-- The two calls' pieces, each with its call's number. -/
def joinPairs (tl : HTailF2) : List (Nat × OnBytes.Model.Piece) :=
  [0, 1].flatMap fun q => (tl.zOf q).pieces.toList.map fun p => (q, p)

theorem joinRuns_eq (tl : HTailF2) (g : Forest.Heard) :
    Fo.joinRuns tl g = (joinPairs tl).map fun x => Fo.joinRun tl g x.1 x.2 := by
  unfold Fo.joinRuns joinPairs
  simp [List.map_map, Function.comp_def]

/-- The piece covers the entry. -/
def pieceCovers (p : OnBytes.Model.Piece) (t r i : Nat) : Bool :=
  decide (p.tree = t ∧ p.row = r ∧ p.c0 ≤ i ∧ i < p.c0 + p.Cp)

/-- Just one piece covers the entry. -/
def oneCover (tl : HTailF2) (t r i : Nat) : Bool :=
  ((joinPairs tl).filter fun x => pieceCovers x.2 t r i).length == 1

/-- On public numbers: each entry that `digitsLive` asks is covered by just one piece. -/
def digitsCover (tl : HTailF2) : Bool :=
  (List.range tl.zzBlocks).all fun b => (List.range tl.mz).all fun u =>
    oneCover tl tl.ix.ZZ b u && oneCover tl tl.ix.ZZ (tl.zzBlocks + b) (tl.mz + u)

/-- The conditions on what the lookup has heard, by name. -/
structure DigitsGood (tl : HTailF2) (g : Forest.Heard) : Prop where
  cEndFree : ∀ x ∈ g.cEnd.ents.toList, x.tree ≠ tl.ix.ZZ
  e : ∀ q, q < 2 → Reading.gl.val (g.e.getD q zeroE) ≠ 0
  zk : ∀ q, q < 2 → ∀ w ∈ (g.zk.getD q #[]).toList,
    Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1
  idx : ∀ x ∈ joinPairs tl,
    eqIndexOK ((g.zk.getD x.1 #[]).extract 0 ((tl.zOf x.1).call.n - x.2.b))
      (x.2.off / 2 ^ x.2.b) = true
  wide : ∀ x ∈ joinPairs tl, x.2.Cp ≤ 2 ^ (Fo.joinZc tl g x.1 x.2).size

theorem pair_lt (tl : HTailF2) (x : Nat × OnBytes.Model.Piece) (h : x ∈ joinPairs tl) :
    x.1 < 2 := by
  unfold joinPairs at h
  obtain ⟨q, hq, hx⟩ := List.mem_flatMap.1 h
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact Nat.succ_pos 1
  · exact Nat.lt_succ_self 1

theorem mem_extract (z : Array E) (a b : Nat) (w : E) (h : w ∈ (z.extract a b).toList) :
    w ∈ z.toList := by
  rw [Array.toList_extract] at h
  first
    | exact List.mem_of_mem_take (List.mem_of_mem_drop h)
    | exact List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- One entry under one cover. -/
theorem live_one (tl : HTailF2) (g : Forest.Heard) (G : DigitsGood tl g) (r i : Nat)
    (h : oneCover tl tl.ix.ZZ r i = true) :
    liveAt { form := Aff.ofConst (Fo.joinConst tl g) - g.cEnd,
             runs := (Fo.joinRuns tl g).toArray } tl.ix.ZZ r i = true := by
  refine liveAt_of_val _ _ _ _ ?_
  unfold coefE
  have he : entsE (Aff.ofConst (Fo.joinConst tl g) - g.cEnd).ents.toList tl.ix.ZZ r i = zeroE :=
    entsE_none _ _ _ _ fun x hx hc => by
      rcases addMul_ents _ _ _ x hx with h1 | ⟨y, hy, e1, -, -⟩
      · simp [Aff.ofConst] at h1
      · exact G.cEndFree y hy (e1.symm.trans hc.1)
  rw [Reading.gl.add]
  show Reading.gl.val (entsE (Aff.ofConst (Fo.joinConst tl g) - g.cEnd).ents.toList
      tl.ix.ZZ r i) + Reading.gl.val (runsE (Fo.joinRuns tl g).toArray.toList tl.ix.ZZ r i) ≠ 0
  rw [he, Reading.gl.zero, zero_add, List.toList_toArray, runsE_sum, joinRuns_eq,
    List.filter_map]
  have hf : ((joinPairs tl).filter
      ((fun R => covers R tl.ix.ZZ r i) ∘ fun x => Fo.joinRun tl g x.1 x.2)) =
      (joinPairs tl).filter fun x => pieceCovers x.2 tl.ix.ZZ r i := rfl
  rw [hf]
  unfold oneCover at h
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 (beq_iff_eq.1 h)
  rw [hx]
  have hm : x ∈ (joinPairs tl).filter fun x => pieceCovers x.2 tl.ix.ZZ r i := by
    rw [hx]
    exact List.mem_singleton.2 rfl
  obtain ⟨hp, hc⟩ := List.mem_filter.1 hm
  have hc' : x.2.tree = tl.ix.ZZ ∧ x.2.row = r ∧ x.2.c0 ≤ i ∧ i < x.2.c0 + x.2.Cp :=
    of_decide_eq_true hc
  have hq := pair_lt tl x hp
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  show Reading.gl.val (subE zeroE (mulE (g.e.getD x.1 zeroE)
      (eqOne ((g.zk.getD x.1 #[]).extract 0 ((tl.zOf x.1).call.n - x.2.b))
        (x.2.off / 2 ^ x.2.b)))) *
    Reading.gl.val ((eqTab (Fo.joinZc tl g x.1 x.2)).getD (0 + (i - x.2.c0)) zeroE) ≠ 0
  rw [Reading.gl.sub, Reading.gl.zero, Reading.gl.mul, Nat.zero_add]
  refine mul_ne_zero (sub_ne_zero.2 (Ne.symm (mul_ne_zero (G.e x.1 hq) ?_))) ?_
  · exact eqOne_ne _ _ (G.idx x hp) fun w hw => G.zk x.1 hq w (mem_extract _ _ _ w hw)
  · refine eqTab_ne _ (fun w hw => G.zk x.1 hq w ?_) _
      (Nat.lt_of_lt_of_le (by omega) (G.wide x hp))
    unfold Fo.joinZc at hw
    exact mem_extract _ _ _ w hw

/-- The claim on the key side, by number. -/
theorem four8_zero (tl : HTailF2) (g : Forest.Heard) : (K9L.four8 tl g)[0]? = some
    { form := Aff.ofConst (Fo.joinConst tl g) - g.cEnd,
      runs := (Fo.joinRuns tl g).toArray } := rfl

/-- **The conditions give `digitsLive`.** -/
theorem digitsLive_of (tl : HTailF2) (g : Forest.Heard) (hg : tl.heard = some g)
    (hC : digitsCover tl = true) (G : DigitsGood tl g) : digitsLive tl = true := by
  unfold digitsLive
  rw [hg]
  simp only [digitsCover, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hC
  simp only [List.all_eq_true, List.mem_range]
  intro b hb u hu
  obtain ⟨c1, c2⟩ := hC b hb u hu
  rw [four8_zero, Option.any_some, Bool.and_eq_true]
  exact ⟨live_one tl g G _ _ c1, live_one tl g G _ _ c2⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqOne_ne
#print axioms VerifiableInference.Desc.First.K8.Honest.runsE_sum
#print axioms VerifiableInference.Desc.First.K8.Honest.addMul_ents
#print axioms VerifiableInference.Desc.First.K8.Honest.joinRuns_eq
#print axioms VerifiableInference.Desc.First.K8.Honest.live_one
#print axioms VerifiableInference.Desc.First.K8.Honest.digitsLive_of
