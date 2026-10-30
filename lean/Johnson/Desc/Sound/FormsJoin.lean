-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FormsJoin.lean: THE JOIN OF THE TWO WORLDS OF Johnson/Desc/Sound/FormsQ.lean: A
FORM THAT A RUN's READER GIVES AT AN EARLIER RECORD IS WORTH, IN THE WORLD OF THE ARRAYS' OWN ROWS
WITH THE READER's LATE SLOTS, WHAT IT IS WORTH IN THE LEDGER's OWN WORLD AT A LATER RECORD AT WHICH
THE ONE SUM IS TAKEN. Five theorems.

What is said. a: the segment's part at the earlier record. b: at the later one (behind the runs
behind the batching: the slots are filled, the virtual rows have their weights). D: any data.
  `entry_join`: at an entry that meets `K9.oneWeight` at b's ledger (row 0 of an array of one own
    row, whose one weight is 1) the ledger's world (kind K9's `entryAt`: the weights applied to the
    array's rows) has the array's own cell.
  `slot_join`: at a slot that is there at a (`slotIn`: late, or filled) and filled at b, where the
    late slots hold at b just what the reader says (`lateOk`) and what lay under a filled slot at a
    has stayed: the forms' world at a has under it what b's ledger has.
  `value_join`: so a form's worth is one in both.
  `vals_join`: the list of the worths of the forms as PLAIN CLAIMS (no runs of entries) in kind K9's
    world at b is the list of their worths in the forms' world at a: A FUNCTION OF THE EARLIER
    RECORD AND THE DATA ALONE: the shape that kind K9's premise on a run of plain claims asks
    (`vals`, in its law file PlainRuns.lean; that file is not imported here).
  `formsQ_of_worths`: AT THE TWO SENTENCES' OWN DATA: where every form that the reader gives at the
    earlier record s is worth 0 in the ledger's own world at the later record s', at the witness's
    tables as read THERE, the sentence "forms" holds at s, at the witness's tables as read at s.
Limits: (1) Premises, not facts of a block: that b's part rides on a's, that the late slots hold at
b what the reader says, that the named slots are filled at b, that the weight is 1: the last three
are public tests (`lateOk`, `K9.joinIn`). (2) Nothing on a claim with runs of entries or an index of
equations. (3) Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.Batch.OneWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (segAt? lateAt lateOk slotIn affIn oneWeight joinIn Read Readers
  formsIn)

section
variable (own : List (ℕ × ℕ))

/-- At such an entry the weights applied to the array's rows give the array's own cell. -/
theorem entry_join (arrayOf : Array (ℕ × String)) (F : Fork) (D : Bound GQ) (x : Ent)
    (c : ℕ × String) (hc : arrayOf[x.tree]? = some c) (h : oneWeight F x = true) :
    entryAt Reading.gl arrayOf (treesFrame F.trees) D x.tree x.row x.idx =
      D.cell c.1 c.2 x.row x.idx := by
  unfold oneWeight at h
  cases hT : F.trees[x.tree]? with
  | none =>
    rw [hT] at h
    exact nomatch h
  | some T =>
    rw [hT] at h
    cases hr : T.rows[0]? with
    | none =>
      simp only [hr] at h
      exact nomatch h
    | some r =>
      simp only [hr] at h
      obtain ⟨h1, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
      obtain ⟨h2, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h
      have e1 : T.R = 1 := of_decide_eq_true h1
      have e2 : x.row = 0 := of_decide_eq_true h2
      have e3 : r.coef.getD 0 zeroE = oneE := of_decide_eq_true h3
      have f1 : (treesFrame F.trees).getD x.tree default = T.frame := by
        simp [treesFrame, Array.getD_eq_getD_getElem?, hT]
      have f2 : T.frame.2.getD 0 default = r.frame := by
        simp [HTree.frame, Array.getD_eq_getD_getElem?, hr]
      have f3 : arrayOf.getD x.tree (0, "") = c := by
        simp [Array.getD_eq_getD_getElem?, hc]
      unfold entryAt
      rw [f1, f3, e2, f2]
      have f4 : T.frame.1.R = 1 := e1
      rw [f4, Finset.sum_range_one]
      have f5 : r.frame.1.coef = r.coef := rfl
      rw [f5, e3, Reading.gl.one, one_mul]

/-- At a slot that is there at a and filled at b. -/
theorem slot_join (free : Option ℕ) (late : List (ℕ × E × E)) (a b : K9.Part)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (hl : lateOk late b = true) (m : ℕ → GQ) (j : ℕ) (hin : slotIn own free late a j = true)
    (hg : b.F.gotF.getD j false = true) :
    Reading.gl.val (b.F.vp.getD j zeroE) - Reading.gl.val (b.F.mf.getD j zeroE) * m j =
      slotW a.F late m j := by
  rw [← slot_rides own free late a b hfill m m j hin rfl]
  exact (slotW_filled b late m j hl hg).symm

/-- **A form's worth is one in both worlds.** -/
theorem value_join (free : Option ℕ) (late : List (ℕ × E × E)) (a b : K9.Part) (D : Bound GQ)
    (harr : b.L.arrayOf = a.L.arrayOf)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (hl : lateOk late b = true) (f : Aff) (hin : affIn own free late a f = true)
    (hj : joinIn b.F f = true) :
    f.value Reading.gl (worldSum b D) = f.value Reading.gl (worldOwn a late D) := by
  unfold affIn at hin
  obtain ⟨i1, i2⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  unfold joinIn at hj
  obtain ⟨j1, j2⟩ := Eq.mp (Bool.and_eq_true _ _) hj
  refine value_eq _ _ f (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨A, hA⟩ := K9.entIn_some own a x (List.all_eq_true.1 i1 x hx)
    obtain ⟨c, _, _, hc, _, _, _⟩ := K9.arrayIn_some own a x.tree A hA
    show entryAt Reading.gl b.L.arrayOf (treesFrame b.F.trees) D x.tree x.row x.idx =
      (match a.L.arrayOf[x.tree]? with
        | some c => D.cell c.1 c.2 x.row x.idx
        | none => 0)
    rw [hc, harr]
    exact entry_join a.L.arrayOf b.F D x c hc (List.all_eq_true.1 j1 x hx)
  · exact slot_join own free late a b hfill hl D.mask x.1 (List.all_eq_true.1 i2 x hx)
      (List.all_eq_true.1 j2 x hx)

/-- **The worths of the forms as plain claims, at the later ledger, are a function of the earlier
record and the data.** -/
theorem vals_join (free : Option ℕ) (late : List (ℕ × E × E)) (a b : K9.Part) (D : Bound GQ)
    (harr : b.L.arrayOf = a.L.arrayOf)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (hl : lateOk late b = true) (fs : List Aff)
    (hin : ∀ f ∈ fs, affIn own free late a f = true) (hj : ∀ f ∈ fs, joinIn b.F f = true) :
    (fs.map fun f => claimValue Reading.gl (worldAt Reading.gl b.L b.F D) { form := f }) =
      fs.map fun f => f.value Reading.gl (worldOwn a late D) := by
  refine List.map_congr_left fun f hf => ?_
  have h := value_join own free late a b D harr hfill hl f (hin f hf) (hj f hf)
  unfold claimValue
  simpa [worldSum] using h

/-- **From the claims' worths at the later record to the sentence at the earlier one.** -/
theorem formsQ_of_worths (Rd : Readers) (piece : ℕ) (run : String) (s : S) (a b : K9.Part)
    (rd : ℕ × ℕ → MsgQ) (ha : segAt? s = some a) (R : Read)
    (hs : Rd.forms piece run s = some R) (hin : formsIn Rd own piece run s = true)
    (hr : Rides own a b) (hl : lateOk R.late b = true)
    (hj : ∀ f ∈ R.forms, joinIn b.F f = true)
    (h0 : ∀ f ∈ R.forms, f.value Reading.gl (worldSum b (dataQ own b rd)) = 0) :
    formsQ Rd own piece run s rd := by
  unfold formsIn at hin
  rw [ha, hs] at hin
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  refine ⟨a, R, ha, hs, hlate, fun f hm => ?_⟩
  have hi : affIn own (K9.mergeOf s) R.late a f = true := List.all_eq_true.1 hall f hm
  refine ⟨hi, ?_⟩
  have h1 := value_join own (K9.mergeOf s) R.late a b (dataQ own b rd) hr.arrays hr.filled hl f hi
    (hj f hm)
  have h2 := hi
  unfold affIn at h2
  obtain ⟨i1, i2⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  have h3 : f.value Reading.gl (worldOwn a R.late (dataQ own b rd)) =
      f.value Reading.gl (worldOwn a R.late (dataQ own a rd)) := by
    refine value_ridesW own (K9.mergeOf s) R.late a a _ _ rfl (fun _ _ _ => ⟨rfl, rfl⟩) f
      (List.all_eq_true.1 i2) (fun x hx c hc => ?_) (fun x hx => ?_)
    · obtain ⟨A, hA⟩ := K9.entIn_some own a x (List.all_eq_true.1 i1 x hx)
      obtain ⟨c', o, y, hc', hq, ho, hy⟩ := K9.arrayIn_some own a x.tree A hA
      obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
      exact cell_rides own a b rd hr c' A o y hq ho hy x.row x.idx
    · obtain ⟨y, hy⟩ := slotIn_mask own (K9.mergeOf s) R.late a x.1 (List.all_eq_true.1 i2 x hx)
      exact mask_rides own a b rd hr y hy x.1
  rw [← h3, ← h1]
  exact h0 f hm

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.formsQ_of_worths
#print axioms VerifiableInference.Desc.Sound.entry_join
#print axioms VerifiableInference.Desc.Sound.slot_join
#print axioms VerifiableInference.Desc.Sound.value_join
#print axioms VerifiableInference.Desc.Sound.vals_join
