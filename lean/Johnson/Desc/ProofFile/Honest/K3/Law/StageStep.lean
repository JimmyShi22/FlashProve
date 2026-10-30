-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/StageStep.lean: the honest side of the kind "lookup" (K3).
Proofs of the two steps of Honest/K3/Law/Statements.lean, for all numbers of the lookup. Both are
conditional on `HB`; and what each says of a row's worth is conditional on the stage's summand
summing as it should. Theorems, with one structure.

Terms. Honest/K3/GLOSSARY.md ("course", "ledger", "stage", "world, worth").

What is shown.
  `stageStep : HB → StageStep`: the step at a stage with end values.
  `leavesStep : HB → LeavesStep`: the step at the leaves, whose row is made late.
On the way: `AtN`, `atN`, `ready_stage`: what stands ready at the stage number n. `endTerm_congr`,
`shown_getD`, `rd_mul`, `rd_sub`: end terms and shown values, as read. `slotsIn_succ`, `sumTake_le`,
`slotsIn_le`, `tail_pos`, `padTo_zero`, `padTo_succ_nil`, `padTo_succ_cons`: counts and lists.

Hypotheses that remain.
  `HB` (Honest/K3/Law/SumWhole.lean): five statements of the law of the masked sumcheck's honest
    part. They are proved in Honest/SumLaw/Law.lean and Honest/SumLaw/LawEnds.lean, not here;
    Honest/K3/Law/HBPaid.lean brings these proofs in.
  What each theorem says of a row's worth is conditional, besides, on the stage's summand summing as
    it should.
  `B` is `HB`'s name. On the way: `hF`, `hn`, `hI`, `hc`: (in `ready_stage`) `Fit R`; s is the stage
    number n; the invariant in front of it; its call is k. `h`, `ht`: a stage's number; two planes
    at least; the stage has an end value. `h0`, `h1`, `h`: elements, or end values, are read alike.

Users. This file is imported by Honest/K3/Good/Step.lean, Honest/K3/Law/Agree.lean and
Honest/K3/Law/LookOne.lean.

Limits. Lemmas about one kind's honest part, played alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.StageFacts
import Johnson.Desc.ProofFile.Honest.K3.Law.SumWhole
import OnBytes.Tie.Pv.Psc.PscRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE addE subE mulE isZeroE)
open OnBytes.Model (Reading Aff Fork)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Sized Filled Later filled_lt)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call shapeOk ownSlots LedgerReady)
open ProofFile.Honest.SumLaw (alone)

variable {W : Type}

/-! ## Counts -/

theorem slotsIn_succ {f : LFace} {n : Nat} {s : Stage} (h : (stages f)[n]? = some s) :
    slotsIn f (n + 1) = slotsIn f n + s.slots f := by
  simp [slotsIn, take_succ_get h]

theorem sumTake_le : ∀ (l : List Nat) (n : Nat), (l.take n).sum ≤ l.sum
  | _, 0 => by simp
  | [], _ + 1 => by simp
  | a :: l, n + 1 => by
    simp only [List.take_succ_cons, List.sum_cons]
    have := sumTake_le l n
    omega

theorem slotsIn_le {f : LFace} (h : 2 ≤ f.planes) (n : Nat) : slotsIn f n ≤ f.slots := by
  rw [← slots_stages f h]
  unfold slotsIn
  rw [List.map_take]
  exact sumTake_le _ n

theorem tail_pos {f : LFace} {s : Stage} (h : 0 < s.tail f) :
    ∃ k e, s.call f = some k ∧ k.ends = some e ∧ e.n = s.tail f := by
  unfold Stage.tail at h ⊢
  cases hc : s.call f with
  | none => simp [hc] at h
  | some k =>
    cases he : k.ends with
    | none => simp [hc, he] at h
    | some e => exact ⟨k, e, rfl, he, by simp [he]⟩

/-! ## The shown end values -/

theorem padTo_zero (a : List E) : padTo 0 a = [] := by simp [padTo]

theorem padTo_succ_nil (n : Nat) : padTo (n + 1) [] = zeroE :: padTo n [] := by
  simp [padTo, List.replicate_succ]

theorem padTo_succ_cons (n : Nat) (x : E) (a : List E) : padTo (n + 1) (x :: a) = x :: padTo n a :=
    by
  simp [padTo]

/-- A shown end value, as read. -/
theorem shown_getD (β : E) : ∀ (n : Nat) (a m : List E) (j : Nat), j < n →
    rd ((addL (padTo n a) (scaleL β (padTo n m))).getD j zeroE) =
      rd (a.getD j zeroE) + rd β * rd (m.getD j zeroE)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], [], 0, _ => by
    simp [padTo_succ_nil, scaleL, addL, Reading.gl.add, Reading.gl.mul]
  | n + 1, x :: a, [], 0, _ => by
    simp [padTo_succ_nil, padTo_succ_cons, scaleL, addL, Reading.gl.add, Reading.gl.mul]
  | n + 1, [], y :: m, 0, _ => by
    simp [padTo_succ_nil, padTo_succ_cons, scaleL, addL, Reading.gl.add, Reading.gl.mul]
  | n + 1, x :: a, y :: m, 0, _ => by
    simp [padTo_succ_cons, scaleL, addL, Reading.gl.add, Reading.gl.mul]
  | n + 1, [], [], j + 1, h => by
    have := shown_getD β n [] [] j (by omega)
    simpa [padTo_succ_nil, scaleL, addL] using this
  | n + 1, x :: a, [], j + 1, h => by
    have := shown_getD β n a [] j (by omega)
    simpa [padTo_succ_nil, padTo_succ_cons, scaleL, addL] using this
  | n + 1, [], y :: m, j + 1, h => by
    have := shown_getD β n [] m j (by omega)
    simpa [padTo_succ_nil, padTo_succ_cons, scaleL, addL] using this
  | n + 1, x :: a, y :: m, j + 1, h => by
    have := shown_getD β n a m j (by omega)
    simpa [padTo_succ_cons, scaleL, addL] using this

theorem rd_mul {x y x' y' : E} (h0 : rd x = rd x') (h1 : rd y = rd y') :
    rd (mulE x y) = rd (mulE x' y') :=
  (Reading.gl.mul x y).trans ((congrArg₂ (· * ·) h0 h1).trans (Reading.gl.mul x' y').symm)

theorem rd_sub {x y x' y' : E} (h0 : rd x = rd x') (h1 : rd y = rd y') :
    rd (subE x y) = rd (subE x' y') :=
  (Reading.gl.sub x y).trans ((congrArg₂ (· - ·) h0 h1).trans (Reading.gl.sub x' y').symm)

/-- The verifier's end term reads as many values as the stage has end values, and it is read alike
on lists that are read alike. -/
theorem endTerm_congr (f : LFace) (a : E) (u v : List E) (s : Stage) (ht : 0 < s.tail f)
    (h : ∀ j, j < s.tail f → rd (u.getD j zeroE) = rd (v.getD j zeroE)) :
    rd (endTerm a s u) = rd (endTerm a s v) := by
  cases s with
  | tie n =>
    cases n with
    | zero =>
      exact rd_sub (h 0 (show 0 < 3 by omega))
        (rd_mul rfl (rd_mul (rd_mul (h 1 (show 1 < 3 by omega)) (h 1 (show 1 < 3 by omega)))
          (h 2 (show 2 < 3 by omega))))
    | succ n =>
      exact rd_mul (rd_mul (h 0 (show 0 < 2 by omega)) (h 0 (show 0 < 2 by omega)))
        (h 1 (show 1 < 2 by omega))
  | bits =>
    exact rd_sub (rd_mul (h 0 (show 0 < 1 by omega)) (h 0 (show 0 < 1 by omega)))
      (h 0 (show 0 < 1 by omega))
  | split _ => exact rd_mul (h 0 (show 0 < 2 by omega)) (h 1 (show 1 < 2 by omega))
  | key _ _ => exact rd_mul (h 0 (show 0 < 2 by omega)) (h 1 (show 1 < 2 by omega))
  | tab _ => exact rd_mul (h 0 (show 0 < 2 by omega)) (h 1 (show 1 < 2 by omega))
  | shift => exact absurd ht (Nat.lt_irrefl 0)
  | alpha => exact absurd ht (Nat.lt_irrefl 0)
  | join => exact absurd ht (Nat.lt_irrefl 0)
  | keyLine _ _ => exact absurd ht (Nat.lt_irrefl 0)
  | tabLine _ => exact absurd ht (Nat.lt_irrefl 0)
  | leaves => exact absurd ht (Nat.lt_irrefl 0)
  | zero => exact absurd ht (Nat.lt_irrefl 0)

/-! ## The ledger in front of a stage is ready for its call -/

/-- What is known of a stage that stands at number n of the row. -/
structure AtN (R : Course W) (n : Nat) (s : Stage) : Prop where
  mem : s ∈ stages R.f
  idx : indexOf R.f s = n
  slot : firstSlot R.f s = slotsIn R.f n

theorem atN {R : Course W} {n : Nat} {s : Stage} (h : (stages R.f)[n]? = some s) : AtN R n s := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 h
  subst hget
  exact ⟨List.getElem_mem hlt, indexOf_getElem R.f n hlt, firstSlot_getElem R.f n hlt⟩

theorem ready_stage {R : Course W} {n : Nat} {s : Stage} {F : Fork} {k : Call} (hF : Fit R)
    (hn : (stages R.f)[n]? = some s) (hI : Inv R n F) (hc : s.call R.f = some k) :
    LedgerReady (R.form s) (R.call s) F := by
  have A := atN hn
  have hown := call_own R hc (lead_zero s k hc)
  have hen : (R.call s).endsN = s.tail R.f := by
    have e1 : (R.call s).ends = k.ends := by rw [call_ends, shapeAt_of hc]
    unfold Call.endsN Stage.tail
    rw [e1, hc]
    simp only [Option.bind_some]
    cases k.ends <;> rfl
  have hb : slotsIn R.f n + s.slots R.f ≤ R.f.slots := by
    rw [← slotsIn_succ hn]
    exact slotsIn_le (two_le_planes_of_ok R.f hF.ok) _
  have hsl : s.slots R.f = s.own R.f + s.tail R.f := rfl
  have hnx := hI.next
  have hrm := hI.room
  refine ⟨hI.sized, ?_, ?_, ?_⟩
  · exact form_slots R (fun j => j < F.ns ∧ Filled F j) hF.ok s A.mem (fun s' hs' hf j hj =>
      have hfil := hI.filled s' (by rw [← A.idx]; exact front_of hs' hf) j hj
      ⟨filled_lt hI.sized.2.2 hfil, hfil⟩)
  · rw [hown, hen]
    omega
  · intro j h1 h2
    rw [hown, hen] at h2
    exact hI.free j h1 (by omega)

/-! ## The step at a stage with end values -/

/-- **Conditional on `HB`: the step at a stage with end values** (the statement `StageStep`), for
all numbers of the lookup. What it says of the row's worth is conditional, besides, on the stage's
summand summing as it should. -/
theorem stageStep (B : HB) : StageStep := by
  intro W R n s F seen x hF hn ht hI hx
  have A := atN hn
  obtain ⟨k, e, hc, he, hen⟩ := tail_pos ht
  have hown : ownSlots ((R.job s).callAt (R.stateAt s).input
      (SumLaw.frontOf (R.stateAt s) seen)).all = s.own R.f := call_own R hc (lead_zero s k hc)
  have hJe : (R.job s).shape.ends = some e := by
    show (shapeAt R.a s).ends = some e
    rw [shapeAt_of hc, he]
  have hx' : alone (sumPart (V := Unit) (sumName R.a.place (indexOf R.f s))
      (endName R.a.place (indexOf R.f s)) (R.job s)) (R.c s) (R.stateAt s) seen (R.draws s) =
      some x := by
    unfold Course.stage at hx
    rw [hc] at hx
    exact hx
  obtain ⟨h, f, G, hw, H⟩ := whole_hon (V := Unit) B (R.job s) (R.c s) (R.stateAt s) seen x
    (R.draws s) (R.form s) F (fun _ v => endTerm R.factor s v) e hJe (shapeOk_stage R hF.ok hc)
    (drawsOk_stage hF A.mem hc) hx' (ready_stage hF hn hI hc)
  have hr : h.r = R.r s := H.r
  have hnx := hI.next
  have hsE : h.sEnd = R.endSlot s := by
    have := H.sEnd
    unfold Course.endSlot
    rw [A.slot, ← hown]
    omega
  have htk := take_succ_get hn
  have hsl : s.slots R.f = s.own R.f + s.tail R.f := rfl
  refine ⟨h, f, G, hw, hr, by rw [hr]; exact beta_ne hF A.mem hc he, hsE, ?_, ?_⟩
  · refine ⟨H.later.sized hI.sized, ?_, by rw [H.later.ns]; exact hI.room, ?_, ?_, ?_⟩
    · have := H.next
      rw [slotsIn_succ hn, hsl, ← hown, ← hen]
      omega
    · intro j h1 h2 hf
      exact hI.free j (Nat.le_trans H.later.next h1) h2 (H.above j h1 hf)
    · intro s' hs' j hj
      rw [htk] at hs'
      rcases List.mem_append.1 hs' with h' | h'
      · exact (H.later.keep _ (hI.filled s' h' j hj)).1
      · obtain rfl : s' = s := by simpa using h'
        rw [← hsE]
        exact H.filled j (by omega)
    · intro H' mask entry hl hM s' hs' j hj
      rw [htk] at hs'
      rcases List.mem_append.1 hs' with h' | h'
      · exact hI.ends H' mask entry (H.later.trans hl) hM s' h' j hj
      · obtain rfl : s' = s := by simpa using h'
        rw [← hsE]
        exact H.ends H' mask entry hl j (by omega) (by rw [hsE]; exact (hM s' A.mem).2 j hj)
  · intro hsum H' mask entry hl hM
    obtain ⟨sh, hsh, hrow⟩ := H.row
    have hC : (R.form s).value Reading.gl (H'.worldOf Reading.gl mask entry) = rd (R.claimed s) :=
      formWorth W R _ s hF.ok (Or.inl A.mem) (fun s' hs' j hj =>
        hI.ends H' mask entry (H.later.trans hl) hM s' (by rw [← A.idx]; exact hs') j hj)
    have hval := hrow H' mask entry (rd (endTerm R.factor s (R.shown s))) hl
      (fun i hi => by
        have := (hM s A.mem).1 i (by rw [← hown]; exact hi)
        rw [hnx, ← A.slot]
        exact this)
      (by rw [hC, hr]; exact hsum)
    rw [hval]
    have hcg : rd (endTerm R.factor s sh) = rd (endTerm R.factor s (R.shown s)) :=
      endTerm_congr R.f R.factor sh (R.shown s) s ht (fun j hj =>
        (hsh j (by omega)).trans (by
          rw [hr]
          exact (shown_getD (R.beta s) (s.tail R.f) (R.ends s) (R.masks s) j hj).symm))
    show rd h.eps * (rd (endTerm R.factor s sh) - rd (endTerm R.factor s (R.shown s))) = 0
    rw [hcg, sub_self, mul_zero]

/-! ## The step at the leaves -/

/-- **Conditional on `HB`: the step at the leaves** (the statement `LeavesStep`), for all numbers of
the lookup. What it says of the late row's worth is conditional, besides, on the leaves' summand
summing to cf. -/
theorem leavesStep (B : HB) : LeavesStep := by
  intro W R n F seen x hF hn hI hx
  have A := atN hn
  have hc : Stage.call R.f .leaves =
      some { lead := 0, vs := VerifiableInference.Desc.K3.leafVars R.f #[], ends := none } := rfl
  have hown : ownSlots ((R.job .leaves).callAt (R.stateAt .leaves).input
      (SumLaw.frontOf (R.stateAt .leaves) seen)).all = Stage.own R.f .leaves := call_own R hc rfl
  have hJe : (R.job .leaves).shape.ends = none := rfl
  have hx' : alone (sumPart (V := Unit) (sumName R.a.place (indexOf R.f .leaves))
      (endName R.a.place (indexOf R.f .leaves)) (R.job .leaves)) (R.c .leaves) (R.stateAt .leaves)
      seen (R.draws .leaves) = some x := hx
  obtain ⟨h, G, hh, O⟩ := open_hon (V := Unit) B (R.job .leaves) (R.c .leaves) (R.stateAt .leaves)
    seen x (R.draws .leaves) (R.form .leaves) F hJe (shapeOk_stage R hF.ok hc)
    (drawsOk_stage hF A.mem hc) hx' (ready_stage hF hn hI hc)
  have hnx := hI.next
  have htk := take_succ_get hn
  have ht0 : Stage.tail R.f .leaves = 0 := rfl
  have hsl : Stage.slots R.f .leaves = Stage.own R.f .leaves + 0 := rfl
  have hb : slotsIn R.f n + Stage.slots R.f .leaves ≤ R.f.slots := by
    rw [← slotsIn_succ hn]
    exact slotsIn_le (two_le_planes_of_ok R.f hF.ok) _
  have hfirst : h.first = R.first + firstSlot R.f .leaves := by
    rw [O.first, hnx, A.slot]
  refine ⟨h, G, hh, O.r, hfirst, ?_, ?_, ?_⟩
  · refine ⟨O.later.sized hI.sized, ?_, by rw [O.later.ns]; exact hI.room, ?_, ?_, ?_⟩
    · have := O.next
      rw [slotsIn_succ hn, hsl, ← hown]
      omega
    · intro j h1 h2 hf
      exact hI.free j (Nat.le_trans O.later.next h1) h2 ((O.same j).1 hf)
    · intro s' hs' j hj
      rw [htk] at hs'
      rcases List.mem_append.1 hs' with h' | h'
      · exact (O.later.keep _ (hI.filled s' h' j hj)).1
      · obtain rfl : s' = .leaves := by simpa using h'
        omega
    · intro H' mask entry hl hM s' hs' j hj
      rw [htk] at hs'
      rcases List.mem_append.1 hs' with h' | h'
      · exact hI.ends H' mask entry (O.later.trans hl) hM s' h' j hj
      · obtain rfl : s' = .leaves := by simpa using h'
        omega
  · intro j h1 h2 hf
    rw [hfirst, A.slot] at h1 h2
    exact hI.free j (by omega) (by omega) ((O.same j).1 hf)
  · intro cf hsum F' G' H' y mask entry hS' hGF hr hl hM
    have hlater : Later F H' := O.later.trans (hGF.trans ((MaskedSum.row_keeps hr).trans hl))
    have hC : (R.form .leaves).value Reading.gl (H'.worldOf Reading.gl mask entry) =
        rd (R.claimed .leaves) :=
      formWorth W R _ .leaves hF.ok (Or.inl A.mem) (fun s' hs' j hj =>
        hI.ends H' mask entry hlater hM s' (by rw [← A.idx]; exact hs') j hj)
    have hval := O.row F' G' H' y oneE mask entry cf hS' hr hl
      (fun i hi => by
        have := (hM .leaves A.mem).1 i (by rw [← hown]; exact hi)
        rw [hnx, ← A.slot]
        exact this)
      (by rw [hC, O.r]; exact hsum)
    rw [hval, Reading.gl.one]

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.slotsIn_succ
#print axioms ProofFile.Honest.K3.Law.sumTake_le
#print axioms ProofFile.Honest.K3.Law.slotsIn_le
#print axioms ProofFile.Honest.K3.Law.tail_pos
#print axioms ProofFile.Honest.K3.Law.padTo_zero
#print axioms ProofFile.Honest.K3.Law.padTo_succ_nil
#print axioms ProofFile.Honest.K3.Law.padTo_succ_cons
#print axioms ProofFile.Honest.K3.Law.shown_getD
#print axioms ProofFile.Honest.K3.Law.rd_mul
#print axioms ProofFile.Honest.K3.Law.rd_sub
#print axioms ProofFile.Honest.K3.Law.endTerm_congr
#print axioms ProofFile.Honest.K3.Law.atN
#print axioms ProofFile.Honest.K3.Law.ready_stage
#print axioms ProofFile.Honest.K3.Law.stageStep
#print axioms ProofFile.Honest.K3.Law.leavesStep
