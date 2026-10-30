-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawReadyEnds.lean: THE SMALLNESS TEST: THE THREE READINGS OF
Johnson/Desc/First/K8/LawReadyRow.lean ARE ENOUGH: FROM THEM, AND FIVE FACTS ON THE RECORD THAT WAS
LAID AT THE LINK'S ENTRY, AND THE CLOSED LIST'S SHAPES, THE BLOCK OF THE DRAW SAYS YES.

LawReadyRow.lean names what each block in front of the draw owes: it leaves `Ready.keep` and
`Ready.closedAt`, and no count waits behind it. Readings that were too poor would make that row
idle. Here the row's end is proved:
  `means_of_readings`: s0: the carried record right behind the laying of the smallness test's record
    tl0; s: the carried record in front of the draw. IF `keep` is at s what it was at s0, the mark
    "closed" stands at s, no count waits at s, and tl0 is undrawn (its field for the matrix is
    empty, its count of draws is 0) and has the place's numbers (matrices, columns, combinations),
    AND ITS ROWS, AND THE CLOSED LIST AT s HAS THE PLACE'S SHAPES (a fourth reading, which the
    closing of the list lays: a premise here), THEN at every round r there is a record s' with
    `MeansAtS p s r s'`: all nine clauses.
  `decide_yes_of_readings`: so the decision of the block of the draw says yes at s, on every one
    round. `step_yes_of_readings`: and the step as the fold calls it, on every round that passes the
    frame's test.
  `readings_of_means`: BACK: a yes gives the mark, "no count waits", and `keep`'s five values: so
    the three readings are also no more than the seven clauses ask.
Statements and proofs.
Limits. THAT THE READINGS ARE KEPT BY THE BLOCKS IN FRONT IS NOT SHOWN HERE: it is what each of them
owes (`Ready.LeavesFront`); nor that a fold over such blocks keeps them (the law on folds is
Johnson/Desc/Sound/FoldHeard.lean's `FoldLeaves`). The five facts on tl0 are facts on public numbers
of a plan: none is shown at a value. Of completeness's kind: no error term, nothing on soundness.

-/
import Johnson.Desc.First.K8.LawReadyRow
import Johnson.Desc.First.K8.LawRowsStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes.Model

/-- **The three readings are enough.** -/
theorem means_of_readings (p : Par) (s0 s : S) (tl0 : HTailF2) (h0 : s0.tl? = some tl0)
    (hk : keep s = keep s0) (hc : closedAt s = some true) (hw : s.noneWaits = true)
    (c1 : tl0.cfF.size = 0) (c2 : tl0.foldDrawn = 0) (d : tl0.NM = p.ks.length)
    (e : tl0.mats.toList.map (·.k) = p.ks)
    (e' : tl0.mats.toList.map (·.m) = p.ms) (f : tl0.tau = p.tau)
    (t : ∀ tl, s.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p) (r : Fmt.RoundView) :
    ∃ s', MeansAtS p s r s' := by
  unfold keep at hk
  unfold closedAt at hc
  rw [h0] at hk
  cases ht : s.tl? with
  | none => rw [ht] at hc; simp at hc
  | some tl =>
    rw [ht] at hk hc
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk hc
    obtain ⟨k1, k2, k3, k4, k5⟩ := hk
    refine ⟨_, tl, ht, hc, (nothingOwed_atS s).1 hw, ⟨by rw [k4]; exact c1, by rw [k5]; exact c2⟩,
      by rw [k1]; exact d, by rw [k2]; exact e, by rw [k2]; exact e', by rw [k3]; exact f, t tl ht,
      rfl⟩

/-- So the decision says yes, on every one round. -/
theorem decide_yes_of_readings {Cl : Type} (p : Par) (s0 s : S) (tl0 : HTailF2)
    (h0 : s0.tl? = some tl0) (hk : keep s = keep s0) (hc : closedAt s = some true)
    (hw : s.noneWaits = true) (c1 : tl0.cfF.size = 0) (c2 : tl0.foldDrawn = 0)
    (d : tl0.NM = p.ks.length) (e : tl0.mats.toList.map (·.k) = p.ks)
    (e' : tl0.mats.toList.map (·.m) = p.ms) (f : tl0.tau = p.tau)
    (t : ∀ tl, s.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p)
    (r : Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    ∃ s', (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s [r] gs = .ok s' := by
  obtain ⟨s', h⟩ := means_of_readings p s0 s tl0 h0 hk hc hw c1 c2 d e e' f t r
  exact ⟨s', (decide_atS_iff p s s' r gs).2 h⟩

/-- And the step as the fold calls it, on every round that passes the frame's test. -/
theorem step_yes_of_readings {Cl : Type} (p : Par) (s0 s : S) (tl0 : HTailF2)
    (h0 : s0.tl? = some tl0) (hk : keep s = keep s0) (hc : closedAt s = some true)
    (hw : s.noneWaits = true) (c1 : tl0.cfF.size = 0) (c2 : tl0.foldDrawn = 0)
    (d : tl0.NM = p.ks.length) (e : tl0.mats.toList.map (·.k) = p.ks)
    (e' : tl0.mats.toList.map (·.m) = p.ms) (f : tl0.tau = p.tau)
    (t : ∀ tl, s.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p)
    (ft : Nat) (r : Fmt.RoundView) (cols : List Col) (hf : roundsFit [round p] [r] = true) :
    ∃ s', (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft s [r] cols = .ok (s', 0) := by
  obtain ⟨s', h⟩ := means_of_readings p s0 s tl0 h0 hk hc hw c1 c2 d e e' f t r
  exact ⟨s', (step_atS_iff p ft s s' 0 [r] cols).2 ⟨r, rfl, hf, h, rfl⟩⟩

/-- **Back**: a yes gives the mark, "no count waits", and the five values. -/
theorem readings_of_means (p : Par) (s s' : S) (r : Fmt.RoundView) (h : MeansAtS p s r s') :
    closedAt s = some true ∧ s.noneWaits = true ∧
      ∃ tl, s.tl? = some tl ∧ keep s = some (tl.NM, tl.mats, tl.tau, tl.cfF, tl.foldDrawn) ∧
        tl.cfF.size = 0 ∧ tl.foldDrawn = 0 ∧ tl.NM = p.ks.length ∧
        tl.mats.toList.map (·.k) = p.ks ∧ tl.tau = p.tau := by
  obtain ⟨tl, ht, ha, hb, ⟨hc1, hc2⟩, hd, he, _, hf, _⟩ := h
  refine ⟨?_, (nothingOwed_atS s).2 hb, tl, ht, ?_, hc1, hc2, hd, he, hf⟩
  · unfold closedAt
    rw [ht, Option.map_some, ha]
  · unfold keep
    rw [ht, Option.map_some]

end VerifiableInference.Desc.First.K8.Ready

#print axioms VerifiableInference.Desc.First.K8.Ready.means_of_readings
#print axioms VerifiableInference.Desc.First.K8.Ready.decide_yes_of_readings
#print axioms VerifiableInference.Desc.First.K8.Ready.step_yes_of_readings
#print axioms VerifiableInference.Desc.First.K8.Ready.readings_of_means
