-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeHeard.lean: the closing of a segment (K10): the job's test `heardAll`
(Honest/K10/SeatLot.lean) passes at a list of challenges that fits a list of declared rounds, where each fold's challenge in
front stands among these rounds and draws an element.

  `drawn_at`        a list of challenges that fits declared rounds has, at each declared number, a challenge that fits
  `heard_of_fit`    so `heardAll` passes

Limits. That the numbers stand among the rounds is a premise here.
-/
import Johnson.Desc.ProofFile.Honest.K10.SeatLot
import Johnson.Desc.ProofFile.Honest.K2.Law.Room

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open ProofFile.Honest.K2 (SegmentPub challengesAt)

/-- A list of challenges that fits declared rounds has, at each declared number, a challenge that fits. -/
theorem drawn_at : ∀ {ds : List Fmt.DeclaredRound} {hs : List Fmt.Drawn} {i : Nat} {d : Fmt.DeclaredRound},
    drawsFit ds hs = true → ds[i]? = some d → ∃ R, hs[i]? = some R ∧ drawFit d R = true
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, h, _ => by simp [drawsFit] at h
  | x :: ds, R :: hs, 0, d, h, e => by
    have h' : (drawFit x R && drawsFit ds hs) = true := h
    obtain ⟨a, -⟩ := Bool.and_eq_true _ _ ▸ h'
    obtain rfl : x = d := by simpa using e
    exact ⟨R, rfl, a⟩
  | x :: ds, R :: hs, i + 1, d, h, e => by
    have h' : (drawFit x R && drawsFit ds hs) = true := h
    obtain ⟨-, b⟩ := Bool.and_eq_true _ _ ▸ h'
    have e' : ds[i]? = some d := by simpa using e
    obtain ⟨R', h1, h2⟩ := drawn_at b e'
    exact ⟨R', by simpa using h1, h2⟩

/-- **`heardAll` passes where each fold's challenge in front stands among the declared rounds and draws an element.** -/
theorem heard_of_fit {ds : List Fmt.DeclaredRound} {hs : List Fmt.Drawn} (h : drawsFit ds hs = true)
    {segs : List SegmentPub}
    (hn : ∀ S ∈ segs.dropLast, ∀ i ∈ S.gamma, ∃ d, ds[i]? = some d ∧ 0 < d.entry.drawE) :
    heardAll segs hs = .ok () := by
  have one : ∀ S ∈ segs.dropLast, ∃ b, challengesAt hs S.gamma = .ok b := by
    intro S hS
    refine ProofFile.Honest.K2.Reads.mapM_of_all _ _ fun i hi => ?_
    obtain ⟨d, hd, p⟩ := hn S hS i hi
    obtain ⟨R, hR, hf⟩ := drawn_at h hd
    have hl : R.elems.length = d.entry.drawE := by
      unfold drawFit at hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hf
      exact hf.1.1.1.1.1.1.1
    obtain ⟨x, xs, ex⟩ : ∃ x xs, R.elems = x :: xs := by
      cases e : R.elems with
      | nil =>
        rw [e] at hl
        simp at hl
        omega
      | cons x xs => exact ⟨x, xs, rfl⟩
    refine ⟨OnBytes.Slice.toE x, ?_⟩
    have e2 : (hs.drop i).head? = some R := by
      rw [List.head?_drop]
      exact hR
    simp only [e2, Option.bind_some, ex, List.head?_cons]
  obtain ⟨r, hr⟩ := ProofFile.Honest.K2.Reads.mapM_of_all (fun S : SegmentPub => challengesAt hs S.gamma) _ one
  unfold heardAll
  rw [hr]
  rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.drawn_at
#print axioms ProofFile.Honest.K10.heard_of_fit
