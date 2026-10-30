-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Filled6.lean: THE HEAD's SUMCHECK FILLS ITS OWN NUMBERS, AND A LATER LEDGER KEEPS THEM (for
K06_law: the claims judged at any ledger G with `Later F1 G`,
OnBytes/Tie/Pv/Psc/PscLater.lean). `sum_runs`: a return of the sumcheck is three runs of layings.
`filled_range`: behind them every number from the claimed sum's to the second end value's is filled
(hideRun_ok). `hidden_later`: the hidden scalar under a filled number is read alike at every
later ledger.
-/
import Mathlib
import OnBytes.Tie.Pv.Psc.PscLater
import Johnson.Desc.Kinds.Law.Lemma2b

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Aff Fork Reading World)
open OnBytes.PscRun (Later Sized hideRun_ok)
open Norm (lt ls d lPd T S2)
open Part.MaskedSum (Var Sent readAll leadScalars rowLaid)

/-- The two defaults are read alike. -/
theorem rd_getD0 (a : Array E) (j : Nat) : rd (a.getD j (0 : E)) = rd (a.getD j zeroE) := by
  by_cases h : j < a.size
  · simp [Array.getD, h]
  · simp only [Array.getD, h, dif_neg, not_false_eq_true]
    rw [rd_zero]
    exact Reading.gl.zero.symm

/-- The hidden scalar under a filled number is read alike at every later ledger. -/
theorem hidden_later {F G : Fork} (mask : Nat → E) {j : Nat} (hL : Later F G)
    (hf : OnBytes.PscRun.Filled F j) :
    rd (hidden G mask j) = rd (hidden F mask j) := by
  obtain ⟨_, h1, h2⟩ := hL.keep j hf
  unfold hidden
  rw [rd_sub, rd_sub, rd_mul, rd_mul, rd_getD0, rd_getD0, rd_getD0, rd_getD0, h1, h2]

theorem sized_of {F : Fork} (h : WellLaid F) : Sized F := ⟨h.2.1, h.2.2, h.1⟩

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- A return of the head's sumcheck is three runs of layings on ranges that follow each other. -/
theorem sum_runs {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum} (hWL : WellLaid F0)
    (hsum : sumcheck zP 2 F0 t = some (S, F1, [])) :
    ∃ (c0 beta : E) (vals : Array E) (Fa G : Fork) (n1 n2 : Nat), vals.size = 2 ∧
      ({ F0 with next := n1 } : Fork).hideRun F0.next #[c0] oneE = some Fa ∧
      ({ Fa with next := n2 } : Fork).hideRun (F0.next + 1 + ownP) vals beta = some G ∧
      G.hideRun (F0.next + 1) (Array.replicate ownP zeroE) (subE zeroE oneE) = some F1 := by
  obtain ⟨ld, cA, Fa, G, hd, es, a1, a2, a3, a4, a5, a6, hS⟩ := sumcheck_spec hsum
  rw [kP_eq] at a2 a4 hS
  obtain ⟨_, Tt, R, hpub, hread, hhd, hrun2⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ :=
    Part.MaskedSum.readAll_spec (show readAll ⟨1, vsP, some ⟨2, 2⟩⟩ t = some R from hread)
  obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.mp hfl
  have hs0' : Sent r0 2 1 [c0, R.mu] [R.eps] := hs0
  have hld : ld = [c0] := by
    have h1 : leadScalars ⟨1, vsP, some ⟨2, 2⟩⟩ t = some ld := a2
    rw [ht, lead_of_sent hs0'] at h1
    exact (Option.some.inj h1).symm
  subst hld
  obtain ⟨run1, hcA⟩ := hide_unfold a3
  obtain ⟨_, _, nFa, _, _⟩ :=
    hideRun_frame (F := { F0 with next := F0.next + [c0].length }) hWL run1
  have hnext : Fa.next = F0.next + 1 := nFa
  have hlenR : R.rounds.length = kP.all.length := hvr.length.2
  have hlen : (Part.MaskedSum.hidingAt (kP.all.zip (R.rounds.map (·.2)))).1.length = ownP := by
    have hz : (kP.all.zip (R.rounds.map (·.2))).map (·.1) = kP.all :=
      List.map_fst_zip (by rw [List.length_map, hlenR])
    rw [hidingAt_length _ ?_ ?_, hz]
    · rfl
    · intro e
      have := congrArg (List.map (·.1)) e
      rw [hz] at this
      exact absurd this (by show vsP ++ [Var.point zeroE 3] ≠ []; simp)
    · intro x hx
      have : x.1 ∈ kP.all := by rw [← hz]; exact List.mem_map_of_mem hx
      rw [allP_d _ this]; omega
  have run3 : G.hideRun (F0.next + 1) (Array.replicate ownP zeroE) (subE zeroE oneE) = some F1 := by
    have h5 := a5
    unfold rowLaid at h5
    rw [hhd] at h5
    dsimp only at h5
    rw [hlen, hnext] at h5
    exact h5
  rw [hnext] at hrun2
  exact ⟨c0, _, R.values.toArray, Fa, G, _, _, by rw [List.size_toArray]; exact hsv.2.1, run1, hrun2,
    run3⟩

/-- **Behind the sumcheck every number that it lays is filled.** -/
theorem filled_range {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum} (hWL : WellLaid F0)
    (hsum : sumcheck zP 2 F0 t = some (S, F1, [])) :
    ∀ j, F0.next ≤ j → j < sEndP F0 + 2 → OnBytes.PscRun.Filled F1 j := by
  obtain ⟨c0, beta, vals, Fa, G, n1, n2, hv, r1, r2, r3⟩ := sum_runs hWL hsum
  obtain ⟨_, sA, fA1, _⟩ := hideRun_ok { F0 with next := n1 } Fa _ _ _ (sized_of hWL) r1
  obtain ⟨_, sG, fG1, oG⟩ := hideRun_ok { Fa with next := n2 } G _ _ _ sA r2
  obtain ⟨_, _, f31, o3⟩ := hideRun_ok G F1 _ _ _ sG r3
  have s3 : (Array.replicate ownP zeroE).size = ownP := Array.size_replicate
  intro j h1 h2
  unfold sEndP at h2
  by_cases c1 : j = F0.next
  · subst c1
    have a := (fA1 0 (by simp)).2.2.1
    rw [Nat.add_zero] at a
    have b := ((oG F0.next (Or.inl (by omega))).2.2).mpr a
    exact ((o3 F0.next (Or.inl (by omega))).2.2).mpr b
  · by_cases c2 : j < F0.next + 1 + ownP
    · have a := (f31 (j - (F0.next + 1)) (by rw [s3]; omega)).2.2.1
      have e : F0.next + 1 + (j - (F0.next + 1)) = j := by omega
      rwa [e] at a
    · have a := (fG1 (j - (F0.next + 1 + ownP)) (by omega)).2.2.1
      have e : F0.next + 1 + ownP + (j - (F0.next + 1 + ownP)) = j := by omega
      rw [e] at a
      exact ((o3 j (Or.inr (by rw [s3]; omega))).2.2).mpr a

end VerifiableInference.Desc.Kinds.Head.Law
