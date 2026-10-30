-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/FilledG.lean: Filled6.lean's two lemmas, GENERAL IN THE POINT z AND THE NUMBER n OF END VALUES
(a reader's debt: filled_range was typed at the head's own point zt ++ halves lPd alone; the
normalization's sumcheck "normed" runs at zt). Over the general names of Law/SumLaw.lean
(vsG, kG, ownG, sEndG). `sum_runsG`: a return of HeadParts.lean's `sumcheck z n` is three
runs of layings. `filled_rangeG`: behind them every number from the claimed sum's to the last end
value's is filled (hideRun_ok). With Filled6.lean's `hidden_later`: a world read off any
later ledger holds the hidden scalars under these numbers: what SumLaw.lean's coreG asks of its world.
THE PROOFS ARE Filled6.lean's, RE-TYPED BY A PROGRAM (zP ↦ z; 2 ↦ n; …P ↦ …G); Lean has checked them.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Filled6
import Johnson.Desc.Kinds.Law.SumLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Aff Fork Reading World)
open OnBytes.PscRun (Later Sized hideRun_ok)
open Part.MaskedSum (Var Sent readAll leadScalars rowLaid)

/-- A return of `sumcheck z n` is three runs of layings on ranges that follow each other. -/
theorem sum_runsG (z : Point) (n : Nat) {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum} (hWL : WellLaid F0)
    (hsum : sumcheck z n F0 t = some (S, F1, [])) :
    ∃ (c0 beta : E) (vals : Array E) (Fa G : Fork) (n1 n2 : Nat), vals.size = n ∧
      ({ F0 with next := n1 } : Fork).hideRun F0.next #[c0] oneE = some Fa ∧
      ({ Fa with next := n2 } : Fork).hideRun (F0.next + 1 + ownG z n) vals beta = some G ∧
      G.hideRun (F0.next + 1) (Array.replicate (ownG z n) zeroE) (subE zeroE oneE) = some F1 := by
  obtain ⟨ld, cA, Fa, G, hd, es, a1, a2, a3, a4, a5, a6, hS⟩ := sumcheck_spec hsum
  rw [kG_eq z n] at a2 a4 hS
  obtain ⟨_, Tt, R, hpub, hread, hhd, hrun2⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ :=
    Part.MaskedSum.readAll_spec (show readAll ⟨1, vsG z, some ⟨2, n⟩⟩ t = some R from hread)
  obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.mp hfl
  have hs0' : Sent r0 2 1 [c0, R.mu] [R.eps] := hs0
  have hld : ld = [c0] := by
    have h1 : leadScalars ⟨1, vsG z, some ⟨2, n⟩⟩ t = some ld := a2
    rw [ht, lead_of_sent hs0'] at h1
    exact (Option.some.inj h1).symm
  subst hld
  obtain ⟨run1, hcA⟩ := hide_unfold a3
  obtain ⟨_, _, nFa, _, _⟩ :=
    hideRun_frame (F := { F0 with next := F0.next + [c0].length }) hWL run1
  have hnext : Fa.next = F0.next + 1 := nFa
  have hlenR : R.rounds.length = (kG z n).all.length := hvr.length.2
  have hlen : (Part.MaskedSum.hidingAt ((kG z n).all.zip (R.rounds.map (·.2)))).1.length = ownG z n := by
    have hz : ((kG z n).all.zip (R.rounds.map (·.2))).map (·.1) = (kG z n).all :=
      List.map_fst_zip (by rw [List.length_map, hlenR])
    rw [hidingAt_length _ ?_ ?_, hz]
    · rfl
    · intro e
      have := congrArg (List.map (·.1)) e
      rw [hz] at this
      exact absurd this (by show vsG z ++ [Var.point zeroE 3] ≠ []; simp)
    · intro x hx
      have : x.1 ∈ (kG z n).all := by rw [← hz]; exact List.mem_map_of_mem hx
      rw [allG_d z n _ this]; omega
  have run3 : G.hideRun (F0.next + 1) (Array.replicate (ownG z n) zeroE) (subE zeroE oneE) = some F1 := by
    have h5 := a5
    unfold rowLaid at h5
    rw [hhd] at h5
    dsimp only at h5
    rw [hlen, hnext] at h5
    exact h5
  rw [hnext] at hrun2
  exact ⟨c0, _, R.values.toArray, Fa, G, _, _, by rw [List.size_toArray]; exact hsv.2.1, run1, hrun2,
    run3⟩

/-- **Behind `sumcheck z n` every number that it lays is filled**: the claimed sum's, its own, the n end
values'. -/
theorem filled_rangeG (z : Point) (n : Nat) {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum} (hWL : WellLaid F0)
    (hsum : sumcheck z n F0 t = some (S, F1, [])) :
    ∀ j, F0.next ≤ j → j < sEndG z n F0 + n → OnBytes.PscRun.Filled F1 j := by
  obtain ⟨c0, beta, vals, Fa, G, n1, n2, hv, r1, r2, r3⟩ := sum_runsG z n hWL hsum
  obtain ⟨_, sA, fA1, _⟩ := hideRun_ok { F0 with next := n1 } Fa _ _ _ (sized_of hWL) r1
  obtain ⟨_, sG, fG1, oG⟩ := hideRun_ok { Fa with next := n2 } G _ _ _ sA r2
  obtain ⟨_, _, f31, o3⟩ := hideRun_ok G F1 _ _ _ sG r3
  have s3 : (Array.replicate (ownG z n) zeroE).size = ownG z n := Array.size_replicate
  intro j h1 h2
  unfold sEndG at h2
  by_cases c1 : j = F0.next
  · subst c1
    have a := (fA1 0 (by simp)).2.2.1
    rw [Nat.add_zero] at a
    have b := ((oG F0.next (Or.inl (by omega))).2.2).mpr a
    exact ((o3 F0.next (Or.inl (by omega))).2.2).mpr b
  · by_cases c2 : j < F0.next + 1 + ownG z n
    · have a := (f31 (j - (F0.next + 1)) (by rw [s3]; omega)).2.2.1
      have e : F0.next + 1 + (j - (F0.next + 1)) = j := by omega
      rwa [e] at a
    · have a := (fG1 (j - (F0.next + 1 + ownG z n)) (by omega)).2.2.1
      have e : F0.next + 1 + ownG z n + (j - (F0.next + 1 + ownG z n)) = j := by omega
      rw [e] at a
      exact ((o3 j (Or.inr (by rw [s3]; omega))).2.2).mpr a


/-- **What coreG asks of its world, at any later ledger.** -/
theorem world_laterG (z : Point) (n : Nat) (mask : Nat → E) {F0 F1 G : Fork} {t : List Fmt.RoundView}
    {S : Sum} (hWL : WellLaid F0) (hsum : sumcheck z n F0 t = some (S, F1, [])) (hL : Later F1 G) :
    ∀ j, F0.next ≤ j → j < sEndG z n F0 + n → rd (hidden G mask j) = rd (hidden F1 mask j) :=
  fun j h1 h2 => hidden_later mask hL (filled_rangeG z n hWL hsum j h1 h2)

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.world_laterG
