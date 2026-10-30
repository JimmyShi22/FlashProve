-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoHead.lean.
The head of the byte-level verifier's lookup routine: three claims are entered in the list of owed
claims, and the shift and alpha are drawn.

OnBytes/Tie/Pv/Lookup/Forest/FoPadCut.lean cuts a run of Forest.pad that returns into the runs of
the routines that it calls
(PadCut). This file reads the first of them, Forest.draws from the state owed3 F.

* owed3_owed, owed3_at: the list of owed claims in owed3 F, and the three numbers in the record.
* owed3_sized, owed3_later, owed3_filled, owed3_next, owed3_under, owed3_rest: nothing else turns.
* drawsEv_rds: the calls of the draws are a row of rounds.
* head_cut: in a run of Forest.pad the state behind the draws is owed3 F; the calls on the channel
  are drawsEv h θ α; θ is 0 where the forest has one call; a is the routine's fold.
* head_theta, head_alpha, head_a: the first three fields of the flat function's end values, at the
  calls of the draws followed by any calls, are ρ θ, ρ α and ρ a. head_fac: ρ a is the flat
  function's public factor at ρ θ and ρ α. For a the public numbers must be lawful (FoNums.ok h).
  head_theta, head_a and head_shiftOf ask that θ is 0 where the forest has one call.
* rdL_rdA: the two names for an array read are one.
* head_shiftOf, draws_shiftRd: in the words of OnBytes/Tie/Pv/Lookup/Forest/FoTraceOf.lean: the
shift as the flat function reads
  it is ρ θ; the calls of the draws are the shift's round, if any, and alpha's.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoDraws
import OnBytes.Tie.Pv.Lookup.Forest.FoTwinsFac
import OnBytes.Tie.Pv.Lookup.Forest.FoRds
import OnBytes.Tie.Pv.Lookup.Forest.FoPadCut
import OnBytes.Tie.Pv.Lookup.Forest.FoTraceOf

set_option autoImplicit false

namespace Fo
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun

theorem owed3_owed (F : Fork) : (owed3 F).owed =
    ((F.owed.push { what := "look-up-mask-claims" }).push { what := "look-up-plane-claims" }).push
      { what := "look-up-join" } := rfl

/-- The three numbers in the record. -/
theorem owed3_at (M : PadMid) (pub : Array Nat) (F : Fork) :
    (M.heard pub F).owedObjects = F.owed.size ∧ (M.heard pub F).owedPlanes = F.owed.size + 1 ∧
      (M.heard pub F).owedJoin = F.owed.size + 2 := by
  refine ⟨rfl, ?_, ?_⟩
  · show (F.owed.push _).size = _
    rw [Array.size_push]
  · show ((F.owed.push _).push _).size = _
    rw [Array.size_push, Array.size_push]

theorem owed3_sized {F : Fork} (h : Sized F) : Sized (owed3 F) := h
theorem owed3_later (F : Fork) : Later F (owed3 F) :=
  ⟨le_refl _, rfl, fun _ h => ⟨h, rfl, rfl⟩⟩
theorem owed3_filled (F : Fork) (j : ℕ) : Filled (owed3 F) j ↔ Filled F j := Iff.rfl
theorem owed3_next (F : Fork) : (owed3 F).next = F.next := rfl
theorem owed3_under (F : Fork) : (owed3 F).vp = F.vp ∧ (owed3 F).mf = F.mf ∧
    (owed3 F).gotF = F.gotF := ⟨rfl, rfl, rfl⟩
theorem owed3_rest (F : Fork) : (owed3 F).trees = F.trees ∧ (owed3 F).ns = F.ns ∧
    (owed3 F).LS = F.LS ∧ (owed3 F).c0 = F.c0 ∧ (owed3 F).nClaim = F.nClaim ∧
    (owed3 F).theta = F.theta ∧ (owed3 F).thetaDrawnF = F.thetaDrawnF ∧
    (owed3 F).planClaimsF = F.planClaimsF ∧ (owed3 F).kapMapF = F.kapMapF ∧
    (owed3 F).doorShutF = F.doorShutF := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem drawsEv_rds (h : Sh) (θ α : E) : Rds (drawsEv h θ α) := by
  unfold drawsEv
  by_cases hN : h.NC > 1
  · rw [if_pos hN]
    exact .ans .lkpShift θ (.ans .lkp α .nil)
  · rw [if_neg hN]
    exact .ans .lkp α .nil

/-- The draws in a run of Forest.pad. -/
theorem head_cut {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Ctx}
    {g : Forest.Heard} {M : PadMid} (hc : PadCut calls pub lid F c g F' c' M) :
    M.F4 = owed3 F ∧ Evs (drawsEv (M.h pub) M.theta M.alpha) c M.c4 ∧
      (¬ (M.h pub).NC > 1 → M.theta = zeroE) ∧ M.a = drawsA (M.h pub) M.theta M.alpha := by
  obtain ⟨d1, d2, d3, d4⟩ := draws_ok _ _ _ _ _ _ _ _ hc.draws
  exact ⟨d2, d1, d3, d4⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem rdL_rdA (z : Array E) : rdL ρ z = rdA ρ z := rfl

/-- The shift as the flat function reads it. -/
theorem head_shiftOf (h : Sh) (θ : E) (hz : ¬ h.NC > 1 → θ = zeroE) :
    shiftOf h (ρ.val θ) = ρ.val θ := by
  unfold shiftOf FoNums.several
  by_cases hN : h.NC > 1
  · rw [if_pos (decide_eq_true hN)]
  · rw [if_neg (by simpa using hN), hz hN, ρ.zero]

/-- The calls of the draws as rounds of plain data. -/
theorem draws_shiftRd (h : Sh) (θ α : E) :
    flEv ρ (drawsEv h θ α) = shiftRd h (ρ.val θ) ++ [([], [ρ.val α])] := by
  rw [draws_fl]
  unfold shiftRd FoNums.several
  by_cases hN : h.NC > 1
  · rw [if_pos hN, if_pos (decide_eq_true hN)]
  · rw [if_neg hN, if_neg (by simpa using hN)]

/-- The flat function's shift. -/
theorem head_theta (h : Sh) (lm jLK : ℕ) (θ α : E) (hz : ¬ h.NC > 1 → θ = zeroE) (l : List Ev) :
    (endsOf h lm jLK (flEv ρ (drawsEv h θ α ++ l))).theta = ρ.val θ :=
  draws_theta ρ h θ α hz l

/-- The flat function's point of comparison. -/
theorem head_alpha (h : Sh) (lm jLK : ℕ) (θ α : E) (l : List Ev) :
    (endsOf h lm jLK (flEv ρ (drawsEv h θ α ++ l))).alpha = ρ.val α := by
  show (forTrace h lm jLK (flEv ρ (drawsEv h θ α ++ l))).lam = ρ.val α
  unfold forTrace
  rw [draws_after]
  rfl

/-- The routine's fold, read, is the flat function's public factor. -/
theorem head_fac (h : Sh) (H : FoNums.ok h = true) (lm jLK : ℕ) (θ α : E) :
    ρ.val (drawsA h θ α) = fac (numsF h lm jLK (ρ.val θ)) (ρ.val α) := by
  rw [Cb.Fo.PadFac.pad_fac h H]
  exact fac_val' ρ h θ α (ok_callOf H)

/-- The flat function's public factor. -/
theorem head_a (h : Sh) (H : FoNums.ok h = true) (lm jLK : ℕ) (θ α : E)
    (hz : ¬ h.NC > 1 → θ = zeroE) (l : List Ev) :
    (endsOf h lm jLK (flEv ρ (drawsEv h θ α ++ l))).a = ρ.val (drawsA h θ α) := by
  show fac (forN h lm jLK (flEv ρ (drawsEv h θ α ++ l)))
    (forTrace h lm jLK (flEv ρ (drawsEv h θ α ++ l))).lam = _
  have e1 : (forTrace h lm jLK (flEv ρ (drawsEv h θ α ++ l))).lam = ρ.val α :=
    head_alpha ρ h lm jLK θ α l
  rw [e1]
  unfold forN
  rw [draws_theta ρ h θ α hz l]
  exact (head_fac ρ h H lm jLK θ α).symm

end
end Fo
