-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/FitsShared.lean: the executable test `Thread.fits` at a shared thread
whose list is alike to the written one and whose count is `sentIn` at the written rounds: the field that
`Sits` asks of the shared chain at its twelve rows.

  `rows_fit`, `hands_fit`   closed lines: the table of rows fits; each tree in hand at each border is fixed
                 by the rounds in front of that border; `hands_bent`: control
  `maps_of_zip`, `roots_of_shaped`   what a shaped block says of its roots
  `fits_shared`  the statement

Limits. Public lists alone: nothing on a run. hsh is the description's own test on its blocks. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OpensLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TableLines
import Johnson.Desc.ProofFile.Honest.Thread.Shared

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open VerifiableInference.Desc (Block Alike₂)
open Desc.K14 (St)
open OnBytes (TableKey)
open P2Law.ProofPlan (WP declProofFull)

/-- The table of rows fits at twelve. -/
theorem rows_fit : fwdFit SharedRows.start (SharedRows.rows true) 12 = true := by decide +kernel

/-- Each tree in hand at each border is fixed by the rounds in front of that border. -/
theorem hands_fit : ((List.range 13).all fun b =>
    (List.range ((sharedR.take b).map (·.2)).sum).all fun i =>
      decide (ProofFile.Honest.Small.sentIn declProofFull.2.1 i ≤ ((sharedR.take b).flatMap (·.1)).length)) = true := by
  decide +kernel

/-- Control: the rounds in front of the member before each border alone: no. -/
theorem hands_bent : ((List.range 13).all fun b =>
    (List.range ((sharedR.take b).map (·.2)).sum).all fun i =>
      decide (ProofFile.Honest.Small.sentIn declProofFull.2.1 i ≤ ((sharedR.take (b - 1)).flatMap (·.1)).length)) = false := by
  decide +kernel

theorem maps_of_zip {A B : Type} (f : A → ℕ) (g : B → ℕ) :
    ∀ (l : List A) (m : List B), m.length = l.length →
      (∀ x ∈ l.zip m, g x.2 = f x.1) → l.map f = m.map g
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: m, h, hx => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have h1 := hx (a, b) (by simp)
    have h2 := maps_of_zip f g l m h fun x hm => hx x (by simp [hm])
    simp only [List.map_cons, h2, show f a = g b from h1.symm]

theorem roots_of_shaped {S Cl : Type} (b : Block S Cl) (h : b.shaped = true) :
    b.oracles.length = b.rounds.length ∧
      b.rounds.map (·.entry.roots) = b.oracles.map (·.length) := by
  unfold Block.shaped at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, maps_of_zip _ _ _ _ h.1 fun x hx => (h.2 x hx).1⟩

variable {Bk : ProverCoinCounts} {Cl W₀ Rc X₀ P₁ Wt : Type}

/-- **`Thread.fits` at twelve.** -/
theorem fits_shared (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt)
    (hsp : L.split = true) (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder L.thread.bs)
    (hsh : ∀ b ∈ L.thread.bs, b.shaped = true)
    (hfx : ∀ i, L.thread.fixed (.own i) = ProofFile.Honest.Small.sentIn declProofFull.2.1 i) :
    L.thread.fits 12 = true := by
  unfold Thread.fits
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, rfl⟩, ?_⟩, ?_⟩
  · show fwdFit SharedRows.start (SharedRows.rows L.split) 12 = true
    rw [hsp]
    exact rows_fit
  · refine List.all_eq_true.2 fun x hx => ?_
    obtain ⟨e1, e2⟩ := roots_of_shaped x (hsh x hx)
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨e1.symm, e2⟩
  · refine List.all_eq_true.2 fun b hb => List.all_eq_true.2 fun σ hσ => ?_
    have hand : L.thread.hand b = (List.range (treesTo L.thread.bs b)).map Fmt.TreeSource.own := rfl
    rw [hand, List.mem_map] at hσ
    obtain ⟨i, hi, rfl⟩ := hσ
    have k₁ := List.all_eq_true.1 hands_fit b hb
    have e : sharedR = L.thread.bs.map roundsTrees := rounds_alike hl
    have ht : treesTo L.thread.bs b = ((sharedR.take b).map (·.2)).sum := by
      rw [trees_rounds, ← e]
    have hr : roundsTo L.thread.bs b = ((sharedR.take b).flatMap (·.1)).length := by
      unfold roundsTo
      rw [decls_rounds, ← e]
    rw [ht] at hi
    have k₂ := List.all_eq_true.1 k₁ i hi
    have hf0 : L.thread.front = 0 := rfl
    rw [hfx, hr, hf0, Nat.zero_add]
    exact k₂
  · exact decide_eq_true (Nat.zero_le _)

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.rows_fit
#print axioms ProofFile.Honest.K12.AtFile.hands_fit
#print axioms ProofFile.Honest.K12.AtFile.hands_bent
#print axioms ProofFile.Honest.K12.AtFile.roots_of_shaped
#print axioms ProofFile.Honest.K12.AtFile.fits_shared
