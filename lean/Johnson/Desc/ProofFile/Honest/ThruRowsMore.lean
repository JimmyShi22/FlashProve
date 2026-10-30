-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruRowsMore.lean: the rows' prover (Honest/ThruRows.lean) against the
laws of Honest/ThruStops.lean, and ready read backwards. NOT IN FRONT OF A LAW OVER COINS where a
value of ThreadsC is a premise or an end.

  stop0B_rows, badB_rows, hidB_rows, halvedAll_rows, rootedAll_rows   the stops and the two tests on
                       places at the rows' prover are the prover's
  ready_rows_back      what ready returns at the rows' prover is what it returns at the prover,
                       read through
  threads_rows_back    so a value of ThreadsC at the prover, wherever ready returns there, gives one
                       at the rows' prover at the R that ready returned

By what. rows_prover_eq, ready_rows_thru (Honest/ThruRows.lean); stop0B_thru, badB_thru, hidB_thru,
halvedAll_thru, rootedAll_thru (Honest/ThruStops.lean); ThreadsC.thru, ThreadsC.withStored
(Honest/ThruThreads.lean).

Limits.
  * hrows, hk and CommittedColumns are premises. They are no law at any filling.
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ThruStops
import Johnson.Desc.ProofFile.Honest.ThruThreads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

variable {Xi W₀ W₀' Rc Rc' Ky Tr X₀ X Sd Xc : Type}

section
variable (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {F : FileDescription Xi} {B : ProverCoinCounts}
  (G : Sides F B W₀' Rc' Ky Tr X₀ X) (Cm : Committer W₀' Rc' Sd Xc Xi Ky) (item₀ : Nat)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key)
include hrows hk

/-- The shared chain's stop at the rows' prover. -/
theorem stop0B_rows : stop0B F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) = stop0B F H := by
  rw [rows_prover_eq G Cm item₀ _ hrows hk]
  funext ds
  exact stop0B_thru g rd d F H ds

/-- Its first stops. -/
theorem badB_rows : badB F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) = badB F H := by
  rw [rows_prover_eq G Cm item₀ _ hrows hk]
  funext ds
  exact badB_thru g rd d F H ds

/-- Its second stops. -/
theorem hidB_rows (w : W₀') (rc : Rc') (x : Xi) :
    hidB F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x =
      hidB F H (g w) (rd rc) x := by
  rw [rows_prover_eq G Cm item₀ _ hrows hk]
  funext ds
  exact hidB_thru g rd d F H w rc x ds

/-- The test that a side stands wherever an item is declared. -/
theorem halvedAll_rows :
    halvedAll F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) = halvedAll F H := by
  rw [rows_prover_eq G Cm item₀ _ hrows hk]
  exact halvedAll_thru g rd d F H

/-- The test that a side stands wherever a root is sent. -/
theorem rootedAll_rows :
    rootedAll F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) = rootedAll F H := by
  rw [rows_prover_eq G Cm item₀ _ hrows hk]
  exact rootedAll_thru g rd d F H

variable (w : W₀') (rc : Rc') (x : Xi) (k : Coins B)
  (hd : H.inRange (g d) = H.inRange H.dummy)
include hd

/-- **What ready returns at the rows' prover is what it returns at the prover, read through.** -/
theorem ready_rows_back {R' : Ready W₀' Rc' Xi Ky Tr X₀ X}
    (h : ready F B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x k = .ok R') :
    ∃ R, ready F B H (g w) (rd rc) x k = .ok R ∧ R' = Ready.thru g rd w rc R := by
  rw [ready_rows_thru g rd d G Cm item₀ H w rc x k hd hrows hk] at h
  cases hR : ready F B H (g w) (rd rc) x k with
  | error e =>
    rw [hR] at h
    have h' : (Except.error e : Except Refusal (Ready W₀' Rc' Xi Ky Tr X₀ X)) = .ok R' := h
    cases h'
  | ok R =>
    rw [hR] at h
    exact ⟨R, rfl, (Except.ok.inj h).symm⟩

/-- **A value of ThreadsC at the prover, wherever ready returns there, gives one at the rows' prover,
at the R that ready returned, with the same falls.** -/
theorem threads_rows_back (hs : CommittedColumns Cm item₀ H g rd w rc)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (T : ∀ R, ready F B H (g w) (rd rc) x k = .ok R →
      ∃ T' : ThreadsC F B H (g w) (rd rc) x k R, T'.f₁ = f₁ ∧ T'.f₂ = f₂ ∧ T'.f₃ = f₃)
    {R' : Ready W₀' Rc' Xi Ky Tr X₀ X}
    (h : ready F B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x k = .ok R') :
    ∃ T' : ThreadsC F B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x k R',
      T'.f₁ = f₁ ∧ T'.f₂ = f₂ ∧ T'.f₃ = f₃ := by
  obtain ⟨R, hR, rfl⟩ := ready_rows_back g rd d G Cm item₀ H hrows hk w rc x k hd h
  obtain ⟨T₀, e₁, e₂, e₃⟩ := T R hR
  have hw : ((H.thru g rd d).withStored (Cm.columnsAt item₀)).storedWords w rc =
      (H.thru g rd d).storedWords w rc := by
    funext it p
    exact hs it p
  have hr := Ready.reads_thru g rd hR
  rw [rows_prover_eq G Cm item₀ _ hrows hk]
  exact ⟨(T₀.thru g rd d hr).withStored _ hw, e₁, e₂, e₃⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.stop0B_rows
#print axioms ProofFile.Honest.badB_rows
#print axioms ProofFile.Honest.hidB_rows
#print axioms ProofFile.Honest.halvedAll_rows
#print axioms ProofFile.Honest.rootedAll_rows
#print axioms ProofFile.Honest.ready_rows_back
#print axioms ProofFile.Honest.threads_rows_back
