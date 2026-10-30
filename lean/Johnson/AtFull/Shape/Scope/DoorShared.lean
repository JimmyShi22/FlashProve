-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/DoorShared.lean: THE SHARED CHAIN OF THE PROOF FILE ONLY GROWS THE STATEMENT, SO ITS
CODES ARE THE PLAN's AT EVERY STATE THAT A FOLD OR A THREAD REACHES: the premise h₂ of the second chain's start.

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.DoorPublic
import E2E.KeyPublic
import Johnson.Desc.ProofFile.Honest.Thread.Thr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Grows foldBlocks OpenedColumn)
open VerifiableInference.Desc.Ground (By groundKeeps_grows)
open VerifiableInference.Desc.Keeps (Decides ChainKeeps chain_flat_keeps)
open Johnson.RunOne.KeyKeeps (st₂ blocksOr_keep onGu_grows onGomega_grows
  k12_decides end_keeps' retype_keeps)
open P5J (F0T TS)
open ProofFile.Honest (Thr Thread ProverCoinCounts Coins Mid)

/-- **The proof file's shared chain keeps «a statement only grows».** -/
theorem shared_grows_file (c : Model.Verify.Chains) (P : _root_.Desc.K14.P14) (N : H2U.Places4) :
    ChainKeeps (By Grows st₂) (_root_.Desc.K14.chainOf c P (VerifiableInference.Desc.K12.Seat.tests N)
      VerifiableInference.Desc.K12.Seat.last) := by
  refine ⟨fun d _ _ d' hd => ?_, fun b hb => (by cases hb), fun L hL => (by cases hL),
    fun b hb => ?_, end_keeps' Grows.refl _ _ _ _ _ _⟩
  · cases hd
    exact Grows.refl _
  · rcases List.mem_append.1 hb with hb | hb
    · exact blocksOr_keep groundKeeps_grows _ b hb
    · rcases List.mem_append.1 hb with hb | hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact onGu_grows _ (k12_decides _)
        · cases hb
      · obtain ⟨nO, _, rfl⟩ := List.mem_map.1 hb
        exact onGomega_grows _ (k12_decides _)

variable {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {o : ProofFile.SecondHashFunctionArgument}

/-- **h₂ along a fold from the shared chain's own start.** -/
theorem shared_fold_codes {bs : List (Block (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).Cl)}
    (hb : ∀ b ∈ bs, b ∈ (F0T o Zp Np cF).shared.blocksInOrder) (ft : Nat) (p : ProofFile.InstPub)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (r : (F0T o Zp Np cF).S₂ × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs ((F0T o Zp Np cF).start₂ p) rs cols = .ok r) :
    (st₂ (show _root_.Desc.K14.St from r.1)).codes = (ProofFile.pAt Zp).codes :=
  AtPublicFiles.AtFiles.fold_codes (S := _root_.Desc.K14.St) st₂ bs
    (fun b hbb => chain_flat_keeps (By Grows st₂) (fun _ => Grows.refl _)
      (fun _ _ _ a c => Grows.trans a c) _
      (retype_keeps (shared_grows_file Zp.p.chains _ Np)) b (hb b hbb)) ft _ rs cols r h

/-- **h₂ at a state of a thread of the shared chain.** -/
theorem shared_thr_codes {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).Cl V W X Pb)
    (hbs : T.bs = (F0T o Zp Np cF).shared.blocksInOrder)
    (hbeg : ∀ k w hd s₀, T.begun k w hd s₀ → ∃ p, s₀ = (F0T o Zp Np cF).start₂ p)
    {b : Nat} {k : Coins Bk} {s : (F0T o Zp Np cF).S₂} {m : Mid W X} {E}
    (hT : Thr T b k s m E) :
    (st₂ (show _root_.Desc.K14.St from s)).codes = (ProofFile.pAt Zp).codes := by
  unfold Thr ProofFile.Honest.Thread.Made at hT
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, c₀, hb₀, -, hfold⟩, -, -⟩ := hT
  obtain ⟨p, rfl⟩ := hbeg _ _ _ _ hb₀
  exact shared_fold_codes (fun x hx => by
    have := List.mem_of_mem_take hx
    rwa [hbs] at this) _ p _ _ _ hfold

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.shared_grows_file
#print axioms Johnson.AtFull.Shape.Scope.shared_fold_codes
#print axioms Johnson.AtFull.Shape.Scope.shared_thr_codes
