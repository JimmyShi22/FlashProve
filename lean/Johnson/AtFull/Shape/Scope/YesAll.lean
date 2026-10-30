-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/YesAll.lean: THE RUN ON SHAPES AT EVERY Z UNDER THE HEAD, FROM RunsAll's
PIECES AT THE STORED FULL-SIZE FILES ALONE. Three theorems; a joining; nothing is evaluated.

* **yes_of_pieces_in_scope**: the premise hyes of first_chain_debts (RuleAtTable.lean) at any Z under
  the head, from the pieces.
* run_at_scope, bool_at_scope: table_run_in_scope and bool_at_border (Scope/RunValue.lean) with the
  steps' relation paid by cells_rel (Scope/Rows.lean).

Limits. RunsAll's pieces stay a premise: in the library no such fact stands yet. Behind it lie the
limits of lay_size's side library and of what the head asks. That the head has a member at a Z is
another file's. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.Rows
import Johnson.AtFull.Shape.Scope.YesSize
import Johnson.AtFull.Shape.Scope.RunValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **hyes AT ANY Z UNDER THE HEAD, FROM THE PIECES AT THE STORED FILES.** -/
theorem yes_of_pieces_in_scope (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (len : Nat → Nat) (c : Nat → ShA) (K : Nat)
    (hp : ∀ k, k < K → RunsAll (ProofFile.Honest.border len k) (len k) (c k) (c (k + 1)))
    (h0 : c 0 = startShA) (hK : ProofFile.Honest.border len K = 358) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true :=
  table_yes h hB (fun _ h₀ Q n hn => cells_rel Q (ProofFile.Law.pub_public h.laid.pub) h₀ n hn)
    len c K hp h0 hK

/-- The run's value at any Z, up to RelAt: no premise on the steps. -/
theorem run_at_scope (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {X₀ : Verify.Public}
    (hX₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    (b : Nat) (hb : b ≤ 358) :
    Alike (α := ShA) (β := ShA) (RelAt Zp.p.X X₀ b)
      ((firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run b startShA)
      ((shapeL (LWn X₀)).run b startShA) :=
  table_run_in_scope Johnson.Unfolds.Layout.lay_size h hB hX₀
    (fun n hn => cells_rel (sameRead_in_scope hX₀ h.scope (ProofFile.Law.pub_public h.laid.pub))
      (ProofFile.Law.pub_public h.laid.pub) hX₀ n hn) b hb

/-- A Bool on shapes that RelAt cannot part, true at the stored files' border, holds at Z's. -/
theorem bool_at_scope (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {X₀ : Verify.Public}
    (hX₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    {b : Nat} (hb : b ≤ 358) (β : ShA → Bool)
    (hβ : ∀ a a', RelAt Zp.p.X X₀ b a a' → β a = β a') {c : ShA}
    (hc : (shapeL (LWn X₀)).run b startShA = .ok c) (h1 : β c = true) :
    ∃ c' : ShA, (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run b startShA = .ok c' ∧
      β c' = true :=
  bool_at_border Johnson.Unfolds.Layout.lay_size h hB hX₀
    (fun n hn => cells_rel (sameRead_in_scope hX₀ h.scope (ProofFile.Law.pub_public h.laid.pub))
      (ProofFile.Law.pub_public h.laid.pub) hX₀ n hn) hb β hβ hc h1

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.yes_of_pieces_in_scope
#print axioms Johnson.AtFull.Shape.Scope.run_at_scope
#print axioms Johnson.AtFull.Shape.Scope.bool_at_scope
