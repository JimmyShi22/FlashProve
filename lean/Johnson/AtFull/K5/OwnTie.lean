-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/K5/OwnTie.lean: the head's example: A CLOSED FACT "atOwn g f = true"
(Johnson/AtFull/K5/AtOwn.lean) SPEAKS OF publicOfO's OWN VALUE AT THE STORED FULL-SIZE FILES.
A statement with its proof: calls and "two returns of one maker are one"; nothing is evaluated.
  **`own_of_atOwn`**: from hsz (the layout file has 224,975 bytes: the one premise of
    `publicOfO_zFull_of_rest`, Johnson/AtFull/Public/Join.lean): ∃ W, publicOfO returns W at the
    three files ∧ ∀ g f, atOwn g f = true → ∃ a, W.A[g]? = some a ∧ f a = true.

Limits. hsz IS A PREMISE: until it is laid in this is an "if". Nothing on soundness.
-/
import Johnson.AtFull.K5.AtOwn
import Johnson.AtFull.Public.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K5
open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Road.K4.Trial.Values (PW yFull polLayout_W)
open _root_.AtFull.Public (publicOfO_zFull_of_rest open_pubC onOk_ex' yFull_p3 yFull_p4 yFull_NGr)

/-- **Under hsz: a closed fact at atOwn is a fact at publicOfO's own plan.** -/
theorem own_of_atOwn (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) :
    ∃ W : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok W ∧
      ∀ (g : Nat) (f : Attention.Plan → Bool), atOwn g f = true →
        ∃ a, W.A[g]? = some a ∧ f a = true := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, -, e4, ⟨e5, -⟩, e6, e7, e8, -, -,
    hX⟩ := publicOfO_zFull_of_rest hsz
  refine ⟨_, hX, fun g f h => ?_⟩
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hR polLayout_W
  unfold atOwn at h
  obtain ⟨sc', wsLay', rope', L, a3, a4, a5, a6, h⟩ := open_pubC h
  obtain rfl : sc = sc' := Except.ok.inj (e1.symm.trans a3)
  rw [yFull_p3] at a4
  obtain rfl : wsLay = wsLay' := Except.ok.inj (e2.symm.trans a4)
  obtain rfl := Except.ok.inj (p10.symm.trans a5)
  obtain rfl : layers = L := Except.ok.inj (e6.symm.trans a6)
  have Ly : layers.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  have Lsc : layers.sc = sc := OnBytes.Road.Hd.pubOf_sc e6
  obtain ⟨G', b1, h⟩ := onOk_ex' h
  obtain rfl : G = G' := Except.ok.inj (e7.symm.trans b1)
  obtain ⟨l', b2, h⟩ := onOk_ex' h
  obtain rfl : l = l' := Except.ok.inj (e4.symm.trans b2)
  obtain ⟨ps', b3, h⟩ := onOk_ex' h
  rw [Ly, Lsc, yFull_NGr] at b3
  obtain rfl : ps = ps' := Except.ok.inj (e5.symm.trans b3)
  obtain ⟨seenA', b4, h⟩ := onOk_ex' h
  rw [Ly, yFull_p4, yFull_NGr] at b4
  obtain rfl : seenA = seenA' := Except.ok.inj (e8.symm.trans b4)
  obtain ⟨a, ha, hf⟩ := (Option.any_eq_true _ _).1 h
  exact ⟨a, ha, hf⟩

end Johnson.AtFull.K5

#print axioms Johnson.AtFull.K5.own_of_atOwn
