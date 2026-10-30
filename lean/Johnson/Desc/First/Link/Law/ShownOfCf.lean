-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/ShownOfCf.lean (kind K10): THE PREMISE hSh OF `hCar_end` (Johnson/Desc/First/Link/Law/HCarEnd.lean: «every leaf of every member is shown, at the strings in front of K10's closing») FROM THE FIELD hCfX OF `K10Heavy` («no collision», `CfAt`). A theorem: a projection.

WHY. `CfAt` (Johnson/Desc/Sound/MsgSig.lean :163-165) IS: ∃ z, smp a i = some z ∧ `ShownAt` G cs l seat y i ∧ no clash: its own head: «EVERY LEAF IS SHOWN (it stands in the promise too …)». And
K10Heavy's hCfX is `CfAt` at every message of the list, at the strings strsOf F a.2 of the statement in front: paid at the constant from the promise (`k10_hCfX_at`, Johnson/P5J/K10VCfAt.lean; by `cf_of_promise`), under `SitsIn`.

What is said.
  `shown_of_cf`: `CfAt` G cs l seat smp i a y ⊢ `ShownAt` G cs l seat y i. General in the reader of samples.
  `hSh_of_cf`: **hCfX's text at one statement ⊢ hSh's text**: ∀ b : {i // memMain lo i}, ShownAt G cs lo seat y b.1; meant at A := Pz × S, a := (z, a.1), y := strsOf F a.2, smp := fun q => smpS q ⟨lo, seat⟩. THAT THESE ARE THE TWO TEXTS IS READ BY EYE (K10Heavy.lean's field
    hCfX: «∀ i, CfAt Gd cs lo seat (fun q => smpS q ⟨lo, seat⟩) i (z, a.1) (strsOf F a.2)»; HCarEnd.lean :102): THIS FILE IMPORTS NEITHER: the first compiled call is the join's.

Limits. hCfX is a premise here. Nothing on soundness.

-/
import Johnson.Desc.Sound.MsgSig
import Johnson.Desc.First.Close.Law.CubeOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes Johnson.G Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.Sound

variable {Xi A : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
  (seat : Fin lo.length → ℕ × ℕ)

/-- «No collision» holds «every leaf is shown». -/
theorem shown_of_cf (smp : A → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp)
    (i : Fin lo.length) (a : A) (y : Strs) (h : CfAt G cs lo seat smp i a y) :
    ShownAt G cs lo seat y i := by
  obtain ⟨_, _, hs, _⟩ := h
  exact hs

/-- **hSh FROM hCfX, AT ONE STATEMENT.** -/
theorem hSh_of_cf (smp : A → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp) (a : A)
    (y : Strs) (h : ∀ i, CfAt G cs lo seat smp i a y) :
    ∀ b : {i // memMain lo i}, ShownAt G cs lo seat y b.1 :=
  fun b => shown_of_cf G cs lo seat smp b.1 a y (h b.1)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.shown_of_cf
#print axioms VerifiableInference.Desc.LinkJoin.hSh_of_cf
