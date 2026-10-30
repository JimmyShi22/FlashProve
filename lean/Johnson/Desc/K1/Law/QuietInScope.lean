-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/QuietInScope.lean: THE FIELD hquiet OF WHAT IS LEFT OF THE LAW OF THE KIND K1
(K1Left), IN THE FIELD's OWN TYPE, FROM THE GOALS' SCOPE, "THE FILES ARE READ" AND THE MAKER's
OPENING. Two theorems: calls.

  kind_24_in_scope  the link at 24, if there is one, has kind 2: IM.ground_named
                    (in scope the links' kinds, groups, names: "there is a link at 24, of kind 2")
                    at the opening's own fields pub and blank.
  hquiet_in_scope   the field: hquiet_atAll (LinksQuietAtAll.lean) at that.
ON WHAT IT HANGS: hS · hR · O: all three are the shared head's (scope · reads · laid.opened); Bs
is the opening's own letter, as in K1Left's field O.
What is not claimed. That the scope can be met. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.LinksQuietAtAll
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K8 (ReadsQuiet.head)
open IM (k1Quiet)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope the link at 24 has kind 2. -/
theorem kind_24_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) :
    ∀ X : LinkH, Bs.G₀.built[24]? = some X → X.kind = 2 := by
  intro X hX
  obtain ⟨-, l, e, hk, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain rfl : l = X := Option.some.inj (e.symm.trans hX)
  exact hk

/-- **hquiet.** -/
theorem hquiet_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) :
    ∀ X, Bs.G₀.built[24]? = some X → ∃ Q, k1Quiet Bs.G₀ 24 X = ReadsQuiet.head Q :=
  hquiet_atAll Bs (kind_24_in_scope hS hR O)

end VerifiableInference.Desc.K1
