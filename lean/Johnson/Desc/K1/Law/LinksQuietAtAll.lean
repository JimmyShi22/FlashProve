-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/LinksQuietAtAll.lean: TWO FIELDS OF WHAT IS LEFT OF THE LAW OF THE KIND K1
(K1Left: hlk · hquiet), EACH IN THE FIELD's OWN TYPE, AT THE CLOSED CONSTANT. Two
theorems: calls.

  hlk_atAll     h.𝔇.lk l = cF.links[l]? (at every l): the constant's lk is ProofFile.linkAt Zp; the
                library's descPure_chain | linkAt_of (Johnson/Desc/ProofFile/Law/LinkAtLaw.lean) say
                that this is the seated description's own first chain's link; the head's fields
                laid.value and laid.pub tie the public part and the chain (first_inj,
                Johnson/Desc/K14/Law/SharedConstReachAt.lean). IT HANGS ON THE HEAD ALONE.
  hquiet_atAll  the field hquiet from quiet_of_kind (OwnHeldAtSendings.lean). IT HANGS ON hkind:
                "the link at 24, if there is one, has kind 2": a closed fact on Bs.G₀.built[24]?,
                shown nowhere here. (That the sort of segment 24 is "head" does not give it:
                ProofFile.subOf sends every kind but 0 and 1 to "head".)
The fields hmono and hidle stand in Johnson/Desc/Kinds/Law/WtK6Mono.lean (hmono_atAll ·
hidle_atAll: at Wp := At.X Zp; on the head alone).
What is not claimed. That the head can be met. hkind. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.OwnHeldAtSendings
import Johnson.Desc.ProofFile.Law.LinkAtLaw
import Johnson.Desc.K14.Law.SharedConstReachAt
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes.Maker (WholeD)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K8 (ReadsQuiet.head)
open IM (k1Quiet)
open ProofFile (Cl)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x : First.Look.Place}

/-- **hlk.** -/
theorem hlk_atAll (h : P5J.AtMgA o Z D r Zp Np cF x) : ∀ l, l < 25 → h.𝔇.lk l = cF.links[l]? := by
  intro l _
  obtain ⟨Z', c, A, B, hZ, hc, _, _, eF⟩ := ProofFile.Law.descPure_chain h.laid.value
  obtain rfl : Z' = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  obtain rfl : cF = c := _root_.Desc.K14.Law.Sh.first_inj eF
  exact ProofFile.Law.linkAt_of Z' cF hc l

/-- **hquiet**, from the kind of the link at 24. -/
theorem hquiet_atAll (Bs : ProofFile.PureBase)
    (hkind : ∀ X : LinkH, Bs.G₀.built[24]? = some X → X.kind = 2) :
    ∀ X, Bs.G₀.built[24]? = some X → ∃ P, k1Quiet Bs.G₀ 24 X = ReadsQuiet.head P :=
  fun X hX => ⟨_, quiet_of_kind Bs.G₀ 24 X hX (hkind X hX)⟩

end VerifiableInference.Desc.K1
