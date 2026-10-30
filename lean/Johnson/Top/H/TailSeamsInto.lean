-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailSeamsInto.lean: the seams of Johnson/Top/H/TailSeams.lean between joints with
their conditions, at the kind of sending that ends at such a joint.

`kSendInto` (Johnson/Top/H/SendInto.lean) is the sending with the last joint
`Cb.Pv.Send.outJInto s A back`, that is `s.N.over (s.N.pull A back)`, with its condition. That is
the joint at which `seamSentP` starts, by definition. So every seam "a sending, then a block over
the old and the new oracle messages" is a seam between joints with their conditions. Definitions,
statements and proofs.

Main names:
  `tailSendOver S s A₀ bk`: the caller of a sending of the family s.N to a statement over S, at the
    base joint A₀ before it.
  `tailSentInto S s A₀ bk C`, `tailSentInto_ok`: from `kSendInto`'s last joint at that caller to
    `jOver (S.sum s.N) C`, for any base joint C; from the two premises of `seamSentP_ok`.
  `tailIntoRng`, `tailIntoRng_ok`: that seam into the draw of the matrix (`KTailRng`).
  `tailFromRng`, `tailFromRng_ok`: from the draw to the sending behind it: no premise.
  `KTailRngCf_fills`: at an assignment of kinds that has `KTailRngCf` at the family rng, that
    family's hypothesis holds.

Limits: those of Johnson/Top/H/TailSeams.lean. The premise `hrel` is shown of no sub-proof here.
-/
import Johnson.Top.H.TailSeams
import Johnson.Top.H.SendInto

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop Cb IOR VerifiableInference.OnPublicFiles

section
variable {E : Type} [Field E] (S : Sig E) {Kc Kc' St Wp Wp' : Type} {E₀ : ExtSpec}

/-- The caller of a sending to a statement over S. -/
@[reducible] def tailSendOver (s : Cb.Pv.Send.Size E) (A₀ : Rels Kc St E₀ (S.Msg × Wp))
    (bk : s.N.Msg → Wp' → Wp) : SendCaller E :=
  ⟨s, Kc, St × S.Smp, S.Wit × Wp, S.Wit × Wp', E₀.prod S.ext, S.over A₀, S.backN s.N bk⟩

/-- From that sending's last joint to a joint over the old and the new oracle messages. -/
@[reducible] noncomputable def tailSentInto (s : Cb.Pv.Send.Size E)
    (A₀ : Rels Kc St E₀ (S.Msg × Wp)) (bk : s.N.Msg → Wp' → Wp)
    (C : Rels Kc' St E₀ ((S.sum s.N).Msg × Wp')) :
    StepD ((kSendInto [tailSendOver S s A₀ bk]).dst (tailSendOver S s A₀ bk))
      (jOver (S.sum s.N) C) :=
  seamSentP S s.N A₀ bk C

theorem tailSentInto_ok (s : Cb.Pv.Send.Size E) (A₀ : Rels Kc St E₀ (S.Msg × Wp))
    (bk : s.N.Msg → Wp' → Wp) (C : Rels Kc' St E₀ ((S.sum s.N).Msg × Wp'))
    (hon : ∀ a, A₀.on a → C.on a)
    (hrel : ∀ a w, A₀.on a → C.relR a w → (S.grow s.N A₀ bk).relR a w) :
    (tailSentInto S s A₀ bk C).OK :=
  seamSentP_ok S s.N A₀ bk C hon hrel

end

/-- The seam from a sending into the draw. -/
@[reducible] noncomputable def tailIntoRng (d : SentCaller) {Kc W₀ : Type}
    (A₀ : Rels Kc d.X d.Ex (d.S.Msg × W₀)) (bk : d.snd.N.Msg → d.Wp → W₀) :
    StepD ((kSendInto [d.before A₀ bk]).dst (d.before A₀ bk)) (KTailRng.src d.caller) :=
  seamToRngP d A₀ bk

theorem tailIntoRng_ok (d : SentCaller) {Kc W₀ : Type} (A₀ : Rels Kc d.X d.Ex (d.S.Msg × W₀))
    (bk : d.snd.N.Msg → d.Wp → W₀)
    (hrel : ∀ a w, A₀.on a → (Cb.Pv.Tail.A d.caller.letters).relR a w →
      (d.S.grow d.snd.N A₀ bk).relR a w) : (tailIntoRng d A₀ bk).OK :=
  seamToRngP_ok d A₀ bk hrel

/-- The seam from the draw to the sending behind it. -/
@[reducible] noncomputable def tailFromRng (c : TailCaller) (snd : Cb.Pv.Send.Size Cb.Gl.E)
    (W' : Type) (back : snd.N.Msg → W' → c.Sg.Wit × c.Wp) :
    StepD (KTailRng.dst c)
      ((kSendInto [sendBehindP c snd W' back]).src (sendBehindP c snd W' back)) :=
  seamFromRngP c snd W' back

theorem tailFromRng_ok (c : TailCaller) (snd : Cb.Pv.Send.Size Cb.Gl.E) (W' : Type)
    (back : snd.N.Msg → W' → c.Sg.Wit × c.Wp) : (tailFromRng c snd W' back).OK :=
  seamFromRngP_ok c snd W' back

/-- The hypothesis of the family rng, where the kind between joints whose condition may fail stands
at it. -/
theorem KTailRngCf_fills (K : PFam → KFam.{1}) (h : K .rng = KTailRngCf) : (K .rng).Good := by
  rw [h]
  exact KTailRngCf_good

end KObj

#print axioms KObj.tailSentInto_ok
#print axioms KObj.tailIntoRng_ok
#print axioms KObj.tailFromRng_ok
#print axioms KObj.KTailRngCf_fills
