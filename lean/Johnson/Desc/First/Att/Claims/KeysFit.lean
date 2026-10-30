-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/KeysFit.lean: kind K5: what the key forms are worth, at the lookup's
own numbers: kf_worth (Johnson/Desc/First/Att/Claims/KeysWorth.lean) at C := callsOf fs and the
scales sclOf S, with its three conditions on the lookup's layout paid by ONE public test on numbers:
CallsFit S fs (Johnson/Road/Lane5CallsOf.lean: decidable; run there at two configurations).

Main name:
  `kf_worth_fit`: CallsFit S fs, and v is the rule value wherever the key forms read it ⇒
    KF (dimOf S) (callsOf fs) p v c = Blocks.ext ((callsOf fs).a c) (keyVec (dimOf S) tb t c)
    ((callsOf fs).zC c p.z).
Limit: that CallsFit holds at a plan is a run's word (a closed test on public numbers).
Used: kf_worth; callsFit_ok, callsFit_deep, callsFit_a01.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Lane5CallsOf
import Johnson.Desc.First.Att.Claims.KeysWorth

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att.End (ReadK)
open OnBytes OnBytes.Road
open Inst.Model (Scl)
open Inst.Model.AttSeg (Pub rv KSc KF keyVec)

variable {Kf : Type} [Field Kf]

/-- **At the lookup's own numbers the three conditions are one public test.** -/
theorem kf_worth_fit {S : Attention.Shape} {fs : Model.Forest.Shape} (hF : L5.CallsFit S fs)
    (tb : Inst.Model.Tables) (p : Pub Kf) (t : Inst.Model.AttSeg.Raw → Kf) {v : KSc → Kf}
    (hv : ∀ k, ReadK (L5.dimOf S) k → v k = rv (L5.dimOf S) (L5.callsOf fs) p t k) (c : Fin 4) :
    letI : Scl := L5.sclOf S
    KF (L5.dimOf S) (L5.callsOf fs) p v c =
      Blocks.ext ((L5.callsOf fs).a c) (keyVec (L5.dimOf S) tb t c) ((L5.callsOf fs).zC c p.z) :=
  letI : Scl := L5.sclOf S
  kf_worth (L5.dimOf S) (L5.callsOf fs) tb p t hv (L5.callsFit_ok hF) (L5.callsFit_deep hF)
    (L5.callsFit_a01 hF) c

end K5Law

#print axioms K5Law.kf_worth_fit
