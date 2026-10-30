-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RefPubStepsFront.lean: `refP_frontIs` (Johnson/Road/K4/RefPubFront.lean [not in this
library]) WITH THE HASH-FREE RECORD `PublicSteps pol KL X`
(Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean) IN THE PLACE OF "`publicOf` returns X". One
statement; the line ok is paid by `steps_ok` (Johnson/Road/K4/RefPubSteps.lean).

OF `FrontIs`' FIVE LINES: pub and ok are theorems here; fo holds by the choice of h3; on and n0 are
handed through: NOBODY MAY SAY THAT `FrontIs` HOLDS AT THE MEMBER. Limits: those of RefPubFront.lean
[not in this library] and RefPubSteps.lean. No soundness is concluded.
-/
import Johnson.Road.K4.RefPubSteps
import Johnson.Road.K4.CloseK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Verify (Public layerShape weightShape)
open VerifiableInference.PlanWritten (PublicSteps)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef)
open OnBytes.Desc.First.K4 (Par Seat)
open VerifiableInference.Desc.Sound (Frame)
open VerifiableInference.Desc.Plain.K04 (Letters)
open VerifiableInference.OnPublicFiles (K3LeftAt)

variable [scl : Scl] {M Xs T Wt : Type} {Fr : Frame} {pol KL : ByteArray}
  {lay : Option ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **`FrontIs` from its line on and its line n0**, at the s0 of the public lines, under `RefPub`.
-/
theorem refS_frontIs (R : RefLetters M Xs) (hg : p.g < 12) (nT nI : ℕ)
    (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp) :
    ∃ s0, (∀ tk', PubLines { p.P with tokv := tk' } p.g (layerShape X.P) X.P.polCalls
        (refL R p.g hg nT nI).plan.full.D (refL R p.g hg nT nI).plan.full.tb
        (weightShape X.P X.y) kRef s0 p.hp.tl) ∧
      ∀ (L : Seat T) (Lt : Letters T Wt Fr) (first : ℕ) (Q3 : Fork → Prop),
        R.n0 = first + Forest.elems X.layers.y.fo →
        (∀ a, Lt.on a →
          K3LeftAt (fun s => some (L.fork s)) L.look p.P.y.fo p.P.y.h.lmb first Q3 a.1) →
        Plan4L.FrontIs (refL R p.g hg nT nI) p L Lt first s0 p.P.y.fo Q3 := by
  obtain ⟨s0, H, hpb⟩ := refP_lines_pub R hg nT nI B hP hG
  refine ⟨s0, H, fun L Lt first Q3 hn on => ⟨on, rfl, hpb, ?_, ?_⟩⟩
  · rw [hP]
    exact steps_ok St
  · rw [hP]
    exact hn

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.refS_frontIs
