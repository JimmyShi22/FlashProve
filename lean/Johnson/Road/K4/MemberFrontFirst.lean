-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MemberFrontFirst.lean: THE FIRST GROUP's TWIN OF `ref_valueMore`
(Johnson/Road/K4/MemberFront.lean) AND `refP_frontIs` (Johnson/Road/K4/RefPubFront.lean [not in this
library]): THE RECORD `Plan4LF.ValueMoreF` (Johnson/Road/K4/CloseRowsFirst.lean) HOLDS OF THE FIRST
GROUP's VALUE AT THE REFERENCE SIZES (`refLF`, Johnson/Road/K4/RefValueFirst.lean), whatever its
free letters; AND THE RECORD `Plan4L.FrontIs` (Johnson/Road/K4/CloseK2.lean) AT THE LETTERS THAT IT
SHARES WITH A LATER GROUP's, UNDER `RefPub` (Johnson/Road/K4/RefPub.lean), FROM ITS LINE on AND ITS
LINE n0, WHICH STAY PREMISES. Two statements.

  `refF_valueMore`: numI and n4 by the value's make; room7F is `refF_room`'s second half: the
    value's ns is MADE large enough; that a ledger's number of slots is the value's is said by
    nothing here.
  `refPF_frontIs`: at the s0 of the public lines and at h3 := the plan's own shape of the lookup.

OF `FrontIs`' FIVE LINES: pub and ok are theorems here; fo holds by the choice of h3; on and n0 are
handed through: NOBODY MAY SAY THAT `FrontIs` HOLDS AT THE MEMBER. Limits: those of RefPubFront.lean
[not in this library] and RefPubFirst.lean. THE PUBLIC SIDE ALONE. No soundness is concluded.

-/
import Johnson.Road.K4.RefPubFirst
import Johnson.Road.K4.CloseRowsFirst
import Johnson.Road.K4.CloseK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Verify (Public publicOf layerShape weightShape)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef)
open OnBytes.Desc.First.K4 (Par Seat)
open VerifiableInference.Desc.Sound (Frame)
open VerifiableInference.Desc.Plain.K04 (Letters)
open VerifiableInference.OnPublicFiles (K3LeftAt)

variable [scl : Scl] {M Xs T Wt : Type} {Fr : Frame} {pol KL : ByteArray}
  {lay : Option ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **`ValueMoreF` holds of the first group's value**, whatever its free letters. -/
theorem refF_valueMore (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ) :
    Plan4LF.ValueMoreF (refLF R tok nT nI) where
  numI := rfl
  n4 := fun _ => rfl
  room7F := (refF_room R tok nT nI).2

/-- **`FrontIs` from its line on and its line n0**, at the first group's value, at the s0 of the
public lines, under `RefPub`. -/
theorem refPF_frontIs (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ)
    (h : publicOf pol KL lay = .ok X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp) :
    ∃ s0, (∀ tk', PubLines { p.P with tokv := tk' } p.g (layerShape X.P) X.P.polCalls
        (refLF R tok nT nI).planF.fullF.D (refLF R tok nT nI).planF.fullF.tb
        (weightShape X.P X.y) kRef s0 p.hp.tl) ∧
      ∀ (L : Seat T) (Lt : Letters T Wt Fr) (first : ℕ) (Q3 : Fork → Prop),
        R.n0 = first + Forest.elems X.layers.y.fo →
        (∀ a, Lt.on a →
          K3LeftAt (fun s => some (L.fork s)) L.look p.P.y.fo p.P.y.h.lmb first Q3 a.1) →
        Plan4L.FrontIs (refLF R tok nT nI).toPlan4L p L Lt first s0 p.P.y.fo Q3 := by
  obtain ⟨s0, H, hpb⟩ := refPF_lines_pub R tok nT nI B hP hG
  refine ⟨s0, H, fun L Lt first Q3 hn on => ⟨on, rfl, hpb, ?_, ?_⟩⟩
  · rw [hP]
    exact pub_ok h
  · rw [hP]
    exact hn

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.refF_valueMore
#print axioms OnBytes.Road.K4.refPF_frontIs
