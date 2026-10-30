-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RowEarly.lean: firstMeans reads a request's public part through "the request
without its reply" alone. A tool for whoever lays the first relation of a description's row.

WHY. RowOwes.first (Johnson/Goal/Meaning/Row.lean) fixes the first relation at EVERY request p:
S.R₀ ((p, rec), y) w ↔ firstMeans X pp putReq (D y rec) p (hid w). The top theorem asks that the
first run read a request through "the request without its reply" (EarlyKept,
Johnson/Flat/ProofOfRow.lean). IF a description meets that by a first record that holds
reqWithoutReply p and not p (none is read here), a first relation that is read off that record
speaks of reqWithoutReply p. At a request whose reply is not 0 these are two requests. Were
firstMeans to tell them apart, RowOwes.first could be met by no such description.
  putReq_early      putReq (reqWithoutReply p) t = putReq p t, at every request and token;
  firstMeans_early  so firstMeans at reqWithoutReply p is firstMeans at p;
  first_of_early    so a first relation that is firstMeans at reqWithoutReply p, at every p, meets
                    RowOwes.first's line.

What is not claimed: that any description's first relation is so made.
-/
import Johnson.Goal.Meaning.Row

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model
open OnBytes OnBytes.Flat
open VerifiableInference.OnPublicFiles.Flat (Holds GE Req)

/-- **putReq reads its request through "the request without its reply" alone.** -/
theorem putReq_early (p : Req) (t : Fin ppref.V) : putReq (reqWithoutReply p) t = putReq p t := by
  by_cases hT : p.val.e < ppref.T
  · have e0 : (⟨0, ppref_V_pos⟩ : Fin ppref.V) = p.val.y := Fin.ext (p.property.2 hT).symm
    have hx : reqWithoutReply p = p := by
      refine Subtype.ext ?_
      show ({ p.val with y := ⟨0, ppref_V_pos⟩ } : Instance ppref) = p.val
      rw [e0]
    rw [hx]
  · refine Subtype.ext ?_
    rw [putReq_val (reqWithoutReply p) t (fun he => absurd he hT),
      putReq_val p t (fun he => absurd he hT)]
    rfl

/-- **So does firstMeans.** -/
theorem firstMeans_early {rows cols : ℕ} (X : Model.Verify.Public) (pp : ScalesAndPolicy)
    (dec : Option (Fin rows → Fin cols → GE)) (p : Req) (w : Hid) :
    firstMeans X pp putReq dec (reqWithoutReply p) w ↔ firstMeans X pp putReq dec p w := by
  unfold firstMeans
  rw [putReq_early]

/-- A relation that is firstMeans at the request without its reply is firstMeans at the request. -/
theorem first_of_early {rows cols : ℕ} {X : Model.Verify.Public} {pp : ScalesAndPolicy}
    {dec : Option (Fin rows → Fin cols → GE)} {p : Req} {w : Hid} {R : Prop}
    (h : R ↔ firstMeans X pp putReq dec (reqWithoutReply p) w) :
    R ↔ firstMeans X pp putReq dec p w :=
  h.trans (firstMeans_early X pp dec p w)

end Meaning

#print axioms Meaning.putReq_early
#print axioms Meaning.firstMeans_early
#print axioms Meaning.first_of_early
