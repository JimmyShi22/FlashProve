-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttPortJoin.lean: the verifier's claim that joins the key forms of an attention
sub-proof to the lookup gives the library-side form of the join.

The verifier's join is a form on slots: the sum over the four calls c of e_c (alpha - c theta - the
key form of call c), plus a public term, less the form of the hidden value at the end of the
lookup's key side (join in OnBytes/Model/Look.lean). The library-side form is joinA on the key forms
kfA (Cb/Pv/Att/End/Join.lean), with a form vF k for the hidden value of each named scalar k.

Main theorem.
 - join_cl: if the verifier's four key forms are the sums of terms of
   Johnson/Road/Rows/AttKeyPort.lean, the value of the verifier's join is that sum, the slot of each
   named scalar that the key forms read is worth its form vF k, the form at the end of the key side
   is worth its library-side form, and the verifier's claim has the value 0, then the claim that
   joinA is 0 holds.

What is taken as given: the record KeyPub of public facts; the formula for the value of the form
that join returns (jv); the ties of slots and forms (hv, hce). What is not claimed: that a run
returns these forms. Nothing is said about probabilities or about hiding. This file is not imported
by the program.


-/
import Johnson.Road.Rows.AttKeyPort
import Cb.Pv.Att.End.Seam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff)
open OnBytes.Attention (Heard ShD)
open Inst.Model (Scl)
open Inst.Model.AttSeg (Calls Pub KSc KF)
open Cb.Pv.Att.End (JoinPub joinVal joinA kfA val_joinA val_kfA ReadK KF_congr)

variable {K : Type} [Field K] {ρ : Reading K} [scl : Scl] {h : Heard} {u : Units} {C : Calls}
  {p : Pub K} {sd : ShD} {pad : E} {W : World K} {J : Type} [Fintype J]

/-- The verifier's join gives the library-side form of the join. r: the form that the verifier's
join returns; q: the join's public letters, read; cE: the verifier's form of the hidden value at the
end of the key side; x: the entries; vF, ce: the library-side forms. -/
theorem join_cl (P : KeyPub ρ h u C p sd pad) (q : JoinPub K) (r cE : Aff)
    (jv : r.value ρ W =
      joinVal q (fun c => (kfPort h u sd pad c).value ρ W) (cE.value ρ W))
    (x : J → K) (vF : KSc → TWhole.Aff K J) (ce : TWhole.Aff K J)
    (hv : ∀ k, ReadK (L5.dimOf h.S) k → slotVal W h u k = (vF k).val x)
    (hce : cE.value ρ W = ce.val x) (v : r.value ρ W = 0) :
    (joinA q (kfA (L5.dimOf h.S) C p vF) ce).claim.Holds x := by
  rw [TWhole.Aff.claim_holds, val_joinA, ← v, jv, hce]
  congr 1
  funext c
  rw [val_kfA, kfPort_value W P c]
  exact (KF_congr (L5.dimOf h.S) C p hv c).symm

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.join_cl
