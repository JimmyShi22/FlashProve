-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadL5OrdL.lean: "the head's link is in order, with the cost ledger", said call by
call, as the verifier's layout lays the head's lookup; keys and identities are the library's,
written with the sizes as letters; and that, at the library's sizes, it gives the statement
HeadOrdL of Johnson/Road/HeadL5Link.lean, for every request.

Johnson/Road/HeadL5Ord.lean has OrdPort: every entry of the matrices is small; in each call of the
verifier's lookup every value in every column at every position is a row of that call's table; the
17 identities of the final normalisation are 0 at every position. Its theorem is for a request for
the next token (r = 1,023), where no position is counted. For any other request the acceptance
policy has four clauses more, on the hidden numbers of the counted positions. OrdPortL adds them, in
the letters of Johnson/Road/HeadSizes.lean, which are written for any sizes z: at every position the
two identities dB4 (c + k = C) and dZ (zs and the looked-up values add up to 2^24), each under the
mark of a counted position; and the two sums sB2 and sB3 over the counted positions. As in OrdPort,
nothing here is a hidden value of a sub-proof, a challenge or a claim.

Main definition: OrdPortL.
Main theorem: ordL_of_ordPortL: at the library's sizes, for EVERY request of the right form (Head3)
and ANY policy pol, OrdPortL at the request Req.of pol x gives HeadOrdL.

The policy. The theorem asks no tie between pol and the shape's three numbers (clip, theta, cap):
OrdPortL reads the policy in the request yq alone. That the verifier's own four claims speak of the
shape's numbers is the matter of Johnson/Road/HeadPolicyForms.lean.

What is not claimed. Nothing derives OrdPortL from a proof file. At other sizes than the library's
OrdPortL is a definition and no more. That OrdPortL can be met is not shown here. The program does
not import this file.
-/
import Johnson.Road.HeadL5Ord
import Johnson.Road.HeadL5Road
import Johnson.Road.HeadTabL

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model (ppref NormPar Instance Mat Index AcceptancePolicy)
open Inst.Model.Head (nT nD nV Req)
open OnBytes.Model (Reading)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Verify (borderOf)

/-- The head's link is in order, with the cost ledger, said call by call. The letters are
those of OrdPort. The policy is read in yq. -/
def OrdPortL (R : Model.Head.Run) (z : HeadSizes.Sizes) (H : ℕ → ℕ → Cb.Gl.E) (yq : Req)
    (Mz : Mats ℤ) : Prop :=
  OrdPort R z H yq Mz ∧
  (∀ a < z.T,
    HeadSizes.dB4 z (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) yq a = 0 ∧
    HeadSizes.dZ z (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) yq a = 0) ∧
  HeadSizes.sB2 z (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) yq = 0 ∧
  HeadSizes.sB3 z (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) yq = 0

/-- **At the library's sizes OrdPortL gives HeadOrdL, for every request.** i: the
index; Wz: digits in which the library's layout reads the output matrix of i; pol: any policy. -/
theorem ordL_of_ordPortL {R : Model.Head.Run} {y : Lay}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hF : R.h.famF = 24)
    (hs : R.h.digSh = 8) (hT : R.h.tabS = 4) (hb : R.b = borderOf y) (pol : AcceptancePolicy)
    (i : Index ppref) (x : Instance ppref) (h3 : Inst.Model.Head3 x) {Wz : Mat}
    (hHz : ∀ j < nD, ∀ v < nV,
      i.val.H j v = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H j v)
    {Mz : Mats ℤ}
    (O : OrdPortL R HeadSizes.ref (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of pol x) Mz) :
    HeadOrdL R.h R.L y (npOf R.h) pol Wz x Mz := by
  obtain ⟨⟨small, keys, idns⟩, jc, s2, s3⟩ := O
  choose w hw using marks_of_layout (R := R) hy
  have Sf : SegsFit R := segsFit_of_layout hy hFull.lt hFull.d hFull.V hFull.XL
  choose fn Kf using fun q => exists_keyFn (hw q)
    (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of pol x))
    (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0)))
  have hc := iw_23 gl_numerals gl_inverse two_ne_gl (R := R) hs
  have rf : Policy.LedgerHead.RF (F := Cb.Gl.E) (npOf R.h)
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of pol x) (cellsH R.h R.L R.b Mz) :=
    ledgerRF_of_calls hc (tz := cellsH R.h R.L R.b Mz)
      (callsFitL_of_layout hy hFull.lt hFull.d hFull.V hFull.XL rfl rfl (tabL_of_layout hy Sf) _
        (npOf R.h) _ _ _) hw Kf (small_cellsHL R.h R.L R.b small)
      (fun q j hj a ha => by
        obtain ⟨u, hu, e⟩ := keys q (w q) (fn q) (hw q) (Kf q) j hj a ha
        rw [e]
        exact rows_of_port gl_numerals hy hF hs hT hj hu)
      idns jc ⟨s2, s3⟩
  rw [hb] at rf
  exact ordL_of_rf hHz small (fun he => by rw [h3.2.2 he]; exact Nat.cast_zero) rf

#print axioms ordL_of_ordPortL

end OnBytes.Road.Hd
