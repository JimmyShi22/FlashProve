-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadL5Link.lean: "link 24 is in order" (LinkOK of Johnson/Road/Lane5.lean) from a
statement on the integer matrices of the verifier's list for the head's sub-proof: for the plain
head, and for the head with the cost ledger.

Johnson/Road/HeadL5.lean fills the library's family of matrices from the head's own list (headMx)
and has the statement HeadOrd for the plain head. This file states its result on the record LinkOK.
It then does the same for the head with the acceptance policy's cost ledger: the family of segments
is Policy.segPol s pol (Policy/Seg/All.lean), whose segment 24 is segHeadPolY s pol; the shape of
the head is Cm.Seg.Hd.main (all features of hf, all 120 bytes of hr). There every request is
covered, not the request for the next token alone.

Main definition: HeadOrdL (the statement on the integer matrices behind the head's sub-proof, with
the ledger).
Main theorems: linkOK_24; link24L_iff, linkOKL_24.

What is not claimed. As in Johnson/Road/HeadL5.lean: nothing derives HeadOrd or HeadOrdL from a
proof file; the sizes are the library's reference sizes. The program does not import this file.
-/
import Johnson.Road.HeadL5
import Johnson.Road.Lane5
import Policy.Seg.All

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model (ppref NormPar Instance Mat AcceptancePolicy)
open Inst.Model.All (DF)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HL)
open OnBytes.Model.Verify (borderOf)

variable {h : Model.Head.Shape} {tau : Array F} {L : HL} {hy : Model.Layer.Shape}
  {pc : List (List String)} {y : Lay}

/-- An entry of segment 24 of headMx is an entry of the head's list. -/
theorem headMx_small {Mh : Mats ℤ} (small : ∀ a r c, |Mh a r c| < 2 ^ 18) (n : Cm.Seg.Name)
    (hk : n.place.1 = 24) : |Cm.Seg.at' (headMx h y Mh) n.place| < 2 ^ 18 := by
  show |headMx h y Mh n.place.1 n.place.2.1 n.place.2.2| < 2 ^ 18
  rw [hk]
  exact small _ _ _

/-- **The plain head: link 24 is in order** at the matrices that are filled from the head's own
list, if that list meets HeadOrd. For a request with e = 1,024. -/
theorem linkOK_24 (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    {s : Cm.Scales} {x : Instance ppref} (he : x.e = 1024) {Wz : Mat} {Mh : Mats ℤ}
    (O : HeadOrd h L y s.nf Wz x Mh) :
    L5.LinkOK Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) Wz x 24 (headMx h y Mh) :=
  L5.linkOK_of_holds (fun n _ hk => headMx_small O.1 n hk)
    (link24_of_ord hF hL hl S Z Z2 he O).2

/-- The head's link is in order, with the cost ledger, said of the integer matrices Mh behind the
head's sub-proof, numbered as the verifier's list numbers them: every entry is below 2^18 in
absolute value; at the cells that the verifier's rule reads in them the clauses of
the head with the ledger hold modulo the protocol's prime (every key of the nine families in its
table, the 17 identities, the ledger's four); and the reply is 0 if e < 1,024. -/
def HeadOrdL (h : Model.Head.Shape) (L : HL) (y : Lay) (np : NormPar) (pol : AcceptancePolicy) (Wz : Mat)
    (x : Instance ppref) (Mh : Mats ℤ) : Prop :=
  (∀ a r c, |Mh a r c| < 2 ^ 18) ∧
  Policy.HeadCl np pol Wz x (cellsH h L (borderOf y) Mh) ∧
  (x.e < ppref.T → ((x.y.val : ℕ) : ZMod Cb.Gl.p) = 0)

/-- **With the ledger: the conditions of segment 24 at headMx are HeadOrdL**, for every request. -/
theorem link24L_iff (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (s : Cm.Scales) (pol : AcceptancePolicy) (x : Instance ppref) (Wz : Mat) (Mh : Mats ℤ) :
    ((∀ a r c, |Mh a r c| < 2 ^ 18) ∧
      (Policy.segPol s pol 24).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz)
        (Cm.Seg.TS.cM (headMx h y Mh))) ↔ HeadOrdL h L y s.nf pol Wz x Mh := by
  rw [Policy.segPol_head]
  exact and_congr_right fun _ =>
    Policy.headPolY_holds_int s pol x Wz (headMx h y Mh) (cellsH h L (borderOf y) Mh)
      (readsAtMain_cellsH hF hL hl S Z Z2 (fun _ _ r c => Mh (h.NHf + 3) r c) (fun _ _ _ => 0) Mh
        (fun _ _ _ _ => rfl))

/-- **With the ledger: link 24 is in order** at the matrices that are filled from the head's own
list, if that list meets HeadOrdL. -/
theorem linkOKL_24 (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    {s : Cm.Scales} {pol : AcceptancePolicy} {x : Instance ppref} {Wz : Mat} {Mh : Mats ℤ}
    (O : HeadOrdL h L y s.nf pol Wz x Mh) :
    L5.LinkOK Cm.Seg.Hd.main (Policy.segPol s pol) Wz x 24 (headMx h y Mh) :=
  L5.linkOK_of_holds (fun n _ hk => headMx_small O.1 n hk)
    ((link24L_iff hF hL hl S Z Z2 s pol x Wz Mh).2 O).2

#print axioms linkOK_24
#print axioms link24L_iff
#print axioms linkOKL_24

end OnBytes.Road.Hd
