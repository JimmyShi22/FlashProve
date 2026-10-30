-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadL5Road.lean: from the field relation of the head with the cost ledger, which the
theorems on the verifier's claims conclude, to the statement HeadOrdL on the verifier's matrices.

Johnson/Road/HeadLinkLPort.lean concludes Policy.LedgerHead.RF over the challenge field, at the
cells that are read in integer matrices Mz. Johnson/Road/HeadL5Link.lean begins at HeadOrdL, which
is said modulo the protocol's prime. This file joins the two. (For the plain head the like is
ord_of_rf in Johnson/Road/HeadL5.lean.)

Main theorem: ordL_of_rf.

What is not claimed. The field relation is a hypothesis here. The theorems that conclude it do so
from claims that hold in a world which nothing ties to a proof file. The program does not import
this file.
-/
import Johnson.Road.HeadL5Link

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model (ppref NormPar Instance Mat AcceptancePolicy)
open Inst.Model.Head (nD nV)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HL)
open OnBytes.Model.Verify (borderOf)

/-- From the field relation of the head with the ledger over the challenge field, at the cells that
are read in small integer matrices, to HeadOrdL. Hz: the output matrix; it is what the library's
layout reads in the digits Wz. h3: the reply is 0 if e < 1,024. -/
theorem ordL_of_rf {h : Model.Head.Shape} {L : HL} {y : Lay} {np : NormPar} {pol : AcceptancePolicy}
    {x : Instance ppref} {Wz Hz : Mat} {Mh : Mats ℤ}
    (hHz : ∀ j < nD, ∀ v < nV,
      Hz j v = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H j v)
    (small : ∀ a r c, |Mh a r c| < 2 ^ 18)
    (h3 : x.e < ppref.T → ((x.y.val : ℕ) : ZMod Cb.Gl.p) = 0)
    (rf : Policy.LedgerHead.RF (F := Cb.Gl.E) np (fun j v => ((Hz j v : ℤ) : Cb.Gl.E))
      (Inst.Model.Head.Req.of pol x) (cellsH h L (borderOf y) Mh)) :
    HeadOrdL h L y np pol Wz x Mh := by
  have r1 := Down.ledgerRF_gl.1 rf
  have r2 : Policy.LedgerHead.RF (F := ZMod Cb.Gl.p) np (Cm.TP.castH Cb.Gl.p Wz)
      (Inst.Model.Head.Req.of pol x) (cellsH h L (borderOf y) Mh) :=
    HeadReq.ledgerRF_of_mat (fun j hj v hv => by rw [hHz j hj v hv]) (fun i _ _ => x.w_lt i) r1
  exact ⟨small, ⟨r2.keys, r2.idns, r2.jc, r2.sums⟩, h3⟩

#print axioms ordL_of_rf

end OnBytes.Road.Hd
