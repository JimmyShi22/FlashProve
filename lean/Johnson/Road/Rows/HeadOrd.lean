-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/HeadOrd.lean: from integer matrices in the verifier's layout that are in order to
the library's clauses for the output head: a dictionary.

OrdPortL (Johnson/Road/HeadL5OrdL.lean) says of integer matrices alone that the head's link is in
order: every entry is small; in each call of the lookup every value is a row of the call's table;
the 17 identities of the final normalisation are 0 at every position; and the four clauses of the
acceptance policy hold. Calls, segments, marks of columns and tables are the verifier's; the
identities, the clauses, the key vectors and the rule that reads cells in matrices are definitions
of the files under Johnson/Road/. OrdPortL names no hidden value, no challenge and no claim.

head_ord: OrdPortL, at a record whose shape, layout and border are the given ones, gives HeadOrdLB
(Johnson/Road/HeadL5BL.lean) at these. It is ordL_of_ordPortL, then ordLB_of_ord. head_ord_idx: the
same at an index that is given as a well-formed digit matrix.

Under: the layout returns; the nine numbers of the shape (FullH); F = 24, sh = 8, sT = 4; the
request has the right form (Head3); the index's output matrix is what the library's layout reads in
the digits Wz.

What is not claimed. That OrdPortL follows from a verifier's acceptance. OrdPortL is the joint of no
chain of blocks as it stands: Johnson/Road/Rows/HeadStart.lean draws it from what stands before the
first round in the blocks' letters. The theorems hold at the full size alone. This file is not
imported by the program.


-/
import Johnson.Road.HeadL5OrdL
import Johnson.Road.HeadL5BL
import Cm.RelBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Inst.Model (ppref Instance Mat Index AcceptancePolicy)
open Inst.Model.Head (nD nV Req)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HL)
open OnBytes.Model.Verify (borderOf)
open OnBytes.Road.Hd

/-- **From matrices in order to the statement on the verifier's arrays.** -/
theorem head_ord {R : Model.Head.Run} {hH : Model.Head.Shape} {L : HL} {y : Lay}
    (hh : R.h = hH) (hL : R.L = L) (hb : R.b = borderOf y)
    (hLy : Model.Head.layout hH tauFCw = .ok L) (hF : FullH hH) (h24 : hH.famF = 24)
    (hs : hH.digSh = 8) (hT : hH.tabS = 4) (pol : AcceptancePolicy) (i : Index ppref) (x : Instance ppref)
    (h3 : Inst.Model.Head3 x) {Wz : Mat}
    (hHz : ∀ j < nD, ∀ v < nV,
      i.val.H j v = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H j v)
    {Mz : Mats ℤ}
    (O : OrdPortL R HeadSizes.ref (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of pol x) Mz) :
    HeadOrdLB hH L y (npOf hH) pol Wz x Mz := by
  subst hh hL
  exact ordLB_of_ord (ordL_of_ordPortL hLy hF h24 hs hT hb pol i x h3 hHz O)

/-- The same at an index given as a well-formed digit matrix, and at any name nf for the shape's
normalisation. -/
theorem head_ord_idx {R : Model.Head.Run} {hH : Model.Head.Shape} {L : HL} {y : Lay}
    {nf : Inst.Model.NormPar} (hh : R.h = hH) (hL : R.L = L) (hb : R.b = borderOf y)
    (hnf : npOf hH = nf) (hLy : Model.Head.layout hH tauFCw = .ok L) (hF : FullH hH)
    (h24 : hH.famF = 24) (hs : hH.digSh = 8) (hT : hH.tabS = 4) (pol : AcceptancePolicy) (i : Cm.Idx)
    (x : Instance ppref) (h3 : Inst.Model.Head3 x) {Mz : Mats ℤ}
    (O : OrdPortL R HeadSizes.ref (fun j v => ((i.index.val.H j v : ℤ) : Cb.Gl.E)) (Req.of pol x)
      Mz) :
    HeadOrdLB hH L y nf pol i.mat x Mz :=
  hnf ▸ head_ord hh hL hb hLy hF h24 hs hT pol i.index x h3 (fun _ _ _ _ => rfl) O

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.head_ord
#print axioms OnBytes.Road.Rows.head_ord_idx
