-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/Lists.lean: "every link is in order, and every copy is its original", said of each
sub-proof's own list of integer matrices, by list number alone.

OrdsL (Johnson/Road/Lane5TopL.lean) says this of matrices that are named by labels, one family of
labelled matrices for each of the 25 sub-proofs. A sub-proof has no labelled matrices: it has a list
of arrays, and each array has a number in that list. This file states the same by list numbers
(OrdsN), lays the lists under the labels (zOf), and shows that OrdsN gives OrdsL.

The seams, in list numbers. Three kinds of arrays are copies of an array of an earlier sub-proof:
  seamFF  the stream that comes into a later group of layers (number iXI of its list) is the stream
          that went out of the group before (number iXO of that group's list);
  seamA   an attention sub-proof's copy of qa (number NAs + 3 of its list) is its group's qa (number
          iQA of the group's list);
  seamH   the head's copy of the stream (number NHf + 3 of its list) is the stream that went out of
          the last group.

Main definitions: OrdsN; numH, labZH (the head's list under the head's labels); zOf.
Main theorems: numH_labH, mzH_labZH; ordsL_of_lists; lists_of_ordsL (the way back: so the two say
the same, and OrdsN has a value wherever OrdsL has one).

What is not claimed. That a proof file which a verifier accepts has lists with OrdsN. The equations
of the seams are asked at all rows and columns, as LabelsAgree asks them.
-/
import Johnson.Road.Lane5TopL
import Johnson.Road.Rows.LayerStartLab

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open OnBytes.Model.Layer (Lay matIx)
open OnBytes.Road.Rows.Norms (numA labZ numA_labA mzA_labZ)

/-- **Every link is in order, and every copy is its original**, by list numbers. MG g: the list of
group g of layers; MA g: the list of the attention sub-proof of group g; MH: the head's list. -/
structure OrdsN (hL : Model.Layer.Shape) (sc : Model.Layer.Scales) (y : Lay)
    (hH : Model.Head.Shape) (L : Model.Head.HL) (nf : NormPar) (pol : AcceptancePolicy)
    (SA : ℕ → Attention.Shape) (Wz : Mat) (x : Instance ppref) (MG : ℕ → Mats ℤ) (MA : ℕ → Zs)
    (MH : Mats ℤ) : Prop where
  layer : ∀ g < 12, LayerOrd hL sc y g (MG g) Wz x
  att : ∀ g < 12, AttOrd (SA g) (MA g)
  head : Hd.HeadOrdLB hH L y nf pol Wz x MH
  seamFF : ∀ g, 0 < g → g < 12 → ∀ r c, MG g (matIx y).iXI r c = MG (g - 1) (matIx y).iXO r c
  seamA : ∀ g < 12, ∀ r c, MA g ((SA g).cf.NAs + 3) r c = MG g (matIx y).iQA r c
  seamH : ∀ r c, MH (hH.NHf + 3) r c = MG 11 (matIx y).iXO r c

/-- The number in the head's list that has the label lab. -/
def numH (h : Model.Head.Shape) (y : Lay) (lab : ℕ) : ℕ :=
  if lab = labA y (y.NGr - 1) (matIx y).iXO then h.NHf + 3 else lab - (1 + y.NGr) * 256

/-- The label of the stream that goes out of a group. -/
theorem labA_out (y : Lay) (g : ℕ) : labA y g (matIx y).iXO = (1 + g) * 256 + (matIx y).iXO :=
  if_neg fun h => xo_ne_xi y h.1

/-- numH undoes labH. -/
theorem numH_labH (h : Model.Head.Shape) (y : Lay) (n : ℕ) (hXO : (matIx y).iXO < 256)
    (hG : 0 < y.NGr) : numH h y (Hd.labH h y n) = n := by
  unfold numH Hd.labH
  by_cases h1 : n = h.NHf + 3
  · rw [if_pos h1, if_pos rfl]
    exact h1.symm
  · rw [if_neg h1, labA_out, if_neg (by omega)]
    omega

/-- The head's numbered matrices under the head's labels. -/
def labZH (h : Model.Head.Shape) (y : Lay) (Mh : Mats ℤ) : ℕ → ℕ → ℕ → ℤ :=
  fun lab r c => Mh (numH h y lab) r c

/-- Read back through the labels they are the numbered matrices. -/
theorem mzH_labZH (h : Model.Head.Shape) (y : Lay) (Mh : Mats ℤ) (hXO : (matIx y).iXO < 256)
    (hG : 0 < y.NGr) : Hd.mzH h y (labZH h y Mh) = Mh := by
  funext n r c
  show Mh (numH h y (Hd.labH h y n)) r c = Mh n r c
  rw [numH_labH h y n hXO hG]

/-- The 25 lists under their labels: sub-proof 24 is the head's; an even one below it a group's; of
an odd one, an attention sub-proof's, the one label that OrdsL reads is its copy of qa. -/
def zOf (hH : Model.Head.Shape) (y : Lay) (SA : ℕ → Attention.Shape) (MG : ℕ → Mats ℤ)
    (MA : ℕ → Zs) (MH : Mats ℤ) : ℕ → ℕ → ℕ → ℕ → ℤ := fun k =>
  if k = 24 then labZH hH y MH
  else if k % 2 = 0 then labZ y (k / 2) (MG (k / 2))
  else fun _ r c => MA (k / 2) ((SA (k / 2)).cf.NAs + 3) r c

section
variable (hH : Model.Head.Shape) (y : Lay) (SA : ℕ → Attention.Shape) (MG : ℕ → Mats ℤ)
  (MA : ℕ → Zs) (MH : Mats ℤ)

theorem zOf_even {g : ℕ} (hg : g < 12) : zOf hH y SA MG MA MH (2 * g) = labZ y g (MG g) := by
  unfold zOf
  rw [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega]

theorem zOf_odd (g : ℕ) :
    zOf hH y SA MG MA MH (2 * g + 1) = fun _ r c => MA g ((SA g).cf.NAs + 3) r c := by
  unfold zOf
  rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega]

theorem zOf_head : zOf hH y SA MG MA MH 24 = labZH hH y MH := if_pos rfl

end

/-- **The lists give the labelled matrices' statement.** -/
theorem ordsL_of_lists {hL : Model.Layer.Shape} {sc : Model.Layer.Scales} {y : Lay}
    {hH : Model.Head.Shape} {L : Model.Head.HL} {nf : NormPar} {pol : AcceptancePolicy}
    {SA : ℕ → Attention.Shape} {Wz : Mat} {x : Instance ppref} {MG : ℕ → Mats ℤ} {MA : ℕ → Zs}
    {MH : Mats ℤ} (hXO : (matIx y).iXO < 256) (h12 : y.NGr = 12)
    (O : OrdsN hL sc y hH L nf pol SA Wz x MG MA MH) :
    OrdsL hL sc y hH L nf pol SA Wz x (zOf hH y SA MG MA MH) MA where
  layer g hg := by
    rw [zOf_even hH y SA MG MA MH hg, mzA_labZ y g (MG g) hXO]
    exact O.layer g hg
  att := O.att
  qa g _ r c := by rw [zOf_odd hH y SA MG MA MH g]
  head := by
    rw [zOf_head, mzH_labZH hH y MH hXO (by omega)]
    exact O.head
  labels :=
    { ff := fun g h0 hg r c => by
        rw [zOf_even hH y SA MG MA MH hg, zOf_even hH y SA MG MA MH (show g - 1 < 12 by omega)]
        show MG g (numA y g (labA y (g - 1) (matIx y).iXO)) r c =
          MG (g - 1) (numA y (g - 1) (labA y (g - 1) (matIx y).iXO)) r c
        rw [← Hd.labA_in y h0, numA_labA y g _ hXO, Hd.labA_in y h0, numA_labA y (g - 1) _ hXO]
        exact O.seamFF g h0 hg r c
      att := fun g hg r c => by
        rw [zOf_odd hH y SA MG MA MH g, zOf_even hH y SA MG MA MH hg]
        show MA g ((SA g).cf.NAs + 3) r c = MG g (numA y g (labA y g (matIx y).iQA)) r c
        rw [numA_labA y g _ hXO]
        exact O.seamA g hg r c
      head := fun r c => by
        rw [zOf_head, show (22 : ℕ) = 2 * 11 from rfl,
          zOf_even hH y SA MG MA MH (show 11 < 12 by omega)]
        show MH (numH hH y (labA y 11 (matIx y).iXO)) r c =
          MG 11 (numA y 11 (labA y 11 (matIx y).iXO)) r c
        rw [numA_labA y 11 _ hXO]
        have e : numH hH y (labA y 11 (matIx y).iXO) = hH.NHf + 3 := by
          unfold numH
          rw [h12]
          exact if_pos rfl
        rw [e]
        exact O.seamH r c }

/-- **Back**: labelled matrices with OrdsL, read through the labels, are lists with OrdsN. -/
theorem lists_of_ordsL {hL : Model.Layer.Shape} {sc : Model.Layer.Scales} {y : Lay}
    {hH : Model.Head.Shape} {L : Model.Head.HL} {nf : NormPar} {pol : AcceptancePolicy}
    {SA : ℕ → Attention.Shape} {Wz : Mat} {x : Instance ppref} {Z : ℕ → ℕ → ℕ → ℕ → ℤ}
    {ZA : ℕ → Zs} (h12 : y.NGr = 12) (O : OrdsL hL sc y hH L nf pol SA Wz x Z ZA) :
    OrdsN hL sc y hH L nf pol SA Wz x (fun g => mzA y (Z (2 * g)) g) ZA (Hd.mzH hH y (Z 24)) where
  layer := O.layer
  att := O.att
  head := O.head
  seamFF g h0 hg r c := by
    show Z (2 * g) (labA y g (matIx y).iXI) r c =
      Z (2 * (g - 1)) (labA y (g - 1) (matIx y).iXO) r c
    rw [Hd.labA_in y h0]
    exact O.labels.ff g h0 hg r c
  seamA g hg r c := by
    show ZA g ((SA g).cf.NAs + 3) r c = Z (2 * g) (labA y g (matIx y).iQA) r c
    rw [← O.qa g hg r c]
    exact O.labels.att g hg r c
  seamH r c := by
    show Z 24 (Hd.labH hH y (hH.NHf + 3)) r c = Z (2 * 11) (labA y 11 (matIx y).iXO) r c
    have e : Hd.labH hH y (hH.NHf + 3) = labA y 11 (matIx y).iXO := by
      unfold Hd.labH
      rw [if_pos rfl, h12]
    rw [e]
    exact O.labels.head r c

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.ordsL_of_lists
#print axioms OnBytes.Road.L5.lists_of_ordsL
