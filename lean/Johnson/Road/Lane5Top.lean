-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5Top.lean

The premise of Lane5.lean, written a second time: in list numbers and labels in place of the
library's places. The plain head: the library's; the programs run the head with the cost ledger
(Lane5Ledger.lean, Lane5TopL.lean), not this one.

This file is a translation, not a step towards a proof file. The premise says three things of each
of 25 links (own cells small; every identity 0; every key in its table), and it has a seam. Here the
same is said of integer matrices that are numbered as the verifier's lists number the arrays of a
sub-proof. These matrices stand for the prover's hidden values behind a sub-proof's arrays; a
verifier holds none of them.
* "LayerOrd" (FormsKeysLinkL.lean), for the twelve groups of layers. It is equivalent to "small, and
  the link is in order" ("layerOrd_iff").
* "AttOrd" (Lane5AttDef.lean), for the twelve attention links. It is the library's relation
  "AttSeg.RFraw".
* "Hd.HeadOrdB" (HeadL5B.lean), for the head.
* The seam: each reader's copy has the entries of its owner's matrix. These are 24 families of
  equations between the matrices of two sub-proofs ("Hd.LabelsAgree", HeadSeam.lean) and 12 ties
  (the field "qa"). They are a hypothesis: they are the seam in other words.
Nothing is discharged: what is gained is the dictionary.

What the statements speak of beside a link's own matrices: one integer matrix Wz of weights, read by
the library's layout; the request x; the words of the scale file and nf; and the library's reference
tables ("tbRef"), not the verifier's.

Whose the numbering is. List numbers and labels are given by formulas of these files, through the
verifier's "matIx" and its two layouts. That they are the numbers, shapes and labels of the
verifier's own lists is shown by theorems that this file does not use (labA_tails, shape_tails_ref,
labH_of_public, group_label_qa). Which array, tensor and call stands where is the library's, by
definition of the three statements: a tensor or a call that the verifier places elsewhere is seen by
no theorem on this road.

The matrices. "Z k" are the matrices of link k, named by labels; of "Z (2 g + 1)" one label alone is
read. "ZA g" is the list of the attention link of group g, by number. The 36 families of equations
are asked at all rows and columns: the matrices are total functions, and whoever delivers them may
take them 0 outside their rows and columns.

Main definitions and theorems:
* "Ords": the 25 statements, the 12 ties and the 24 families of equations.
* "allMx": the library's matrices of all links, from Z and ZA ("Hd.D5", the dictionary by labels).
  Off the places of cells it holds whatever Z holds at the label that the formula names.
* "premise_of_ords": under eleven public hypotheses and e = 1,024, Ords gives the premise of
  Lane5.lean at the plain head. The three dictionaries are carried to the one by labels with
  "linkOK_congr" (Lane5Congr.lean).
* "reply_of_ords": so, besides at a lawful table, the matrix of an index, r = 1,023 and e = 1,024,
  the reply is the first choice of the integer model's logits at the last position.

The eleven public hypotheses, which this file takes as they are: the layers' layout returns y, and
four conditions on the layers' shape ("Switches", "Sized", "Sized2", p4); twelve groups; nine
numbers of the head's shape ("Hd.FullH"), and the head's layout returns L; for each group the sizes
of the attention link's shape ("AttSized"), that the table's shift is the shape's, and that the
shape's table of exponentials is the library's. The letters hL, pc, y, hH, tau, L, sc, nf, SA are
free: nothing here says that they come from one parameter file.

Not claimed: that a proof file which a verifier accepts has matrices with Ords; all that the
imported files do not claim. That Ords can be met: Lane5TopMet.lean.
-/
import Johnson.Road.Lane5Plain
import Johnson.Road.Lane5Congr
import Johnson.Road.FormsKeysLinkL
import Johnson.Road.FormsKeysDictD
import Johnson.Road.HeadL5B
import Johnson.Road.HeadSeam
import Johnson.Road.HeadSeam24
import Johnson.Road.Lane5AttLink
import Johnson.Road.Lane5AttD5

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open OnBytes.Model.Layer (Lay matIx)

/-- Attention's own segments, from the attention links' lists: the letter At of the dictionary by
labels. -/
def atOf (SA : ℕ → Attention.Shape) (ZA : ℕ → Zs) : ℕ → ℕ → ℕ → ℤ :=
  fun g r c => attMx (SA g) g (ZA g) (2 * g + 1) r c

/-- **The library's matrices of all links**, from the matrices Z k of link k, named by labels, and
the attention links' lists ZA g. -/
def allMx (hH : Model.Head.Shape) (y : Lay) (SA : ℕ → Attention.Shape) (ZA : ℕ → Zs)
    (Z : ℕ → ℕ → ℕ → ℕ → ℤ) : ℕ → Mx :=
  fun k => Hd.D5 hH y (atOf SA ZA) (Z k)

/-- **Every link is in order, and every copy is its original**, said of integer matrices that are
numbered as the verifier's lists number a sub-proof's arrays. The plain head. -/
structure Ords (hL : Model.Layer.Shape) (sc : Model.Layer.Scales) (y : Lay)
    (hH : Model.Head.Shape) (L : Model.Head.HL) (nf : NormPar) (SA : ℕ → Attention.Shape)
    (Wz : Mat) (x : Instance ppref) (Z : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs) : Prop where
  layer : ∀ g < 12, LayerOrd hL sc y g (mzA y (Z (2 * g)) g) Wz x
  att : ∀ g < 12, AttOrd (SA g) (ZA g)
  qa : ∀ g < 12, ∀ r c,
    Z (2 * g + 1) (labA y g (matIx y).iQA) r c = ZA g ((SA g).cf.NAs + 3) r c
  head : Hd.HeadOrdB hH L y nf Wz x (Hd.mzH hH y (Z 24))
  labels : Hd.LabelsAgree y Z

section Top

variable {hL : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
  {hH : Model.Head.Shape} {tau : Array F} {L : Model.Head.HL} {sc : Model.Layer.Scales}
  {nf : NormPar} {SA : ℕ → Attention.Shape} {Wz : Mat} {x : Instance ppref}
  {Z : ℕ → ℕ → ℕ → ℕ → ℤ} {ZA : ℕ → Zs}

/-- **Under eleven public hypotheses and e = 1,024, Ords gives the premise at the plain head.** -/
theorem premise_of_ords (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hSA : ∀ g < 12, AttSized (SA g))
    (hsh : ∀ g < 12, ((scalesOf hL sc nf).kap (4 * g)).sh = (SA g).cf.sh.getD 0 0)
    (hE : ∀ g < 12, ∀ ι : ℕ, ι < (SA g).u0 → (((SA g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (he : x.e = 1024) (O : Ords hL sc y hH L nf SA Wz x Z ZA) :
    Premise Cm.Seg.Hd.plain (Cm.Seg.TS.segM (scalesOf hL sc nf)) Wz x (allMx hH y SA ZA Z) := by
  refine ⟨fun k hk => ?_,
    Hd.seam_reads Cm.Seg.Hd.plain hH (fun _ => atOf SA ZA) O.labels⟩
  rcases Cm.Seg.seg_cases hk with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
  · exact linkOK_congr (laws_plain _) hk
      (dict_D5 hy S Zd Z2 hp4 hH Cm.Seg.Hd.plain (atOf SA ZA) (Z (2 * g)) hg)
      (linkOK_layer hy S Zd Z2 hp4 Cm.Seg.Hd.plain hg nf (O.layer g hg))
  · exact linkOK_congr (laws_plain _) hk
      (attMx_D5 Cm.Seg.Hd.plain hH y (SA g) hg (ZA g) (atOf SA ZA) (Z (2 * g + 1))
        (fun _ _ => rfl) (O.qa g hg))
      (linkA_of_ord hg (hSA g hg) (hsh g hg) (hE g hg) (O.att g hg) Wz x)
  · exact linkOK_congr (laws_plain _) hk
      (Hd.headMx_D5 Cm.Seg.Hd.plain hH h12 (atOf SA ZA) (Z 24))
      (Hd.linkOK_24B hF hLy hy S Zd Z2 (s := scalesOf hL sc nf) he O.head)

/-- **So, at a lawful table, the matrix of an index, r = 1,023 and e = 1,024, the reply is the first
choice of the integer model's logits at the last position.** -/
theorem reply_of_ords {i : Cm.Idx} (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hSA : ∀ g < 12, AttSized (SA g))
    (hsh : ∀ g < 12, ((scalesOf hL sc nf).kap (4 * g)).sh = (SA g).cf.sh.getD 0 0)
    (hE : ∀ g < 12, ∀ ι : ℕ, ι < (SA g).u0 → (((SA g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (hs : (scalesOf hL sc nf).Lawful) (hr : x.r = 1023) (he : x.e = 1024)
    (O : Ords hL sc y hH L nf SA i.mat x Z ZA) (pol : AcceptancePolicy) :
    RinfR ppref (scalesOf hL sc nf).kap (scalesOf hL sc nf).nf (fun _ => tbRef) pol i.index x :=
  reply_first hs hr he (premise_of_ords hy S Zd Z2 hp4 h12 hF hLy hSA hsh hE he O) pol

end Top

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.premise_of_ords
#print axioms OnBytes.Road.L5.reply_of_ords
