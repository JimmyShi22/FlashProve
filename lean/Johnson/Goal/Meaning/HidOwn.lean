-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidOwn.lean: the hidden values of Johnson/Goal/Meaning/Row.lean, made from one
list of matrices for each sub-proof (Part B: the list behind its committed symbols), so that the
three clauses on seams hold by the make.

Means (Johnson/Goal/Meaning/Row.lean) has 14 clauses. Three of them are seams: they say that an
array which one sub-proof borrows is the array of the sub-proof that owns it (LaySeam, AttSeam), and
that the head's last stream is the one that the last group's list holds (HeadSeam). Whoever lays a
map from a witness to Hid may choose how a borrowed array is read. Here it is read IN ITS OWNER'S
LIST.

PART A. own k: the list of integer matrices of sub-proof k (2 g: group g of layers; 2 g + 1: its
attention sub-proof), a letter.
  mgOf, maOf, hidOf   the make. Group g's list is own (2 g), but number iXI of a later group is
             number iXO of own (2 (g - 1)). Attention's list is own (2 g + 1), but number NAs + 3 is
             number iQA of own (2 g). The head's stream is lastOf at group 11's list.
  laySeam_hidOf, attSeam_hidOf, headSeam_hidOf   the three seams, for every own.
  MeansOwn, means_hidOf_iff   Means at hidOf is the eleven other clauses.
  ownG_of_ord, ownA_of_ord (and back), ownA_congr   the library's records LayerOrd and AttOrd give
             the five clauses each; attention's five read the cells of valid names alone.
  attSmall_congr, attKey_congr, attOwn1_congr, attOwn2_congr, attRidden_congr   the same, one clause
             at a time.
  OneWord, OwnApart, mgOf_seen, maOf_seen, ownA_maOf, oneWord_of_seen, means_of_seen   WHERE THE
             DEBT GOES. See below.
  byLab, mgOf_lab, maOf_lab, maOf_plan   the make follows the labels of the verifier's own plans.
PART B. own from committed symbols.
  ownOf s y k   mzTot (mzAt (y k)): the small integers whose packing the symbols y k are
             (Cb/Pv/Tail/Unique.lean: cellsOf; Johnson/Road/Rows/HeadBase.lean: mzAt), as matrices
             on all numbers (Johnson/Road/Rows/LayerStart.lean: mzTot).
  ownOf_unique   under BaseAt (y k) Mz and the three inequalities Size.Uniq, ownOf s y k is mzTot
    Mz.
  ownOf_matsOf, ownOf_zsOf, small_ownOf   the library's two other total forms against it; smallness.

WHICH ENTRIES ARE BORROWED, in the verifier's own text. A group of layers: number iXI alone, from
the second group on (OnBytes/Model/LayerPlan.lean: tailsOf; the formula labA,
Johnson/Road/FormsKeysDictA.lean, with labA_tails). An attention sub-proof: number NAs + 3 alone:
the parts of as, ah, ao and bA are of kind 0, qa is of kind 1 (OnBytes/Model/AttentionPlan.lean:
matrices). The head: entry NHf + 3, which bears the label of the last group's iXO
(Johnson/Road/HeadDict.lean: labH).

WHAT IS NOT CLAIMED, AND WHERE THE DEBT GOES.
- THE SEAMS ARE NOT PAID FOR: THEY ARE MOVED. A sub-proof's law speaks of the list as that sub-proof
  reads it, its copies of borrowed arrays among them (att_ord_base,
  Johnson/Road/Rows/AttStartBase.lean, concludes at all numbers of one signature, number NAs + 3
  too). hidOf's lists have the owner's array at these numbers. To carry a law of a group of layers
  or of an attention sub-proof from its own reading to hidOf's lists one needs that reader and owner
  read one array: OneWord, 23 equations: 11 of matrices, 12 at the places of borrowed names (the
  library's Hd.LabelsAgree without the head's, by list numbers). No theorem derives it from a run or
  from the commitments (oneWord_of_seen here and oneWord_of_means in
  Johnson/Goal/Meaning/HidOwnGuard.lean only restate it): it is a matter of the commitments (one
  committed word, read twice).
- THE FENCE. Were all 23 equations asked at all rows and columns, the 12 on qa could not be paid
  from what the caller of the library's law on an attention sub-proof holds: that law concludes at
  zsOf pl Mz, which reads some real cell outside the sizes too, while a group's list is 0 there. So
  these 12 are asked at the places of the valid names of borrowed cells alone, and attention's
  clauses are carried by ownA_congr in place of an equation of functions. THE FENCE TAKES THE SIZES
  OUT OF THE STATEMENT, NOT OUT OF THE PAYMENT: whoever pays the 12 at zsOf pl Mz against a group's
  mzTot still needs that each borrowed name's place lies within attention's sizes (PlaceOK binds pl
  there alone) and within the group's sizes of qa (outside them mzTot is 0), and that the committed
  cells are the same there: the premises of oneWord_zsOf (Johnson/Goal/Meaning/HidZs.lean).
  oneWord_ownOf (Johnson/Goal/Meaning/HidWord.lean) gives OneWord at ownOf.
- THE 11 EQUATIONS ON THE STREAM ARE NOT FENCED: both sides are
  lists of groups of layers, which the library's law has as mzTot, 0 outside the sizes, so they can
  be paid where reader's and owner's sizes agree (by its text tailsOf gives the two streams one
  size; that a signature follows the plans is the premise Follows of
  Johnson/Goal/Meaning/HidPlan.lean). To fence them one would need that the five clauses of OwnG
  read valid names alone. The library has that for the keys (Johnson/Road/FormsKeysValid.lean); for
  the identities Johnson/Road/FormsKeysIdn.lean speaks of matrices that hold the cells at valid
  names, and whether that gives such a congruence is not worked out.
- means_of_seen has a public premise: OwnApart (no own cell of attention lies in number NAs + 3).
- THE HEAD'S SEAM IS OWED SEPARATELY, in two steps that OneWord does not cover: that the head's copy
  (entry NHf + 3 of its own list) is the last group's number iXO, and that the head's rule for
  reading the stream in its copy gives lastOf, which reads by the groups' rule. Here HeadPlain stays
  a clause at lastOf at group 11's list. The two steps are stated in
  Johnson/Goal/Meaning/HidHead.lean (HeadWord, the 24th equation, concluded by no theorem;
  lastIn_head, proved).
- That hidOf's lists are what any extractor gives; that the signatures s k are those of the plans.
- ownOf at symbols that are the packing of nothing small is 0 there (cellsOf); nothing is said then.
- Where seen (2 g + 1) is ownOf and not zsOf: the library's law on an attention sub-proof
  (att_ord_base) concludes at zsOf pl Mz, not at mzTot Mz. Outside the sizes ownOf is 0, while zsOf
  reads whatever cell its map of places names: the two agree within the sizes alone (ownOf_zsOf).
  The bridge is in Johnson/Goal/Meaning/HidLaws.lean (attOrd_ownOf), under PlaceOK and a named
  public premise: every valid name's place lies within the sizes. The layers have no such gap
  (layer_start_base concludes at mzTot Mz).
Nothing on probabilities or on hiding. The program does not import this file.
-/
import Johnson.Goal.Meaning.Row
import Johnson.Road.Rows.AttStartBase
import Johnson.Road.Rows.HeadBase
import Johnson.Road.Lane5AttPub
import Johnson.Road.Lane5AttValid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open Inst.Model.AttSeg (Raw)

/-! ## Part A. The make -/

/-- The list of group g of layers: its own; but the stream that comes into a later group is read in
the list of the group before, which owns it. -/
def mgOf (y : Lay) (own : ℕ → Mats ℤ) (g : ℕ) : Mats ℤ := fun a =>
  if a = (matIx y).iXI ∧ 0 < g then own (2 * (g - 1)) (matIx y).iXO else own (2 * g) a

/-- The list of the attention sub-proof of group g: its own; but qa is read in the list of its
group, which owns it. -/
def maOf (X : Model.Verify.Public) (own : ℕ → Mats ℤ) (g : ℕ) : Zs := fun a =>
  if a = (Hd.shapeA X g).cf.NAs + 3 then own (2 * g) (matIx X.y).iQA else own (2 * g + 1) a

/-- **The hidden values, from each sub-proof's own arrays.** -/
def hidOf (X : Model.Verify.Public) (tok : Fin ppref.V) (own : ℕ → Mats ℤ) : Hid where
  tok := tok
  MG := mgOf X.y own
  MA := maOf X own
  Xl := lastOf X.y (mgOf X.y own 11)

/-- qa and the stream that comes in have different numbers in the list. -/
theorem qa_ne_xi (y : Lay) : (matIx y).iQA ≠ (matIx y).iXI := by
  show y.parts.getD 0 0 + y.parts.getD 1 0 + 2 ≠ y.parts.getD 0 0 + y.parts.getD 1 0 + 4
  omega

section Seams
variable (X : Model.Verify.Public) (tok : Fin ppref.V) (own : ℕ → Mats ℤ)

/-- **The layers' seam holds by the make.** -/
theorem laySeam_hidOf (g : ℕ) : LaySeam X.y (hidOf X tok own).MG g := by
  intro hg r c
  show mgOf X.y own g (matIx X.y).iXI r c = mgOf X.y own (g - 1) (matIx X.y).iXO r c
  unfold mgOf
  rw [if_pos ⟨rfl, hg⟩, if_neg fun h => xo_ne_xi X.y h.1]

/-- **Attention's seam holds by the make.** -/
theorem attSeam_hidOf (g : ℕ) :
    AttSeam X.y (Hd.shapeA X g) ((hidOf X tok own).MG g) ((hidOf X tok own).MA g) := by
  intro r c
  show maOf X own g ((Hd.shapeA X g).cf.NAs + 3) r c = mgOf X.y own g (matIx X.y).iQA r c
  unfold maOf mgOf
  rw [if_pos rfl, if_neg fun h => qa_ne_xi X.y h.1]

/-- **The head's seam holds by the make.** -/
theorem headSeam_hidOf : HeadSeam X.y ((hidOf X tok own).MG 11) (hidOf X tok own).Xl :=
  fun _ _ _ _ => rfl

end Seams

/-- The five clauses of a group of layers that are left. -/
structure OwnG (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) (Mg : Mats ℤ) (g : ℕ) :
    Prop where
  small : SmallM X.y Mg
  norm : NormField (layerShape X.P) X.layers.sc X.y g Mg i.mat x
  hot : HotField (layerShape X.P) X.layers.sc X.y g Mg i.mat x
  emb : EmbField (layerShape X.P) X.layers.sc X.y g Mg i.mat x
  key : KeyField (layerShape X.P) X.layers.sc X.y g Mg i.mat

/-- The five clauses of an attention sub-proof that are left. -/
structure OwnA (S : Attention.Shape) (Za : Zs) : Prop where
  small : AttSmall S Za
  key : AttKey S Za
  own1 : AttOwn1 S Za
  own2 : AttOwn2 S Za
  ridden : AttRidden S Za

/-- **The eleven clauses that are left**, at the lists that hidOf makes of own. -/
structure MeansOwn (X : Model.Verify.Public) (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref)
    (own : ℕ → Mats ℤ) : Prop where
  layers : ∀ g < 12, OwnG X i x (mgOf X.y own g) g
  attention : ∀ g < 12, OwnA (Hd.shapeA X g) (maOf X own g)
  head : HeadPlain pp i x (lastOf X.y (mgOf X.y own 11))

/-- **Means at hidOf is the eleven clauses.** -/
theorem means_hidOf_iff {X : Model.Verify.Public} {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref}
    {tok : Fin ppref.V} {own : ℕ → Mats ℤ} :
    Means X pp i x (hidOf X tok own) ↔ MeansOwn X pp i x own := by
  constructor
  · intro M
    exact ⟨fun g hg => ⟨(M.layers g hg).small, (M.layers g hg).norm, (M.layers g hg).hot,
        (M.layers g hg).emb, (M.layers g hg).key⟩,
      fun g hg => ⟨(M.attention g hg).small, (M.attention g hg).key, (M.attention g hg).own1,
        (M.attention g hg).own2, (M.attention g hg).ridden⟩, M.head.plain⟩
  · intro O
    exact ⟨fun g hg => ⟨(O.layers g hg).small, (O.layers g hg).norm, (O.layers g hg).hot,
        (O.layers g hg).emb, (O.layers g hg).key, laySeam_hidOf X tok own g⟩,
      fun g hg => ⟨(O.attention g hg).small, (O.attention g hg).key, (O.attention g hg).own1,
        (O.attention g hg).own2, (O.attention g hg).ridden, attSeam_hidOf X tok own g⟩,
      ⟨headSeam_hidOf X tok own, O.head⟩⟩

/-! ## The library's records and the clauses -/

/-- The library's record on a group of layers gives the five clauses. -/
theorem ownG_of_ord {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {Mg : Mats ℤ}
    {g : ℕ} (O : LayerOrd (layerShape X.P) X.layers.sc X.y g Mg i.mat x) : OwnG X i x Mg g := by
  obtain ⟨a, b, c, d, e⟩ := layer_fields O
  exact ⟨a, b, c, d, e⟩

theorem ord_of_ownG {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {Mg : Mats ℤ}
    {g : ℕ} (O : OwnG X i x Mg g) : LayerOrd (layerShape X.P) X.layers.sc X.y g Mg i.mat x :=
  layer_start O.small O.norm O.hot O.emb O.key

/-- **The library's record on an attention sub-proof gives the five clauses.** -/
theorem ownA_of_ord {S : Attention.Shape} {Za : Zs} (O : AttOrd S Za) : OwnA S Za :=
  ⟨O.rel.1, O.rel.2.1, fun k b g' n hv => O.rel.2.2 (.at1 k b g' n) hv,
    fun b g' n hv => O.rel.2.2 (.at2 b g' n) hv, fun b g' n hv => O.rel.2.2 (.at3 b g' n) hv⟩

theorem ord_of_ownA {S : Attention.Shape} {Za : Zs} (O : OwnA S Za) : AttOrd S Za :=
  ⟨⟨O.small, O.key, fun j hj => by
    cases j with
    | at1 k b g' n => exact O.own1 k b g' n hj
    | at2 b g' n => exact O.own2 b g' n hj
    | at3 b g' n => exact O.ridden b g' n hj⟩⟩

/-- **The five clauses of an attention sub-proof read the cells of valid names alone**: two lists
that agree at the place addrA S c of every valid name c meet them together. A corollary of the
library's rfraw_valid (Johnson/Road/Lane5AttValid.lean). -/
theorem ownA_congr {S : Attention.Shape} {Za Za' : Zs}
    (H : ∀ c : Raw, c.Valid (dimOf S) → zAt Za (addrA S c) = zAt Za' (addrA S c)) :
    OwnA S Za ↔ OwnA S Za' :=
  ⟨fun O => ownA_of_ord ⟨V.rfraw_valid (scl := sclOf S) H (ord_of_ownA O).rel⟩,
    fun O => ownA_of_ord
      ⟨V.rfraw_valid (scl := sclOf S) (fun c hc => (H c hc).symm) (ord_of_ownA O).rel⟩⟩

/-- The same, ONE CLAUSE AT A TIME (for a caller that comes with one clause): by the library's
keyVec_agree and idnVal_agree (Johnson/Road/Lane5AttValid.lean). -/
theorem castT_agree {S : Attention.Shape} {Za Za' : Zs}
    (H : ∀ c : Raw, c.Valid (dimOf S) → zAt Za (addrA S c) = zAt Za' (addrA S c)) :
    V.AgreeD (dimOf S) (AttSeg.castT (cellsA S Za) : Raw → Cb.Gl.F) (AttSeg.castT (cellsA S Za')) :=
  fun c hc => by
    show ((zAt Za (addrA S c) : ℤ) : Cb.Gl.F) = ((zAt Za' (addrA S c) : ℤ) : Cb.Gl.F)
    rw [H c hc]

section Clause
variable {S : Attention.Shape} {Za Za' : Zs}
  (H : ∀ c : Raw, c.Valid (dimOf S) → zAt Za (addrA S c) = zAt Za' (addrA S c))
include H

theorem attSmall_congr (O : AttSmall S Za) : AttSmall S Za' := fun c hc => by
  show |zAt Za' (addrA S c)| < 2 ^ 18
  rw [← H c hc]
  exact O c hc

theorem attKey_congr (O : AttKey S Za) : AttKey S Za' := fun c n hn => by
  rw [← V.keyVec_agree (scl := sclOf S) (castT_agree H) (tbOf S) c n]
  exact O c n hn

theorem attOwn1_congr (O : AttOwn1 S Za) : AttOwn1 S Za' := fun k b g' n hv => by
  rw [← V.idnVal_agree (castT_agree H) hv]
  exact O k b g' n hv

theorem attOwn2_congr (O : AttOwn2 S Za) : AttOwn2 S Za' := fun b g' n hv => by
  rw [← V.idnVal_agree (castT_agree H) hv]
  exact O b g' n hv

theorem attRidden_congr (O : AttRidden S Za) : AttRidden S Za' := fun b g' n hv => by
  rw [← V.idnVal_agree (castT_agree H) hv]
  exact O b g' n hv

end Clause

/-! ## Where the debt goes: reader and owner read one array -/

/-- **Reader and owner read one array.** seen k: the list of sub-proof k as that sub-proof itself
reads it, its copies of borrowed arrays among them.
ff: a later group's copy of the stream against the group before, AT ALL ROWS AND COLUMNS: so reader
and owner have to agree outside the sizes too. They do where both lists are 0 there and the sizes
agree; the library's law on a group of layers concludes at such lists (mzTot: layer_start_base).
att: an attention sub-proof's copy of qa against its group, FENCED: at the places of the valid names
of borrowed cells alone (Raw.Own c = false: qry, out, key, val). Nothing is asked outside these
places, where the library's zsOf pl Mz reads some real cell and mzTot reads 0. What a payer still
needs: the file's head, "THE FENCE". -/
structure OneWord (X : Model.Verify.Public) (seen : ℕ → Mats ℤ) : Prop where
  ff : ∀ g, 0 < g → g < 12 → ∀ r c,
    seen (2 * g) (matIx X.y).iXI r c = seen (2 * (g - 1)) (matIx X.y).iXO r c
  att : ∀ g < 12, ∀ c : Raw, c.Valid (dimOf (Hd.shapeA X g)) → c.Own = false →
    zAt (seen (2 * g + 1)) (addrA (Hd.shapeA X g) c) =
      seen (2 * g) (matIx X.y).iQA (addrA (Hd.shapeA X g) c).2.1 (addrA (Hd.shapeA X g) c).2.2

/-- A borrowed cell has its place in number NAs + 3 of the list. -/
theorem addrA_borrowed (S : Attention.Shape) {c : Raw} (h : c.Own = false) :
    (addrA S c).1 = S.cf.NAs + 3 := by
  cases c <;> first | rfl | exact Bool.noConfusion (h : true = false)

/-- The equations at all rows and columns give the fenced ones. -/
theorem OneWord.of_all {X : Model.Verify.Public} {seen : ℕ → Mats ℤ}
    (ff : ∀ g, 0 < g → g < 12 → ∀ r c,
      seen (2 * g) (matIx X.y).iXI r c = seen (2 * (g - 1)) (matIx X.y).iXO r c)
    (att : ∀ g < 12, ∀ r c,
      seen (2 * g + 1) ((Hd.shapeA X g).cf.NAs + 3) r c = seen (2 * g) (matIx X.y).iQA r c) :
    OneWord X seen :=
  ⟨ff, fun g hg c _ ho => by
    unfold zAt
    rw [addrA_borrowed _ ho]
    exact att g hg _ _⟩

/-- A public premise: no valid name of an attention sub-proof's OWN cell has its place in number NAs
+ 3 of the list. (By its text addrA lays ah's cells in number NAs and ao's in NAs + 1; a cell of as
lies in part number n / 2^lmS / (kAs / NAs), which hangs on the shape's numbers. In scope:
ownApart_of_core, Johnson/Goal/Meaning/HidLaws.lean.) -/
def OwnApart (S : Attention.Shape) : Prop :=
  ∀ c : Raw, c.Valid (dimOf S) → c.Own = true → (addrA S c).1 ≠ S.cf.NAs + 3

section Seen
variable {X : Model.Verify.Public} {seen : ℕ → Mats ℤ}

/-- Under OneWord the list that hidOf makes for a group is the list as the group's sub-proof reads
it. -/
theorem mgOf_seen (A : OneWord X seen) {g : ℕ} (hg : g < 12) : mgOf X.y seen g = seen (2 * g) := by
  funext a r c
  unfold mgOf
  by_cases h : a = (matIx X.y).iXI ∧ 0 < g
  · rw [if_pos h, h.1]
    exact (A.ff g h.2 hg r c).symm
  · rw [if_neg h]

/-- Under OneWord the list that hidOf makes for an attention sub-proof has, at the place of every
valid name, what the sub-proof itself reads there. -/
theorem maOf_seen (A : OneWord X seen) {g : ℕ} (hg : g < 12) (hO : OwnApart (Hd.shapeA X g))
    (c : Raw) (hc : c.Valid (dimOf (Hd.shapeA X g))) :
    zAt (maOf X seen g) (addrA (Hd.shapeA X g) c) =
      zAt (seen (2 * g + 1)) (addrA (Hd.shapeA X g) c) := by
  cases ho : c.Own with
  | false =>
    rw [A.att g hg c hc ho]
    unfold zAt maOf
    rw [if_pos (addrA_borrowed _ ho)]
  | true =>
    unfold zAt maOf
    rw [if_neg (hO c hc ho)]

/-- Where the equation on qa holds at all rows and columns, the two lists are one. -/
theorem maOf_of_all {g : ℕ} (att : ∀ r c,
    seen (2 * g + 1) ((Hd.shapeA X g).cf.NAs + 3) r c = seen (2 * g) (matIx X.y).iQA r c) :
    maOf X seen g = seen (2 * g + 1) := by
  funext a r c
  unfold maOf
  by_cases h : a = (Hd.shapeA X g).cf.NAs + 3
  · rw [if_pos h, h]
    exact (att r c).symm
  · rw [if_neg h]

/-- So the five clauses hold at the one list exactly if they hold at the other. -/
theorem ownA_maOf (A : OneWord X seen) {g : ℕ} (hg : g < 12) (hO : OwnApart (Hd.shapeA X g)) :
    OwnA (Hd.shapeA X g) (maOf X seen g) ↔ OwnA (Hd.shapeA X g) (seen (2 * g + 1)) :=
  ownA_congr (maOf_seen A hg hO)

/-- And OneWord is no more than the carrying needs: if hidOf's lists are the sub-proofs' own
readings, reader and owner read one array. -/
theorem oneWord_of_seen (hG : ∀ g < 12, mgOf X.y seen g = seen (2 * g))
    (hA : ∀ g < 12, maOf X seen g = seen (2 * g + 1)) : OneWord X seen := by
  refine OneWord.of_all (fun g h0 hg r c => ?_) fun g hg r c => ?_
  · rw [← hG g hg]
    unfold mgOf
    rw [if_pos ⟨rfl, h0⟩]
  · rw [← hA g hg]
    unfold maOf
    rw [if_pos rfl]

/-- **From each group's and each attention sub-proof's clauses at its own reading, OneWord, and the
head's clause at the stream that group 11's own list holds, to Means at hidOf.** The step to that
clause from the head's own copy is owed: see the file's head and Johnson/Goal/Meaning/HidHead.lean.
-/
theorem means_of_seen {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref} (tok : Fin ppref.V)
    (A : OneWord X seen) (hO : ∀ g < 12, OwnApart (Hd.shapeA X g))
    (G : ∀ g < 12, OwnG X i x (seen (2 * g)) g)
    (At : ∀ g < 12, OwnA (Hd.shapeA X g) (seen (2 * g + 1)))
    (H : HeadPlain pp i x (lastOf X.y (seen 22))) : Means X pp i x (hidOf X tok seen) :=
  means_hidOf_iff.mpr
    ⟨fun g hg => by rw [mgOf_seen A hg]; exact G g hg,
      fun g hg => (ownA_maOf A hg (hO g hg)).mpr (At g hg),
      by rw [mgOf_seen A (by norm_num : 11 < 12)]; exact H⟩

end Seen

/-! ## The make follows the labels of the verifier's plans -/

/-- The sub-proofs' own arrays under the labels that the plans give to owned arrays of the groups of
layers: label 256 (1 + g) + n is number n of group g's list. -/
def byLab (own : ℕ → Mats ℤ) : ℕ → ℕ → ℕ → ℤ := fun lab => own (2 * (lab / 256 - 1)) (lab % 256)

/-- **A group's list, as hidOf makes it, is the arrays under the labels of the group's list in the
verifier's plan** (labA; labA_tails, Johnson/Road/FormsKeysDictA.lean, holds it against tailsOf). -/
theorem mgOf_lab (y : Lay) (own : ℕ → Mats ℤ) (g : ℕ) {a : ℕ} (h : (matIx y).iXO < 256)
    (ha : a < 256) : mgOf y own g a = mzA y (byLab own) g a := by
  show mgOf y own g a = byLab own (labA y g a)
  unfold mgOf byLab labA
  by_cases h1 : a = (matIx y).iXI ∧ 0 < g
  · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩,
      show (g * 256 + (matIx y).iXO) / 256 - 1 = g - 1 by omega,
      show (g * 256 + (matIx y).iXO) % 256 = (matIx y).iXO by omega]
  · rw [if_neg h1, if_neg (fun hh => h1 ⟨hh.1, by omega⟩),
      show ((1 + g) * 256 + a) / 256 - 1 = g by omega, show ((1 + g) * 256 + a) % 256 = a by omega]

/-- Attention's copy of qa, as hidOf makes it, is the array under the label of the group's qa. -/
theorem maOf_lab (X : Model.Verify.Public) (own : ℕ → Mats ℤ) (g : ℕ)
    (h : (matIx X.y).iQA < 256) :
    maOf X own g ((Hd.shapeA X g).cf.NAs + 3) = byLab own (labA X.y g (matIx X.y).iQA) := by
  unfold maOf byLab labA
  rw [if_pos rfl, if_neg (fun hh => qa_ne_xi X.y hh.1),
    show ((1 + g) * 256 + (matIx X.y).iQA) / 256 - 1 = g by omega,
    show ((1 + g) * 256 + (matIx X.y).iQA) % 256 = (matIx X.y).iQA by omega]

/-- **And that label is the one which the plan X.A[g] itself gives to number NAs + 3 of its list.**
-/
theorem maOf_plan {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (hX : publicOf pol KL lay = .ok X) (hp4 : (layerShape X.P).p4 = true) {g : ℕ}
    (hg : g < X.y.NGr) (h : (matIx X.y).iQA < 256) (own : ℕ → Mats ℤ) :
    ∃ Ag lab, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      (Ag.seam.tl.mats[Ag.S.cf.NAs + 3]?).map (fun M => M.aId) = some lab ∧
      maOf X own g ((Hd.shapeA X g).cf.NAs + 3) = byLab own lab := by
  obtain ⟨Ag, h1, h2, h3⟩ := label_public hX hp4 hg
  exact ⟨Ag, _, h1, h2, h3, maOf_lab X own g h⟩

/-! ## Part B. The sub-proofs' own arrays, from the committed symbols -/

open Cb.Pv.Tail (Size Syms JCell BaseAt Base)

/-- **The list of sub-proof k, from its committed symbols**: the small integers whose packing the
symbols are, as matrices on all numbers. s k: the sizes of sub-proof k's signature. -/
noncomputable def ownOf (s : ℕ → Size) (y : ∀ k, Syms Cb.Gl.E (s k)) : ℕ → Mats ℤ := fun k =>
  mzTot (Rows.mzAt (y k))

section Own
variable {s : ℕ → Size} {y : ∀ k, Syms Cb.Gl.E (s k)} {k : ℕ}

/-- **The symbols name the list**: whatever integers stand behind them by BaseAt are ownOf. -/
theorem ownOf_unique (p : ℕ) [CharP Cb.Gl.E p] (hu : (s k).Uniq p)
    {Mz : ∀ μ : Fin (s k).NM, Fin ((s k).k μ) → Fin ((s k).m μ) → ℤ} (h : BaseAt (y k) Mz) :
    ownOf s y k = mzTot Mz := by
  unfold ownOf Rows.mzAt
  rw [← Cb.Pv.Tail.baseAt_unique p hu h]

/-- The head's file has the same total matrices under another name. -/
theorem ownOf_matsOf : Rows.matsOf (s k) (Rows.mzAt (y k)) = ownOf s y k := by
  funext a r c
  unfold Rows.matsOf ownOf mzTot
  by_cases h : a < (s k).NM
  · by_cases hc : c < (s k).k (⟨a, h⟩ : Fin (s k).NM)
    · by_cases hr : r < (s k).m (⟨a, h⟩ : Fin (s k).NM)
      · rw [dif_pos ⟨h, hc, hr⟩, dif_pos h, dif_pos hc, dif_pos hr]
      · rw [dif_neg (fun hh => hr hh.2.2), dif_pos h, dif_pos hc, dif_neg hr]
    · rw [dif_neg (fun hh => hc hh.2.1), dif_pos h, dif_neg hc]
  · rw [dif_neg (fun hh => h hh.1), dif_neg h]

/-- Attention's file numbers the integers through a map of places: within the sizes, under PlaceOK,
it gives the same entries. -/
theorem ownOf_zsOf {pl : ℕ → ℕ → ℕ → JCell (s k)} (hp : Rows.PlaceOK pl) (μ : Fin (s k).NM)
    (c : Fin ((s k).k μ)) (r : Fin ((s k).m μ)) :
    Rows.zsOf pl (Rows.mzAt (y k)) μ.val r.val c.val = ownOf s y k μ.val r.val c.val := by
  rw [Rows.zsOf_at hp]
  unfold ownOf mzTot
  rw [dif_pos μ.isLt, dif_pos c.isLt, dif_pos r.isLt]

/-- If the symbols are the packing of small integers, the list's entries are small. -/
theorem small_ownOf (hB : Base (y k)) (hβ : 2 * ((s k).beta : ℤ) ≤ 2 ^ 18) (yl : Lay) :
    SmallM yl (ownOf s y k) :=
  small_mzTot ((Rows.baseAt_mzAt (y k)).mpr hB) hβ yl

end Own

end Meaning

#print axioms Meaning.qa_ne_xi
#print axioms Meaning.laySeam_hidOf
#print axioms Meaning.attSeam_hidOf
#print axioms Meaning.headSeam_hidOf
#print axioms Meaning.means_hidOf_iff
#print axioms Meaning.ownG_of_ord
#print axioms Meaning.ord_of_ownG
#print axioms Meaning.ownA_of_ord
#print axioms Meaning.ord_of_ownA
#print axioms Meaning.ownA_congr
#print axioms Meaning.castT_agree
#print axioms Meaning.attSmall_congr
#print axioms Meaning.attKey_congr
#print axioms Meaning.attOwn1_congr
#print axioms Meaning.attOwn2_congr
#print axioms Meaning.attRidden_congr
#print axioms Meaning.addrA_borrowed
#print axioms Meaning.OneWord.of_all
#print axioms Meaning.mgOf_seen
#print axioms Meaning.maOf_seen
#print axioms Meaning.maOf_of_all
#print axioms Meaning.ownA_maOf
#print axioms Meaning.oneWord_of_seen
#print axioms Meaning.means_of_seen
#print axioms Meaning.mgOf_lab
#print axioms Meaning.maOf_lab
#print axioms Meaning.maOf_plan
#print axioms Meaning.ownOf_unique
#print axioms Meaning.ownOf_matsOf
#print axioms Meaning.ownOf_zsOf
#print axioms Meaning.small_ownOf
