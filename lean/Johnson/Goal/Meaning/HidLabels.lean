-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidLabels.lean: in the verifier's own plans, reader and owner bear one label,
at all 24 pairs.

The verifier's plans give each entry of a sub-proof's list of matrices a label (the field aId of a
record TMat); an entry that a sub-proof borrows bears its owner's label. hidOf
(Johnson/Goal/Meaning/HidOwn.lean) reads a borrowed array in its owner's list, and the 24 equations
OneWord and HeadWord say that reader and owner read one array. This file shows the public side of
that: at what publicOf returns, under the public core, the reader's entry and the owner's entry are
there in the plans X.G, X.A, X.H and have one label.

Main names:
  labG X g n, labAtt X g n, labHead X n   the label of entry n in the list of the plan of group g,
    of its attention sub-proof, of the head; nothing if there is no such plan or entry.
  labG_eq, labAtt_eq, labHead_eq   in scope these are the layers' formula labA
    (Johnson/Road/FormsKeysDictA.lean) at the owner's group and number.
  OneLabel X, oneLabel_of_core   THE 24 PAIRS: a later group's iXI and the group before's iXO (11);
    an attention sub-proof's NAs + 3 and its group's iQA (12); the head's NHf + 3 and group 11's iXO
    (1).

All of it is the library's: labA_tails, plan_labels, public_plans, labH_of_public, labH_lent
(Johnson/Road/FormsKeysDictA.lean, HeadDict.lean), label_public (Lane5AttPub.lean), labA_in
(HeadSeam.lean); here the pieces are laid side by side, in one form, with the entries' being there.

What is not claimed. That an entry with another sub-proof's label is read in the owner's commitment:
which message, row and place a label has is the frame's matter. That reader's and owner's entries
have the same rows and columns in the plans (by their text tailsOf gives xbI and xbO the same sizes;
for qa and for the head's copy the plans' makers test it; not shown here). That no label is owned
twice (the verifier tests it: labelsHeld, OnBytes/Model/VerifyCross.lean). The full size alone. The
program does not import this file.
-/
import Johnson.Goal.Meaning.HidHead
import Johnson.Road.HeadSeam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx tailsOf)

/-- The label of entry n of the list in the plan of group g. -/
def labG (X : Model.Verify.Public) (g n : ℕ) : Option ℕ :=
  (X.G[g]?).bind fun P => (P.tl.mats[n]?).map fun M => M.aId

/-- The label of entry n of the list in the plan of the attention sub-proof of group g. -/
def labAtt (X : Model.Verify.Public) (g n : ℕ) : Option ℕ :=
  (X.A[g]?).bind fun P => (P.seam.tl.mats[n]?).map fun M => M.aId

/-- The label of entry n of the list in the head's plan. -/
def labHead (X : Model.Verify.Public) (n : ℕ) : Option ℕ := (X.H.tl.mats[n]?).map fun M => M.aId

/-- Entry n of the verifier's list for group g is there and has the label labA. -/
theorem tails_at (y : Lay) {g n : ℕ} (hg : g < y.NGr)
    (hn : n < y.parts.getD 0 0 + y.parts.getD 1 0 + 5) :
    (((tailsOf y).getD g {}).mats[n]?).map (fun M => M.aId) = some (labA y g n) := by
  have hs : n < ((tailsOf y).getD g {}).mats.size := by
    unfold tailsOf
    dsimp only
    rw [range_map_at _ _ _ hg]
    simp only [List.size_toArray, List.length_map, List.length_zipIdx, List.length_append,
      List.length_range, List.length_cons, List.length_nil]
    omega
  have L := labA_tails y hg hn
  generalize ((tailsOf y).getD g {}).mats = a at hs L ⊢
  rw [← L, Array.getElem?_eq_getElem hs, Array.getD, dif_pos hs]
  rfl

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **In scope entry n of the list in the plan X.G[g] is there and has the label labA X.y g n.** -/
theorem labG_eq (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g n : ℕ} (hg : g < 12)
    (hn : n < X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 5) :
    labG X g n = some (labA X.y g n) := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
  obtain ⟨hsz, hall⟩ := Hd.plan_labels hP hG
  have hgs : g < X.G.size := by
    rw [hsz, B.groups]
    exact hg
  have e : X.G[g]? = some X.G[g] := Array.getElem?_eq_getElem hgs
  have k0 := congrArg (fun z : Array ℕ => z[n]?) (hall g _ e)
  have k : (X.G[g].tl.mats[n]?).map (fun M => M.aId) =
      (((tailsOf X.y).getD g {}).mats[n]?).map fun M => M.aId := by simpa using k0
  unfold labG
  rw [e]
  show (X.G[g].tl.mats[n]?).map (fun M => M.aId) = _
  rw [k, tails_at X.y (by rw [B.groups]; exact hg) hn]

/-- **In scope number NAs + 3 of the list in the plan X.A[g] is there and has the label of the
group's qa.** -/
theorem labAtt_eq (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12) :
    labAtt X g ((Hd.shapeA X g).cf.NAs + 3) = some (labA X.y g (matIx X.y).iQA) := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨Ag, h1, h2, h3⟩ := label_public h B.p4 (by rw [B.groups]; exact hg : g < X.y.NGr)
  unfold labAtt
  rw [h1, ← h2]
  exact h3

/-- **In scope number NHf + 3 of the list in the head's plan is there and has the label of the
stream that goes out of group 11.** -/
theorem labHead_eq (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    labHead X (X.hS.NHf + 3) = some (labA X.y 11 (matIx X.y).iXO) := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (Hd.numH_of_layout B.full B.head).NHf
  have L := Hd.labH_of_public h hN (n := X.hS.NHf + 3) (by omega)
  rw [Hd.labH_lent X.hS B.groups] at L
  obtain ⟨H0, hH, e⟩ := (Hd.publicH_of_public h).plan
  obtain ⟨stream, -, hm⟩ := Hd.planH2_label hH
  have em : X.H.tl.mats = Model.Head.matsH X.hS X.HLy (Model.Verify.borderOf X.y) (1 + X.y.NGr)
      stream.aId := by
    rw [e]
    exact hm
  have hs : X.hS.NHf + 3 < X.H.tl.mats.size := by
    rw [em]
    unfold Model.Head.matsH
    rw [hN]
    simp
  unfold labHead
  rw [Array.getElem?_eq_getElem hs, ← L, Array.getD, dif_pos hs]
  rfl

/-- **Reader and owner bear one label.** -/
structure OneLabel (X : Model.Verify.Public) : Prop where
  ff : ∀ g, 0 < g → g < 12 → ∃ l, labG X g (matIx X.y).iXI = some l ∧
    labG X (g - 1) (matIx X.y).iXO = some l
  att : ∀ g < 12, ∃ l, labAtt X g ((Hd.shapeA X g).cf.NAs + 3) = some l ∧
    labG X g (matIx X.y).iQA = some l
  head : ∃ l, labHead X (X.hS.NHf + 3) = some l ∧ labG X 11 (matIx X.y).iXO = some l

/-- **In scope, at all 24 pairs.** -/
theorem oneLabel_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    OneLabel X := by
  have i2 : (matIx X.y).iQA < X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 5 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 2 < _
    omega
  have i3 : (matIx X.y).iXO < X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 5 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 < _
    omega
  have i4 : (matIx X.y).iXI < X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 5 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 < _
    omega
  refine ⟨fun g h0 hg => ⟨_, ?_, labG_eq h C (by omega) i3⟩,
    fun g hg => ⟨_, labAtt_eq h C hg, labG_eq h C hg i2⟩,
    ⟨_, labHead_eq h C, labG_eq h C (by norm_num) i3⟩⟩
  rw [labG_eq h C hg i4, Hd.labA_in X.y h0]

end Core

end Meaning

#print axioms Meaning.tails_at
#print axioms Meaning.labG_eq
#print axioms Meaning.labAtt_eq
#print axioms Meaning.labHead_eq
#print axioms Meaning.oneLabel_of_core
