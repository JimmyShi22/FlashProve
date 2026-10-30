-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidPlanFit.lean: the test planFit on the verifier's plans comes out true at
every public file in scope.

planFit X (Johnson/Goal/Meaning/HidPlan.lean) asks, at each of the 24 pairs of reader and owner,
that both entries are there in the lists of X's plans, with the same rows, the same columns and one
label. This file proves it of what publicOf returns under the public core.

Main names:
  entryG   in scope, in the list of the plan of group g, the entries qa, the stream that comes in
    and the stream that goes out are there, with the layout's rows and columns and the label labA.
  entryA   number NAs + 3 of the list of the plan of the attention sub-proof of group g is there,
    with 65,536 rows, 1,536 columns and the label of the group's qa.
  entryH   number NHf + 3 of the head's list is there, with the rows and columns of a matrix of the
    stream and the label of the stream that goes out of group 11.
  planFit_of_core   planFit X = true.
  words_of_core   so, in scope, if the sizes s follow the plans, the 24 equations hold at the lists
    of every witness, whatever function of the label the seats are.
  means_follows   THE SUM at every such s: the 24 records at a witness's lists and the head's clause
    give Means at the witness's hidden values.

It rests on the library's plan_sizes, tails_pairs, sizesTab_at (Johnson/Road/FormsKeysPlan.lean,
FormsKeysTab.lean), nCol_eq (FormsKeysAddr.lean), planH2_label (HeadSeg.lean), and on the files on
labels, fills and plan sizes beside this one.

What is not claimed. THE SEAMS ARE STILL MOVED, NOT PAID. What is owed: that a real signature
follows the plans (Follows); that the layout's seats ARE seatBy f for one f (f is a letter under
"for all": the theorems hold at a constant f too); that the messages msg are what is committed; and
the premises G, At and H of means_follows, which speak of the lists ownAt at that f and that msg and
are met by no theorem here. No guard shows that some f and msg meet G, At and H in this form: the
guards of Johnson/Goal/Meaning/HidLawsGuard.lean are at made-up families, not at ownAt. The full
size alone. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidPlanSizes
import Johnson.Goal.Meaning.HidLabels
import Johnson.Road.FormsKeysTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model (TMat)
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx tailsOf)
open Inst.Model.All (DF)
open Cb.Pv.Tail (Size)

theorem matsAt_even {X : Model.Verify.Public} {g : ℕ} (hg : g < 12) {P : Model.Layer.HPlan2}
    (h : X.G[g]? = some P) : matsAt X (2 * g) = P.tl.mats := by
  unfold matsAt tlAt
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega, h]
  rfl

theorem matsAt_odd {X : Model.Verify.Public} {g : ℕ} (hg : g < 12) {P : Attention.Plan}
    (h : X.A[g]? = some P) : matsAt X (2 * g + 1) = P.seam.tl.mats := by
  unfold matsAt tlAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show (2 * g + 1) / 2 = g by omega, h]
  rfl

theorem matsAt_head (X : Model.Verify.Public) : matsAt X 24 = X.H.tl.mats := by
  unfold matsAt tlAt
  rw [if_neg (by omega), if_pos rfl]

/-- What pairFit asks, from two entries that are there. -/
theorem pairFit_of {X : Model.Verify.Public} {k a k' a' : ℕ} {M M' : TMat}
    (h : (matsAt X k)[a]? = some M) (h' : (matsAt X k')[a']? = some M') (hm : M.m = M'.m)
    (hk : M.k = M'.k) (hl : M.aId = M'.aId) : pairFit X k a k' a' = true := by
  have s1 : a < (matsAt X k).size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at h
    cases h
  have s2 : a' < (matsAt X k').size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at h'
    cases h'
  unfold pairFit labAt
  rw [getD_of h, getD_of h']
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨s1, s2⟩, hm⟩, hk⟩, hl⟩

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **An entry of a group's list**: mat = 3: qa; 4: the stream that comes in; 5: the stream that
goes out. -/
theorem entryG (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12)
    {mat : ℕ} (h3 : 3 ≤ mat) (h5 : mat ≤ 5) :
    ∃ M, (matsAt X (2 * g))[firstM X.y mat]? = some M ∧ M.m = rowsM X.y mat ∧
      M.k = colsM X.y mat ∧ M.aId = labA X.y g (firstM X.y mat) := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
  obtain ⟨hsz, -⟩ := Hd.plan_labels hP hG
  have hgs : g < X.G.size := by
    rw [hsz, B.groups]
    exact hg
  have e : X.G[g]? = some X.G[g] := Array.getElem?_eq_getElem hgs
  have hgN : g < X.y.NGr := by
    rw [B.groups]
    exact hg
  have hp1 : (0 : ℕ) < partsM X.y mat := by
    have c : mat = 3 ∨ mat = 4 ∨ mat = 5 := by omega
    rcases c with rfl | rfl | rfl <;> exact Nat.one_pos
  obtain ⟨l1, l2⟩ := sizesTab_at X.y h5 hp1
  rw [Nat.add_zero] at l1 l2
  have hn : firstM X.y mat < X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 5 := by
    rw [← sizesTab_length]
    exact l1
  have S := (plan_sizes hP hG e).1
  have k0 := congrArg (fun z : Array (ℕ × ℕ) => z[firstM X.y mat]?) S
  have k : (X.G[g].tl.mats[firstM X.y mat]?).map (fun M => (M.m, M.k)) =
      some (rowsM X.y mat, colsM X.y mat) := by
    have k1 : (X.G[g].tl.mats[firstM X.y mat]?).map (fun M => (M.m, M.k)) =
        (matsR X.y g)[firstM X.y mat]? := by simpa using k0
    rw [k1]
    unfold matsR
    rw [tails_pairs X.y hgN, List.getElem?_toArray, ← l2, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem l1]
    rfl
  have L := labG_eq h C hg hn
  unfold labG at L
  rw [e] at L
  have L' : (X.G[g].tl.mats[firstM X.y mat]?).map (fun M => M.aId) =
      some (labA X.y g (firstM X.y mat)) := L
  rw [matsAt_even hg e]
  cases hM : X.G[g].tl.mats[firstM X.y mat]? with
  | none =>
    rw [hM] at k
    cases k
  | some M =>
    rw [hM] at k L'
    have k2 : (M.m, M.k) = (rowsM X.y mat, colsM X.y mat) := Option.some.inj k
    exact ⟨M, rfl, congrArg Prod.fst k2, congrArg Prod.snd k2, Option.some.inj L'⟩

/-- The rows and the columns of qa in the layers' layout. -/
theorem qa_sizes (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    rowsM X.y 3 = 65536 ∧ colsM X.y 3 = 1536 := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have F := Hd.fillRef_of_core C B
  obtain ⟨e, -⟩ := laid_of_layout B.lay B.switches.p3
  have S' : Switches X.y.h := by rw [e]; exact B.switches
  have Z' : Sized X.y.h DF := by rw [e]; exact B.sized
  have Z2' : Sized2 X.y.h DF := by rw [e]; exact B.sized2
  have p4 : X.y.h.p4 = true := by rw [e]; exact B.p4
  exact ⟨F.mrow, ((nCol_eq (laid2_of_layout B.lay) S' Z' Z2').2.2.2.1 p4).trans
    Inst.Model.FFSeg.ref_shapes.2.2.2.2.2.1⟩

/-- **Attention's copy of qa in its plan's list.** -/
theorem entryA (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12) :
    ∃ M, (matsAt X (2 * g + 1))[(Hd.shapeA X g).cf.NAs + 3]? = some M ∧ M.m = 65536 ∧
      M.k = 1536 ∧ M.aId = labA X.y g (matIx X.y).iQA := by
  have E := Hd.eleven_of_core h C (Hd.npOf X.hS)
  have hS := E.2.1 g hg
  obtain ⟨i, e⟩ := matsAt_att h C hg
  have t := matrices_tail (Hd.shapeA X g) i 3
  have hM : (matsAt X (2 * g + 1))[(Hd.shapeA X g).cf.NAs + 3]? = some (fixed
      { name := "qa", m := (Hd.shapeA X g).cf.wcQ * (Hd.shapeA X g).T,
        k := (Hd.shapeA X g).fillQ / (Hd.shapeA X g).cf.wcQ, kind := 1, foreign := some 0,
        aId := i.midQ, wp := i.wpq }) := by
    rw [e, Array.getElem?_map, t]
    rfl
  obtain ⟨Ag, h1, -, -⟩ := label_public h E.1.p4 (by rw [E.1.groups]; exact hg : g < X.y.NGr)
  have L := labAtt_eq h C hg
  unfold labAtt at L
  rw [h1] at L
  have L' : (Ag.seam.tl.mats[(Hd.shapeA X g).cf.NAs + 3]?).map (fun M => M.aId) =
      some (labA X.y g (matIx X.y).iQA) := L
  rw [← matsAt_odd hg h1, hM] at L'
  refine ⟨_, hM, ?_, ?_, Option.some.inj L'⟩
  · rw [fixed_m]
    show (Hd.shapeA X g).cf.wcQ * (Hd.shapeA X g).T = 65536
    rw [hS.wcQ, hS.T]
  · rw [fixed_k]
    show (Hd.shapeA X g).fillQ / (Hd.shapeA X g).cf.wcQ = 1536
    have f := fills_eq_of_core h C g hg
    rw [f.2.2, hS.wcQ]

/-- **The head's copy of the stream in its plan's list.** -/
theorem entryH (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    ∃ M, (matsAt X 24)[X.hS.NHf + 3]? = some M ∧ M.m = rowsM X.y 5 ∧ M.k = colsM X.y 5 ∧
      M.aId = labA X.y 11 (matIx X.y).iXO := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (Hd.numH_of_layout B.full B.head).NHf
  obtain ⟨H0, hH, e⟩ := (Hd.publicH_of_public h).plan
  obtain ⟨stream, -, hm⟩ := Hd.planH2_label hH
  have em : X.H.tl.mats = Model.Head.matsH X.hS X.HLy (Model.Verify.borderOf X.y) (1 + X.y.NGr)
      stream.aId := by
    rw [e]
    exact hm
  have hM : (matsAt X 24)[X.hS.NHf + 3]? = some
      { name := "xbL", m := X.y.mxb, k := X.y.kxb, kind := 1, foreign := some 0, ttOff := 0,
        aId := stream.aId } := by
    rw [matsAt_head, em]
    unfold Model.Head.matsH
    rw [hN]
    rfl
  have L := labHead_eq h C
  unfold labHead at L
  rw [← matsAt_head, hM] at L
  exact ⟨_, hM, rfl, rfl, Option.some.inj L⟩

/-- **The test on the plans comes out true in scope.** -/
theorem planFit_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    planFit X = true := by
  obtain ⟨q1, q2⟩ := qa_sizes h C
  unfold planFit
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun g hg => ?_, ?_⟩
  · have hg' := List.mem_range.1 hg
    rw [Bool.and_eq_true, Bool.or_eq_true]
    refine ⟨?_, ?_⟩
    · by_cases h0 : g = 0
      · exact Or.inl (beq_iff_eq.2 h0)
      · obtain ⟨M, a1, a2, a3, a4⟩ := entryG h C hg' (mat := 4) (by norm_num) (by norm_num)
        obtain ⟨M', b1, b2, b3, b4⟩ :=
          entryG h C (by omega : g - 1 < 12) (mat := 5) (by norm_num) (by norm_num)
        refine Or.inr (pairFit_of a1 b1 (a2.trans b2.symm) (a3.trans b3.symm) ?_)
        rw [a4, b4]
        exact Hd.labA_in X.y (by omega)
    · obtain ⟨M, a1, a2, a3, a4⟩ := entryA h C hg'
      obtain ⟨M', b1, b2, b3, b4⟩ := entryG h C hg' (mat := 3) (by norm_num) (by norm_num)
      exact pairFit_of a1 b1 (a2.trans (b2.trans q1).symm) (a3.trans (b3.trans q2).symm)
        (a4.trans b4.symm)
  · obtain ⟨M, a1, a2, a3, a4⟩ := entryH h C
    obtain ⟨M', b1, b2, b3, b4⟩ :=
      entryG h C (by norm_num : 11 < 12) (mat := 5) (by norm_num) (by norm_num)
    exact pairFit_of a1 b1 (a2.trans b2.symm) (a3.trans b3.symm) (a4.trans b4.symm)

/-- **In scope, at sizes that follow the plans, the 24 equations hold at the lists of every
witness**, whatever function of the label the seats are. -/
theorem words_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {s : ℕ → Size}
    (F : Follows X s) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs) :
    OneWord X (ownAt s (seatBy f X s) msg) ∧ HeadWord X (ownAt s (seatBy f X s) msg) :=
  words_of_planFit F f (planFit_of_core h C) msg

/-- **The sum, in scope, at every family of sizes that follows the plans**: the 24 records at the
lists of a witness, and the head's clause at the stream that the library reads in the head's own
cells, give Means at the witness's hidden values. The seats enter in the form seatBy f alone; f is a
letter. -/
theorem means_follows (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {s : ℕ → Size}
    (F : Follows X s) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) {pp : Inst.Model.ScalesAndPolicy} {i : Cm.Idx}
    {x : Inst.Model.Instance Inst.Model.ppref} (tok : Fin Inst.Model.ppref.V) (msg : Msgs)
    (G : ∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
      (ownAt s (seatBy f X s) msg (2 * g)) i.mat x)
    (At : ∀ g < 12, AttOrd (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X (ownAt s (seatBy f X s) msg 24))) :
    Means X pp i x (hidAt X s (seatBy f X s) tok msg) :=
  means_hidAt h C (sizesFit_of_planFit F (planFit_of_core h C))
    (seatsOne_of_planFit f (planFit_of_core h C)) tok msg G At H

end Core

end Meaning

#print axioms Meaning.matsAt_even
#print axioms Meaning.matsAt_odd
#print axioms Meaning.matsAt_head
#print axioms Meaning.pairFit_of
#print axioms Meaning.entryG
#print axioms Meaning.qa_sizes
#print axioms Meaning.entryA
#print axioms Meaning.entryH
#print axioms Meaning.planFit_of_core
#print axioms Meaning.words_of_core
#print axioms Meaning.means_follows
