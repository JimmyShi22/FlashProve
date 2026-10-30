-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidSumGuard.lean: the premises of the sum means_follows can be met together, in
the very form in which it asks them: at the lists ownAt s (seatBy f X s) msg of some seats' function
f and some messages msg.

means_follows (Johnson/Goal/Meaning/HidPlanFit.lean) takes three premises G, At and H on the lists
that ownAt reads in a witness's messages, at seats that are a function of the label. A theorem whose
premises exclude each other says nothing. The guards of Johnson/Goal/Meaning/HidLawsGuard.lean meet
the premises of means_of_ords at made-up families of lists, not at ownAt. This file shows: at public
files in the goals' scope, for every index and every request that is true at it under the files'
policy, and for all sizes s that follow the plans with the radix 2^20 and the shift 2^17, there are
f and msg that meet G, At and H.

The guard is not empty itself. A true request exists wherever the files are read:
Policy.TrueGuards.some_true at lawful_of_read (sum_met_some). Sizes that follow the plans, with that
radix and shift, exist in scope (follows_of_core, Johnson/Goal/Meaning/HidPlanNM.lean). That some
files are in scope is an evaluation (a guard in Ladder/Guards.lean), no theorem; it is the premise
that the top statements carry too.

How. Hidden values w that meet Means (means_of_true, Johnson/Goal/Meaning/RowGuard.lean) give a
family of 25 lists. Entries that are not small are set to 0 (clip): the records read none of them.
The family is packed into messages, one for each label (msgOf, Johnson/Goal/Meaning/HidPack.lean); a
label names its owner (owner_cases, Johnson/Goal/Meaning/HidOwner.lean), and reader and owner have
the same rows (planFit_of_core) and the same entries (Means' own seams). So ownAt gives the family
back, cut to the sizes (ownAt_msgOf). The records read entries within the sizes alone
(layerOrd_congr_core, Johnson/Goal/Meaning/HidLayCongr.lean; ownA_congr with inside_of_follows;
lastIn_congr).

Main names:
  clip, seenC X w   the family.
  entry_in, inZ_in   in scope the matrices' shapes lie within sizes that follow the plans.
  ownSame_seenC   the family meets OwnSame.
  sum_met   THE STATEMENT ABOVE.
  sum_met_means   with means_follows: at these f and msg Means holds at hidAt.
  sum_met_run   sum_met at the library's own sizes of the closed records, under ClosedAt
    (Johnson/Goal/Meaning/HidClosed.lean; in scope ClosedAt can be met: closedAt_core,
    Johnson/Goal/Meaning/HidOpen.lean).
  sum_met_some   from the three premises on the files alone: some index, request, f and msg meet G,
    At and H, at the library's own sizes of the plans' records.

What is not claimed. THE MESSAGES ARE MADE UP: one message a label, whose row i holds at place c the
i-th symbol of column c: the release lays its arrays otherwise (by the layout file), the head's own
seven matrices hold copies of the stream, and the matrices of counts hold whatever w holds or 0. So
this is no evidence that an honest prover's files meet the premises; it shows that the premises do
not exclude each other. Anything on a protocol or on the commitments. The program does not import
this file.
-/
import Johnson.Goal.Meaning.HidPack
import Johnson.Goal.Meaning.HidLayCongr
import Johnson.Goal.Meaning.HidClosed
import Johnson.Goal.Meaning.HidLawsGuard
import Policy.Rel.TrueGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open Cb.Pv.Tail (Size)

/-- An entry that is not below 2^18 in absolute value is set to 0. -/
def clip (L : Mats ℤ) : Mats ℤ := fun a r c => if |L a r c| < 2 ^ 18 then L a r c else 0

theorem clip_small (L : Mats ℤ) (a r c : ℕ) : |clip L a r c| < 2 ^ 18 := by
  unfold clip
  by_cases h : |L a r c| < 2 ^ 18
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    norm_num

theorem clip_of_small {L : Mats ℤ} {a r c : ℕ} (h : |L a r c| < 2 ^ 18) :
    clip L a r c = L a r c := by
  unfold clip
  rw [if_pos h]

theorem clip_congr {L L' : Mats ℤ} {a r c a' : ℕ} (h : L a r c = L' a' r c) :
    clip L a r c = clip L' a' r c := by
  unfold clip
  rw [h]

/-- The family: the lists of hidden values, with a head's list that holds the last group's stream,
clipped. -/
def seenC (X : Model.Verify.Public) (w : Hid) : ℕ → Mats ℤ := fun k => clip (seenOf X w k)

/-- What the test on sizes at one pair says. -/
theorem sizeAt_spec {s s' : Size} {a a' : ℕ} (f : sizeAt s s' a a' = true) :
    a < s.NM ∧ a' < s'.NM ∧ s.m a = s'.m a' ∧ s.k a = s'.k a' ∧ s.rad = s'.rad ∧
      s.beta = s'.beta := by
  unfold sizeAt at f
  simp only [Bool.and_eq_true, decide_eq_true_eq] at f
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := f
  exact ⟨a1, a2, a3, a4, a5, a6⟩

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public} {s : ℕ → Size}

/-- In scope part p of the matrix with the number mat lies, with its rows and columns, within sizes
that follow the plans. -/
theorem entry_in (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (F : Follows X s) {g : ℕ}
    (hg : g < 12) {mat p : ℕ} (hmat : mat ≤ 5) (hp : p < partsM X.y mat) {r c : ℕ}
    (hr : r < rowsM X.y mat) (hc : c < colsM X.y mat) :
    firstM X.y mat + p < (s (2 * g)).NM ∧ c < (s (2 * g)).k (firstM X.y mat + p) ∧
      r < (s (2 * g)).m (firstM X.y mat + p) := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
  obtain ⟨P, e⟩ := planG_there h C hg
  obtain ⟨l1, l2⟩ := sizesTab_at X.y hmat hp
  have hn : firstM X.y mat + p < (matsAt X (2 * g)).size := by
    rw [size_even h C hg, ← show (sizesTab X.y).length = 9 by rw [sizesTab_length, p0, p1]]
    exact l1
  have k0 := congrArg (fun z : Array (ℕ × ℕ) => z[firstM X.y mat + p]?) (plan_sizes hP hG e).1
  have k : (P.tl.mats[firstM X.y mat + p]?).map (fun M => (M.m, M.k)) =
      some (rowsM X.y mat, colsM X.y mat) := by
    have k1 : (P.tl.mats[firstM X.y mat + p]?).map (fun M => (M.m, M.k)) =
        (matsR X.y g)[firstM X.y mat + p]? := by simpa using k0
    rw [k1]
    unfold matsR
    rw [tails_pairs X.y (by rw [B.groups]; exact hg), List.getElem?_toArray, ← l2,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem l1]
    rfl
  have hk : 2 * g < 25 := by omega
  rw [F.NM _ hk, F.m _ hk _ hn, F.k _ hk _ hn]
  rw [matsAt_even hg e] at hn ⊢
  cases hM : P.tl.mats[firstM X.y mat + p]? with
  | none =>
    rw [hM] at k
    cases k
  | some M =>
    rw [hM] at k
    have k2 : (M.m, M.k) = (rowsM X.y mat, colsM X.y mat) := Option.some.inj k
    have e1 : M.m = rowsM X.y mat := congrArg Prod.fst k2
    have e2 : M.k = colsM X.y mat := congrArg Prod.snd k2
    rw [getD_of hM, e1, e2]
    exact ⟨hn, hc, hr⟩

/-- In scope the shapes of the matrices that hold cells lie within sizes that follow the plans. -/
theorem inZ_in (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (F : Follows X s) {g : ℕ}
    (hg : g < 12) {σ r c : ℕ} (hz : InZ X.y σ r c) :
    portNo X.y σ < (s (2 * g)).NM ∧ c < (s (2 * g)).k (portNo X.y σ) ∧
      r < (s (2 * g)).m (portNo X.y σ) := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, -⟩ := Hd.parts_ref B.lay B.switches B.sized2
  have q0 : partsM X.y 0 = 3 := p0
  obtain ⟨hσ, hr, hc⟩ := hz
  interval_cases σ
  · exact entry_in h C F hg (mat := 0) (p := 0) (by norm_num) (by rw [q0]; norm_num) hr hc
  · exact entry_in h C F hg (mat := 0) (p := 1) (by norm_num) (by rw [q0]; norm_num) hr hc
  · exact entry_in h C F hg (mat := 0) (p := 2) (by norm_num) (by rw [q0]; norm_num) hr hc
  · exact entry_in h C F hg (mat := 1) (p := 0) (by norm_num)
      (by rw [show partsM X.y 1 = X.y.parts.getD 1 0 from rfl,
        (Hd.parts_ref B.lay B.switches B.sized2).2]; norm_num) hr hc
  · exact entry_in h C F hg (mat := 2) (p := 0) (by norm_num) Nat.one_pos hr hc
  · exact entry_in h C F hg (mat := 3) (p := 0) (by norm_num) Nat.one_pos hr hc
  · exact entry_in h C F hg (mat := 4) (p := 0) (by norm_num) Nat.one_pos hr hc
  · exact entry_in h C F hg (mat := 5) (p := 0) (by norm_num) Nat.one_pos hr hc

/-- **The family meets OwnSame**: an entry that bears another's label has its owner's radix, rows
and entries. -/
theorem ownSame_seenC (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (F : Follows X s)
    {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref} {w : Hid} (M : Means X pp i x w) {k : ℕ}
    (hk : k < 25) : OwnSame X s (seenC X w) k := by
  have fit := sizesFit_of_planFit F (planFit_of_core h C)
  obtain ⟨fa, fb⟩ := sizes_of_fit fit
  have fc : sizeAt (s 24) (s 22) (X.hS.NHf + 3) (matIx X.y).iXO = true := by
    unfold sizesFit at fit
    rw [Bool.and_eq_true] at fit
    exact fit.2
  have key : ∀ a < (s k).NM,
      (s (ownerK (labAt X k a))).rad = (s k).rad ∧
      (s (ownerK (labAt X k a))).m (ownerA (labAt X k a)) = (s k).m a ∧
      ∀ r c, seenC X w (ownerK (labAt X k a)) (ownerA (labAt X k a)) r c = seenC X w k a r c := by
    intro a ha
    rw [F.NM k hk] at ha
    rcases owner_cases h C hk ha with ⟨o1, o2⟩ | ⟨g, h0, hg, rfl, rfl, o1, o2⟩ |
      ⟨g, hg, rfl, rfl, o1, o2⟩ | ⟨rfl, rfl, o1, o2⟩
    · rw [o1, o2]
      exact ⟨rfl, rfl, fun _ _ => rfl⟩
    · rw [o1, o2]
      obtain ⟨-, -, e3, -, e5, -⟩ := sizeAt_spec (fa g h0 hg)
      refine ⟨e5.symm, e3.symm, fun r c => clip_congr ?_⟩
      rw [seenOf_even X w hg, seenOf_even X w (by omega : g - 1 < 12)]
      exact ((M.layers g hg).seam h0 r c).symm
    · rw [o1, o2]
      obtain ⟨-, -, e3, -, e5, -⟩ := sizeAt_spec (fb g hg)
      refine ⟨e5.symm, e3.symm, fun r c => clip_congr ?_⟩
      rw [seenOf_odd, seenOf_even X w hg]
      exact ((M.attention g hg).seam r c).symm
    · rw [o1, o2]
      obtain ⟨-, -, e3, -, e5, -⟩ := sizeAt_spec fc
      refine ⟨e5.symm, e3.symm, fun r c => clip_congr ?_⟩
      rw [show (22 : ℕ) = 2 * 11 from rfl, seenOf_even X w (by norm_num : 11 < 12)]
      rfl
  exact ⟨fun a ha => (key a ha).1, fun a ha => (key a ha).2.1,
    fun a ha r _ c _ => (key a ha).2.2 r c⟩

end Core

/-- **The premises of the sum can be met together, at ownAt**: at every true request in scope, at
all sizes that follow the plans with the radix 2^20 and the shift 2^17. -/
theorem sum_met {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) {s : ℕ → Size} (F : Follows X s)
    (hb : ∀ k < 25, (s k).beta = 2 ^ 17) (hr : ∀ k < 25, (s k).rad = 2 ^ 20) :
    ∃ (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs),
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
        (ownAt s (seatBy f X s) msg (2 * g)) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1))) ∧
      HeadPlain pp i x (headStream X (ownAt s (seatBy f X s) msg 24)) := by
  obtain ⟨w, -, M⟩ := means_of_true hZ hR h i x T
  have C := Hd.core_of_scope hZ hR h
  have N := xoNum_of_core h C
  have E : ∀ k < 25, ownAt s (seatBy seat0 X s) (msgOf s (seenC X w)) k =
      mzTot (cutOf (s k) (seenC X w k)) := fun k hk =>
    ownAt_msgOf Cb.Gl.p (Cb.Pv.Tail.uniq_gl (hb k hk) (hr k hk))
      (fun a _ r _ c _ => by
        rw [hb k hk]
        have := clip_small (seenOf X w k) a r c
        have e : (2 : ℤ) * ((2 ^ 17 : ℕ) : ℤ) = 2 ^ 18 := by norm_num
        rw [e]
        exact this)
      (ownSame_seenC h C F M hk)
  refine ⟨seat0, msgOf s (seenC X w), fun g hg => ?_, fun g hg => ?_, ?_⟩
  · rw [E _ (by omega)]
    refine layerOrd_congr_core h C hg (fun σ r c hz => ?_) (M.layers g hg).ord
    obtain ⟨a1, a2, a3⟩ := inZ_in h C F hg hz
    rw [mzTot_cutOf _ _ a1 a2 a3]
    show w.MG g (portNo X.y σ) r c = clip (seenOf X w (2 * g)) (portNo X.y σ) r c
    rw [seenOf_even X w hg, clip_of_small ((M.layers g hg).small σ r c hz)]
  · rw [E _ (by omega)]
    refine ord_of_ownA ((ownA_congr fun c hv => ?_).mp (ownA_of_ord (M.attention g hg).ord))
    obtain ⟨a1, a2, a3⟩ := inside_of_follows h C F hg c hv
    unfold zAt
    rw [mzTot_cutOf _ _ a1 a2 a3]
    show _ = clip (seenOf X w (2 * g + 1)) _ _ _
    rw [seenOf_odd, clip_of_small ((M.attention g hg).small c hv)]
  · rw [E 24 (by norm_num)]
    have H0 : HeadPlain pp i x (headStream X (seenOf X w 24)) := by
      refine SaysHead.congr (fun pos hp j hj => ?_) (fun _ _ _ => rfl) M.head.plain
      rw [M.head.seam pos hp j hj, lastOf_lastIn N (w.MG 11) pos hp j hj,
        ← lastIn_head h C (seenOf X w 24) pos hp j hj]
      rfl
    obtain ⟨Mh, b1, b2, b3, -⟩ := entryH h C
    have hn : X.hS.NHf + 3 < (matsAt X 24).size := (Array.getElem?_eq_some_iff.1 b1).1
    have e24 : ∀ r < 65536, ∀ c < 400, seenOf X w 24 (X.hS.NHf + 3) r c =
        mzTot (cutOf (s 24) (seenC X w 24)) (X.hS.NHf + 3) r c := by
      intro r hr' c hc'
      have a1 : X.hS.NHf + 3 < (s 24).NM := by
        rw [F.NM 24 (by norm_num)]
        exact hn
      have a2 : c < (s 24).k (X.hS.NHf + 3) := by
        rw [F.k 24 (by norm_num) _ hn, getD_of b1, b3]
        show c < X.y.kxb
        rw [N.kxb]
        exact hc'
      have a3 : r < (s 24).m (X.hS.NHf + 3) := by
        rw [F.m 24 (by norm_num) _ hn, getD_of b1, b2]
        show r < X.y.mxb
        rw [N.mxb]
        exact hr'
      rw [mzTot_cutOf _ _ a1 a2 a3]
      show _ = clip (seenOf X w 24) (X.hS.NHf + 3) r c
      refine (clip_of_small ?_).symm
      show |w.MG 11 (matIx X.y).iXO r c| < 2 ^ 18
      exact (M.layers 11 (by norm_num)).small 7 r c
        ⟨by norm_num, by show r < X.y.mxb; rw [N.mxb]; exact hr',
          by show c < X.y.kxb; rw [N.kxb]; exact hc'⟩
    exact SaysHead.congr (fun pos hp j hj =>
      (lastIn_head h C (seenOf X w 24) pos hp j hj).symm.trans
        ((lastIn_congr N e24 pos hp j hj).trans (lastIn_head h C _ pos hp j hj)))
      (fun _ _ _ => rfl) H0

/-- With the sum: at these seats and messages Means holds at the witness's hidden values. -/
theorem sum_met_means {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) {s : ℕ → Size} (F : Follows X s)
    (hb : ∀ k < 25, (s k).beta = 2 ^ 17) (hr : ∀ k < 25, (s k).rad = 2 ^ 20) :
    ∃ (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs),
      ∀ tok, Means X pp i x (hidAt X s (seatBy f X s) tok msg) := by
  obtain ⟨f, msg, G, At, H⟩ := sum_met hZ hR h i x T F hb hr
  exact ⟨f, msg, fun tok => means_follows h (Hd.core_of_scope hZ hR h) F f tok msg G At H⟩

/-- The same at the library's own sizes of the closed records, at which the smallness tests stand.
-/
theorem sum_met_run {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) {tl : ℕ → Model.HTailF2}
    (c : ClosedAt X tl) :
    ∃ (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs),
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
        (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
          (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg (2 * g)) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g)
        (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
          (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg (2 * g + 1))) ∧
      HeadPlain pp i x (headStream X
        (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
          (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg 24)) :=
  sum_met hZ hR h i x T (follows_run h (Hd.core_of_scope hZ hR h) c) (fun _ _ => rfl)
    (fun _ _ => rfl)

/-- From the three premises on the files alone. -/
theorem sum_met_some {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs),
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
        (ownAt (sizesOf X) (seatBy f X (sizesOf X)) msg (2 * g)) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g)
        (ownAt (sizesOf X) (seatBy f X (sizesOf X)) msg (2 * g + 1))) ∧
      HeadPlain pp i x (headStream X (ownAt (sizesOf X) (seatBy f X (sizesOf X)) msg 24)) :=
  ⟨_, _, sum_met hZ hR h _ _ (Policy.TrueGuards.some_true (lawful_of_read hR) pp.pol)
    (follows_of_core h (Hd.core_of_scope hZ hR h)) (fun _ _ => rfl) (fun _ _ => rfl)⟩

end Meaning

#print axioms Meaning.clip_small
#print axioms Meaning.clip_of_small
#print axioms Meaning.clip_congr
#print axioms Meaning.sizeAt_spec
#print axioms Meaning.entry_in
#print axioms Meaning.inZ_in
#print axioms Meaning.ownSame_seenC
#print axioms Meaning.sum_met
#print axioms Meaning.sum_met_means
#print axioms Meaning.sum_met_run
#print axioms Meaning.sum_met_some
