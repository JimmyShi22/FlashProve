-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidTwelveMet.lean: the twelve clauses of the sum from single clauses can be met
together, at ONE family of messages, which is a packing.

means_of_twelveF (Johnson/Goal/Meaning/HidFamilyParts.lean) gives Means from twelve clauses: four at
each group's list, four at each attention sub-proof's list, four at the head's list. The guard
sum_met (Johnson/Goal/Meaning/HidSumGuard.lean) ends, at the head, in HeadPlain at the stream of a
made-up list (copies of the stream): the head's four clauses do not hold there. Here the head's list
is the honest one: the library's trace of a true request (OrdsL, Johnson/Road/Lane5TopL.lean) holds
the 24 records, the head's record and the ties of the copies at ONE family of matrices.

Main names:
  trace_of_true   at every true request in scope: hidden values w that meet Means AND a head's list
    Mh that meets Hd.HeadOrdLB, whose copy of the stream is the stream that goes out of group 11 in
    w.
  seenT X w Mh   the family: the lists of w, and Mh for the head; clipped.
  ownSame_seenT   it meets OwnSame.
  head_in   in scope the four ranges of Hd.SmallH lie within sizes that follow the plans.
  twelve_met   THE STATEMENT: at every true request in scope, at all sizes that follow the plans
    with the radix 2^20 and the shift 2^17: ONE msg at which BaseSeg holds at all 25 sub-proofs and
    all twelve clauses hold (with the three on smallness: all fifteen).
  twelve_metF   the same at a family of readings (the constant one), with MsgsOne: the premises of
    means_of_twelveF.

What is not claimed. What the head of Johnson/Goal/Meaning/HidSumGuard.lean disclaims: the messages
and the seats are made up (seat0: one message a label); the integers behind them are the library's
honest trace, not a prover's files. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidHeadCongr
import Johnson.Goal.Meaning.HidBaseMember
import Johnson.Goal.Meaning.HidFamily
import Johnson.Road.Lane5TopLTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open OnBytes.Model.Layer (Lay matIx)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)
open Cb.Pv.Tail (Size)

section Trace
variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **One trace for the 24 records and the head's.** -/
theorem trace_of_true (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) :
    ∃ (w : Hid) (Mh : Mats ℤ), w.tok = x.y ∧ Means X pp i x w ∧
      Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x Mh ∧
      ∀ r c, Mh (X.hS.NHf + 3) r c = w.MG 11 (matIx X.y).iXO r c := by
  have A := Hd.core_of_scope hZ hR h
  have E := Hd.eleven_of_core h A (Hd.npOf X.hS)
  have B := E.1
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp lay X hR h
  have tS' : Cm.Scales.of pp = scalesAt X := tS (A.num 2)
  have hs : (scalesAt X).Lawful := tS' ▸ lawful_of_read hR
  have hpol : Policy.PolCond (Hd.polOf X.hS) := tP ▸ polCond_of_read hR
  have T' : Policy.IsTrueUnder (scalesAt X) (Hd.polOf X.hS) i x := by
    rw [← tS', ← tP]
    exact T
  have hre : x.r < x.e := T.2.1.1
  obtain ⟨Zl, ZA, O⟩ : ∃ (Zl : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
        (Hd.shapeA X) i.mat x Zl ZA :=
    ⟨_, _, ordsL_of_true B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head E.2.1
      E.2.2.2.2 E.2.2.1 E.2.2.2.1 hs hpol i x T'⟩
  have N := lists_of_ordsL B.groups O
  have bound := lastOf_bound_of_ords hR h A hre O
  obtain ⟨-, same⟩ := layersSay Z pp lay X hR h A i x _ _ N.layer N.att N.seamFF N.seamA bound
  have S : Says pp i.index.val x (streamOf pp i.index.val x) := says_of_true T
  refine ⟨⟨x.y, fun g => mzA X.y (Zl (2 * g)) g, ZA, lastOf X.y (mzA X.y (Zl (2 * 11)) 11)⟩,
    Hd.mzH X.hS X.y (Zl 24), rfl,
    ⟨fun g hg => ?_, fun g hg => ?_, fun _ _ _ _ => rfl, ?_⟩, O.head, fun r c => ?_⟩
  · obtain ⟨a, b, c, d, e⟩ := layer_fields (N.layer g hg)
    exact ⟨a, b, c, d, e, fun h0 => N.seamFF g h0 hg⟩
  · have R := (N.att g hg).rel
    exact ⟨R.1, R.2.1, fun k b g' n hv => R.2.2 (.at1 k b g' n) hv,
      fun b g' n hv => R.2.2 (.at2 b g' n) hv, fun b g' n hv => R.2.2 (.at3 b g' n) hv,
      N.seamA g hg⟩
  · exact (says_iff_halves.1 S).2.congr (fun a ha j hj => (same a ha j hj).symm)
      fun _ _ _ => rfl
  · show Zl 24 (Hd.labH X.hS X.y (X.hS.NHf + 3)) r c = Zl (2 * 11) (labA X.y 11 (matIx X.y).iXO) r c
    unfold Hd.labH
    rw [if_pos rfl, B.groups]
    exact O.labels.head r c

end Trace

/-- The family: the lists of w, and Mh for the head; clipped. -/
def seenT (X : Model.Verify.Public) (w : Hid) (Mh : Mats ℤ) : ℕ → Mats ℤ := fun k =>
  if k = 24 then clip Mh else seenC X w k

theorem seenT_ne (X : Model.Verify.Public) (w : Hid) (Mh : Mats ℤ) {k : ℕ} (hk : k ≠ 24) :
    seenT X w Mh k = seenC X w k := if_neg hk

theorem seenT_head (X : Model.Verify.Public) (w : Hid) (Mh : Mats ℤ) :
    seenT X w Mh 24 = clip Mh := if_pos rfl

theorem seenT_small (X : Model.Verify.Public) (w : Hid) (Mh : Mats ℤ) (k a r c : ℕ) :
    |seenT X w Mh k a r c| < 2 ^ 18 := by
  by_cases hk : k = 24
  · rw [hk, seenT_head]
    exact clip_small _ _ _ _
  · rw [seenT_ne X w Mh hk]
    exact clip_small _ _ _ _

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public} {s : ℕ → Size}

/-- The family meets OwnSame. -/
theorem ownSame_seenT (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (F : Follows X s)
    {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref} {w : Hid} (M : Means X pp i x w) {Mh : Mats ℤ}
    (hM : ∀ r c, Mh (X.hS.NHf + 3) r c = w.MG 11 (matIx X.y).iXO r c) {k : ℕ} (hk : k < 25) :
    OwnSame X s (seenT X w Mh) k := by
  have O := ownSame_seenC h C F M hk
  refine ⟨O.rad, O.m, fun a ha r hr c hc => ?_⟩
  have ha' : a < (matsAt X k).size := by rw [← F.NM k hk]; exact ha
  rcases owner_cases h C hk ha' with ⟨o1, o2⟩ | ⟨g, h0, hg, rfl, rfl, o1, o2⟩ |
    ⟨g, hg, rfl, rfl, o1, o2⟩ | ⟨rfl, rfl, o1, o2⟩
  · rw [o1, o2]
  · have v := O.val _ ha r hr c hc
    rw [o1] at v ⊢
    rw [seenT_ne X w Mh (by omega), seenT_ne X w Mh (by omega)]
    exact v
  · have v := O.val _ ha r hr c hc
    rw [o1] at v ⊢
    rw [seenT_ne X w Mh (by omega), seenT_ne X w Mh (by omega)]
    exact v
  · rw [o1, o2, seenT_ne X w Mh (by norm_num), seenT_head]
    refine clip_congr ?_
    rw [show (22 : ℕ) = 2 * 11 from rfl, seenOf_even X w (by norm_num : 11 < 12)]
    exact (hM r c).symm

/-- **In scope the four ranges of Hd.SmallH lie within sizes that follow the plans.** -/
theorem head_in (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (F : Follows X s) :
    (∀ a < X.hS.NHf, a < (s 24).NM ∧ (s 24).m a = X.HLy.m ∧ (s 24).k a = X.HLy.k) ∧
    (X.hS.NHf < (s 24).NM ∧ (s 24).m X.hS.NHf = X.HLy.mD ∧ (s 24).k X.hS.NHf = X.HLy.kD) ∧
    (X.hS.NHf + 1 < (s 24).NM ∧ (s 24).m (X.hS.NHf + 1) = X.HLy.mR ∧
      (s 24).k (X.hS.NHf + 1) = X.HLy.kR) ∧
    (X.hS.NHf + 3 < (s 24).NM ∧ (s 24).m (X.hS.NHf + 3) = (borderOf X.y).mxb ∧
      (s 24).k (X.hS.NHf + 3) = (borderOf X.y).kxb) := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (Hd.numH_of_layout B.full B.head).NHf
  obtain ⟨H0, hH, e⟩ := (Hd.publicH_of_public h).plan
  obtain ⟨stream, -, hm⟩ := Hd.planH2_label hH
  have em : matsAt X 24 = Model.Head.matsH X.hS X.HLy (borderOf X.y) (1 + X.y.NGr) stream.aId := by
    rw [matsAt_head, e]
    exact hm
  have sz := size_head h C
  have one : ∀ a < 8, a < (s 24).NM ∧ (s 24).m a = ((matsAt X 24).getD a {}).m ∧
      (s 24).k a = ((matsAt X 24).getD a {}).k := fun a ha =>
    ⟨by rw [F.NM 24 (by norm_num), sz]; exact ha, F.m 24 (by norm_num) a (by rw [sz]; exact ha),
      F.k 24 (by norm_num) a (by rw [sz]; exact ha)⟩
  have ent : ∀ a < 8, ((matsAt X 24).getD a {}).m =
        ((Model.Head.matsH X.hS X.HLy (borderOf X.y) (1 + X.y.NGr) stream.aId).getD a {}).m ∧
      ((matsAt X 24).getD a {}).k =
        ((Model.Head.matsH X.hS X.HLy (borderOf X.y) (1 + X.y.NGr) stream.aId).getD a {}).k :=
    fun a _ => by rw [em]; exact ⟨rfl, rfl⟩
  rw [hN]
  refine ⟨fun a ha => ?_, ?_, ?_, ?_⟩
  · obtain ⟨a1, a2, a3⟩ := one a (by omega)
    obtain ⟨b1, b2⟩ := ent a (by omega)
    rw [a2, a3, b1, b2]
    refine ⟨a1, ?_⟩
    unfold Model.Head.matsH
    rw [hN]
    have c : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
    rcases c with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  · obtain ⟨a1, a2, a3⟩ := one 4 (by norm_num)
    obtain ⟨b1, b2⟩ := ent 4 (by norm_num)
    rw [a2, a3, b1, b2]
    refine ⟨a1, ?_⟩
    unfold Model.Head.matsH
    rw [hN]
    exact ⟨rfl, rfl⟩
  · obtain ⟨a1, a2, a3⟩ := one 5 (by norm_num)
    obtain ⟨b1, b2⟩ := ent 5 (by norm_num)
    rw [a2, a3, b1, b2]
    refine ⟨a1, ?_⟩
    unfold Model.Head.matsH
    rw [hN]
    exact ⟨rfl, rfl⟩
  · obtain ⟨a1, a2, a3⟩ := one 7 (by norm_num)
    obtain ⟨b1, b2⟩ := ent 7 (by norm_num)
    rw [a2, a3, b1, b2]
    refine ⟨a1, ?_⟩
    unfold Model.Head.matsH
    rw [hN]
    exact ⟨rfl, rfl⟩

end Core

/-- **The clauses of the sum can be met together, at one msg that is a packing.** -/
theorem twelve_met {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) {s : ℕ → Size} (F : Follows X s)
    (hb : ∀ k < 25, (s k).beta = 2 ^ 17) (hr : ∀ k < 25, (s k).rad = 2 ^ 20) :
    ∃ msg : Msgs,
      (∀ k < 25, BaseSeg s (seatBy seat0 X s) msg k) ∧
      (∀ g < 12, OwnG X i x (ownAt s (seatBy seat0 X s) msg (2 * g)) g) ∧
      (∀ g < 12, OwnA (Hd.shapeA X g) (ownAt s (seatBy seat0 X s) msg (2 * g + 1))) ∧
      Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x
        (ownAt s (seatBy seat0 X s) msg 24) := by
  obtain ⟨w, Mh, -, M, OH, hM⟩ := trace_of_true hZ hR h i x T
  have C := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have sm : ∀ k < 25, ∀ a < (s k).NM, ∀ r < (s k).m a, ∀ c < (s k).k a,
      |seenT X w Mh k a r c| < 2 * ((s k).beta : ℤ) := fun k hk a _ r _ c _ => by
    rw [hb k hk]
    have e : (2 : ℤ) * ((2 ^ 17 : ℕ) : ℤ) = 2 ^ 18 := by norm_num
    rw [e]
    exact seenT_small X w Mh k a r c
  have E : ∀ k < 25, ownAt s (seatBy seat0 X s) (msgOf s (seenT X w Mh)) k =
      mzTot (cutOf (s k) (seenT X w Mh k)) := fun k hk =>
    ownAt_msgOf Cb.Gl.p (Cb.Pv.Tail.uniq_gl (hb k hk) (hr k hk)) (sm k hk)
      (ownSame_seenT h C F M hM hk)
  refine ⟨msgOf s (seenT X w Mh), fun k hk => baseSeg_msgOf Cb.Gl.p
    (Cb.Pv.Tail.uniq_gl (hb k hk) (hr k hk)) (sm k hk) (ownSame_seenT h C F M hM hk),
    fun g hg => ?_, fun g hg => ?_, ?_⟩
  · rw [E _ (by omega), seenT_ne X w Mh (by omega)]
    refine ownG_of_ord (layerOrd_congr_core h C hg (fun σ r c hz => ?_) (M.layers g hg).ord)
    obtain ⟨a1, a2, a3⟩ := inZ_in h C F hg hz
    rw [mzTot_cutOf _ _ a1 a2 a3]
    show w.MG g (portNo X.y σ) r c = clip (seenOf X w (2 * g)) (portNo X.y σ) r c
    rw [seenOf_even X w hg, clip_of_small ((M.layers g hg).small σ r c hz)]
  · rw [E _ (by omega), seenT_ne X w Mh (by omega)]
    refine (ownA_congr fun c hv => ?_).mp (ownA_of_ord (M.attention g hg).ord)
    obtain ⟨a1, a2, a3⟩ := inside_of_follows h C F hg c hv
    unfold zAt
    rw [mzTot_cutOf _ _ a1 a2 a3]
    show _ = clip (seenOf X w (2 * g + 1)) _ _ _
    rw [seenOf_odd, clip_of_small ((M.attention g hg).small c hv)]
  · rw [E 24 (by norm_num), seenT_head]
    obtain ⟨q1, q2, q3, q4⟩ := head_in h C F
    refine headOrd_congr (Hd.numH_of_layout B.full B.head)
      (Hd.borderH_of_layout B.lay B.switches B.sized B.sized2) ⟨fun a ha r hr' c hc' => ?_,
        fun r hr' c hc' => ?_, fun r hr' c hc' => ?_, fun r hr' c hc' => ?_⟩ OH
    · obtain ⟨a1, a2, a3⟩ := q1 a ha
      rw [mzTot_cutOf _ _ a1 (a3 ▸ hc') (a2 ▸ hr'), clip_of_small (OH.1.1 a ha r hr' c hc')]
    · obtain ⟨a1, a2, a3⟩ := q2
      rw [mzTot_cutOf _ _ a1 (a3 ▸ hc') (a2 ▸ hr'), clip_of_small (OH.1.2.1 r hr' c hc')]
    · obtain ⟨a1, a2, a3⟩ := q3
      rw [mzTot_cutOf _ _ a1 (a3 ▸ hc') (a2 ▸ hr'), clip_of_small (OH.1.2.2.1 r hr' c hc')]
    · obtain ⟨a1, a2, a3⟩ := q4
      rw [mzTot_cutOf _ _ a1 (a3 ▸ hc') (a2 ▸ hr'), clip_of_small (OH.1.2.2.2 r hr' c hc')]

/-- The same at a family of readings, with MsgsOne and BaseSegF. -/
theorem twelve_metF {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) {s : ℕ → Size} (F : Follows X s)
    (hb : ∀ k < 25, (s k).beta = 2 ^ 17) (hr : ∀ k < 25, (s k).rad = 2 ^ 20) :
    ∃ msgF : ℕ → Msgs, MsgsOne X s seat0 msgF ∧
      (∀ k < 25, BaseSegF s (seatBy seat0 X s) msgF k) ∧
      (∀ g < 12, OwnG X i x (ownAtF s (seatBy seat0 X s) msgF (2 * g)) g) ∧
      (∀ g < 12, OwnA (Hd.shapeA X g) (ownAtF s (seatBy seat0 X s) msgF (2 * g + 1))) ∧
      Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x
        (ownAtF s (seatBy seat0 X s) msgF 24) := by
  obtain ⟨msg, Bs, G, At, H⟩ := twelve_met hZ hR h i x T F hb hr
  exact ⟨fun _ => msg, msgsOne_const X s seat0 msg, Bs, G, At, H⟩

end Meaning

#print axioms Meaning.trace_of_true
#print axioms Meaning.seenT_ne
#print axioms Meaning.seenT_head
#print axioms Meaning.seenT_small
#print axioms Meaning.ownSame_seenT
#print axioms Meaning.head_in
#print axioms Meaning.twelve_met
#print axioms Meaning.twelve_metF
