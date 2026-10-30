-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidLawsGuard.lean: the premises of means_of_ords
(Johnson/Goal/Meaning/HidLaws.lean) can be met together.

means_of_ords has five premises on a family seen of 25 lists: the 23 equations OneWord, the 24th
HeadWord, the 12 records LayerOrd, the 12 records AttOrd, and the head's clause at the stream that
the library reads in the head's own cells. A theorem whose premises exclude each other says nothing.
This file shows: at public files in the goals' scope, for every index and every request that is true
at it under the files' policy, some family meets all five.

Main names:
  seenOf X w   the family: the lists of hidden values w; the head's list has, at every number, the
    last group's number iXO.
  ords_met   the statement above.
  seenTooth, ords_met_tooth   A TOOTH: the same family with 1 added in attention 0's copy of qa at
    row 65,536, column 0 (outside qa's rows): it meets the five premises, so Means follows at hidOf,
    while the equation on qa at all rows and columns, the unfenced form, fails in it. hidOf does not
    read attention's own copy of qa, so the added 1 does not reach Hid: what the tooth tries is the
    five premises with the unfenced equation false, not that Means withstands a change.

What is not claimed. That an honest prover's files hold this family (its head's list is made up but
for the copy of the stream). ords_met does not try the fence (in its family attention's copy of qa
is the group's at all rows and columns); ords_met_tooth does, at one made-up place. Neither is
evidence that a run at zsOf pays OneWord. Anything on a protocol or on the commitments. The program
does not import this file.
-/
import Johnson.Goal.Meaning.HidLaws
import Johnson.Goal.Meaning.HidOwnGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)

/-- The lists of hidden values, with a head's list that holds the last group's stream. -/
def seenOf (X : Model.Verify.Public) (w : Hid) : ℕ → Mats ℤ := fun k =>
  if k = 24 then fun _ => w.MG 11 (matIx X.y).iXO else ownsOf w k

theorem seenOf_even (X : Model.Verify.Public) (w : Hid) {g : ℕ} (hg : g < 12) :
    seenOf X w (2 * g) = w.MG g := by
  unfold seenOf
  rw [if_neg (by omega), ownsOf_even]

theorem seenOf_odd (X : Model.Verify.Public) (w : Hid) (g : ℕ) :
    seenOf X w (2 * g + 1) = w.MA g := by
  unfold seenOf
  rw [if_neg (by omega), ownsOf_odd]

/-- **The five premises of means_of_ords can be met together**, at every true request in scope. -/
theorem ords_met {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) :
    ∃ seen : ℕ → Mats ℤ, OneWord X seen ∧ HeadWord X seen ∧
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g (seen (2 * g)) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g) (seen (2 * g + 1))) ∧
      HeadPlain pp i x (headStream X (seen 24)) := by
  obtain ⟨w, -, M⟩ := means_of_true hZ hR h i x T
  have C := Hd.core_of_scope hZ hR h
  have N := xoNum_of_core h C
  refine ⟨seenOf X w, OneWord.of_all (fun g h0 hg r c => ?_) (fun g hg r c => ?_),
    fun r _ c _ => ?_, fun g hg => ?_, fun g hg => ?_, ?_⟩
  · rw [seenOf_even X w hg, seenOf_even X w (by omega : g - 1 < 12)]
    exact (M.layers g hg).seam h0 r c
  · rw [seenOf_odd, seenOf_even X w hg]
    exact (M.attention g hg).seam r c
  · rw [show (22 : ℕ) = 2 * 11 from rfl, seenOf_even X w (by norm_num : 11 < 12)]
    rfl
  · rw [seenOf_even X w hg]
    exact (M.layers g hg).ord
  · rw [seenOf_odd]
    exact (M.attention g hg).ord
  · refine SaysHead.congr (fun pos hp j hj => ?_) (fun _ _ _ => rfl) M.head.plain
    rw [M.head.seam pos hp j hj, lastOf_lastIn N (w.MG 11) pos hp j hj,
      ← lastIn_head h C (seenOf X w 24) pos hp j hj]
    rfl

/-! ## A tooth: the fence is tried -/

/-- seenOf, but with 1 added in attention 0's copy of qa at row 65,536, column 0: outside the rows
of qa. -/
def seenTooth (X : Model.Verify.Public) (w : Hid) : ℕ → Mats ℤ := fun k a r c =>
  if k = 1 ∧ a = (Hd.shapeA X 0).cf.NAs + 3 ∧ r = 65536 ∧ c = 0 then seenOf X w k a r c + 1
  else seenOf X w k a r c

theorem seenTooth_ne (X : Model.Verify.Public) (w : Hid) {k : ℕ} (hk : k ≠ 1) :
    seenTooth X w k = seenOf X w k := by
  funext a r c
  unfold seenTooth
  rw [if_neg fun h => hk h.1]

/-- **The fence is tried**: at every true request in scope there is a family that meets the five
premises of means_of_ords, in which the equation on qa AT ALL ROWS AND COLUMNS, the unfenced form,
fails, and at which Means holds at hidOf. -/
theorem ords_met_tooth {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) :
    ∃ seen : ℕ → Mats ℤ, OneWord X seen ∧ HeadWord X seen ∧
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g (seen (2 * g)) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g) (seen (2 * g + 1))) ∧
      HeadPlain pp i x (headStream X (seen 24)) ∧
      (¬ ∀ r c, seen (2 * 0 + 1) ((Hd.shapeA X 0).cf.NAs + 3) r c =
        seen (2 * 0) (matIx X.y).iQA r c) ∧
      ∀ tok, Means X pp i x (hidOf X tok seen) := by
  suffices K : ∃ seen : ℕ → Mats ℤ, OneWord X seen ∧ HeadWord X seen ∧
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g (seen (2 * g)) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g) (seen (2 * g + 1))) ∧
      HeadPlain pp i x (headStream X (seen 24)) ∧
      ¬ ∀ r c, seen (2 * 0 + 1) ((Hd.shapeA X 0).cf.NAs + 3) r c =
        seen (2 * 0) (matIx X.y).iQA r c by
    obtain ⟨seen, a, b, c, d, e, f⟩ := K
    exact ⟨seen, a, b, c, d, e, f, fun tok =>
      means_of_ords h (Hd.core_of_scope hZ hR h) tok a b c d e⟩
  obtain ⟨w, -, M⟩ := means_of_true hZ hR h i x T
  have C := Hd.core_of_scope hZ hR h
  have E := Hd.eleven_of_core h C (Hd.npOf X.hS)
  obtain ⟨seen0, e0, A, W, G, At, H⟩ : ∃ s0, s0 = seenOf X w ∧ OneWord X s0 ∧ HeadWord X s0 ∧
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g (s0 (2 * g)) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g) (s0 (2 * g + 1))) ∧
      HeadPlain pp i x (headStream X (s0 24)) := by
    have N := xoNum_of_core h C
    refine ⟨_, rfl, OneWord.of_all (fun g h0 hg r c => ?_) (fun g hg r c => ?_),
      fun r _ c _ => ?_, fun g hg => ?_, fun g hg => ?_, ?_⟩
    · rw [seenOf_even X w hg, seenOf_even X w (by omega : g - 1 < 12)]
      exact (M.layers g hg).seam h0 r c
    · rw [seenOf_odd, seenOf_even X w hg]
      exact (M.attention g hg).seam r c
    · rw [show (22 : ℕ) = 2 * 11 from rfl, seenOf_even X w (by norm_num : 11 < 12)]
      rfl
    · rw [seenOf_even X w hg]
      exact (M.layers g hg).ord
    · rw [seenOf_odd]
      exact (M.attention g hg).ord
    · refine SaysHead.congr (fun pos hp j hj => ?_) (fun _ _ _ => rfl) M.head.plain
      rw [M.head.seam pos hp j hj, lastOf_lastIn N (w.MG 11) pos hp j hj,
        ← lastIn_head h C (seenOf X w 24) pos hp j hj]
      rfl
  subst e0
  -- at the place of every valid name the tooth's list of attention 0 is the old one
  have same : ∀ g < 12, ∀ c : Inst.Model.AttSeg.Raw, c.Valid (dimOf (Hd.shapeA X g)) →
      zAt (seenOf X w (2 * g + 1)) (addrA (Hd.shapeA X g) c) =
        zAt (seenTooth X w (2 * g + 1)) (addrA (Hd.shapeA X g) c) := by
    intro g hg c hv
    by_cases hg0 : 2 * g + 1 = 1
    · have g0 : g = 0 := by omega
      subst g0
      unfold zAt seenTooth
      rw [if_neg]
      rintro ⟨-, ha, hr, -⟩
      -- the row of a valid name in number NAs + 3 is below 65,536
      have hS := E.2.1 0 hg
      have ho : c.Own = false := by
        cases hc : c.Own with
        | false => rfl
        | true => exact absurd ha (ownApart_of_core h C 0 hg c hv hc)
      have hq : (Inst.Model.AttSeg.addr Inst.Model.All.DA Inst.Model.All.KA c).1 = .qa := by
        cases c <;> first | rfl | exact Bool.noConfusion (ho : true = false)
      obtain ⟨b1, -⟩ := qa_range c (valid_ref hS hv) hq
      have e1 : (addrA (Hd.shapeA X 0) c).2.1 =
          (Inst.Model.AttSeg.addr Inst.Model.All.DA Inst.Model.All.KA c).2.1 := by
        rw [addrA_ref hS c]
        unfold portOf
        rw [hq]
      omega
    · rw [seenTooth_ne X w hg0]
  refine ⟨seenTooth X w, ⟨fun g h0 hg r c => ?_, fun g hg c hv ho => ?_⟩, fun r hr c hc => ?_,
    fun g hg => ?_, fun g hg => ?_, ?_, fun all => ?_⟩
  · rw [seenTooth_ne X w (by omega), seenTooth_ne X w (by omega)]
    exact A.ff g h0 hg r c
  · rw [← same g hg c hv, seenTooth_ne X w (by omega : 2 * g ≠ 1)]
    exact A.att g hg c hv ho
  · rw [seenTooth_ne X w (by norm_num), seenTooth_ne X w (by norm_num)]
    exact W r hr c hc
  · rw [seenTooth_ne X w (by omega)]
    exact G g hg
  · exact ord_of_ownA ((ownA_congr (same g hg)).mp (ownA_of_ord (At g hg)))
  · rw [seenTooth_ne X w (by norm_num)]
    exact H
  · have k := all 65536 0
    have k0 : seenOf X w (2 * 0 + 1) ((Hd.shapeA X 0).cf.NAs + 3) 65536 0 =
        seenOf X w (2 * 0) (matIx X.y).iQA 65536 0 := by
      rw [seenOf_odd, seenOf_even X w (by norm_num : 0 < 12)]
      exact (M.attention 0 (by norm_num)).seam 65536 0
    rw [seenTooth_ne X w (by norm_num : 2 * 0 ≠ 1)] at k
    unfold seenTooth at k
    rw [if_pos ⟨rfl, rfl, rfl, rfl⟩, k0] at k
    omega

end Meaning

#print axioms Meaning.seenTooth_ne
#print axioms Meaning.ords_met_tooth
#print axioms Meaning.seenOf_even
#print axioms Meaning.seenOf_odd
#print axioms Meaning.ords_met
