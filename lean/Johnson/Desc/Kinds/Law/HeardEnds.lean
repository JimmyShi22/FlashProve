-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeardEnds.lean.
WHAT IT DOES NOT SHOW. That the hearing returns (Law/Returns.lean); that what was sent is true.
Nothing on soundness, on probabilities or on hiding.
WHAT IT IS. WHAT A RETURN OF heardBy LEAVES IN THE LEDGER, IN THE LETTERS OF WHAT THE PART's READER
READ. heardBy_ends: where heardBy returns on its own rounds from a WellLaid ledger: the lead ld and
the reading R are there; the lead's hidden scalars are what was sent less the mask entries; the
sumcheck's own hidden scalars are the mask entries themselves; end value j lies under the slot
sEnd + j, is shown as R's value j, and its hidden scalar is that value less beta times the mask
entry; what the part's hearing handed back is heardRec of R.
The steps stand, for lead 1 and lead 0, inside other files' laws (Law/SumLaw.lean: coreG;
Law/LevelLaw.lean: coreL; Law/LedgerAt.lean: hidden_vals): here they are one statement for any lead.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Returns
import Johnson.Desc.Kinds.Law.LevelLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE subE)
open OnBytes.Model (Aff Fork Reading)
open Part.MaskedSum (readAll leadScalars ownSlots hidingAt rowLaid challenges)
open Came (hiddenFrom_get heardBy_cut round_some)

theorem getD_zero (l : List E) (i : Nat) : rd (l.getD i (0 : E)) = rd (l.getD i zeroE) := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rfl

/-- **WHAT A RETURN OF heardBy LEAVES IN THE LEDGER.** -/
theorem heardBy_ends {lead : Nat} {C : Array Hid → Form} {z : Point} {ends : Nat} {F0 F1 : Fork}
    {t : List Fmt.RoundView} {c : Array Hid} {S : Sum} (hW : WellLaid F0)
    (h : heardBy lead C z ends F0 t = some ((c, S), F1, [])) (mask : Nat → E) :
    ∃ (ld : List E) (R : Part.MaskedSum.Read) (T : E),
      leadScalars (callOf lead z ends) t = some ld ∧ readAll (callOf lead z ends) t = some R ∧
      c = hidOf F0.next ld ∧ R.values.length = ends ∧
      S.psc = some (heardRec (C c) T R (callOf lead z ends) (F0.next + ld.length)) ∧
      S.r = (challenges (callOf lead z ends)
        (heardRec (C c) T R (callOf lead z ends) (F0.next + ld.length))).toArray ∧
      (∀ s, s < ld.length →
        rd (hidden F1 mask (F0.next + s)) = rd (ld.getD s zeroE) - rd (mask (F0.next + s))) ∧
      (∀ i, i < ownSlots (callOf lead z ends).all →
        rd (hidden F1 mask (F0.next + ld.length + i)) = rd (mask (F0.next + ld.length + i))) ∧
      ∀ j, j < ends →
        S.end_ j = { var := Aff.slot (F0.next + ld.length + ownSlots (callOf lead z ends).all + j),
                     shown := R.values.getD j zeroE } ∧
        rd (hidden F1 mask (F0.next + ld.length + ownSlots (callOf lead z ends).all + j)) =
          rd (R.values.getD j zeroE) - rd ((R.rounds.map (·.2)).getLastD zeroE) *
            rd (mask (F0.next + ld.length + ownSlots (callOf lead z ends).all + j)) := by
  obtain ⟨ld, Fa, G, hd, es, _, a2, a3, a4, a5, a6, hs⟩ := heardBy_spec h
  obtain ⟨run1, hc⟩ := hide_unfold a3
  obtain ⟨_, T, R, _, hread, hhd, run2⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨_, _, _, _, _, _, _, _, hsv⟩ := Part.MaskedSum.readAll_spec
    (show readAll ⟨lead, z.toList.map (.point · 3), some ⟨2, ends⟩⟩ t = some R from hread)
  have hvl : R.values.length = ends := hsv.2.1
  have hown := own_length lead z ends hread
  obtain ⟨w1, _, n1, v1, m1⟩ := hideRun_frame
    (F := ({ F0 with next := F0.next + ld.length } : Fork)) hW run1
  have hFa : Fa.next = F0.next + ld.length := n1
  obtain ⟨w2, _, _, v2, m2⟩ := hideRun_frame
    (F := ({ Fa with next := Fa.next + ownSlots (callOf lead z ends).all + R.values.length }
      : Fork)) w1 run2
  have run3 : G.hideRun Fa.next
      (Array.replicate (ownSlots (callOf lead z ends).all) zeroE) (subE zeroE oneE) = some F1 := by
    have h5 := a5
    unfold rowLaid at h5
    rw [hhd] at h5
    dsimp only at h5
    rw [hown] at h5
    exact h5
  obtain ⟨_, _, _, v3, m3⟩ := hideRun_frame w2 run3
  have s1 : ld.toArray.size = ld.length := List.size_toArray
  have s2 : R.values.toArray.size = ends := by rw [List.size_toArray, hvl]
  have s3 : (Array.replicate (ownSlots (callOf lead z ends).all) zeroE).size =
      ownSlots (callOf lead z ends).all := Array.size_replicate
  have hrec : hd = heardRec (C c) T R (callOf lead z ends) (F0.next + ld.length) := by
    rw [hhd, hFa]
    rfl
  have one : rd oneE = 1 := Reading.gl.one
  refine ⟨ld, R, T, a2, hread, hc, hvl, by rw [hs, hrec], by rw [hs, hrec], ?_, ?_, ?_⟩
  · intro s hs'
    unfold hidden
    rw [v3, m3, if_neg (by rw [s3, hFa]; omega), if_neg (by rw [s3, hFa]; omega), v2, m2,
      if_neg (by rw [s2, hFa]; omega), if_neg (by rw [s2, hFa]; omega), v1, m1,
      if_pos (by rw [s1]; omega), if_pos (by rw [s1]; omega), rd_sub, rd_mul, one, one_mul,
      Nat.add_sub_cancel_left]
    show rd (ld.getD s (0 : E)) - _ = _
    rw [getD_zero]
  · intro i hi
    unfold hidden
    rw [v3, m3, if_pos (by rw [s3, hFa]; omega), if_pos (by rw [s3, hFa]; omega), rd_sub, rd_mul,
      rd_neg_one]
    have e0 : rd ((Array.replicate (ownSlots (callOf lead z ends).all) zeroE).toList.getD
        (F0.next + ld.length + i - Fa.next) (0 : E)) = 0 := by
      rw [hFa, Nat.add_sub_cancel_left, Array.toList_replicate, List.getD_eq_getElem?_getD,
        List.getElem?_replicate, if_pos hi]
      exact Reading.gl.zero
    rw [e0]
    ring
  · intro j hj
    have hvp : ∀ x : E, F1.vp.getD (F0.next + ld.length + ownSlots (callOf lead z ends).all + j) x
        = R.values.getD j x := by
      intro x
      rw [v3, if_neg (by rw [s3, hFa]; omega), v2, if_pos (by rw [s2, hFa]; omega), hFa,
        Nat.add_sub_cancel_left]
    refine ⟨?_, ?_⟩
    · have he : hd.sEnd = F0.next + ld.length + ownSlots (callOf lead z ends).all := by
        rw [hrec]
        rfl
      rw [he] at a6
      rw [hs]
      show es.getD j {} = _
      rw [hiddenFrom_get a6 j hj, hvp]
    · unfold hidden
      rw [hvp, m3, if_neg (by rw [s3, hFa]; omega), m2, if_pos (by rw [s2, hFa]; omega), rd_sub,
        rd_mul, getD_zero]

theorem leadScalars_len {k : Part.MaskedSum.Call} {rs : List Fmt.RoundView} {ld : List E}
    (h : leadScalars k rs = some ld) : ld.length = k.lead := by
  cases rs with
  | nil => simp [leadScalars] at h
  | cons r _ =>
    simp only [leadScalars, List.head?_cons, Option.bind_some] at h
    cases hr : Part.MaskedSum.roundOf (k.lead + 1) 1 r with
    | none => simp [Part.MaskedSum.firstRound, hr] at h
    | some x =>
      obtain ⟨s, dr⟩ := x
      have hl : s.length = k.lead + 1 := (Part.MaskedSum.roundOf_spec hr).2.1
      simp only [Part.MaskedSum.firstRound, hr, Option.map_some, Option.some.injEq] at h
      rw [← h, List.length_take, hl]
      omega

/-- The same for "level z start": t: the level's rounds, LINE's with them. -/
theorem level_ends {z : Point} {start : Form} {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum}
    (hW : WellLaid F0) (h : level z start F0 t = some (S, F1, [])) (mask : Nat → E) :
    ∃ (R : Part.MaskedSum.Read) (T : E),
      readAll (callOf 0 z 2) (t.take (z.size + 3)) = some R ∧ R.values.length = 2 ∧
      S.psc = some (heardRec start T R (callOf 0 z 2) (F0.next + 0)) ∧
      S.r = (challenges (callOf 0 z 2) (heardRec start T R (callOf 0 z 2) (F0.next + 0))).toArray ∧
      (∀ i, i < ownSlots (callOf 0 z 2).all →
        rd (hidden F1 mask (F0.next + 0 + i)) = rd (mask (F0.next + 0 + i))) ∧
      ∀ j, j < 2 →
        S.end_ j = { var := Aff.slot (F0.next + 0 + ownSlots (callOf 0 z 2).all + j),
                     shown := R.values.getD j zeroE } ∧
        rd (hidden F1 mask (F0.next + 0 + ownSlots (callOf 0 z 2).all + j)) =
          rd (R.values.getD j zeroE) - rd ((R.rounds.map (·.2)).getLastD zeroE) *
            rd (mask (F0.next + 0 + ownSlots (callOf 0 z 2).all + j)) := by
  unfold level at h
  obtain ⟨cs, G1, l1, h1, k1⟩ := bind_some h
  obtain ⟨c, s⟩ := cs
  dsimp only at k1
  obtain ⟨ag, G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨a, g⟩ := ag
  dsimp only at k2
  obtain ⟨dn, G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, rfl, rfl⟩ := need_some h3
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k3
  have hG : G1 = G2 := round_some h2
  subst hG
  obtain ⟨e1, _, _⟩ := heardBy_cut h1
  obtain ⟨ld, R, T, b1, b2, _, b4, b5, b6, _, b8, b9⟩ := heardBy_ends hW e1 mask
  have hl0 : ld.length = 0 := leadScalars_len b1
  rw [hl0] at b5 b6 b8 b9
  exact ⟨R, T, b2, b4, b5, b6, b8, b9⟩

/-- The same for "sumcheck z n". -/
theorem sumcheck_ends {z : Point} {n : Nat} {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum}
    (hW : WellLaid F0) (h : sumcheck z n F0 t = some (S, F1, [])) (mask : Nat → E) :
    ∃ (c0 : E) (R : Part.MaskedSum.Read) (T : E),
      leadScalars (callOf 1 z n) t = some [c0] ∧ readAll (callOf 1 z n) t = some R ∧
      R.values.length = n ∧ S.claimed = (hidOf F0.next [c0]).getD 0 {} ∧
      S.psc = some (heardRec ((hidOf F0.next [c0]).getD 0 {}).var T R (callOf 1 z n)
        (F0.next + 1)) ∧
      S.r = (challenges (callOf 1 z n) (heardRec ((hidOf F0.next [c0]).getD 0 {}).var T R
        (callOf 1 z n) (F0.next + 1))).toArray ∧
      rd (hidden F1 mask F0.next) = rd c0 - rd (mask F0.next) ∧
      (∀ i, i < ownSlots (callOf 1 z n).all →
        rd (hidden F1 mask (F0.next + 1 + i)) = rd (mask (F0.next + 1 + i))) ∧
      ∀ j, j < n →
        S.end_ j = { var := Aff.slot (F0.next + 1 + ownSlots (callOf 1 z n).all + j),
                     shown := R.values.getD j zeroE } ∧
        rd (hidden F1 mask (F0.next + 1 + ownSlots (callOf 1 z n).all + j)) =
          rd (R.values.getD j zeroE) - rd ((R.rounds.map (·.2)).getLastD zeroE) *
            rd (mask (F0.next + 1 + ownSlots (callOf 1 z n).all + j)) := by
  unfold sumcheck at h
  obtain ⟨cs, G1, l1, h1, k1⟩ := bind_some h
  obtain ⟨c, s⟩ := cs
  dsimp only at k1
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k1
  obtain ⟨ld, R, T, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := heardBy_ends hW h1 mask
  have hl1 : ld.length = 1 := leadScalars_len b1
  obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.mp hl1
  subst b3
  refine ⟨c0, R, T, b1, b2, b4, rfl, b5, b6, ?_, b8, b9⟩
  have := b7 0 (by simp)
  simpa using this

end VerifiableInference.Desc.Kinds.Head.Law
