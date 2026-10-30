-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieClaimL1.lean: THE
CLAIMS' TIE AT THE KIND'S OWN BLOCK OF THE SECOND LOOKUP (borders 10 and 11 of the key file's first
chain): the second and the fourth of the four implications that a tie by Leads.conseq asks at the
field r1_10. As at the first lookup (TieClaimFront.lean, TieClaimBehind.lean), and besides: what the
first lookup has left in the record rides: the table's items rows 0 and kclaims 0 against the links'
Early (TieEarly.lean), under what the history gives of the record's rows and claims on keys
(OffWalk.lean).

Main names:
  done_zero: under the table's promise at border 10 or 11 the record holds the first lookup's rows,
    not none, and at least as many claims on keys as the lookup has parts.
  claim_front₁: On₁ … 10 a with RowsOff of a's record, (rowT 1 2).rel a ⊢ Cl₁ … 10 a.
  claim_behind₁: On₁ … 11 b with RowsOff and KeysLow of b's record, (rowT 1 3).on b, Cl₁ … 11 b ⊢
    (rowT 1 3).rel b.

Object: the links' rows and the table of the first chain (TieStated.lean).
User: FieldR110.lean.
Letters and premises: those of claim_front₀ and claim_behind₀, and those of rec_of_hist.

Limits. One way each. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieClaimBehind
import Johnson.RunOne.Law.TieEarly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieClaimL1
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Fork)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Source KRead Where KItem closedAt mkOf matOf valOf
  sentB groupB doneB core₁ shape₁_iff)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁)
open Johnson.RunOne.KeyRows1 (open₁ n₁ on₁_two plan₁ readers₁ book₁ slots₁ meaning₁At)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.LinkKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.FrontSteps
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.LettersAt
open Johnson.RunOne.Law.Walk
open Johnson.RunOne.Law.OffWalk
open Johnson.RunOne.Law.TieStated
open Johnson.RunOne.Law.TiePromise
open Johnson.RunOne.Law.TieKeys
open Johnson.RunOne.Law.TieClaimFront
open Johnson.RunOne.Law.TieClaimBack
open Johnson.RunOne.Law.TieClaimBehind
open Johnson.RunOne.Law.TieAgree
open Johnson.RunOne.Law.TieEarly
open Johnson.RunOne.Law.TieDone
open LPFD (On₁')

variable {Cells Mm Smp Rec : Type} {X : Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces} {D : WholeD} {B : BaseSt Cells Mm Smp Rec}
  {at_ : Where} {R : KRead Cells Mm} {coll : Strs → Rec → Prop}

/-- What doneB says of the first lookup where one lookup is done. -/
theorem done_parts (s : FirstState) (L : WfLookup) (hL : X.Y.k.oneTime.ranges.lookups[0]? = some L)
    (h : doneB (plan₁ X.Y.k.oneTime) (readers₁ X.Y.k.oneTime) 2 1 s = true) :
    ∃ rows keys, s.base.rows[0]? = some rows ∧ rows ≠ [] ∧ s.base.keys[0]? = some keys ∧
      L.parts.length ≤ keys.length := by
  unfold doneB at h
  have h0 := List.all_eq_true.1 h 0 (by simp)
  simp only [Nat.zero_lt_one, if_true, Bool.and_eq_true] at h0
  obtain ⟨hA, hB⟩ := h0
  have hA' : (s.base.rows[0]?).any (fun r => !r.isEmpty) = true := hA
  cases hr : s.base.rows[0]? with
  | none => rw [hr] at hA'; cases hA'
  | some rows =>
    rw [hr] at hA'
    have hne : rows ≠ [] := by
      rintro rfl
      cases hA'
    have hB' : (match (s.base.keys[0]?).bind (Johnson.RunOne.KeyReaders.pendingOf X.Y.k.oneTime 0),
        X.Y.k.oneTime.ranges.lookups[0]? with
      | some ks, some L => ks.length == L.parts.length
      | _, _ => false) = true := hB
    rw [hL] at hB'
    cases hk : s.base.keys[0]? with
    | none => rw [hk] at hB'; cases hB'
    | some keys =>
      rw [hk] at hB'
      have e : Johnson.RunOne.KeyReaders.pendingOf X.Y.k.oneTime 0 keys = some ((L.parts.zip
          keys).map
          fun x => Wf.pendingRow (Wf.matrixOf X.Y.k.oneTime.lin) L x.1 x.2
            (Wf.eqPlaces (Wf.matrixOf X.Y.k.oneTime.lin) x.2.point)) := by
        unfold Johnson.RunOne.KeyReaders.pendingOf
        rw [hL]
        rfl
      have hB'' : (match Johnson.RunOne.KeyReaders.pendingOf X.Y.k.oneTime 0 keys, some L with
        | some ks, some L => ks.length == L.parts.length
        | _, _ => false) = true := hB'
      rw [e] at hB''
      have e2 := beq_iff_eq.1 hB''
      rw [List.length_map, List.length_zip] at e2
      exact ⟨rows, keys, rfl, hne, rfl, by omega⟩

/-- Under the table's promise at border 10 or 11. -/
theorem done_zero (k : ℕ) (hk : k = 10 ∨ k = 11) (a : (Xi × FirstState) × (fr₁ D).E.Str)
    (hon : On₁ X N P D B at_ R coll k a) (L : WfLookup)
    (hL : X.Y.k.oneTime.ranges.lookups[0]? = some L) :
    ∃ rows keys, a.1.2.base.rows[0]? = some rows ∧ rows ≠ [] ∧
      a.1.2.base.keys[0]? = some keys ∧ L.parts.length ≤ keys.length := by
  have h2 := on₁_two _ _ _ _ _ _ _ k a hon
  obtain hm | ⟨hs, -⟩ := hon
  · exact absurd rfl hm
  rw [h2] at hs
  have hc := ((shape₁_iff _ _ _ _ _ _ _).1 hs).2
  refine done_parts a.1.2 L hL ?_
  rcases hk with rfl | rfl
  · have h' : ((sentB (plan₁ X.Y.k.oneTime) (readers₁ X.Y.k.oneTime) a.1.2 0 &&
      sentB (plan₁ X.Y.k.oneTime) (readers₁ X.Y.k.oneTime) a.1.2 1 && !sentB (plan₁ X.Y.k.oneTime)
          (readers₁ X.Y.k.oneTime) a.1.2 2 &&
      groupB (readers₁ X.Y.k.oneTime) a.1.2 false 0 && doneB (plan₁ X.Y.k.oneTime) (readers₁
          X.Y.k.oneTime) 2 1 a.1.2 &&
      ((readers₁ X.Y.k.oneTime).pile a.1.2).isNone) && _) = true := hc
    have h1 := (Bool.and_eq_true_iff.1 h').1
    simp only [Bool.and_eq_true] at h1
    exact h1.1.2
  · have h' : ((sentB (plan₁ X.Y.k.oneTime) (readers₁ X.Y.k.oneTime) a.1.2 0 &&
      sentB (plan₁ X.Y.k.oneTime) (readers₁ X.Y.k.oneTime) a.1.2 1 && !sentB (plan₁ X.Y.k.oneTime)
          (readers₁ X.Y.k.oneTime) a.1.2 2 &&
      groupB (readers₁ X.Y.k.oneTime) a.1.2 false 0 && doneB (plan₁ X.Y.k.oneTime) (readers₁
          X.Y.k.oneTime) 2 1 a.1.2 &&
      ((readers₁ X.Y.k.oneTime).pile a.1.2).isNone) && _) = true := hc
    have h1 := (Bool.and_eq_true_iff.1 h').1
    simp only [Bool.and_eq_true] at h1
    exact h1.1.2

/-- **THE CLAIMS' TIE IN FRONT OF THE KIND'S BLOCK OF LOOKUP 1, ONE WAY.** -/
theorem claim_front₁ (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (hp : (FK X N P).planOk = true) (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (a : (Xi × FirstState) × (fr₁ D).E.Str) (hon : On₁ X N P D B at_ R coll 10 a)
    (hoff : RowsOff a.1.2) (hrel : (rowT X N P D B at_ R coll 1 2).rel a) :
    Cl₁ X N P D B at_ R 10 a := by
  obtain ⟨⟨p₀, s⟩, y⟩ := a
  have h2 := on₁_two _ _ _ _ _ _ _ 10 _ hon
  have hW := fk_admitted X N P hp
  have t0 := tests_at hW (i := 0) (by rw [hn]; omega)
  have t1 := tests_at hW (i := 1) (by rw [hn]; omega)
  obtain ⟨rows0, keys0, z1, z2, z3, z4⟩ := done_zero 10 (Or.inl rfl) ((p₀, s), y) hon _ t0.1
  unfold rowT at hrel
  obtain ⟨w, ⟨hdec, hE, -, hO⟩, hIn⟩ := (upF_rel (Fr := fr₁ D) _ p₀ s y).1 hrel
  obtain ⟨q1, q2, q3⟩ := decT_some hdec
  have hK1 := (in_iff _ _ _ _ _ _ _).1 hIn
  rw [matOf_cut] at hK1
  obtain ⟨rows, keys, e1, e2, e3, e4⟩ := hE 0 (by omega)
  have e1' : (s.base.rows.take 1)[0]? = some rows := e1
  have e2' : (s.base.keys.take 1)[0]? = some keys := e2
  rw [List.getElem?_take_of_lt (by omega)] at e1' e2'
  obtain rfl := Option.some.inj (e1'.symm.trans z1)
  obtain rfl := Option.some.inj (e2'.symm.trans z3)
  have hmem : ∀ i ∈ open₁ 2 10, i = KItem.unmarked ∨ i = .pinT ∨ i = .inRange 1 ∨ i = .pin 0 ∨
      i = .srow 0 ∨ i = .pin 1 ∨ i = .srow 1 ∨ i = .rows 0 ∨ i = .kclaims 0 := by decide
  refine ⟨w.1, ?_⟩
  show ∀ i ∈ open₁ (n₁ X.Y.k.oneTime) 10, _
  rw [h2]
  intro i hi
  rcases hmem i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rfl
  · exact (pinw_atSt p₀ 1 s _ _).1 q1
  · refine ⟨_, t1.1, ?_⟩
    rw [hsame]
    exact (inRange_iff _ _ _ _ t1.2.1 t1.2.2).2 hK1
  · exact (pin_atSt hS p₀ 1 s _ _ _ _).1 q2
  · exact srow_atSt 0 p₀ 1 s _ _ _ (hO (strsOf (fr₁ D) y)).1
  · exact (pin_atSt hS p₀ 1 s _ _ _ _).1 q3
  · exact srow_atSt 1 p₀ 1 s _ _ _ (hO (strsOf (fr₁ D) y)).2
  · exact rows_of_allSay hsame 0 p₀ 1 s _ w.1 hoff rows z1 z2 e3
  · exact kclaims_of_pend hsame 0 p₀ s _ w.1 _ t0.1 keys z3 z4 e4

set_option maxHeartbeats 1600000 in
/-- **THE CLAIMS' TIE BEHIND THE KIND'S BLOCK OF LOOKUP 1, ONE WAY.** -/
theorem claim_behind₁ (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (hp : (FK X N P).planOk = true) (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (hbit : ∀ (valB : ℕ → E) (n : ℕ),
      n < 2 ^ ((faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
          X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 1))).mu + (faceOfLkp (Wf.lookupOf
              X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
                  1))).d) →
      readE (VerifiableInference.Desc.Key.bitVec X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 1 valB n)
          =
        Planes.bitsOf X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 1 (fun k => readE (valB k))
          (n / 2 ^ (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
              X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 1))).mu) (n % 2 ^ (faceOfLkp (Wf.lookupOf
                  X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
                      1))).mu))
    (b : (Xi × FirstState) × (fr₁ D).E.Str) (hon : On₁ X N P D B at_ R coll 11 b)
    (hoff : RowsOff b.1.2) (hlow : KeysLow b.1.2)
    (hT : (rowT X N P D B at_ R coll 1 3).on b) (hcl : Cl₁ X N P D B at_ R 11 b) :
    (rowT X N P D B at_ R coll 1 3).rel b := by
  obtain ⟨⟨p₀, s⟩, y⟩ := b
  have h2 := on₁_two _ _ _ _ _ _ _ 11 _ hon
  have hW := fk_admitted X N P hp
  have hid := fk_messageId X N P hp
  have t0 := tests_at hW (i := 0) (by rw [hn]; omega)
  have t1 := tests_at hW (i := 1) (by rw [hn]; omega)
  have hadm := Lk6.adm_of_tests X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) _
      t1.2.1 t1.2.2
  obtain ⟨w', hw'⟩ := hcl
  have hall : ∀ i ∈ open₁ (n₁ X.Y.k.oneTime) 11, _ := hw'
  rw [h2] at hall
  have iT := hall .pinT (by decide)
  have i0 := hall (.pin 0) (by decide)
  have i1 := hall (.pin 1) (by decide)
  have s0 := hall (.srow 0) (by decide)
  have s1 := hall (.srow 1) (by decide)
  have ro := hall (.rows 0) (by decide)
  have kc := hall (.kclaims 0) (by decide)
  obtain ⟨-, Sg1, g1, G1, a1, a2, a3, fo⟩ := hall (.forms 1 "objects") (by decide)
  obtain ⟨Sg2, L2, g2, G2, b1, b2, b3, b4, wp⟩ := hall (.worth 1 "planes") (by decide)
  obtain ⟨Sg3, L3, g3, G3, c1, c2, c3, c4, wk⟩ := hall (.worth 1 "keys") (by decide)
  have e0 : VerifiableInference.Desc.Key.lkpOf (plan₁ X.Y.k.oneTime) X.Y.k.oneTime.ranges 1 = some
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
          1)) :=
    Johnson.RunOne.Law.LinkAtFK.look_at X.Y.k.oneTime 1 (by rw [hn]; omega)
  obtain rfl := Option.some.inj (a1.symm.trans e0)
  obtain rfl := Option.some.inj (b1.symm.trans e0)
  obtain rfl := Option.some.inj (c1.symm.trans e0)
  obtain rfl := Option.some.inj (b2.symm.trans t1.1)
  obtain rfl := Option.some.inj (c2.symm.trans t1.1)
  obtain rfl := Option.some.inj (b3.symm.trans a2)
  obtain rfl := Option.some.inj (c3.symm.trans a2)
  obtain rfl := Option.some.inj (b4.symm.trans a3)
  obtain rfl := Option.some.inj (c4.symm.trans a3)
  have wp' := wp.resolve_right fun h => absurd h.1 (by decide)
  have wk' := wk.resolve_left fun h => absurd h.1 (by decide)
  obtain ⟨u, hu⟩ := decT_of_pins (X := X) (N := N) (P := P) (D := D) (B := B) (at_ := at_)
    (a := (pullK (stK p₀ 1 s), y)) (w := w')
    ⟨(pinw_atSt p₀ 1 s _ _).2 iT, (pin_atSt hS p₀ 1 s _ _ _ _).2 i0,
      (pin_atSt hS p₀ 1 s _ _ _ _).2 i1⟩
  obtain ⟨q1, q2, q3⟩ := decT_some hu
  have hag : Agree R w' u := agree_of_pins 11 (by omega) (by omega) ((p₀, s), y) hon w' u iT
    ((pinw_atSt p₀ 1 s _ _).1 q1) i0 ((pin_atSt hS p₀ 1 s _ _ _ _).1 q2) i1
    ((pin_atSt hS p₀ 1 s _ _ _ _).1 q3)
  have h3 := size_three 11 (by omega) (by omega) ((p₀, s), y) hon
  unfold rowT at hT
  obtain ⟨-, ⟨hInv, hHeard⟩, -⟩ := (rows7_on (Fr := fr₁ D) _ _ _ _ _ _ _ _ _ p₀ _ _ _ _ _ _ 1 3
    (by omega) s y).1 ((upF_on (Fr := fr₁ D) _ p₀ s y).1 hT)
  obtain ⟨G0, g0, d1, d2, -, -, -, d6, d7⟩ := hHeard
  obtain rfl := Option.some.inj (d1.symm.trans a3)
  obtain rfl := Option.some.inj (d2.symm.trans a2)
  have fo' := fo
  have wp'' := wp'.2
  have wk'' := wk'.2
  rw [hsame] at fo' wp'' wk''
  have hhome : VerifiableInference.Desc.Key.K3At.home Johnson.RunOne.KeyRows1.k3At₁ s = _ := hInv.1
  rw [hhome] at fo' wp'' wk''
  obtain ⟨cl, G', hc, hDone⟩ := done_of_sentences
    (A := AK X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime 1) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
            X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 1)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 1) 0 (TK Xi))
    (sl := slk X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime 1) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
            X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 1)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 1) 0 (TK Xi))
    (μ := msgk X.Y.k.oneTime 1 X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime 1) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
            X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 1)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 1) 0 (TK Xi) (wdT X R) (mxT X R)
            u)
    (w := wdT X R u) (x := X.Y.k.oneTime.ranges) (codes := X.Y.k.oneTime.codes) (i := 1) hadm
    (tiedK _ _ _ _ _ _ _ _ _ _) (Lof X.Y.k.oneTime 1) t1.1 (mkOf (plan₁ X.Y.k.oneTime) R w')
    (fun z hz => by
      show readE (valOf (plan₁ X.Y.k.oneTime) R u z.oracle .mask z.index) =
        readE (valOf (plan₁ X.Y.k.oneTime) R w' z.oracle .mask z.index)
      rw [valOf_agree X.Y.k.oneTime hag z.oracle (by rw [← h3]; exact (hInv.2.1.2 z hz).1)])
    (stK p₀ 1 s) X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (matOf (plan₁
        X.Y.k.oneTime) R w') rfl
    t1.2.1 t1.2.2
    (by
      have hk := keysAreK (T := TK Xi) (id := X.Y.k.oneTime.ranges.messageId)
        (m := Wf.matrixOf X.Y.k.oneTime.lin) (l := Lof X.Y.k.oneTime 1) (hs := _) (stK p₀ 1 s)
        (msgk X.Y.k.oneTime 1 X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime 1) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
                X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 1)
          (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
              X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 1) 0 (TK Xi) (wdT X R) (mxT X R)
            u)
      rw [matOf_cut] at hk
      rw [matOf_agree X.Y.k.oneTime hag]
      exact hk)
    _ (fun n hnn => by
      rw [hbit _ n hnn, hid, hag.2.2]
      rfl)
    g0 G0 (fun q hq => d7 q (lt_of_lt_of_eq hq (List.length_map _).symm))
    fo' wp'' wk''
  obtain ⟨tp, hpl⟩ := closed_planes hc
  obtain ⟨rows, r1, r2⟩ := allSay_of_rows (X := X) hsame 0 p₀ 1 s _ u hoff
    (rows_agree hag 0 (p₀, s) h3 _ ro)
  obtain ⟨keys, k1, k2⟩ := pend_of_kclaims (X := X) hsame 0 p₀ s _ u _ t0.1
    (kclaims_agree hag 0 (p₀, s) h3 hlow _ kc)
  unfold rowT
  refine (upF_rel (Fr := fr₁ D) _ p₀ s y).2 ⟨(u, ()), ⟨hu, fun k hk => ?_,
    fun k h1 hk => absurd hk (by rw [hn]; omega),
    fun y' => ⟨srow_to_atSt 0 p₀ 1 s _ _ _ (srow_agree _ hag 0 (p₀, s) h3 _ s0),
      srow_to_atSt 1 p₀ 1 s _ _ _ (srow_agree _ hag 1 (p₀, s) h3 _ s1)⟩⟩, _,
    ⟨G0, g0, G0, cl, G', tp, G', a3, a2, PscRun.Later.refl _, hpl, PscRun.Later.refl _, rfl⟩,
    hDone⟩
  obtain rfl : k = 0 := by omega
  refine ⟨rows, keys, ?_, ?_, r2, k2⟩
  · show (s.base.rows.take 1)[0]? = some rows
    rw [List.getElem?_take_of_lt (by omega)]
    exact r1
  · show (s.base.keys.take 1)[0]? = some keys
    rw [List.getElem?_take_of_lt (by omega)]
    exact k1

end Johnson.RunOne.Law.TieClaimL1

#print axioms Johnson.RunOne.Law.TieClaimL1.done_zero
#print axioms Johnson.RunOne.Law.TieClaimL1.claim_front₁
#print axioms Johnson.RunOne.Law.TieClaimL1.claim_behind₁
