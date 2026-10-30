-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/ScalesReturn.lean: what the goals' reader accepts, the verifier's tests on the
scale file take. No return of publicOf is asked.

publicOf (OnBytes/Model/VerifyPublic.lean:152) puts three tests to the scale file: scalesOf (its
length), scalesHeld (the ranges of its words) and noWrap (no sum wraps around in the field), all in
OnBytes/Model/LayerLayout.lean. The goals' reader (VerifierAndGoals.readFiles) asks Lawful
(Inst/Model/Scales.lean:104): closed intervals (Ranges, Inst/Model/FF/ScalesDef.lean:154). The
library's theorem lawfulW_iff (Inst/Model/FF/Lawful.lean:100) says that Ranges is LawfulW; that
LawfulW renders the verifier's checks is said by LawfulW's docstring alone. Here the verifier's own
text comes in: under the intervals it refuses nothing.
  shapeAt e1 e2 eF: the hand-written shape hKF but for the three free numbers.
  WordsOK s l: the intervals, at the words of layer l as the verifier reads them.
  heldAt_ok, noWrapAt_ok: under WordsOK the tests on layer l refuse nothing. Each clause of noWrapAt
    is evaluated in Lean's kernel at every value of its interval (at most 1,584 values a clause).
  held_ok, noWrap_ok: so the whole tests, with the three free numbers below 2^48.
  wordsOK_of_lawful: lawful settings off a scale file of 48 layers give WordsOK at all 48.
  shape_of_read: in the goals' scope the verifier's scan of the parameter file returns, and the
    shape that the verifier makes of it is shapeAt at the numbers that the goals' reader read.
  scales_return: in the goals' scope the three tests pass at that shape and the width 5120.
Not claimed: that publicOf returns; that its layout's field dq is 5120 (that is read off a layout
that has returned); anything on attention's shift, which these three tests do not read.
-/
import Johnson.Goal.Meaning.Pub34Scope
import Johnson.Flat.ScalesSame
import Johnson.Flat.SettingsRead

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Ret

open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.Road

/-- The layers' shape in the goals' scope: hKF but for the three free numbers. -/
abbrev shapeAt (e1 e2 eF : ℕ) : Shape := { hKF with eps1 := e1, eps2 := e2, epsF := eF }

/-! ## Steps that may refuse, one after the other -/

theorem seq_ok {α : Type} {x : Except String PUnit} {y : Except String α} {r : α}
    (hx : x = .ok PUnit.unit) (hy : y = .ok r) : (do x; y) = .ok r := by
  rw [hx]
  exact hy

theorem refuse_ok {b : Bool} (n : String) (h : b = false) : refuseIf b n = .ok () := by
  rw [h]
  rfl

theorem need_ok {b : Bool} (n : String) (h : b = true) : need b n = .ok () := by
  rw [h]
  rfl

theorem forM_ok {α : Type} (f : α → Except String Unit) :
    ∀ l : List α, (∀ a ∈ l, f a = .ok ()) → l.forM f = .ok ()
  | [], _ => rfl
  | a :: l, h => by
    show (f a >>= fun _ => l.forM f) = .ok ()
    rw [h a List.mem_cons_self]
    exact forM_ok f l fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem forIn_two_ok {α : Type} (a b : α) (f : α → PUnit → Except String (ForInStep PUnit))
    (ha : f a PUnit.unit = .ok (.yield PUnit.unit))
    (hb : f b PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn [a, b] PUnit.unit f = .ok PUnit.unit := by
  rw [List.forIn_cons, ha]
  show forIn [b] PUnit.unit f = _
  rw [List.forIn_cons, hb]
  rfl

theorem all_at {p : ℕ → Bool} {n : ℕ} (h : (List.range n).all p = true) {k : ℕ} (hk : k < n) :
    p k = true :=
  List.all_eq_true.1 h k (List.mem_range.2 hk)

theorem ok_of_isOk {x : Except String Unit} (h : x.isOk = true) : x = .ok () := by
  cases x with
  | error e => cases h
  | ok u => rfl

/-! ## The ranges, in the verifier's letters -/

/-- The closed intervals of the library's Ranges (Inst/Model/FF/ScalesDef.lean:154), at the words of
layer l as the verifier reads them. -/
structure WordsOK (s : Scales) (l : ℕ) : Prop where
  kq : 5 ≤ s.kl l Lkq ∧ s.kl l Lkq ≤ 32
  kk : 5 ≤ s.kl l Lkk ∧ s.kl l Lkk ≤ 32
  qk : s.kl l Lkq = s.kl l Lkk ∨ (16 ≤ s.kl l Lkq ∧ 16 ≤ s.kl l Lkk)
  kv : 1 ≤ s.kl l Lkv ∧ s.kl l Lkv ≤ 24
  ko : 1 ≤ s.kl l Lko ∧ s.kl l Lko ≤ 19
  kg : 1 ≤ s.kl l Lkg ∧ s.kl l Lkg ≤ 24
  ku : 1 ≤ s.kl l Lku ∧ s.kl l Lku ≤ 24
  kd : 10 ≤ s.kl l Lkd ∧ s.kl l Lkd ≤ 19
  n1 : 24 ≤ s.kl l LM1 ∧ s.kl l LM1 ≤ 47 ∧ 17 ≤ s.kl l LK1 ∧ s.kl l LK1 ≤ 32 ∧
    s.kl l LM1 ≤ s.kl l LK1 + 14
  n2 : 24 ≤ s.kl l LM2 ∧ s.kl l LM2 ≤ 47 ∧ 17 ≤ s.kl l LK2 ∧ s.kl l LK2 ≤ 32 ∧
    s.kl l LM2 ≤ s.kl l LK2 + 14
  rp : s.klRp l ≤ 1
  kr : l % 2 = 1 → 8 ≤ s.klM l 0 ∧ s.klM l 0 ≤ 24
  kgR : l % 2 = 1 → 1 ≤ s.klM l 1 ∧ s.klM l 1 ≤ 24
  kuR : l % 2 = 1 → 1 ≤ s.klM l 2 ∧ s.klM l 2 ≤ 24

/-! ## scalesHeldAt -/

theorem shift_ok {k form top : ℕ}
    (ht : (if form == 0 then 16 else if form == 1 then 24 else 32) = top)
    (h : 1 ≤ k ∧ k ≤ top) : shiftHeld k form = .ok () := by
  unfold shiftHeld
  refine refuse_ok _ ?_
  rw [ht]
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt]
  exact h

theorem norm_ok {M K : ℕ} (h : 24 ≤ M ∧ M ≤ 47 ∧ 17 ≤ K ∧ K ≤ 32 ∧ M ≤ K + 14) :
    refuseIf (decide (M < 24) || decide (M > 47) || decide (K + 14 < M) || decide (K < 17) ||
      decide (K > 32)) "KL-norm" = .ok () := by
  refine refuse_ok _ ?_
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt, gt_iff_lt]
  omega

theorem isMoe_at (e1 e2 eF l : ℕ) : (shapeAt e1 e2 eF).isMoeL l = (l % 2 == 1) := by
  show ((shapeAt e1 e2 eF).p3 && l % 2 == 1) = _
  have : (shapeAt e1 e2 eF).p3 = true := rfl
  rw [this, Bool.true_and]

theorem heldAt_ok (e1 e2 eF : ℕ) {s : Scales} {l : ℕ} (W : WordsOK s l) :
    scalesHeldAt (shapeAt e1 e2 eF) s l = .ok () := by
  unfold scalesHeldAt
  refine seq_ok (shift_ok rfl W.kg) <| seq_ok (shift_ok rfl W.ku) <|
    seq_ok (shift_ok (top := 24) rfl ⟨by have := W.kd; omega, by have := W.kd; omega⟩) <|
    seq_ok (shift_ok (top := 32) rfl ⟨by have := W.kq; omega, W.kq.2⟩) <|
    seq_ok (shift_ok (top := 32) rfl ⟨by have := W.kk; omega, W.kk.2⟩) <|
    seq_ok (shift_ok rfl W.kv) <|
    seq_ok (shift_ok (top := 24) rfl ⟨W.ko.1, by have := W.ko; omega⟩) <| seq_ok (refuse_ok _ ?_) <|
    seq_ok ?_ <| seq_ok (refuse_ok _ ?_) ?_
  · rcases W.qk with e | ⟨a, b⟩
    · rw [e]
      simp
    · simp only [Bool.and_eq_false_iff, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt]
      exact Or.inr ⟨a, b⟩
  · exact forIn_two_ok _ _ _ (seq_ok (norm_ok W.n1) rfl) (seq_ok (norm_ok W.n2) rfl)
  · simp only [decide_eq_false_iff_not, not_lt, gt_iff_lt]
    exact W.rp
  · rw [isMoe_at]
    by_cases hl : l % 2 = 1
    · rw [if_pos (by simpa using hl)]
      exact seq_ok (shift_ok (top := 24) rfl ⟨by have := W.kr hl; omega, (W.kr hl).2⟩) <|
        seq_ok (shift_ok rfl (W.kgR hl)) (shift_ok rfl (W.kuR hl))
    · rw [if_neg (by simpa using hl)]
      rfl

/-! ## noWrapAt -/

/-- The bound on a committed cell at which noWrap asks its conditions. -/
abbrev TY : ℕ := 2 ^ (1 + lbz)

theorem site_range (n : String) (form A SP Qb lo hi : ℕ)
    (H : ((List.range (hi + 1)).all fun k =>
      decide (k < lo) || (noWrapSite TY n k form A SP Qb).isOk) = true)
    {k : ℕ} (h : lo ≤ k ∧ k ≤ hi) : noWrapSite TY n k form A SP Qb = .ok () := by
  have a := all_at H (k := k) (by omega)
  rw [Bool.or_eq_true, decide_eq_true_eq] at a
  rcases a with a | a
  · omega
  · exact ok_of_isOk a

theorem ite_ok {c : Prop} [Decidable c] {x : Except String PUnit}
    (h : c → x = .ok PUnit.unit) : (if c then x else pure PUnit.unit) = .ok PUnit.unit := by
  by_cases hc : c
  · rw [if_pos hc]
    exact h hc
  · rw [if_neg hc]
    rfl

theorem gate_ok {k : ℕ} (h : 1 ≤ k ∧ k ≤ 24) :
    noWrapSite TY "gate" k 1 (5120 * clampBound * BW) (2 * (128 + 2 ^ 22) + 1) (128 + 2 ^ 22) =
      .ok () :=
  site_range _ _ _ _ _ 1 24 (by decide +kernel) h

theorem up_ok {k : ℕ} (h : 1 ≤ k ∧ k ≤ 24) :
    noWrapSite TY "up" k 1 (5120 * clampBound * BW) (2 ^ 16) (2 ^ 15) = .ok () :=
  site_range _ _ _ _ _ 1 24 (by decide +kernel) h

theorem normSite_ok {M K : ℕ} (hM : M ≤ 47) (hK : 17 ≤ K ∧ K ≤ 32) :
    noWrapSite TY "norm" K 2 (2 ^ M + 2 ^ (39 - 1)) (2 ^ 16) (2 ^ 15) = .ok () := by
  have H : ((List.range 48).all fun M => (List.range 33).all fun K =>
      decide (K < 17) ||
        (noWrapSite TY "norm" K 2 (2 ^ M + 2 ^ (39 - 1)) (2 ^ 16) (2 ^ 15)).isOk) = true := by
    decide +kernel
  have a := all_at (all_at H (k := M) (by omega)) (k := K) (by omega)
  rw [Bool.or_eq_true, decide_eq_true_eq] at a
  rcases a with a | a
  · omega
  · exact ok_of_isOk a

theorem down_ok {k : ℕ} (h : 10 ≤ k ∧ k ≤ 19) :
    noWrapSite TY "down" k 1 (16384 * (SMAXTOP + 1) * 2 ^ LBU * BW) (2 ^ (39 + 2)) (2 ^ (39 + 1)) =
      .ok () :=
  site_range _ _ _ _ _ 10 19 (by decide +kernel) h

theorem qk_ok {k : ℕ} (h : 5 ≤ k ∧ k ≤ 32) :
    noWrapSite TY "qk" k 2 (2 * 2 ^ 12 * (5120 * clampBound * BW)) (2 ^ 16) (2 ^ 15) = .ok () :=
  site_range _ _ _ _ _ 5 32 (by decide +kernel) h

theorem o_ok {k : ℕ} (h : 1 ≤ k ∧ k ≤ 19) :
    noWrapSite TY "o" k 1 (5120 * clampBound * BW) (2 ^ (39 + 2)) (2 ^ (39 + 1)) = .ok () :=
  site_range _ _ _ _ _ 1 19 (by decide +kernel) h

theorem v_ok {k : ℕ} (h : 1 ≤ k ∧ k ≤ 24) :
    noWrapSite TY "v" k 1 (5120 * clampBound * BW) (2 ^ 16) (2 ^ 15) = .ok () :=
  site_range _ _ _ _ _ 1 24 (by decide +kernel) h

theorem lr_ok {k : ℕ} (h : 8 ≤ k ∧ k ≤ 24) :
    noWrapSite TY "lr" k 1 (5120 * clampBound * BW) (16 * (TY * 257) + 15) (8 * (TY * 257) + 7) =
      .ok () :=
  site_range _ _ _ _ _ 8 24 (by decide +kernel) h

theorem grc_ok {k : ℕ} (h : 8 ≤ k ∧ k ≤ 24) :
    need (decide ((5120 * clampBound * BW + 2 ^ (k - 1)) / 2 ^ (k + 3) + 1 + 2 ^ 15 + 2 ^ 16 <
      2 ^ 25)) "guard-radix-clamp" = .ok () := by
  have H : ((List.range 25).all fun k => decide (k < 8) ||
      decide ((5120 * clampBound * BW + 2 ^ (k - 1)) / 2 ^ (k + 3) + 1 + 2 ^ 15 + 2 ^ 16 <
        2 ^ 25)) = true := by decide +kernel
  have a := all_at H (k := k) (by omega)
  rw [Bool.or_eq_true, decide_eq_true_eq] at a
  rcases a with a | a
  · omega
  · exact need_ok _ a

theorem odd_of_moe {e1 e2 eF l : ℕ} (h : (shapeAt e1 e2 eF).isMoeL l = true) : l % 2 = 1 := by
  rw [isMoe_at] at h
  simpa using h

theorem noWrapAt_ok (e1 e2 eF : ℕ) {s : Scales} {l : ℕ} (W : WordsOK s l) :
    noWrapAt (shapeAt e1 e2 eF) s 5120 TY l = .ok () := by
  unfold noWrapAt
  by_cases hm : (shapeAt e1 e2 eF).isMoeL l = true
  · have ho := odd_of_moe hm
    simp only [hm, ↓reduceIte, Bool.true_and]
    exact seq_ok (gate_ok W.kg) <| seq_ok (gate_ok (W.kgR ho)) <|
      seq_ok (up_ok W.ku) <| seq_ok (up_ok (W.kuR ho)) <|
      seq_ok (normSite_ok W.n1.2.1 ⟨W.n1.2.2.1, W.n1.2.2.2.1⟩) <|
      seq_ok (normSite_ok W.n2.2.1 ⟨W.n2.2.2.1, W.n2.2.2.2.1⟩) <|
      seq_ok (down_ok W.kd) <| seq_ok (qk_ok W.kq) <| seq_ok (qk_ok W.kk) <| seq_ok (o_ok W.ko) <|
      seq_ok (v_ok W.kv) <| seq_ok (lr_ok (W.kr ho)) <|
      seq_ok (grc_ok (W.kr ho)) (need_ok _ (by decide +kernel))
  · have hf : (shapeAt e1 e2 eF).isMoeL l = false := by simpa using hm
    simp only [hf, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    exact seq_ok (gate_ok W.kg) <| seq_ok rfl <| seq_ok (up_ok W.ku) <| seq_ok rfl <|
      seq_ok (normSite_ok W.n1.2.1 ⟨W.n1.2.2.1, W.n1.2.2.2.1⟩) <|
      seq_ok (normSite_ok W.n2.2.1 ⟨W.n2.2.2.1, W.n2.2.2.2.1⟩) <|
      seq_ok (down_ok W.kd) <| seq_ok (qk_ok W.kq) <| seq_ok (qk_ok W.kk) <| seq_ok (o_ok W.ko) <|
      seq_ok (v_ok W.kv) <| seq_ok rfl rfl

/-! ## The three tests, whole -/

theorem held_ok (e1 e2 eF : ℕ) {s : Scales} (W : ∀ l < 48, WordsOK s l) :
    scalesHeld (shapeAt e1 e2 eF) s = .ok () :=
  forM_ok _ _ fun l hl => heldAt_ok e1 e2 eF (W l (List.mem_range.1 hl))

theorem noWrap_ok {e1 e2 eF : ℕ} (h1 : e1 < 2 ^ 48) (h2 : e2 < 2 ^ 48) (hF : eF < 2 ^ 48)
    {s : Scales} (W : ∀ l < 48, WordsOK s l) : noWrap (shapeAt e1 e2 eF) s 5120 = .ok () := by
  unfold noWrap noWrapWith
  refine seq_ok (forM_ok _ _ fun l hl => noWrapAt_ok e1 e2 eF (W l (List.mem_range.1 hl))) ?_
  simp only [show (shapeAt e1 e2 eF).p3 = true from rfl, show hKF.gcl = true from rfl,
    show hKF.NE = 128 from rfl, show hKF.xl = 5 from rfl, show hKF.d = 5120 from rfl, ↓reduceIte]
  exact seq_ok (need_ok _ (by decide +kernel)) <| seq_ok (need_ok _ (by decide +kernel)) <|
    seq_ok (need_ok _ (by decide +kernel)) <| seq_ok (need_ok _ (by decide +kernel)) <|
    seq_ok (need_ok _ (by decide +kernel)) <| seq_ok (need_ok _ (by decide +kernel)) <|
    seq_ok (need_ok _ (by decide +kernel)) <| seq_ok (need_ok _ (by decide +kernel)) <|
    seq_ok (need_ok _ (by decide +kernel)) <| seq_ok (need_ok _ (by decide +kernel)) <|
    seq_ok (need_ok _ (decide_eq_true h1)) <| seq_ok (need_ok _ (decide_eq_true h2)) <|
    need_ok _ (decide_eq_true hF)

/-! ## What the goals' reader accepts -/

section Read
open Inst.Model VerifiableInference.OnPublicFiles.Flat

/-- The record that scalesOf makes of a scale file at the shape in scope. -/
abbrev recOf (KL : ByteArray) : Scales := ⟨fileWords KL, 13, 48⟩

/-- Where klFileOf returns at 48 layers, the file has the length that the verifier asks. -/
theorem len_of_klFile {h : Hdr} {KL : ByteArray} {f : KLFile} (hL : h.L = 48)
    (hf : OnBytes.Flat.klFileOf h KL = some f) : (fileWords KL).size = 13 * 48 + 3 * 24 := by
  unfold OnBytes.Flat.klFileOf at hf
  dsimp only at hf
  split at hf
  · rename_i c
    have e := c.2.2
    rw [hL, Array.size_map] at e
    exact e
  · cases hf

/-- The words of a layer, as the reader has laid them, are the verifier's. -/
theorem lay_word {h : Hdr} {KL : ByteArray} {f : KLFile} (hL : h.L = 48)
    (hf : OnBytes.Flat.klFileOf h KL = some f) (L : Fin 48) (j : Fin 13) :
    f.lay L j = (recOf KL).kl L.val j.val := by
  rw [(klFileOf_fields hf).1 L j (by rw [hL]; exact L.isLt), word_same]
  rfl

theorem moe_word {h : Hdr} {KL : ByteArray} {f : KLFile} (hL : h.L = 48)
    (hf : OnBytes.Flat.klFileOf h KL = some f) (e : Fin 24) (j : Fin 3) :
    f.moe e j = (recOf KL).klM (2 * e.val + 1) j.val := by
  rw [(klFileOf_fields hf).2.1 e j (by rw [hL]; have := e.isLt; omega), word_same, hL]
  show _ = (fileWords KL).getD (13 * 48 + 3 * ((2 * e.val + 1) / 2) + j.val) 0
  rw [show (2 * e.val + 1) / 2 = e.val by omega]

/-- Lawful settings off a scale file: the ranges at the verifier's words. -/
theorem wordsOK_of_lawful {h : Hdr} {KL : ByteArray} {f : KLFile} {pp : ScalesAndPolicy} (hL : h.L = 48)
    (hf : OnBytes.Flat.klFileOf h KL = some f) (ho : ofKL f = some pp) (hw : Lawful pp) :
    ∀ l < 48, WordsOK (recOf KL) l := by
  intro l hl
  unfold ofKL at ho
  split at ho
  · rename_i hrp
    cases ho
    have R := hw.ff ⟨l, hl⟩
    have w : ∀ j : Fin 13, f.lay ⟨l, hl⟩ j = (recOf KL).kl l j.val := lay_word hL hf ⟨l, hl⟩
    have n1 := R.n1
    have n2 := R.n2
    unfold NormPar.OK at n1 n2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (w 0) ▸ R.kq
    · exact (w 1) ▸ R.kk
    · exact (w 0) ▸ (w 1) ▸ R.qk
    · exact (w 2) ▸ R.kv
    · exact (w 3) ▸ R.ko
    · exact (w 4) ▸ R.kg
    · exact (w 5) ▸ R.ku
    · exact (w 6) ▸ R.kd
    · have a : 24 ≤ f.lay ⟨l, hl⟩ 7 ∧ f.lay ⟨l, hl⟩ 7 ≤ 47 ∧ 17 ≤ f.lay ⟨l, hl⟩ 8 ∧
          f.lay ⟨l, hl⟩ 8 ≤ 32 ∧ f.lay ⟨l, hl⟩ 7 - 14 ≤ f.lay ⟨l, hl⟩ 8 := n1.2.2
      rw [w 7, w 8] at a
      obtain ⟨a1, a2, a3, a4, a5⟩ : 24 ≤ (recOf KL).kl l LM1 ∧ (recOf KL).kl l LM1 ≤ 47 ∧
        17 ≤ (recOf KL).kl l LK1 ∧ (recOf KL).kl l LK1 ≤ 32 ∧
        (recOf KL).kl l LM1 - 14 ≤ (recOf KL).kl l LK1 := a
      exact ⟨a1, a2, a3, a4, by omega⟩
    · have a : 24 ≤ f.lay ⟨l, hl⟩ 9 ∧ f.lay ⟨l, hl⟩ 9 ≤ 47 ∧ 17 ≤ f.lay ⟨l, hl⟩ 10 ∧
          f.lay ⟨l, hl⟩ 10 ≤ 32 ∧ f.lay ⟨l, hl⟩ 9 - 14 ≤ f.lay ⟨l, hl⟩ 10 := n2.2.2
      rw [w 9, w 10] at a
      obtain ⟨a1, a2, a3, a4, a5⟩ : 24 ≤ (recOf KL).kl l LM2 ∧ (recOf KL).kl l LM2 ≤ 47 ∧
        17 ≤ (recOf KL).kl l LK2 ∧ (recOf KL).kl l LK2 ≤ 32 ∧
        (recOf KL).kl l LM2 - 14 ≤ (recOf KL).kl l LK2 := a
      exact ⟨a1, a2, a3, a4, by omega⟩
    · have a := hrp ⟨l, hl⟩
      rw [w 12] at a
      have a' : (recOf KL).kl l 12 = if l % 4 = 3 then 0 else 1 := a
      show (recOf KL).kl l 12 ≤ 1
      rw [a']
      split <;> omega
    · intro hodd
      have a : 8 ≤ (if l % 2 = 1 then f.moe ⟨l / 2, by omega⟩ 0 else 17) ∧
          (if l % 2 = 1 then f.moe ⟨l / 2, by omega⟩ 0 else 17) ≤ 24 := R.kr
      rw [if_pos hodd, moe_word hL hf, show 2 * (l / 2) + 1 = l by omega] at a
      exact a
    · intro hodd
      have a : 1 ≤ (if l % 2 = 1 then f.moe ⟨l / 2, by omega⟩ 1 else 16) ∧
          (if l % 2 = 1 then f.moe ⟨l / 2, by omega⟩ 1 else 16) ≤ 24 := R.kg'
      rw [if_pos hodd, moe_word hL hf, show 2 * (l / 2) + 1 = l by omega] at a
      exact a
    · intro hodd
      have a : 1 ≤ (if l % 2 = 1 then f.moe ⟨l / 2, by omega⟩ 2 else 20) ∧
          (if l % 2 = 1 then f.moe ⟨l / 2, by omega⟩ 2 else 20) ≤ 24 := R.ku'
      rw [if_pos hodd, moe_word hL hf, show 2 * (l / 2) + 1 = l by omega] at a
      exact a
  · cases ho

/-- scalesOf takes a file of the right length. -/
theorem scalesOf_ok (e1 e2 eF : ℕ) {KL : ByteArray}
    (h : (fileWords KL).size = 13 * 48 + 3 * 24) :
    Layer.scalesOf (shapeAt e1 e2 eF) (fileWords KL) = .ok (recOf KL) := by
  unfold Layer.scalesOf
  refine seq_ok (refuse_ok _ ?_) rfl
  rw [h, show (shapeAt e1 e2 eF).p4 = true from rfl, show (shapeAt e1 e2 eF).p3 = true from rfl,
    show (shapeAt e1 e2 eF).L = 48 from rfl]
  decide

/-- At all public files in the goals' scope the verifier's scan of the parameter file returns, and
the layers' shape that the verifier makes of the scan is shapeAt at the three free numbers that the
goals' reader read. No return of publicOf is asked. -/
theorem shape_of_read {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) :
    ∃ P, polScan Z.pol = .ok P ∧
      Verify.layerShape P = shapeAt (VerifierAndGoals.freeLinesOf pp).eps1 (VerifierAndGoals.freeLinesOf pp).eps2
        (VerifierAndGoals.freeLinesOf pp).epsF := by
  obtain ⟨P, f, hP, -, -⟩ := OnBytes.Flat.settingsAny_parts (OnBytes.Flat.settingsAtRef_eq hR)
  refine ⟨P, hP, ?_⟩
  rw [Hd.policy_of_scope hZ hR] at hP
  obtain ⟨e1, -, -, e4, -, -, -⟩ := VerifierAndGoals.Lines.hdr_free hP
  have e : Verify.layerShape P = { hKF with
      eps1 := P.h.eps.getD 0 0, eps2 := P.h.eps.getD 1 0, epsF := P.h.epsF } := by
    rw [VerifierAndGoals.Lines.scan_closed hP]
    exact P34.shape_of_closed _
  rw [e, e1, e4]
  rfl

/-- **WHAT THE GOALS' READER ACCEPTS, THE VERIFIER's TESTS ON THE SCALE FILE TAKE.** At all public
files in the goals' scope, at the layers' shape of shape_of_read: scalesOf returns, and scalesHeld
and noWrap (at the width 5120 of the queries) refuse nothing. -/
theorem scales_return {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) :
    Layer.scalesOf (shapeAt (VerifierAndGoals.freeLinesOf pp).eps1 (VerifierAndGoals.freeLinesOf pp).eps2
        (VerifierAndGoals.freeLinesOf pp).epsF) (fileWords Z.KL) = .ok (recOf Z.KL) ∧
      scalesHeld (shapeAt (VerifierAndGoals.freeLinesOf pp).eps1 (VerifierAndGoals.freeLinesOf pp).eps2
        (VerifierAndGoals.freeLinesOf pp).epsF) (recOf Z.KL) = .ok () ∧
      noWrap (shapeAt (VerifierAndGoals.freeLinesOf pp).eps1 (VerifierAndGoals.freeLinesOf pp).eps2
        (VerifierAndGoals.freeLinesOf pp).epsF) (recOf Z.KL) 5120 = .ok () := by
  have hs := OnBytes.Flat.settingsAtRef_eq hR
  obtain ⟨P, f, hP, hf, ho⟩ := OnBytes.Flat.settingsAny_parts hs
  obtain ⟨-, -, -, hw⟩ := OnBytes.Flat.settingsAny_iff.1 hs
  rw [Hd.policy_of_scope hZ hR] at hP
  have eP := VerifierAndGoals.Lines.scan_closed hP
  have hL : P.h.L = 48 := by
    rw [eP]
    rfl
  have W := wordsOK_of_lawful hL hf ho hw
  have n1 := (hw.ff 0).n1
  have n2 := (hw.ff 0).n2
  have nf := hw.nf
  unfold NormPar.OK at n1 n2 nf
  refine ⟨scalesOf_ok _ _ _ (len_of_klFile hL hf), held_ok _ _ _ W, noWrap_ok ?_ ?_ ?_ W⟩
  · show (pp.w 0).n1.eps.toNat < 2 ^ 48
    have a : (pp.w 0).n1.eps < 2 ^ 48 := n1.2.1
    omega
  · show (pp.w 0).n2.eps.toNat < 2 ^ 48
    have a : (pp.w 0).n2.eps < 2 ^ 48 := n2.2.1
    omega
  · show pp.nf.eps.toNat < 2 ^ 48
    have a : pp.nf.eps < 2 ^ 48 := nf.2.1
    omega

end Read

#print axioms heldAt_ok
#print axioms noWrapAt_ok
#print axioms noWrap_ok
#print axioms wordsOK_of_lawful
#print axioms shape_of_read
#print axioms scales_return

end Meaning.Ret
