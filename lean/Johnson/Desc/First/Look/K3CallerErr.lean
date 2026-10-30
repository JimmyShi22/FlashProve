-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerErr.lean: THE ERRORS OF THE PROVED LOOKUP BLOCK AS NUMBERS: at every
record of public numbers that passes the test FoNums.ok, whoever calls: each round's number of bad
challenges, times 2^158, is at most the number of that round's challenges; and the block has at most
2048 rounds. And the least errors of written rounds that bear the block's (BearsT), as a function.
NO SOUNDNESS OF ANY TEXT THAT RUNS IS CLAIMED.

Why. The library says of these errors that each is below its round's number of challenges
(lookupC_small): «no sum of quotients is bounded here» (ShiftKArith.lean's own Limits). A condition
at the release wants the errors as numbers, against 2^-128 for a step.

Main names.
  TwRound.LB B q c e: c · B ≤ the size of the challenge set that the entry e says at a field of q
    elements. lb_entN, lb_all, allK_lb: ShiftKArith.lean's lt_entN, lt_all, allK_small, line for
    line, with «c · B ≤ n» in the place of «c < n».
  Cb.Fo.forB_lb_gl: AT THE CHALLENGE FIELD, B = 2^158, from FoNums.ok h alone (v < 32, d < 32, and
    2^191 < the field's size).
  TwRound.epsN_len2: the length of the library's own list epsN in closed form, at all sizes.
  Cb.Fo.forB_rounds_le: the block's list of errors has at most 2048 members (by the closed form,
    at all v' < 32, d < 32).
  lookupC_lb, lookupC_rounds: the two at the kind's own ε and R, at every caller of a list that
    passes OkLookupC; by lookupCR_eps and lookupCR_R they speak of the kind with riders too.
  ratio_sum_le: a list of counts and a list of sizes with c · B ≤ n, member by member, have a sum of
    quotients of at most (the number of members) / B.
  lookupC_sum: SO THE SUM OF THE BLOCK's QUOTIENTS IS AT MOST 2048 / 2^158 = 2^-147.
  bearT ds s' ε: the written rounds' errors: the typed count times the bound w of the written
    round's sampler; NONE WHERE THE TWO LISTS OF ROUNDS DIFFER IN LENGTH (no round gets an error for
    nothing). bearT_bears: it meets BearsT. bearT_list: as a list of numbers.

Limits. THE NUMBERS ARE THE TYPED BLOCK's: counts out of the typed challenge sets (q, q - 1, q^5,
q^(5+d)). A written round draws blocks of 256 bits; its count is the typed count times w, out of
2^(256 b) (times 2^work) values; the library's Run.planDraws_law says w · |C| ≤ (1 + 2^-128)^b ·
2^(256 b): so a written round's quotient is the typed one times at most (1 + 2^-128)^b. THAT LAST
STEP IS NOT TYPED HERE. 2^158 is what the bounds v < 32 and d < 32 leave below 2^191; at a place's
own v and d more holds. Nothing is said of the sending's, the closing's or the batching's errors.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.LookupC
import OnBytes.Tie.Pv.Lookup.Shift.ShiftKArith
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelKitT
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace TwRound
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn TwPlan TwErr OnBytes.G4 List

/-- the count c, times B, is at most the size of the challenge set that the entry says -/
def LB (B q c : ℕ) (e : Fmt.Entry) : Prop := c * B ≤ sizeOf q e

theorem lb_rd {B q c k : ℕ} (name : String) (s : ℕ) (h : c * B ≤ q ^ k) :
    LB B q c (rd 0 name s k) := by
  simpa [LB, sizeOf, rd] using h
theorem lb_Y {B q c : ℕ} (s : ℕ) (h : c * B ≤ q - 1) : LB B q c (rd 0 "PSC Y" s 1 1) := by
  simpa [LB, sizeOf, rd] using h
theorem lb_none (B q : ℕ) (name : String) (s : ℕ) : LB B q 0 (rdNone name s) := by
  simp [LB, sizeOf, rdNone]

theorem lb_one {B q c : ℕ} (name : String) (s : ℕ) (h : c * B ≤ q) : LB B q c (rd 0 name s 1) :=
  lb_rd name s (by rw [pow_one]; exact h)

theorem lb_psc (B q k g gY vals : ℕ) (h1 : 1 * B ≤ q) (hg : g * B ≤ q) (hY : gY * B ≤ q - 1) :
    Forall₂ (LB B q) (pscC k g gY) (pscN 0 (replicate k g) true gY vals) := by
  unfold pscC pscN
  rw [if_pos rfl, map_replicate]
  exact f2_append (f2_append (.cons (lb_one _ _ h1) .nil) (f2_rep (lb_one _ _ hg) k))
    (.cons (lb_Y _ hY) (.cons (lb_none _ _ _ _) .nil))

theorem lb_clo (B q d w : ℕ) (h1 : 1 * B ≤ q) (h2 : 2 * B ≤ q) :
    Forall₂ (LB B q) ([1] ++ replicate d 2 ++ replicate w 1)
      (pscN 0 (replicate d 2 ++ replicate w 1) false 0 0) := by
  have e : pscN 0 (replicate d 2 ++ replicate w 1) false 0 0 =
      [rd 0 "PSC epsilon" 1 1] ++ replicate d (rd 0 "PSC round" 2 1) ++
        replicate w (rd 0 "PSC round" 1 1) := by
    simp [pscN]
  rw [e]
  exact f2_append (f2_append (.cons (lb_one _ _ h1) .nil) (f2_rep (lb_one _ _ h2) d))
    (f2_rep (lb_one _ _ h1) w)

theorem point_lb {B q w : ℕ} (h : w * B ≤ q) : w * q ^ (w - 1) * B ≤ q ^ w := by
  cases w with
  | zero => simp
  | succ k =>
    rw [Nat.add_sub_cancel, pow_succ]
    calc (k + 1) * q ^ k * B = q ^ k * ((k + 1) * B) := by ring
      _ ≤ q ^ k * q := Nat.mul_le_mul_left _ h

theorem lb_entN (B q v' d w n : ℕ) (h3 : 3 * B ≤ q - 1) (hv : 2 ^ (v' + 1) * B ≤ q)
    (hw : (w + d) * B ≤ q) : Forall₂ (LB B q) (epsN v' d w n q) (entN 0 v' d w n) := by
  have h0 : 0 * B ≤ q := by omega
  have h1 : 1 * B ≤ q := by omega
  have h2 : 2 * B ≤ q := by omega
  have h2' : 2 * B ≤ q - 1 := by omega
  have hv1 : (2 ^ (v' + 1) - 1) * B ≤ q :=
    Nat.le_trans (Nat.mul_le_mul_right B (Nat.sub_le _ _)) hv
  have hw1 : w * B ≤ q := Nat.le_trans (Nat.mul_le_mul_right B (Nat.le_add_right w d)) hw
  unfold epsN entN
  rw [append_assoc [rd 0 "LKP" 0 1]]
  refine f2_append (f2_append (f2_append (f2_append (f2_append (f2_append (f2_append
    (.cons (lb_one _ _ hv1) .nil)
    (f2_first (lb_psc B q 0 0 3 3 h1 h0 h3) (lb_psc B q 0 0 3 2 h1 h0 h3) n))
    (.cons (lb_rd _ _ (point_lb hw1)) .nil))
    (f2_flat _ _ (fun l => f2_append (lb_psc B q l 2 2 2 h1 h2 h2')
      (.cons (lb_one _ _ h1) .nil)) _))
    (f2_flat _ _ (fun l => f2_append (lb_psc B q (w + l) 2 2 2 h1 h2 h2')
      (.cons (lb_one _ _ h1) .nil)) _))
    (lb_clo B q d w h1 h2))
    (.cons (lb_rd _ _ (point_lb hw)) .nil))
    (lb_psc B q (w + d) 2 2 1 h1 h2 h2')

theorem lb_all (B q v' d w n dS : ℕ) (several : Bool) (h3 : 3 * B ≤ q - 1)
    (hv : 2 ^ (v' + 1) * B ≤ q) (hw : (w + d) * B ≤ q) (hS : 2 ^ dS * B ≤ q) :
    Forall₂ (LB B q) (shHead several (2 ^ dS) ++ epsN v' d w n q)
      (shHead several (shiftN 0) ++ entN 0 v' d w n) := by
  refine f2_append ?_ (lb_entN B q v' d w n h3 hv hw)
  cases several with
  | true => exact .cons (lb_one _ _ hS) .nil
  | false => exact .nil

section
variable {E St : Type} [Field E] [Fintype E]
variable (V : ∀ (Y : PscPar E) Ex, TWhole.ShortK Y Ex)
  (VC : ∀ (Y : PscPar E) Ex, TWhole.ShortKC Y Ex)
  (Ex : ExtSpec) (A0 : LkAsmH E) (P : ShiftQ E St (A0.J → E)) (several : Bool)

/-- Every error, times B, is at most its round's number of challenges. -/
theorem allK_lb (ho : A0.oE = Fin.revPerm) (B : ℕ) (h3 : 3 * B ≤ Fintype.card E - 1)
    (hv : 2 ^ (A0.v' + 1) * B ≤ Fintype.card E) (hw : (A0.w + A0.d) * B ≤ Fintype.card E)
    (hS : 2 ^ P.d * B ≤ Fintype.card E) :
    Forall₂ (fun c n => c * B ≤ n) (TWhole.errList (P.allK A0 several V VC (Ex := Ex)).e)
      ((P.allK A0 several V VC (Ex := Ex)).R.shape.map fun r => Nat.card r.Chal) := by
  rw [allK_eps V VC Ex A0 P several ho, allK_sizes V VC Ex A0 P several ho,
    Nat.card_eq_fintype_card]
  exact forall₂_map_right_iff.2 (lb_all B _ _ _ _ _ _ several h3 hv hw hS)

end

/-- The number of rounds does not hang on the field's size. -/
theorem epsN_length (v' d w n q q' : ℕ) :
    (epsN v' d w n q).length = (epsN v' d w n q').length := by
  simp only [epsN, length_append, length_cons, length_nil]

theorem pscC_len (k g gY : ℕ) : (pscC k g gY).length = k + 3 := by
  simp only [pscC, length_append, length_cons, length_nil, length_replicate]
  omega

/-- Lists of one length c, one for each number below m. -/
theorem flat_const (f : ℕ → List ℕ) (c : ℕ) (hf : ∀ l, (f l).length = c) :
    ∀ m, ((range m).flatMap f).length = m * c
  | 0 => by simp
  | m + 1 => by
    have ih := flat_const f c hf m
    rw [range_succ, flatMap_append, length_append, ih, flatMap_cons, flatMap_nil, append_nil, hf]
    ring

/-- Lists of the lengths a, a + 1, a + 2, …: twice the whole length, without a subtraction. -/
theorem flat_len (f : ℕ → List ℕ) (a : ℕ) (hf : ∀ l, (f l).length = a + l) :
    ∀ m, 2 * ((range m).flatMap f).length + m = m * m + 2 * m * a
  | 0 => by simp
  | m + 1 => by
    have ih := flat_len f a hf m
    rw [range_succ, flatMap_append, length_append, flatMap_cons, flatMap_nil, append_nil, hf]
    generalize ((range m).flatMap f).length = X at ih ⊢
    have e : (m + 1) * (m + 1) + 2 * (m + 1) * a = (m * m + 2 * m * a) + (2 * a + 2 * m + 1) := by
      ring
    rw [e, ← ih]
    ring

/-- **The number of the lookup's rounds, in closed form** (twice, without a subtraction). -/
theorem epsN_len2 (v' d w n q : ℕ) :
    2 * (epsN v' d w n q).length + (v' + 1) + d =
      2 * (1 + (n + 1) * 3 + 1 + (1 + d + w) + 1 + (w + d + 3)) +
        ((v' + 1) * (v' + 1) + 2 * (v' + 1) * 4) + (d * d + 2 * d * (w + 4)) := by
  have h1 := flat_const (fun _ => pscC 0 0 3) 3 (fun _ => pscC_len 0 0 3) (n + 1)
  have h2 := flat_len (fun l => pscC l 2 2 ++ [1]) 4 (fun l => by
    rw [length_append, pscC_len, length_singleton]
    omega) (v' + 1)
  have h3 := flat_len (fun l => pscC (w + l) 2 2 ++ [1]) (w + 4) (fun l => by
    rw [length_append, pscC_len, length_singleton]
    omega) d
  simp only [epsN, length_append, length_cons, length_nil, length_replicate, pscC_len, h1]
  generalize ((range (v' + 1)).flatMap fun l => pscC l 2 2 ++ [1]).length = X at h2 ⊢
  generalize ((range d).flatMap fun l => pscC (w + l) 2 2 ++ [1]).length = Y at h3 ⊢
  linarith

/-- By the closed form, at all sizes below 32. -/
theorem epsN_len_le : ∀ v' < 32, ∀ d < 32, (epsN v' d 5 30 0).length ≤ 2047 := by
  intro v' hv d hd
  have h := epsN_len2 v' d 5 30 0
  have hA : (v' + 1) * (v' + 1) ≤ 32 * 32 := Nat.mul_le_mul (by omega) (by omega)
  have hB : d * d ≤ 31 * 31 := Nat.mul_le_mul (by omega) (by omega)
  generalize (epsN v' d 5 30 0).length = N at h ⊢
  generalize (v' + 1) * (v' + 1) = A at h hA
  generalize d * d = B at h hB
  omega

end TwRound

namespace Cb.Fo
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwRound

theorem gl_big : 2 ^ 191 < Fintype.card Cb.Gl.E := by
  rw [Cb.Gl.gl_card.2.1]
  exact Cb.Gl.gl_card.2.2.1

/-- From the one Bool: both depths are below 32. -/
theorem ok_depths {h : Sh} (H : FoNums.ok h = true) : FoNums.v' h + 1 < 32 ∧ h.d < 32 := by
  obtain ⟨⟨_, _, _, _, a5, _⟩, _, _, _, _, _, _, f3⟩ := ok_parts H
  refine ⟨by rw [← ok_v H]; exact a5, ?_⟩
  have h1 : 2 ^ (h.d + 32) < 2 ^ 64 := Nat.lt_trans f3 (UInt64.toNat_lt _)
  have h2 : h.d + 32 < 64 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
  omega

section
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : Sh) (L : Lay Cb.Gl.E St₀ J₀)
  (Ex : ExtSpec)

/-- **Each round's number of bad challenges, times 2^158, is at most the number of its
challenges.** -/
theorem forB_lb_gl (H : FoNums.ok h = true) :
    List.Forall₂ (fun c n => c * 2 ^ 158 ≤ n)
      (errList (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e)
      ((forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape.map fun r => Nat.card r.Chal) := by
  obtain ⟨hv, hd⟩ := ok_depths H
  have hq := gl_big
  have top : (2 : ℕ) ^ 31 * 2 ^ 158 ≤ 2 ^ 191 := by norm_num
  have pw : ∀ k, k < 32 → 2 ^ k * 2 ^ 158 ≤ Fintype.card Cb.Gl.E := fun k hk =>
    Nat.le_trans (Nat.le_trans (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by norm_num) (by omega : k ≤ 31))) top) (Nat.le_of_lt hq)
  refine allK_lb V₀ V₀C Ex (forA Cb.Gl.E h L) (forP Cb.Gl.E h L) (FoNums.several h) rfl (2 ^ 158)
    ?_ ?_ ?_ ?_
  · exact Nat.le_sub_one_of_lt (Nat.lt_of_le_of_lt (by norm_num) hq)
  · exact pw _ hv
  · show (FoNums.w + h.d) * 2 ^ 158 ≤ _
    have e : FoNums.w + h.d ≤ 36 := by
      have : FoNums.w = 5 := rfl
      omega
    exact Nat.le_trans (Nat.le_trans (Nat.mul_le_mul_right _ e) (by norm_num : 36 * 2 ^ 158 ≤
      2 ^ 191)) (Nat.le_of_lt hq)
  · show 2 ^ h.d * 2 ^ 158 ≤ _
    exact pw _ hd

/-- **The block has at most 2048 rounds.** -/
theorem forB_rounds_le (H : FoNums.ok h = true) :
    (errList (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e).length ≤ 2048 := by
  obtain ⟨hv, hd⟩ := ok_depths H
  rw [forB_eps]
  unfold forEps
  rw [List.length_append, epsN_length _ _ _ _ _ 0]
  have h1 : (shHead (FoNums.several h) (2 ^ h.d)).length ≤ 1 := by
    cases FoNums.several h <;> simp [shHead]
  have h2 : (TwErr.epsN (FoNums.v' h) h.d FoNums.w FoNums.n 0).length ≤ 2047 :=
    epsN_len_le _ (by omega) _ hd
  omega

end
end Cb.Fo

namespace VerifiableInference.OnPublicFiles
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole Cb.Fo

/-- At the kind's own errors and rounds. -/
theorem lookupC_lb (L : List LookupCCaller) (hL : OkLookupC L) : ∀ c ∈ L,
    List.Forall₂ (fun a n => a * 2 ^ 158 ≤ n) (errList ((kLookupC L).ε c))
      (((kLookupC L).R c).shape.map fun r => Nat.card r.Chal) :=
  fun c hc => forB_lb_gl c.h c.L c.Ex (hL c hc)

theorem lookupC_rounds (L : List LookupCCaller) (hL : OkLookupC L) : ∀ c ∈ L,
    (errList ((kLookupC L).ε c)).length ≤ 2048 :=
  fun c hc => forB_rounds_le c.h c.L c.Ex (hL c hc)

theorem ratio_le {B c n : ℕ} (hB : 0 < B) (h : c * B ≤ n) : (c : ℚ) / n ≤ 1 / B := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_div_iff₀ (by exact_mod_cast hn) (by exact_mod_cast hB), one_mul]
    exact_mod_cast h

/-- The sum of the quotients is at most the number of members over B. -/
theorem ratio_sum_le {B : ℕ} (hB : 0 < B) : ∀ {cs ns : List ℕ},
    List.Forall₂ (fun c n => c * B ≤ n) cs ns →
      (List.zipWith (fun (c n : ℕ) => (c : ℚ) / (n : ℚ)) cs ns).sum ≤
        (cs.length : ℚ) * (1 / (B : ℚ))
  | _, _, .nil => by simp
  | _, _, .cons (l₁ := cs) h t => by
    have h1 := ratio_le hB h
    have h2 := ratio_sum_le hB t
    rw [List.zipWith_cons_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

theorem sum_le_of {cs ns : List ℕ} (h1 : List.Forall₂ (fun c n => c * 2 ^ 158 ≤ n) cs ns)
    (h2 : cs.length ≤ 2048) :
    (List.zipWith (fun (c n : ℕ) => (c : ℚ) / (n : ℚ)) cs ns).sum ≤
      2048 * (1 / ((2 ^ 158 : ℕ) : ℚ)) := by
  refine le_trans (ratio_sum_le (B := 2 ^ 158) (by positivity) h1) ?_
  have h3 : (cs.length : ℚ) ≤ 2048 := by exact_mod_cast h2
  exact mul_le_mul_of_nonneg_right h3 (by positivity)

/-- **The sum of the block's quotients is at most 2048 / 2^158.** -/
theorem lookupC_sum (L : List LookupCCaller) (hL : OkLookupC L) : ∀ c ∈ L,
    (List.zipWith (fun (a n : ℕ) => (a : ℚ) / (n : ℚ)) (errList ((kLookupC L).ε c))
      (((kLookupC L).R c).shape.map fun r => Nat.card r.Chal)).sum ≤
        2048 * (1 / ((2 ^ 158 : ℕ) : ℚ)) :=
  fun c hc => sum_le_of (lookupC_lb L hL c hc) (lookupC_rounds L hL c hc)

end VerifiableInference.OnPublicFiles

namespace Fo.Peel
open Iop IOR Prob Cb TWhole OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Run

/-- **The least errors of the written rounds that bear the typed ones**; none where the two lists of
rounds differ in length. -/
def bearT : (ds : List RDT) → (s' : Shape) → Err s' → Option (Err (uLT (ckP .two) ds))
  | [], [], _ => some ()
  | d :: ds, _ :: s', ε =>
    (bearT ds s' ε.2).map fun t => (ε.1 * (bsRound .two d.entry d.kind).w, t)
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none

theorem bearT_bears : ∀ (ds : List RDT) (s' : Shape) (ε : Err s') (ε' : Err (uLT (ckP .two) ds)),
    bearT ds s' ε = some ε' → BearsT ds s' ε ε'
  | [], [], _, _, _ => trivial
  | d :: ds, _ :: s', ε, ε', h => by
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨le_refl _, bearT_bears ds s' ε.2 t ht⟩
  | [], _ :: _, _, _, _ => trivial
  | _ :: _, [], _, _, _ => trivial

theorem bearT_some : ∀ (ds : List RDT) (s' : Shape) (ε : Err s'), ds.length = s'.length →
    (bearT ds s' ε).isSome = true
  | [], [], _, _ => rfl
  | d :: ds, _ :: s', ε, h => by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (bearT_some ds s' ε.2 (Nat.succ.inj h))
    show ((bearT ds s' ε.2).map _).isSome = true
    rw [ht]
    rfl
  | [], _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], _, h => absurd h (by simp)

/-- As a list of numbers: the typed counts times the written rounds' samplers' bounds. -/
theorem bearT_list : ∀ (ds : List RDT) (s' : Shape) (ε : Err s') (ε' : Err (uLT (ckP .two) ds)),
    bearT ds s' ε = some ε' →
      errList ε' = List.zipWith (· * ·) (errList ε)
        (ds.map fun d => (bsRound .two d.entry d.kind).w)
  | [], [], _, _, _ => rfl
  | d :: ds, _ :: s', ε, ε', h => by
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    show _ :: errList t = _ :: _
    rw [bearT_list ds s' ε.2 t ht]
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

end Fo.Peel

#print axioms TwRound.lb_entN
#print axioms TwRound.allK_lb
#print axioms TwRound.epsN_len2
#print axioms TwRound.epsN_len_le
#print axioms Cb.Fo.forB_lb_gl
#print axioms Cb.Fo.forB_rounds_le
#print axioms VerifiableInference.OnPublicFiles.lookupC_lb
#print axioms VerifiableInference.OnPublicFiles.lookupC_rounds
#print axioms VerifiableInference.OnPublicFiles.lookupC_sum
#print axioms Fo.Peel.bearT_bears
#print axioms Fo.Peel.bearT_some
#print axioms Fo.Peel.bearT_list
