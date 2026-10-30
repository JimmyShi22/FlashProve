-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadLinesC.lean: what the forms of the output head's lookup keys are worth on cells:
the top digit of a margin (HD0) and the two families of looked-up values (HE0, HE1).

Johnson/Road/HeadLines.lean says in what sense a form of the verifier (LINE in
OnBytes/Model/HeadForms.lean) is a key of the library, and has the tools. This file has three more
families.

HD0. The key is not affine in the cells: it holds the logits, which are products of cells and
weights. The form has one slot in their place. The theorem says what the form is worth beside the
slot: the weighted sum of the extensions of the key less its part in the logits. The form also
carries a factor, the program's inverse of 2^(sh + 15); the library's key does not. The factor
stays in the statement as it is; iw_value and iw_23 say what it is under a reading that takes
inverses to inverses.

Main definitions: preOf (the sums of the first weights, as the verifier gathers them).
Main theorems: costSum_value, gap_cells, preOf_value, placeTermH_wsum, middleDigit_cells,
lowDigit_cells (the parts of a margin); line_HD0, line_HE0, line_HE1 (sizes as letters);
line_HD0_ref, line_HD0_plain, line_HE0_ref, line_HE1_ref (at the library's sizes, in the library's
own names); iw_value, iw_23.

What is not claimed. Nothing is said about what the slot holds, about when a world is true, about
the weights' origin, or about what a verifier's acceptance shows. Every theorem on a form begins "if
the routine succeeds": none says that it does. That the hypotheses on a run (Laid, SegFit, PosFit,
ReqFits, the two numbers 8 and 5, the number of the call) hold of what the verifier's own functions
return is not shown here. The program does not import this file.
-/
import Johnson.Road.HeadLines

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM)
open Inst.Model (NormPar)
open HeadSizes (Sizes)

variable {K : Type} [Field K]

/-! ## Arrays and sums -/

/-- An entry of an array that got one more member: an old entry. -/
theorem getD_push_lt {α : Type} (a : Array α) (x d : α) {k : ℕ} (h : k < a.size) :
    (a.push x).getD k d = a.getD k d := by
  have h2 : k < a.size + 1 := Nat.lt_succ_of_lt h
  simp [Array.getD, Array.getElem_push, h, h2]

/-- An entry of an array that got one more member: the new entry. -/
theorem getD_push_eq {α : Type} (a : Array α) (x d : α) : (a.push x).getD a.size d = x := by
  simp [Array.getD]

/-- An entry of an array whose members were changed by a rule that sees their numbers. -/
theorem getD_mapIdx_lt {α β : Type} (a : Array α) (f : ℕ → α → β) {i : ℕ} (h : i < a.size) (d : β)
    (d' : α) : (a.mapIdx f).getD i d = f i (a.getD i d') := by
  simp [Array.getD, h]

/-- The sum of the first b members of an array that has no more than b. -/
theorem sumE_extract (ρ : Reading K) (v : Array E) (b : ℕ) (hb : v.size ≤ b) :
    ρ.val (Model.sumE (v.extract 0 b)) = ∑ x ∈ range v.size, ρ.val (v.getD x zeroE) := by
  have hs : (v.extract 0 b).size = v.size := by rw [Array.size_extract]; omega
  rw [sumE_value', hs]
  refine sum_congr rfl fun x hx => ?_
  have h1 : x < v.size := mem_range.mp hx
  have h2 : x < b := Nat.lt_of_lt_of_le h1 hb
  simp [Array.getD, h1, h2]

/-- A sum over the numbers below V of the terms with a number below w. -/
theorem sum_below (g : ℕ → K) {w V : ℕ} (h : w ≤ V) :
    ∑ x ∈ range V, g x * (if x < w then 1 else 0) = ∑ x ∈ range w, g x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.sum_range_add]
  have a1 : ∑ x ∈ range w, g x * (if x < w then (1 : K) else 0) = ∑ x ∈ range w, g x :=
    sum_congr rfl fun x hx => by rw [if_pos (mem_range.mp hx), mul_one]
  have a2 : ∑ x ∈ range m, g (w + x) * (if w + x < w then (1 : K) else 0) = 0 :=
    sum_eq_zero fun x _ => by rw [if_neg (by omega), mul_zero]
  rw [a1, a2, add_zero]

/-- A fold that adds a term at the numbers that a test picks. -/
theorem foldl_pick (ρ : Reading K) (on : ℕ → Bool) (e : ℕ → E) : ∀ n : ℕ,
    ρ.val ((List.range n).foldl (fun s t => if on t then addE s (e t) else s) zeroE) =
      ∑ t ∈ range n, if on t then ρ.val (e t) else 0
  | 0 => by simp [ρ.zero]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← foldl_pick ρ on e n]
    split
    · rw [ρ.add]
    · rw [add_zero]

/-- The weighted sum of a margin's affine part, in its pieces: A and r depend on the position
alone. -/
theorem wsum_margin (g : ℕ → K) (lt : ℕ) (u : ℕ → K) (n : ℕ) (A r : ℕ → K) (B d1 d2 : ℕ → ℕ → K)
    (k o1 o2 : K) :
    wsum g lt u n (fun x i => A i - B x i - k * (d1 x i + o1 * r i) - (d2 x i + o2 * r i)) =
      (∑ x ∈ range n, g x) * (Blocks.ext lt A u - (k * o1 + o2) * Blocks.ext lt r u) -
        wsum g lt u n B - k * wsum g lt u n d1 - wsum g lt u n d2 := by
  rw [wsum_sub, wsum_sub, wsum_sub, wsum_smul, wsum_add, wsum_add, wsum_smul, wsum_smul,
    wsum_pos, wsum_pos]
  ring

/-! ## The term that makes the first of equal logits the largest -/

/-- The sums of the first 0, 1, ..., n weights, as the verifier gathers them, and the last of these
sums. -/
def preOf (ew : Array E) (n : ℕ) : Array E × E :=
  (List.range n).foldl
    (fun (a : Array E × E) v =>
      (a.1.push (addE a.2 (ew.getD v zeroE)), addE a.2 (ew.getD v zeroE))) (#[zeroE], zeroE)

/-- One more sum. -/
theorem preOf_succ (ew : Array E) (n : ℕ) : preOf ew (n + 1) =
    ((preOf ew n).1.push (addE (preOf ew n).2 (ew.getD n zeroE)),
      addE (preOf ew n).2 (ew.getD n zeroE)) := by
  unfold preOf
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- There are n + 1 sums, and sum number k reads as the sum of the first k weights. -/
theorem preOf_value (ρ : Reading K) (ew : Array E) : ∀ n : ℕ,
    (preOf ew n).1.size = n + 1 ∧
      ρ.val (preOf ew n).2 = ∑ v ∈ range n, ρ.val (ew.getD v zeroE) ∧
      ∀ k, k ≤ n → ρ.val ((preOf ew n).1.getD k zeroE) = ∑ v ∈ range k, ρ.val (ew.getD v zeroE)
  | 0 => by
    refine ⟨rfl, ?_, ?_⟩
    · show ρ.val zeroE = _
      rw [ρ.zero, Finset.sum_range_zero]
    · intro k hk
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      show ρ.val zeroE = _
      rw [ρ.zero, Finset.sum_range_zero]
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := preOf_value ρ ew n
    rw [preOf_succ]
    refine ⟨?_, ?_, ?_⟩
    · show ((preOf ew n).1.push _).size = _
      rw [Array.size_push, h1]
    · show ρ.val (addE (preOf ew n).2 (ew.getD n zeroE)) = _
      rw [ρ.add, h2, Finset.sum_range_succ]
    · intro k hk
      show ρ.val (((preOf ew n).1.push (addE (preOf ew n).2 (ew.getD n zeroE))).getD k zeroE) = _
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · rw [getD_push_lt _ _ _ (by rw [h1]; exact hlt), h3 k (Nat.le_of_lt_succ hlt)]
      · have e : k = (preOf ew n).1.size := by rw [h1]; omega
        rw [e, getD_push_eq, ρ.add, h2, h1, Finset.sum_range_succ]

/-- The public term of the margins, on the request: the weighted sum of the extension of the
indicator "covered, and the entry stands before the checked token". The checked token of a covered
position must be an entry of the vocabulary: the verifier has no sum of more than V - 1 weights. -/
theorem placeTermH_wsum (ρ : Reading K) (R : Model.Head.Run) (ew P : Array E) (rho : ℕ → K)
    (win : ℕ → ℕ) (hP : P.size = R.h.lt)
    (hr : ∀ i, i < 2 ^ R.h.lt → rho i = if R.cov.hOn.getD i false then 1 else 0)
    (hw : ∀ i, i < 2 ^ R.h.lt → R.cov.hOn.getD i false = true →
      win i = R.x.win.getD i 0 ∧ win i < R.h.V) :
    ρ.val (Model.Head.placeTermH R ew (Model.eqTab P)) =
      wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt (pt ρ P) R.h.V
        (fun x i => rho i * if x < win i then 1 else 0) := by
  have e : Model.Head.placeTermH R ew (Model.eqTab P) = (List.range (2 ^ R.h.lt)).foldl
      (fun s t => if R.cov.hOn.getD t false then
        addE s (mulE ((Model.eqTab P).getD t zeroE)
          ((preOf ew (R.h.V - 1)).1.getD (R.x.win.getD t 0) zeroE)) else s) zeroE := rfl
  rw [e, foldl_pick ρ (fun t => R.cov.hOn.getD t false) (fun t =>
    mulE ((Model.eqTab P).getD t zeroE) ((preOf ew (R.h.V - 1)).1.getD (R.x.win.getD t 0) zeroE))]
  unfold wsum Blocks.ext
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < 2 ^ R.h.lt := mem_range.mp hi
  rw [hr i hi']
  by_cases hon : R.cov.hOn.getD i false = true
  · obtain ⟨w1, w2⟩ := hw i hi' hon
    have sb : ∑ x ∈ range R.h.V, ρ.val (ew.getD x zeroE) * (if x < win i then 1 else 0) =
        ∑ x ∈ range (win i), ρ.val (ew.getD x zeroE) :=
      sum_below (fun x => ρ.val (ew.getD x zeroE)) (Nat.le_of_lt w2)
    simp only [if_pos hon]
    rw [ρ.mul, eqTab_value ρ P i (by rw [hP]; exact hi'), hP, ← w1,
      (preOf_value ρ ew (R.h.V - 1)).2.2 (win i) (by omega), ← sb, mul_sum]
    exact sum_congr rfl fun x _ => by ring
  · simp only [if_neg hon]
    exact (sum_eq_zero fun x _ => by ring).symm

/-! ## The cost of a position -/

/-- The name of the table of the matrix hr under the weights of the positions with a cost. -/
theorem hr_phiC : "hr@" ++ "phiC" = "hr@phiC" := by decide

/-- The sum of the weights of the positions with a cost is the extension, at the point P, of the
indicator of these positions. -/
theorem costSum_value (ρ : Reading K) (R : Model.Head.Run) (P : Array E) (f : ℕ → K)
    (hP : P.size = R.h.lt)
    (hf : ∀ i, i < 2 ^ R.h.lt → f i = if R.cov.hOnC.getD i false then 1 else 0) :
    ρ.val (Model.Head.costWeights R.cov P).2.1 = Blocks.ext R.h.lt f (pt ρ P) := by
  have e : (Model.Head.costWeights R.cov P).2.1 = Model.sumE ((Model.eqTab P).mapIdx
      fun t x => if R.cov.hOnC.getD t false then x else zeroE) := rfl
  rw [e, sumE_value', Array.size_mapIdx, eqTab_size, hP]
  unfold Blocks.ext
  refine sum_congr rfl fun X hX => ?_
  have hX' : X < 2 ^ P.size := by rw [hP]; exact mem_range.mp hX
  have hs : X < (Model.eqTab P).size := by rw [eqTab_size]; exact hX'
  rw [getD_mapIdx_lt _ _ hs zeroE zeroE, hf X (mem_range.mp hX)]
  by_cases hc : R.cov.hOnC.getD X false = true
  · rw [if_pos hc, if_pos hc, eqTab_value ρ P X hX', hP, mul_one]
  · rw [if_neg hc, if_neg hc, ρ.zero, mul_zero]

/-- The indicator of the counted positions, read in K. -/
theorem ReqFits.rhoCK {R : Model.Head.Run} {z : Sizes} {y : Inst.Model.Head.Req}
    (Y : ReqFits R z y) (Z : Laid R z) (i : ℕ) (hi : i < 2 ^ R.h.lt) :
    ((HeadSizes.rhoC z y i : ℤ) : K) = if R.cov.hOnC.getD i false then 1 else 0 := by
  rw [Y.rhoC i (by rw [Z.T]; exact hi)]
  split <;> simp

variable {ρ : Reading K} {W : World K}

/-- One of the six numbers of the cost ledger, on cells. The table holds the cells hr under the
weights c of the positions, and wE is the sum of these weights. The number has n digits, from digit
99 + o of the ledger on; a digit is its cell plus 128. -/
theorem gap_cells (hρ : Numerals ρ) {R : Model.Head.Run} {i o n : ℕ} {wE : E}
    {F G : Fork} {C D : Ctx} {a : Aff} {u c : ℕ → K} {hr : ℕ → ℕ → K} (hXL : R.h.XL = 5)
    (hg : Model.ledG.getD i (0, 0) = (o, n))
    (hC : ShortAt W R (colsOf F R.iU3) "hr@phiC" R.h.lt u (fun φ j => c j * hr φ j))
    (hw : ρ.val wE = Blocks.ext R.h.lt c u)
    (h : Ok (Model.Head.gapAt R "phiC" i wE) F C a G D) :
    G = F ∧ D = C ∧ a.value ρ W = Blocks.ext R.h.lt
      (fun j => c j * Inst.Model.Ledger.b256 (fun m => 128 + hr m j) (99 + o) n) u := by
  obtain ⟨e1, e2, tb, hst, hval, hv⟩ := gapAt_value ρ W hρ h
  refine ⟨e1, e2, ?_⟩
  have e99 : Model.ledNR 5 = 99 := rfl
  rw [hr_phiC] at hst
  rw [hg, hXL, e99] at hval hv
  dsimp only at hval hv
  have s1 : ∀ l, l < n →
      rdW W R.iU3 (colsOf F R.iU3) (tb + (99 + o + l)) + 128 * ρ.val wE =
        Blocks.ext R.h.lt (fun j => c j * (128 + hr (99 + o + l) j)) u := by
    intro l hl
    have e : (fun j => c j * (128 + hr (99 + o + l) j)) =
        fun j => c j * hr (99 + o + l) j + 128 * c j := funext fun j => by ring
    rw [hC tb hst _ (hval l hl), hw, e, Blocks.ext_add, Blocks.ext_smul]
  have s2 : ∑ l ∈ range n, (256 : K) ^ l *
        (rdW W R.iU3 (colsOf F R.iU3) (tb + (99 + o + l)) + 128 * ρ.val wE) =
      ∑ l ∈ range n, (256 : K) ^ l *
        Blocks.ext R.h.lt (fun j => c j * (128 + hr (99 + o + l) j)) u :=
    sum_congr rfl fun l hl => by rw [s1 l (mem_range.mp hl)]
  have s3 : ∑ l ∈ range n, (256 : K) ^ l *
        Blocks.ext R.h.lt (fun j => c j * (128 + hr (99 + o + l) j)) u =
      Blocks.ext R.h.lt
        (fun j => ∑ l ∈ range n, (256 : K) ^ l * (c j * (128 + hr (99 + o + l) j))) u :=
    ext_limbs R.h.lt n (fun l j => c j * (128 + hr (99 + o + l) j)) u
  rw [hv, s2, s3]
  refine Blocks.ext_congr (fun j _ => ?_) u
  show ∑ l ∈ range n, (256 : K) ^ l * (c j * (128 + hr (99 + o + l) j)) =
    c j * ∑ l ∈ range n, (256 : K) ^ l * (128 + hr (99 + o + l) j)
  rw [mul_sum]
  exact sum_congr rfl fun l _ => by ring

/-! ## The two lower digits -/

/-- The middle digit of the margins under a segment's weights, on cells. -/
theorem middleDigit_cells (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {sn : String} {wR : E} {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K}
    {t : Inst.Model.Head.Cells K}
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (h : Ok (Model.Head.middleDigit R sn wR) F C a G D) :
    G = F ∧ D = C ∧ ∃ wh, Ok (Model.Head.ewh R sn) F C wh F C ∧
      ∀ ew : Array E, Blocked ρ ew wh R.h.ls low →
        a.value ρ W = 32896 * ρ.val wR +
          wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (wh.size * 2 ^ R.h.ls)
            (fun x i => HeadSizes.d1 z t x i) := by
  unfold Model.Head.middleDigit at h
  rw [ok_bind] at h
  obtain ⟨s, F3, C3, h5, h6⟩ := h
  obtain ⟨rfl, rfl, wh, hwh, hs⟩ := Sl_cells hρ hL
    (fun l _ => by
      rw [Z.oD1, Z.JV]
      exact Nat.dvd_add (Dvd.dvd.mul_left Z.Sd 4) (Dvd.dvd.mul_left Z.SV l)) h5
  rw [ok_pure] at h6
  obtain ⟨rfl, rfl, rfl⟩ := h6
  refine ⟨rfl, rfl, wh, hwh, fun ew hB => ?_⟩
  rw [Aff.value_add, Aff.value_ofConst, hs ew hB, ρ.mul, o2_value hρ]
  have e : (fun x i => HeadSizes.d1 z t x i) = fun x i =>
      ∑ l ∈ range 2, (256 : K) ^ l * t.hf (R.L.oD1 + l * R.L.JV + x) i := by
    funext x i
    show (∑ l ∈ range 2, (256 : K) ^ l * t.hf (4 * z.d + z.V * l + x) i) = _
    rw [Z.oD1, Z.JV]
    simp only [Nat.mul_comm]
  rw [e]

/-- The low digit of the margins under a segment's weights, on cells. -/
theorem lowDigit_cells (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {sn : String} {wR : E} {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K}
    {t : Inst.Model.Head.Cells K}
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (h : Ok (Model.Head.lowDigit R sn wR) F C a G D) :
    G = F ∧ D = C ∧ ∃ wh, Ok (Model.Head.ewh R sn) F C wh F C ∧
      ∀ ew : Array E, Blocked ρ ew wh R.h.ls low →
        a.value ρ W = 128 * ρ.val wR +
          wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (wh.size * 2 ^ R.h.ls)
            (fun x i => HeadSizes.d2 z t x i) := by
  unfold Model.Head.lowDigit at h
  rw [ok_bind] at h
  obtain ⟨s, F3, C3, h5, h6⟩ := h
  obtain ⟨rfl, rfl, wh, hwh, hs⟩ := Sl_cells hρ hL
    (fun l _ => by
      rw [Z.oD2, Z.JV]
      exact Nat.dvd_add
        (Nat.dvd_add (Dvd.dvd.mul_left Z.Sd 4) (Dvd.dvd.mul_left Z.SV 2))
        (Dvd.dvd.mul_left Z.SV l)) h5
  rw [ok_pure] at h6
  obtain ⟨rfl, rfl, rfl⟩ := h6
  refine ⟨rfl, rfl, wh, hwh, fun ew hB => ?_⟩
  rw [Aff.value_add, Aff.value_ofConst, hs ew hB, ρ.mul, o1_value hρ]
  have e : (fun x i => HeadSizes.d2 z t x i) = fun x i =>
      ∑ l ∈ range 1, (256 : K) ^ l * t.hf (R.L.oD2 + l * R.L.JV + x) i := by
    funext x i
    show t.hf (4 * z.d + 2 * z.V + x) i = _
    rw [Z.oD2, Finset.sum_range_one, pow_zero, one_mul, Nat.zero_mul, Nat.add_zero]
  rw [e]

/-! ## HD0 -/

/-- The family HD0, the top digit of a margin. The key holds the logits, which are not affine in the
cells; the form has a slot in their place. Beside the slot, the form is worth the weighted sum of
the extensions of the key less its part in the logits, all times the program's inverse of
2^(sh + 15). -/
theorem line_HD0 (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req} (Y : ReqFits R z y)
    (hsh : R.h.digSh = 8) (hXL : R.h.XL = 5)
    (hqH : Model.Head.callNo R.L "HD0" = some R.x.qH)
    (hwin : ∀ i, i < z.T → R.cov.hOn.getD i false = true → y.win i < z.V)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (hC : ShortAt W R (colsOf F R.iU3) "hr@phiC" R.h.lt u
      (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hr φ i))
    (S : SegFit ρ R "HD0" z.V low) (U : PosFit ρ R "HD0" u)
    (h : Ok (Model.Head.LINE R "HD0") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "HD0") F C ew F C ∧
      a.value ρ W = ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
        ((2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl +
          wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.V (fun x i =>
            HeadSizes.key z (npOf R.h) t H y .HD0 x i - ((y.rho i : ℤ) : K) *
              (HeadSizes.lg z t H i (y.win i) - HeadSizes.lg z t H i x))) := by
  -- the point of the call, under the number that the run keeps
  obtain ⟨q, hq, hqs, hqu⟩ := id U
  rw [hqH] at hq
  obtain rfl := Option.some.inj hq
  have hE : ρ.val (Model.Head.ercOf R) =
      Blocks.ext R.h.lt (fun i => ((HeadSizes.rhoC z y i : ℤ) : K)) u := by
    have e : Model.Head.ercOf R =
      (Model.Head.costWeights R.cov (Model.Head.ztOf R.h R.L R.x.g1 R.x.qH)).2.1 := rfl
    rw [e, costSum_value ρ R _ (fun i => ((HeadSizes.rhoC z y i : ℤ) : K)) hqs (Y.rhoCK Z)]
    exact ext_point _ hqu
  have hPl : ∀ ew : Array E, ρ.val (Model.Head.placeTermH R ew
        (Model.eqTab (Model.Head.ztOf R.h R.L R.x.g1 R.x.qH))) =
      wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.V
        (fun x i => ((y.rho i : ℤ) : K) * if x < y.win i then 1 else 0) := by
    intro ew
    rw [placeTermH_wsum ρ R ew _ (fun i => ((y.rho i : ℤ) : K)) y.win hqs (Y.rhoK Z)
      (fun i hi hon => ⟨Y.win i (by rw [Z.T]; exact hi) hon,
        by rw [Z.V]; exact hwin i (by rw [Z.T]; exact hi) hon⟩), Z.V]
    unfold wsum
    exact sum_congr rfl fun x _ => by rw [ext_point _ hqu]
  -- the routine, step by step
  unfold Model.Head.LINE at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨ew, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, _⟩ := ok_ewOf h1
  replace h2 : Ok (Model.Head.ztSeg R "HD0" >>= fun zt =>
      Model.Head.gapAt R "phiC" 0 (Model.Head.ercOf R) >>= fun c0 =>
      Model.Head.gapAt R "phiC" 1 (Model.Head.ercOf R) >>= fun c1 =>
      Model.Head.middleDigit R "HD0"
        (mulE (Model.Head.wxOf R ew) (Model.Head.onSum R zt)) >>= fun m =>
      Model.Head.lowDigit R "HD0"
        (mulE (Model.Head.wxOf R ew) (Model.Head.onSum R zt)) >>= fun lo =>
      pure (((Aff.slot R.x.tH.sCl).scale (Model.Head.pw R.h.lPd) +
          (c0 + c1.scale (Model.ofNat Model.bigH)).scale (Model.Head.wxOf R ew) -
          Aff.ofConst (addE
            (Model.Head.placeTermH R ew (Model.eqTab (Model.Head.ztOf R.h R.L R.x.g1 R.x.qH)))
            zeroE) -
          m.scale (Model.Head.pw R.h.digSh) - lo).scale
        (invE (Model.Head.pw (R.h.digSh + 15))))) F1 C1 a G D := h2
  rw [ok_bind] at h2
  obtain ⟨zt, F2, C2, h3, h4⟩ := h2
  obtain ⟨rfl, rfl, hzs, hzu⟩ := U.zt h3
  rw [ok_bind] at h4
  obtain ⟨c0, F3, C3, h5, h6⟩ := h4
  obtain ⟨rfl, rfl, v0⟩ := gap_cells hρ (i := 0) (o := 0) (n := 5)
    (c := fun j => ((HeadSizes.rhoC z y j : ℤ) : K)) (hr := t.hr) hXL rfl hC hE h5
  rw [ok_bind] at h6
  obtain ⟨c1, F4, C4, h7, h8⟩ := h6
  obtain ⟨rfl, rfl, v1⟩ := gap_cells hρ (i := 1) (o := 5) (n := 1)
    (c := fun j => ((HeadSizes.rhoC z y j : ℤ) : K)) (hr := t.hr) hXL rfl hC hE h7
  rw [ok_bind] at h8
  obtain ⟨m, F5, C5, h9, h10⟩ := h8
  obtain ⟨rfl, rfl, wh, hwh, vm⟩ := middleDigit_cells hρ Z hL h9
  rw [ok_bind] at h10
  obtain ⟨lo, F6, C6, h11, h12⟩ := h10
  obtain ⟨rfl, rfl, wh', hwh', vl⟩ := lowDigit_cells hρ Z hL h11
  rw [ok_pure] at h12
  obtain ⟨rfl, rfl, rfl⟩ := h12
  obtain ⟨b1, b2, b3⟩ := S.blocked h1 hwh
  obtain ⟨_, b2', b3'⟩ := S.blocked h1 hwh'
  refine ⟨rfl, rfl, ew, h1, ?_⟩
  -- the value, part by part
  generalize invE (Model.Head.pw (R.h.digSh + 15)) = iw
  have eB : ((Model.bigH : ℕ) : K) = 2 ^ 37 := by
    unfold Model.bigH
    rw [Nat.cast_pow, Nat.cast_ofNat]
  have vX : ρ.val (Model.Head.wxOf R ew) = ∑ x ∈ range z.V, ρ.val (ew.getD x zeroE) := by
    rw [wxOf_value ρ R ew (by rw [b1, Z.V]), Z.V]
  have vR : ρ.val (mulE (Model.Head.wxOf R ew) (Model.Head.onSum R zt)) =
      (∑ x ∈ range z.V, ρ.val (ew.getD x zeroE)) *
        Blocks.ext R.h.lt (fun i => ((y.rho i : ℤ) : K)) u := by
    rw [ρ.mul, vX, onSum_value ρ R zt (fun i => ((y.rho i : ℤ) : K)) hzs (Y.rhoK Z),
      ext_point _ hzu]
  have vA : ((Aff.slot R.x.tH.sCl).scale (Model.Head.pw R.h.lPd)).value ρ W =
      (2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl := by
    rw [Aff.value_scale, Aff.value_slot, pw_value hρ]
  have vB : ((c0 + c1.scale (Model.ofNat Model.bigH)).scale (Model.Head.wxOf R ew)).value ρ W =
      (∑ x ∈ range z.V, ρ.val (ew.getD x zeroE)) *
        (Blocks.ext R.h.lt (fun j => ((HeadSizes.rhoC z y j : ℤ) : K) *
            Inst.Model.Ledger.b256 (fun m => 128 + t.hr m j) (99 + 0) 5) u + 2 ^ 37 *
          Blocks.ext R.h.lt (fun j => ((HeadSizes.rhoC z y j : ℤ) : K) *
            Inst.Model.Ledger.b256 (fun m => 128 + t.hr m j) (99 + 5) 1) u) := by
    rw [Aff.value_scale, Aff.value_add, Aff.value_scale, v0, v1, vX, hρ.ofNat, eB]
  have vC : (Aff.ofConst (addE
        (Model.Head.placeTermH R ew (Model.eqTab (Model.Head.ztOf R.h R.L R.x.g1 R.x.qH)))
        zeroE)).value ρ W =
      wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.V
        (fun x i => ((y.rho i : ℤ) : K) * if x < y.win i then 1 else 0) := by
    rw [Aff.value_ofConst, ρ.add, ρ.zero, add_zero, hPl ew]
  have vM : (m.scale (Model.Head.pw R.h.digSh)).value ρ W = 2 ^ 8 *
      (32896 * ((∑ x ∈ range z.V, ρ.val (ew.getD x zeroE)) *
          Blocks.ext R.h.lt (fun i => ((y.rho i : ℤ) : K)) u) +
        wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.V
          (fun x i => HeadSizes.d1 z t x i)) := by
    rw [Aff.value_scale, vm ew b3, b2, vR, pw_value hρ, hsh]
  have vL : lo.value ρ W =
      128 * ((∑ x ∈ range z.V, ρ.val (ew.getD x zeroE)) *
          Blocks.ext R.h.lt (fun i => ((y.rho i : ℤ) : K)) u) +
        wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.V
          (fun x i => HeadSizes.d2 z t x i) := by
    rw [vl ew b3', b2', vR]
  rw [Aff.value_scale, Aff.value_sub, Aff.value_sub, Aff.value_sub, Aff.value_add, vA, vB, vC,
    vM, vL]
  -- the key's affine part
  have e : (fun x i => HeadSizes.key z (npOf R.h) t H y .HD0 x i - ((y.rho i : ℤ) : K) *
        (HeadSizes.lg z t H i (y.win i) - HeadSizes.lg z t H i x)) = fun x i =>
      ((HeadSizes.rhoC z y i : ℤ) : K) *
          (Inst.Model.Head.hidC t i + 2 ^ 37 * Inst.Model.Head.hidB t i) -
        ((y.rho i : ℤ) : K) * (if x < y.win i then 1 else 0) -
        2 ^ 8 * (HeadSizes.d1 z t x i + 32896 * ((y.rho i : ℤ) : K)) -
        (HeadSizes.d2 z t x i + 128 * ((y.rho i : ℤ) : K)) := by
    funext x i
    show (((y.rho i : ℤ) : K) * (HeadSizes.lg z t H i (y.win i) - HeadSizes.lg z t H i x -
          if x < y.win i then 1 else 0) + ((HeadSizes.rhoC z y i : ℤ) : K) *
          (Inst.Model.Head.hidC t i + 2 ^ 37 * Inst.Model.Head.hidB t i)) -
        2 ^ 8 * (HeadSizes.d1 z t x i + 32896 * ((y.rho i : ℤ) : K)) -
        (HeadSizes.d2 z t x i + 128 * ((y.rho i : ℤ) : K)) - ((y.rho i : ℤ) : K) *
        (HeadSizes.lg z t H i (y.win i) - HeadSizes.lg z t H i x) =
      ((HeadSizes.rhoC z y i : ℤ) : K) *
          (Inst.Model.Head.hidC t i + 2 ^ 37 * Inst.Model.Head.hidB t i) -
        ((y.rho i : ℤ) : K) * (if x < y.win i then 1 else 0) -
        2 ^ 8 * (HeadSizes.d1 z t x i + 32896 * ((y.rho i : ℤ) : K)) -
        (HeadSizes.d2 z t x i + 128 * ((y.rho i : ℤ) : K))
    ring
  have eA : Blocks.ext R.h.lt (fun i => ((HeadSizes.rhoC z y i : ℤ) : K) *
        (Inst.Model.Head.hidC t i + 2 ^ 37 * Inst.Model.Head.hidB t i)) u =
      Blocks.ext R.h.lt (fun j => ((HeadSizes.rhoC z y j : ℤ) : K) *
        Inst.Model.Ledger.b256 (fun m => 128 + t.hr m j) (99 + 0) 5) u + 2 ^ 37 *
      Blocks.ext R.h.lt (fun j => ((HeadSizes.rhoC z y j : ℤ) : K) *
        Inst.Model.Ledger.b256 (fun m => 128 + t.hr m j) (99 + 5) 1) u := by
    have e2 : (fun i => ((HeadSizes.rhoC z y i : ℤ) : K) *
          (Inst.Model.Head.hidC t i + 2 ^ 37 * Inst.Model.Head.hidB t i)) = fun j =>
        ((HeadSizes.rhoC z y j : ℤ) : K) *
            Inst.Model.Ledger.b256 (fun m => 128 + t.hr m j) (99 + 0) 5 +
          2 ^ 37 * (((HeadSizes.rhoC z y j : ℤ) : K) *
            Inst.Model.Ledger.b256 (fun m => 128 + t.hr m j) (99 + 5) 1) := by
      funext j
      show ((HeadSizes.rhoC z y j : ℤ) : K) *
          (Inst.Model.Ledger.b256 (fun m => 128 + t.hr m j) (99 + 0) 5 +
            2 ^ 37 * Inst.Model.Ledger.b256 (fun m => 128 + t.hr m j) (99 + 5) 1) =
        ((HeadSizes.rhoC z y j : ℤ) : K) *
            Inst.Model.Ledger.b256 (fun m => 128 + t.hr m j) (99 + 0) 5 +
          2 ^ 37 * (((HeadSizes.rhoC z y j : ℤ) : K) *
            Inst.Model.Ledger.b256 (fun m => 128 + t.hr m j) (99 + 5) 1)
      ring
    rw [e2, Blocks.ext_add, Blocks.ext_smul]
  rw [e, wsum_margin, eA]
  ring

/-- Under a reading that takes inverses to inverses, in a field where 2 is not 0, the program's
inverse of 2^k is the inverse of 2^k. -/
theorem iw_value (hρ : Numerals ρ) (hI : Inverse ρ) (h2 : (2 : K) ≠ 0) (k : ℕ) :
    (2 : K) ^ k * ρ.val (invE (Model.Head.pw k)) = 1 := by
  rw [hI, pw_value hρ]
  exact mul_inv_cancel₀ (pow_ne_zero k h2)

/-- The factor of the form of HD0, at the shift 8: its product with 2^23 is 1. -/
theorem iw_23 (hρ : Numerals ρ) (hI : Inverse ρ) (h2 : (2 : K) ≠ 0) {R : Model.Head.Run}
    (hsh : R.h.digSh = 8) : ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) * 2 ^ 23 = 1 := by
  rw [hsh, mul_comm]
  exact iw_value hρ hI h2 23

/-! ## HE0, HE1 -/

/-- The weighted sum of a key of the families HE0 and HE1, in its pieces: r depends on the position
alone. -/
theorem wsum_he (g : ℕ → K) (lt : ℕ) (u : ℕ → K) (n : ℕ) (r : ℕ → K) (d1 ex : ℕ → ℕ → K)
    (o1 k o3 : K) :
    wsum g lt u n (fun x i => d1 x i + o1 * r i + k * (o3 + ex x i)) =
      (∑ x ∈ range n, g x) * (o1 * Blocks.ext lt r u + k * o3) + wsum g lt u n d1 +
        k * wsum g lt u n ex := by
  rw [wsum_add, wsum_add, wsum_smul, wsum_smul, wsum_add, wsum_const, wsum_pos]
  ring

/-- The difference between a looked-up value and its three cells. -/
theorem offE_value : ((Model.Head.offE : ℕ) : K) = 8421505 := by
  have e : Model.Head.offE = 8421505 := rfl
  rw [e, Nat.cast_ofNat]

/-- What the forms of HE0 and HE1 share. The segment sn has n entries; entry x stands for entry
v0 + x of the vocabulary; none stands behind the vocabulary. -/
theorem he_value (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z) {sn : String}
    {v0 n : ℕ} {ew : Array E} {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K}
    {t : Inst.Model.Head.Cells K} {y : Inst.Model.Head.Req} (Y : ReqFits R z y)
    (hv0 : 2 ^ R.h.ls ∣ v0) (hn : n ≤ R.h.V - v0)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R sn n low) (U : PosFit ρ R sn u)
    (h1 : Ok (Model.Head.ewOf R sn) F C ew F C)
    (h : Ok (Model.Head.ztSeg R sn >>= fun zt =>
      Model.Head.Sl R sn (R.L.oD1 + v0) 2 R.L.JV >>= fun s1 =>
      Model.Head.Sl R sn (R.L.oE + v0) 3 R.L.JV >>= fun s2 =>
      pure (Aff.ofConst (mulE (mulE Model.Head.o2 (Model.sumE (ew.extract 0 (R.h.V - v0))))
          (Model.Head.onSum R zt)) + s1 +
        (Aff.ofConst (Model.scaleNat (Model.sumE ew) Model.Head.offE) + s2).scale
          (Model.Head.pw 16))) F C a G D) :
    G = F ∧ D = C ∧ a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u n
      (fun x i => HeadSizes.K1 z t y (v0 + x) i + 2 ^ 16 * HeadSizes.ex z t (v0 + x) i) := by
  rw [ok_bind] at h
  obtain ⟨zt, F2, C2, h3, h4⟩ := h
  obtain ⟨rfl, rfl, hzs, hzu⟩ := U.zt h3
  rw [ok_bind] at h4
  obtain ⟨s1, F3, C3, h5, h6⟩ := h4
  obtain ⟨rfl, rfl, wh, hwh, v1⟩ := Sl_cells hρ hL
    (fun l _ => by
      rw [Z.oD1, Z.JV]
      exact Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left Z.Sd 4) hv0) (Dvd.dvd.mul_left Z.SV l)) h5
  rw [ok_bind] at h6
  obtain ⟨s2, F4, C4, h7, h8⟩ := h6
  obtain ⟨rfl, rfl, wh', hwh', v2⟩ := Sl_cells hρ hL
    (fun l _ => by
      rw [Z.oE, Z.JV]
      exact Nat.dvd_add (Nat.dvd_add
        (Nat.dvd_add (Dvd.dvd.mul_left Z.Sd 4) (Dvd.dvd.mul_left Z.SV 3)) hv0)
        (Dvd.dvd.mul_left Z.SV l)) h7
  rw [ok_pure] at h8
  obtain ⟨rfl, rfl, rfl⟩ := h8
  obtain ⟨b1, b2, b3⟩ := S.blocked h1 hwh
  obtain ⟨_, b2', b3'⟩ := S.blocked h1 hwh'
  refine ⟨rfl, rfl, ?_⟩
  have vW : ρ.val (Model.sumE ew) = ∑ x ∈ range n, ρ.val (ew.getD x zeroE) := by
    rw [sumE_value', b1]
  have vX : ρ.val (Model.sumE (ew.extract 0 (R.h.V - v0))) =
      ∑ x ∈ range n, ρ.val (ew.getD x zeroE) := by
    rw [sumE_extract ρ ew _ (by rw [b1]; exact hn), b1]
  have vO : (Aff.ofConst (mulE (mulE Model.Head.o2 (Model.sumE (ew.extract 0 (R.h.V - v0))))
        (Model.Head.onSum R zt))).value ρ W =
      32896 * (∑ x ∈ range n, ρ.val (ew.getD x zeroE)) *
        Blocks.ext R.h.lt (fun i => ((y.rho i : ℤ) : K)) u := by
    rw [Aff.value_ofConst, ρ.mul, ρ.mul, o2_value hρ, vX,
      onSum_value ρ R zt (fun i => ((y.rho i : ℤ) : K)) hzs (Y.rhoK Z), ext_point _ hzu]
  have vE : (Aff.ofConst (Model.scaleNat (Model.sumE ew) Model.Head.offE)).value ρ W =
      8421505 * ∑ x ∈ range n, ρ.val (ew.getD x zeroE) := by
    rw [Aff.value_ofConst, hρ.scaleNat, vW, offE_value]
  rw [Aff.value_add, Aff.value_add, Aff.value_scale, Aff.value_add, vO, vE, v1 ew b3, v2 ew b3',
    b2, b2', pw_value hρ]
  have e : (fun x i => HeadSizes.K1 z t y (v0 + x) i + 2 ^ 16 * HeadSizes.ex z t (v0 + x) i) =
      fun x i => (∑ l ∈ range 2, (256 : K) ^ l * t.hf (R.L.oD1 + v0 + l * R.L.JV + x) i) +
        32896 * ((y.rho i : ℤ) : K) + 2 ^ 16 *
        (8421505 + ∑ l ∈ range 3, (256 : K) ^ l * t.hf (R.L.oE + v0 + l * R.L.JV + x) i) := by
    funext x i
    have i1 : ∀ l, R.L.oD1 + v0 + l * R.L.JV + x = 4 * z.d + z.V * l + (v0 + x) := by
      intro l
      rw [Z.oD1, Z.JV]
      ring
    have i2 : ∀ l, R.L.oE + v0 + l * R.L.JV + x = 4 * z.d + 3 * z.V + z.V * l + (v0 + x) := by
      intro l
      rw [Z.oE, Z.JV]
      ring
    simp only [i1, i2]
    rfl
  rw [e, wsum_he]
  ring

/-- The family HE0: the middle digit of a margin with the value looked up at it, for the first Va
entries of the vocabulary. -/
theorem line_HE0 (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req} (Y : ReqFits R z y) (hVa : z.Va ≤ z.V)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "HE0" z.Va low) (U : PosFit ρ R "HE0" u)
    (h : Ok (Model.Head.LINE R "HE0") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "HE0") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.Va
        (fun x i => HeadSizes.key z (npOf R.h) t H y .HE0 x i) := by
  unfold Model.Head.LINE at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨ew, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, _⟩ := ok_ewOf h1
  obtain ⟨e1, e2, hv⟩ := he_value hρ Z (sn := "HE0") (v0 := 0) (n := z.Va) Y (Nat.dvd_zero _)
    (by rw [Z.V, Nat.sub_zero]; exact hVa) hL S U h1 h2
  refine ⟨e1, e2, ew, h1, ?_⟩
  simp only [Nat.zero_add] at hv
  exact hv

/-- The family HE1: the same for the entries of the vocabulary from entry Va on. -/
theorem line_HE1 (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req} (Y : ReqFits R z y) (hSa : 2 ^ R.h.ls ∣ z.Va)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "HE1" (z.V - z.Va) low) (U : PosFit ρ R "HE1" u)
    (h : Ok (Model.Head.LINE R "HE1") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "HE1") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (z.V - z.Va)
        (fun x i => HeadSizes.key z (npOf R.h) t H y .HE1 x i) := by
  unfold Model.Head.LINE at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨ew, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, _⟩ := ok_ewOf h1
  obtain ⟨e1, e2, hv⟩ := he_value hρ Z (sn := "HE1") (v0 := R.L.JVa) (n := z.V - z.Va) Y
    (by rw [Z.JVa]; exact hSa) (le_of_eq (by rw [Z.V, Z.JVa])) hL S U h1 h2
  refine ⟨e1, e2, ew, h1, ?_⟩
  rw [Z.JVa] at hv
  exact hv

/-! ## At the library's sizes, in the library's own names -/

/-- HD0 at the library's sizes, on the key of Policy/Rel/LedgerHead.lean. -/
theorem line_HD0_ref (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req} (Y : ReqFits R HeadSizes.ref y) (hy : y.OK)
    (hsh : R.h.digSh = 8) (hXL : R.h.XL = 5)
    (hqH : Model.Head.callNo R.L "HD0" = some R.x.qH)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (hC : ShortAt W R (colsOf F R.iU3) "hr@phiC" R.h.lt u
      (fun φ i => ((y.rhoC i : ℤ) : K) * t.hr φ i))
    (S : SegFit ρ R "HD0" (Inst.Model.Head.len .HD0) low) (U : PosFit ρ R "HD0" u)
    (h : Ok (Model.Head.LINE R "HD0") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "HD0") F C ew F C ∧
      a.value ρ W = ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
        ((2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl +
          wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Inst.Model.Head.len .HD0) (fun x i =>
            Policy.LedgerHead.key (npOf R.h) t H y .HD0 x i - ((y.rho i : ℤ) : K) *
              (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i x))) :=
  line_HD0 hρ Z H Y hsh hXL hqH (fun i _ _ => hy i) hL hC S U h

/-- Where no position is counted, the margin has no cost: the key of Policy/Rel/LedgerHead.lean is
that of Cm/TargetPHead.lean. -/
theorem key_HD0_plain {t : Inst.Model.Head.Cells K} (np : NormPar) (H : ℕ → ℕ → K)
    {y : Inst.Model.Head.Req} {i : ℕ} (h0 : y.rhoC i = 0) (x : ℕ) :
    Policy.LedgerHead.key np t H y .HD0 x i = Cm.Plain.TP.key np t H y .HD0 x i := by
  show (((y.rho i : ℤ) : K) * (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i x -
        if x < y.win i then 1 else 0) + ((y.rhoC i : ℤ) : K) *
        (Inst.Model.Head.hidC t i + 2 ^ 37 * Inst.Model.Head.hidB t i)) -
      2 ^ 8 * Inst.Model.Head.K1 t y x i - Inst.Model.Head.K2 t y x i =
    ((y.rho i : ℤ) : K) * (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i x -
        if x < y.win i then 1 else 0) -
      2 ^ 8 * Inst.Model.Head.K1 t y x i - Inst.Model.Head.K2 t y x i
  rw [h0, Int.cast_zero, zero_mul, add_zero]

/-- HD0 at the library's sizes, for a request without a counted position, on the key of
Cm/TargetPHead.lean. -/
theorem line_HD0_plain (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req} (Y : ReqFits R HeadSizes.ref y) (hy : y.OK)
    (h0 : ∀ i, i < 1024 → y.rhoC i = 0)
    (hsh : R.h.digSh = 8) (hXL : R.h.XL = 5)
    (hqH : Model.Head.callNo R.L "HD0" = some R.x.qH)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (hC : ShortAt W R (colsOf F R.iU3) "hr@phiC" R.h.lt u
      (fun φ i => ((y.rhoC i : ℤ) : K) * t.hr φ i))
    (S : SegFit ρ R "HD0" (Cm.Plain.len .HD0) low) (U : PosFit ρ R "HD0" u)
    (h : Ok (Model.Head.LINE R "HD0") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "HD0") F C ew F C ∧
      a.value ρ W = ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
        ((2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl +
          wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Cm.Plain.len .HD0) (fun x i =>
            Cm.Plain.TP.key (npOf R.h) t H y .HD0 x i - ((y.rho i : ℤ) : K) *
              (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i x))) := by
  obtain ⟨e1, e2, ew, h1, hv⟩ := line_HD0_ref hρ Z H Y hy hsh hXL hqH hL hC S U h
  refine ⟨e1, e2, ew, h1, ?_⟩
  have e : wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Inst.Model.Head.len .HD0)
        (fun x i => Policy.LedgerHead.key (npOf R.h) t H y .HD0 x i - ((y.rho i : ℤ) : K) *
          (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i x)) =
      wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Cm.Plain.len .HD0)
        (fun x i => Cm.Plain.TP.key (npOf R.h) t H y .HD0 x i - ((y.rho i : ℤ) : K) *
          (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i x)) := by
    unfold wsum
    refine sum_congr rfl fun x _ => ?_
    have e3 : Blocks.ext R.h.lt
          (fun i => Policy.LedgerHead.key (npOf R.h) t H y .HD0 x i - ((y.rho i : ℤ) : K) *
            (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i x)) u =
        Blocks.ext R.h.lt
          (fun i => Cm.Plain.TP.key (npOf R.h) t H y .HD0 x i - ((y.rho i : ℤ) : K) *
            (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i x)) u :=
      Blocks.ext_congr (fun i hi => by
        have hi' : i < 1024 := by
          have hT : (1024 : ℕ) = 2 ^ R.h.lt := Z.T
          rw [hT]
          exact hi
        rw [key_HD0_plain (npOf R.h) H (h0 i hi') x]) u
    exact congrArg (fun w => ρ.val (ew.getD x zeroE) * w) e3
  rw [hv, e]

/-- HE0 at the library's sizes, on the key of Policy/Rel/LedgerHead.lean. -/
theorem line_HE0_ref (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req} (Y : ReqFits R HeadSizes.ref y)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "HE0" (Inst.Model.Head.len .HE0) low) (U : PosFit ρ R "HE0" u)
    (h : Ok (Model.Head.LINE R "HE0") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "HE0") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Inst.Model.Head.len .HE0)
        (fun x i => Policy.LedgerHead.key (npOf R.h) t H y .HE0 x i) :=
  line_HE0 hρ Z H Y (by show (131072 : ℕ) ≤ 202048; omega) hL S U h

/-- HE1 at the library's sizes, on the key of Policy/Rel/LedgerHead.lean. -/
theorem line_HE1_ref (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req} (Y : ReqFits R HeadSizes.ref y)
    (hSa : 2 ^ R.h.ls ∣ 131072)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "HE1" (Inst.Model.Head.len .HE1) low) (U : PosFit ρ R "HE1" u)
    (h : Ok (Model.Head.LINE R "HE1") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "HE1") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Inst.Model.Head.len .HE1)
        (fun x i => Policy.LedgerHead.key (npOf R.h) t H y .HE1 x i) :=
  line_HE1 hρ Z H Y hSa hL S U h

#print axioms placeTermH_wsum
#print axioms gap_cells
#print axioms line_HD0
#print axioms line_HD0_ref
#print axioms line_HD0_plain
#print axioms line_HE0_ref
#print axioms line_HE1_ref
#print axioms iw_value
#print axioms iw_23
#print axioms costSum_value
#print axioms line_HE0
#print axioms line_HE1

end OnBytes.Road.Hd
