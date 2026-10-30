-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Clamp.lean: FROM READS THAT ARE TRUE BELOW THEIR LENGTHS TO THE HEAD's THREE LAWS
(K06Statement.lean): `k06Glue`, `k06Core`, `k06Out`, `k06Back`; and CORE and OUT AT THE RULE BY NAME
(`k06Core_at`, `k06Out_at`: at Lemma2b.lean's badP). K06Glue.lean and K06Proof.lean prove
them for reads that are true AT EVERY INDEX, which no real run's letters are. THE DEVICE: `clamp c`:
the letters' own entries below each read's length, and beyond it the constant form that holds the
true sum. The clamped reads are true at every index; AND EACH OF THE BLOCK's FORMS IS THE SAME FORM
UNDER BOTH, because it calls entries below the lengths alone (`…_clamp`): here, and nowhere else, the
indices are counted.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06Proof

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E invE okE addE mulE)
open OnBytes.Model (Aff Fork Reading World)
open Norm (lt ls d lPd T S2)

/-! ## Counting -/

theorem sumTo_congr (n : Nat) (f g : Nat → Form) (h : ∀ i, i < n → f i = g i) :
    sumTo n f = sumTo n g := by
  unfold sumTo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      ih fun i hi => h i (Nat.lt_succ_of_lt hi)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [h n (Nat.lt_succ_self n)]

/-- Block i of a stretch of n features from feature a on lies below the number of blocks. -/
theorem idx_lt {a n S N i : Nat} (hS : 0 < S) (hi : i < n / S) (h : a + n ≤ N) :
    a / S + i < N / S := by
  have h1 : (a / S + (i + 1)) * S ≤ N := by
    have e1 : a / S * S ≤ a := Nat.div_mul_le_self a S
    have e2 : (i + 1) * S ≤ n / S * S := Nat.mul_le_mul_right S hi
    have e3 : n / S * S ≤ n := Nat.div_mul_le_self n S
    rw [Nat.add_mul]
    omega
  have h2 := (Nat.le_div_iff_mul_le hS).mpr h1
  omega

variable [Sizes] [Policy] [Request] [Token]

theorem JVa_le (hV : 0 < V) : JVa ≤ JV := by
  have hJ : 0 < JV := lt_of_lt_of_le hV V_le_JV
  unfold JVa clog2
  split
  · simp; omega
  · rename_i h
    have h1 : JV - 1 ≠ 0 := by omega
    have := Nat.log2_self_le h1
    simp only [Nat.add_sub_cancel]
    omega

theorem number_lt (n : Number) (l : Nat) (hl : l < n.digits.2) : NR + n.digits.1 + l < NR + 21 := by
  cases n <;> simp only [Number.digits] at hl ⊢ <;> omega

section Letters
variable [FinalNorm.In] [In] [Heard] [R : Reads] (c : Cells)

/-- The letters' own entries below each read's length; beyond it the true sum as a constant form. -/
@[reducible] def clamp : Reads :=
  ⟨fun r i => if i < readLen r then R.entry r i else ((readAt c r.of i : E) : Form)⟩

theorem atCosts_clamp (n : Number) : atCosts n = (letI := clamp c; atCosts n) := by
  unfold atCosts
  refine sumTo_congr _ _ _ fun l hl => ?_
  show _ = (256 ^ l : Nat) • ((if NR + n.digits.1 + l < readLen .rowAtCosts then
    R.entry .rowAtCosts (NR + n.digits.1 + l) else _) + off1 * ERC)
  rw [if_pos (show NR + n.digits.1 + l < readLen .rowAtCosts from number_lt n l hl)]

theorem summed_clamp (n : Number) : summed n = (letI := clamp c; summed n) := by
  unfold summed
  refine sumTo_congr _ _ _ fun l hl => ?_
  show _ = (256 ^ l : Nat) • ((if NR + n.digits.1 + l < readLen .rowCount then
    R.entry .rowCount (NR + n.digits.1 + l) else _) + off1 * RC)
  rw [if_pos (show NR + n.digits.1 + l < readLen .rowCount from number_lt n l hl)]

theorem wideAt_clamp (k : Key) (f0 nl stride : Nat)
    (hb : ∀ l, l < nl → f0 + l * stride + len k ≤ 4 * d + 6 * JV) :
    wideAt k f0 nl stride = (letI := clamp c; wideAt k f0 nl stride) := by
  unfold wideAt
  refine sumTo_congr _ _ _ fun i hi => ?_
  refine sumTo_congr _ _ _ fun l hl => ?_
  show _ = (256 ^ l * ewh k i) • (if (f0 + l * stride) / S2 + i < readLen .wideAtKeys then
    R.entry .wideAtKeys ((f0 + l * stride) / S2 + i) else _)
  rw [if_pos (show (f0 + l * stride) / S2 + i < readLen .wideAtKeys from
    idx_lt S2_pos hi (hb l hl))]

theorem tableValuesAtCosts_clamp :
    tableValuesAtCosts = (letI := clamp c; tableValuesAtCosts) := by
  have h : (sumTo 3 fun l => sumTo (JV / S2) fun i =>
      (256 ^ l : Nat) • entry .wideAtCosts ((4 * d + (3 + l) * JV) / S2 + i))
      = (letI := clamp c; sumTo 3 fun l => sumTo (JV / S2) fun i =>
        (256 ^ l : Nat) • entry .wideAtCosts ((4 * d + (3 + l) * JV) / S2 + i)) := by
    refine sumTo_congr _ _ _ fun l hl => ?_
    refine sumTo_congr _ _ _ fun i hi => ?_
    show _ = (256 ^ l : Nat) • (if (4 * d + (3 + l) * JV) / S2 + i < readLen .wideAtCosts then
      R.entry .wideAtCosts ((4 * d + (3 + l) * JV) / S2 + i) else _)
    rw [if_pos (show (4 * d + (3 + l) * JV) / S2 + i < readLen .wideAtCosts from
      idx_lt S2_pos hi (by interval_cases l <;> omega))]
  unfold tableValuesAtCosts
  rw [h]

theorem len_le (hV : 0 < V) (k : Key) : first k + len k ≤ JV := by
  have := JVa_le hV
  cases k <;> simp only [first, len] <;> omega

theorem mid_clamp (k : Key) (v0 : Nat) (hv : v0 + len k ≤ JV) :
    mid k v0 = (letI := clamp c; mid k v0) := by
  unfold mid
  rw [wideAt_clamp c k (4 * d + v0) 2 JV (fun l hl => by interval_cases l <;> omega)]

theorem low_clamp (k : Key) (hv : len k ≤ JV) : low k = (letI := clamp c; low k) := by
  unfold low
  rw [wideAt_clamp c k (4 * d + 2 * JV) 1 JV (fun l hl => by interval_cases l; omega)]

theorem tableValue_clamp (k : Key) (v0 : Nat) (hv : v0 + len k ≤ JV) :
    tableValue k v0 = (letI := clamp c; tableValue k v0) := by
  unfold tableValue
  rw [wideAt_clamp c k (4 * d + 3 * JV + v0) 3 JV (fun l hl => by interval_cases l <;> omega)]

theorem top_clamp (hV : 0 < V) : top = (letI := clamp c; top) := by
  have h := len_le hV .marginTop
  simp only [first] at h
  unfold top
  rw [atCosts_clamp c .paid, atCosts_clamp c .over, mid_clamp c .marginTop 0 h,
    low_clamp c .marginTop (by omega)]

theorem key_clamp (hV : 0 < V) (k : Key) : key k = (letI := clamp c; key k) := by
  have h := len_le hV k
  cases k with
  | marginTop => exact top_clamp c hV
  | marginMid => exact mid_clamp c .marginMid 0 h
  | marginLow => exact low_clamp c .marginLow (by simp only [first] at h; omega)
  | tableA =>
    show mid .tableA 0 + (2 ^ 16 : Nat) • tableValue .tableA 0 = _
    rw [mid_clamp c .tableA 0 h, tableValue_clamp c .tableA 0 h]
    rfl
  | tableB =>
    show mid .tableB JVa + (2 ^ 16 : Nat) • tableValue .tableB JVa = _
    rw [mid_clamp c .tableB JVa h, tableValue_clamp c .tableB JVa h]
    rfl

theorem clip_clamp : clip = (letI := clamp c; clip) := by
  unfold clip
  rw [atCosts_clamp c .paid, atCosts_clamp c .slackClip]

theorem table_clamp : table = (letI := clamp c; table) := by
  unfold table
  rw [atCosts_clamp c .slackTable, tableValuesAtCosts_clamp c]

theorem mean_clamp : mean = (letI := clamp c; mean) := by
  unfold mean
  rw [summed_clamp c .paid, summed_clamp c .over, summed_clamp c .slackMean]

theorem count_clamp : count = (letI := clamp c; count) := by
  unfold count
  rw [summed_clamp c .over, summed_clamp c .slackCap]

theorem logitForms_clamp : logitForms = (letI := clamp c; logitForms) := by
  have h : (sumTo d fun k => eq rs k • FinalNorm.actAt (entry .actAtLogits) k)
      = (letI := clamp c; sumTo d fun k => eq rs k • FinalNorm.actAt (entry .actAtLogits) k) := by
    refine sumTo_congr _ _ _ fun k hk => ?_
    unfold FinalNorm.actAt
    show _ = eq rs k • ((if k < readLen .actAtLogits then R.entry .actAtLogits k else _)
      + (256 : Nat) • (if d + k < readLen .actAtLogits then R.entry .actAtLogits (d + k) else _))
    rw [if_pos (show k < readLen .actAtLogits from (show k < 2 * d by omega)),
      if_pos (show d + k < readLen .actAtLogits from (show d + k < 2 * d by omega))]
  unfold logitForms
  rw [h]

/-- The clamped reads are true at every index. -/
theorem trueAll_clamp {F : Fork} {mask : Nat → E} {ent : Nat → Nat → Nat → E}
    (h : TrueReads c F mask ent) : (letI := clamp c; TrueReadsAll c F mask ent) := by
  intro r i
  show atWorld F mask ent (if i < readLen r then R.entry r i else ((readAt c r.of i : E) : Form)) = _
  split
  · rename_i hi; exact h r i hi
  · rfl

end Letters

/-- **THE GLUE.** -/
theorem k06Glue : K06GlueStatement := by
  intro _ _ _ _ _ _ _ _ c F mask ent hreq hy hw hzt hr hc
  have hV : 0 < V := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  have hT := trueAll_clamp c hr
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    @k06GlueAll _ _ _ _ _ _ _ (clamp c) c F mask ent hreq hy hw hzt hT hc
  refine ⟨fun k => ?_, ?_, ?_, ?_, ?_⟩
  · rw [key_clamp c hV k]; exact h1 k
  · rw [clip_clamp c]; exact h2
  · rw [table_clamp c]; exact h3
  · rw [mean_clamp c]; exact h4
  · rw [count_clamp c]; exact h5

/-! ## The laws AT THE RULE BY NAME

Whoever takes a law's "there is a rule" apart gets a rule of which nothing is known but the law. What
is proved of Lemma2b.lean's badP (its sets are empty at the truth: bEP_empty, bdP_empty; NoBadTrue.lean:
noBad_true) can be spent only where the law names badP. So each law stands first at that rule; the
closed statement follows in a line. -/

/-- **THE CORE, at the rule badP.** -/
theorem k06Core_at [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : Cells)
    (mask : Nat → E) (F0 : Fork) (hreq : Request.ok = true) (hy : y < V) (hWL : WellLaid F0)
    (hzt : (FinalNorm.zt).size = lt) :
    ∀ (F1 : Fork) (t : List Fmt.RoundView) (S : Sum) (G : Fork) (ent : Nat → Nat → Nat → E)
      [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads] [Reads],
      Canonical t →
      sumcheck (FinalNorm.zt ++ halves lPd) 2 F0 t = some (S, F1, []) → OnBytes.PscRun.Later F1 G →
      let _ : Heard := { logits := S }
      TrueReads c G mask ent → WeightTrue c G mask ent →
      (∀ fs, claims.lookup "logits" = some fs → ∀ f, f ∈ fs → atWorld G mask ent f = 0) →
      NoBad (badP c mask F0) t →
      (2 ^ lPd : E) * atWorld G mask ent logits.claimed.var = trueSum c := by
  intro F1 t S G ent _ _ _ _ hcan hsum hL _ hreads hwt hclaims hnb
  have hlog : ∀ f, f ∈ logitForms → atWorld G mask ent f = 0 :=
    hclaims logitForms (by simp [claims, List.lookup])
  rw [logitForms_clamp c] at hlog
  have hT := trueAll_clamp c hreads
  exact @k06CoreAll _ _ _ _ _ _ c mask F0 hreq hy hWL hzt F1 t S G ent (clamp c) hcan hsum hL hT hwt
    hlog hnb

/-- **THE CORE.** -/
theorem k06Core : K06CoreStatement := fun c mask F0 hreq hy hWL hzt =>
  ⟨badP c mask F0, fun h => bad_length _ _ _ _ h, k06Core_at c mask F0 hreq hy hWL hzt⟩

/-- **OUT, TO THE LOOKUP, at the rule badP.** -/
theorem k06Out_at [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : Cells)
    (mask : Nat → E) (F0 : Fork) (hreq : Request.ok = true) (hy : y < V) (hWL : WellLaid F0)
    (hw : WeightsOk) (hzt : (FinalNorm.zt).size = lt) :
    ∀ (F1 : Fork) (t : List Fmt.RoundView) (S : Sum) (G : Fork) (ent : Nat → Nat → Nat → E)
      [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads] [Reads],
      Canonical t →
      sumcheck (FinalNorm.zt ++ halves lPd) 2 F0 t = some (S, F1, []) → OnBytes.PscRun.Later F1 G →
      let _ : Heard := { logits := S }
      TrueReads c G mask ent → WeightTrue c G mask ent →
      (∀ fs, claims.lookup "logits" = some fs → ∀ f, f ∈ fs → atWorld G mask ent f = 0) →
      NoBad (badP c mask F0) t →
      (∀ k, atWorld G mask ent (key k) =
        sumTo (len k) fun x => sumTo T fun t =>
          In.ew k x * eq FinalNorm.zt t * keyAt c (corner x t) k) ∧
      atWorld G mask ent clip = (sumTo T fun t => eq FinalNorm.zt t * clipAt c (corner 0 t)) ∧
      atWorld G mask ent table = (sumTo T fun t => eq FinalNorm.zt t * tableAt c (corner 0 t)) := by
  intro F1 t S G ent _ _ _ _ hcan hsum hL _ hreads hwt hclaims hnb
  have hV : 0 < V := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  have hlog : ∀ f, f ∈ logitForms → atWorld G mask ent f = 0 :=
    hclaims logitForms (by simp [claims, List.lookup])
  rw [logitForms_clamp c] at hlog
  have hT := trueAll_clamp c hreads
  obtain ⟨h1, h2, h3⟩ :=
    @k06OutAll _ _ _ _ _ _ c mask F0 hreq hy hWL hw hzt F1 t S G ent (clamp c) hcan hsum hL hT hwt
      hlog hnb
  refine ⟨fun k => ?_, ?_, ?_⟩
  · rw [key_clamp c hV k]; exact h1 k
  · rw [clip_clamp c]; exact h2
  · rw [table_clamp c]; exact h3

/-- **OUT, TO THE LOOKUP.** -/
theorem k06Out : K06OutStatement := fun c mask F0 hreq hy hWL hw hzt =>
  ⟨badP c mask F0, fun h => bad_length _ _ _ _ h, k06Out_at c mask F0 hreq hy hWL hw hzt⟩

/-- **BACK, FROM THE LOOKUP.** -/
theorem k06Back : K06BackStatement := by
  intro _ _ _ _ sT tab c hplan hreq hy htab hW hA F mask ent _ _ _ _ hsmall hreads hmean hcount
    hkeys hguests
  rw [mean_clamp c] at hmean
  rw [count_clamp c] at hcount
  have hT := trueAll_clamp c hreads
  exact @k06BackAll _ _ _ _ sT tab c hplan hreq hy htab hW hA F mask ent _ _ _ (clamp c) hsmall hT
    hmean hcount hkeys hguests

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k06Glue
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k06Core
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k06Out
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k06Back
