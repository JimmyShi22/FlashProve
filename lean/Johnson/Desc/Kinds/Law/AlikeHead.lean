-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/AlikeHead.lean.
WHAT IT DOES NOT SHOW. No soundness. A TOOL AND ITS USE ON THE HEAD's OWN FORMS: no law by itself.
That
any two fillings of the reads stand in a relation: a premise (hR). The normalization's 29 forms and
four keys: another file. The form of "join": not here.
LETTERS. R, R': two fillings of the head's reads' places; Q: any relation of two forms that Kept2
asks; under "there is" (the two lists): f: a member of the list at R.
OBJECT. Desc/Kinds/Head.lean's policy (four forms), logitForms (two), key (five), at two fillings of
the class Reads.
USER. Whoever holds the forms as a seat states them (each read's entry a variable) and must speak of
the forms at the reads in truth (each entry a constant): Law/RowAtDecide.lean's OpenedAt.
WHAT IT IS. THE SAME FORM, MADE AT TWO FILLINGS OF THE READS' PLACES, STANDS IN EVERY RELATION THAT
THE
FORMS' ARITHMETIC KEEPS AND THAT HOLDS OF THE TWO FILLINGS' ENTRIES BELOW EACH READ's LENGTH. The
walk
through the making, with every index's bound, is Law/Covered.lean's, for a relation of two.
  Kept2 Q           Q (a + k b) (a' + k b') of Q a a' and Q b b'; Q f f at every form without an
  entry.
  Rel, ListRel      a form, a list of forms, as functions of the filling, at R and at R'.
  rel_*             atCosts, summed, wideAt, tableValuesAtCosts, mid, low, tableValue, clip, table,
                    mean, count, top.
  rel_key           the five keys.
  rel_policy, rel_logitForms   the two lists: to each member at R' a member at R.

-/
import Johnson.Desc.Kinds.Law.Covered

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff)
open Norm (lt ls d lPd T S2)

/-- The relation is kept by the forms' arithmetic, and holds of a form without an entry and itself.
-/
structure Kept2 (Q : Form → Form → Prop) : Prop where
  addMul : ∀ {a a' b b' : Form} (k : E), Q a a' → Q b b' →
    Q (Aff.addMul a b k) (Aff.addMul a' b' k)
  bare : ∀ f : Form, f.ents = #[] → Q f f

namespace Kept2

variable {Q : Form → Form → Prop} (C : Kept2 Q)
include C

theorem const (v : E) : Q (Aff.ofConst v) (Aff.ofConst v) := C.bare _ rfl
theorem slot (j : Nat) : Q (Aff.slot j) (Aff.slot j) := C.bare _ rfl
theorem add {f f' g g' : Form} (hf : Q f f') (hg : Q g g') : Q (f + g) (f' + g') :=
  C.addMul _ hf hg
theorem sub {f f' g g' : Form} (hf : Q f f') (hg : Q g g') : Q (f - g) (f' - g') :=
  C.addMul _ hf hg
theorem scale {f f' : Form} (hf : Q f f') (k : E) : Q (Aff.scale f k) (Aff.scale f' k) :=
  C.addMul _ (C.bare _ rfl) hf
theorem smulE (k : E) {f f' : Form} (hf : Q f f') : Q (k • f) (k • f') := C.scale hf _
theorem smulN (n : Nat) {f f' : Form} (hf : Q f f') : Q (n • f) (n • f') := C.scale hf _
theorem addN {f f' : Form} (hf : Q f f') (n : Nat) :
    Q (HAdd.hAdd (α := Form) (β := Nat) (γ := Form) f n)
      (HAdd.hAdd (α := Form) (β := Nat) (γ := Form) f' n) := C.addMul _ hf (C.const _)
theorem subN {f f' : Form} (hf : Q f f') (n : Nat) :
    Q (HSub.hSub (α := Form) (β := Nat) (γ := Form) f n)
      (HSub.hSub (α := Form) (β := Nat) (γ := Form) f' n) := C.addMul _ hf (C.const _)
theorem addE {f f' : Form} (hf : Q f f') (x : E) :
    Q (HAdd.hAdd (α := Form) (β := E) (γ := Form) f x)
      (HAdd.hAdd (α := Form) (β := E) (γ := Form) f' x) := C.addMul _ hf (C.const _)
theorem Eadd (x : E) {f f' : Form} (hf : Q f f') :
    Q (HAdd.hAdd (α := E) (β := Form) (γ := Form) x f)
      (HAdd.hAdd (α := E) (β := Form) (γ := Form) x f') := C.addMul _ (C.const _) hf
theorem subE {f f' : Form} (hf : Q f f') (x : E) :
    Q (HSub.hSub (α := Form) (β := E) (γ := Form) f x)
      (HSub.hSub (α := Form) (β := E) (γ := Form) f' x) := C.addMul _ hf (C.const _)
theorem natCast (n : Nat) : Q ((n : Nat) : Form) ((n : Nat) : Form) := C.const _

theorem sumTo (n : Nat) (f f' : Nat → Form) (h : ∀ i, i < n → Q (f i) (f' i)) :
    Q (Kinds.sumTo n f) (Kinds.sumTo n f') := by
  unfold Kinds.sumTo
  induction n with
  | zero => exact C.const _
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact C.add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n (Nat.lt_succ_self n))

end Kept2

section Head

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Heard]

/-- A form as a function of the filling, at the two fillings. -/
abbrev Rel (Q : Form → Form → Prop) (R R' : Reads) (t : [Reads] → Form) : Prop :=
  Q (@t R) (@t R')

/-- A list of forms as a function of the filling: to each member at R' a member at R. -/
abbrev ListRel (Q : Form → Form → Prop) (R R' : Reads) (t : [Reads] → List Form) : Prop :=
  ∀ f', f' ∈ @t R' → ∃ f, f ∈ @t R ∧ Q f f'

variable {Q : Form → Form → Prop} (C : Kept2 Q) (R R' : Reads)
  (hR : ∀ r i, i < readLen r → Q (R.entry r i) (R'.entry r i))
include C hR

theorem rel_atCosts (n : Number) : Rel Q R R' (atCosts n) := by
  unfold Rel atCosts
  exact C.sumTo _ _ _ fun l hl => C.smulN _
    (C.addE (hR _ _ (show _ < readLen .rowAtCosts from number_lt0 n l hl)) _)

theorem rel_summed (n : Number) : Rel Q R R' (summed n) := by
  unfold Rel summed
  exact C.sumTo _ _ _ fun l hl => C.smulN _
    (C.addN (hR _ _ (show _ < readLen .rowCount from number_lt0 n l hl)) _)

theorem rel_wideAt (k : Key) (f0 nl stride : Nat)
    (hb : ∀ l, l < nl → f0 + l * stride + len k ≤ 4 * d + 6 * JV) :
    Rel Q R R' (wideAt k f0 nl stride) := by
  unfold Rel wideAt
  exact C.sumTo _ _ _ fun i hi => C.sumTo _ _ _ fun l hl => C.smulE _
    (hR _ _ (show _ < readLen .wideAtKeys from idx_lt0 S2_pos0 hi (hb l hl)))

theorem rel_tableValuesAtCosts : Rel Q R R' tableValuesAtCosts := by
  unfold Rel tableValuesAtCosts
  refine C.Eadd _ (C.sumTo _ _ _ fun l hl => C.sumTo _ _ _ fun i hi =>
    C.smulN _ (hR _ _ (show _ < readLen .wideAtCosts from idx_lt0 S2_pos0 hi ?_)))
  have : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  rcases this with rfl | rfl | rfl <;> omega

theorem rel_mid (k : Key) (v0 : Nat) (hv : v0 + len k ≤ JV) : Rel Q R R' (mid k v0) := by
  unfold Rel mid
  refine C.Eadd _ (rel_wideAt C R R' hR k _ 2 JV fun l hl => ?_)
  have : l = 0 ∨ l = 1 := by omega
  rcases this with rfl | rfl <;> omega

theorem rel_low (k : Key) (hv : len k ≤ JV) : Rel Q R R' (low k) := by
  unfold Rel low
  refine C.Eadd _ (rel_wideAt C R R' hR k _ 1 JV fun l hl => ?_)
  have : l = 0 := by omega
  subst this; omega

theorem rel_tableValue (k : Key) (v0 : Nat) (hv : v0 + len k ≤ JV) :
    Rel Q R R' (tableValue k v0) := by
  unfold Rel tableValue
  refine C.Eadd _ (rel_wideAt C R R' hR k _ 3 JV fun l hl => ?_)
  have : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  rcases this with rfl | rfl | rfl <;> omega

theorem rel_clip : Rel Q R R' clip := by
  unfold Rel clip
  exact C.subE (C.add (rel_atCosts C R R' hR _) (rel_atCosts C R R' hR _)) _

theorem rel_table : Rel Q R R' table := by
  unfold Rel table
  exact C.subE (C.add (rel_atCosts C R R' hR _) (rel_tableValuesAtCosts C R R' hR)) _

theorem rel_mean : Rel Q R R' mean := by
  unfold Rel mean
  exact C.subN (C.add (C.add (rel_summed C R R' hR _)
    (C.smulN _ (rel_summed C R R' hR _))) (rel_summed C R R' hR _)) _

theorem rel_count : Rel Q R R' count := by
  unfold Rel count
  exact C.sub (C.add (rel_summed C R R' hR _) (rel_summed C R R' hR _)) (C.natCast _)

theorem rel_top (hJ : len .marginTop ≤ JV) (hc : Q logits.claimed.var logits.claimed.var) :
    Rel Q R R' top := by
  unfold Rel top
  exact C.smulE _ (C.sub (C.sub (C.subE (C.add (C.smulN _ hc)
    (C.smulE _ (C.add (rel_atCosts C R R' hR _) (C.smulN _ (rel_atCosts C R R' hR _))))) _)
    (C.smulN _ (rel_mid C R R' hR _ 0 (by omega)))) (rel_low C R R' hR _ hJ))

/-- **The five keys.** -/
theorem rel_key (hJ : JVa ≤ JV) (hc : Q logits.claimed.var logits.claimed.var) (k : Key) :
    Rel Q R R' (key k) := by
  cases k with
  | marginTop => exact rel_top C R R' hR (Nat.le_refl _) hc
  | marginMid => exact rel_mid C R R' hR _ 0 (by simp only [len]; omega)
  | marginLow => exact rel_low C R R' hR _ (Nat.le_refl _)
  | tableA =>
    exact C.add (rel_mid C R R' hR _ 0 (by simp only [len]; omega))
      (C.smulN _ (rel_tableValue C R R' hR _ 0 (by simp only [len]; omega)))
  | tableB =>
    exact C.add (rel_mid C R R' hR _ JVa (by simp only [len]; omega))
      (C.smulN _ (rel_tableValue C R R' hR _ JVa (by simp only [len]; omega)))

/-- **The policy's four.** -/
theorem rel_policy : ListRel Q R R' policy := by
  intro f' hf'
  unfold policy at hf'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
  rcases hf' with rfl | rfl | rfl | rfl
  · exact ⟨@mean _ _ _ R, by unfold policy; simp, rel_mean C R R' hR⟩
  · exact ⟨@count _ _ _ R, by unfold policy; simp, rel_count C R R' hR⟩
  · exact ⟨@clip _ _ _ _ R, by unfold policy; simp, rel_clip C R R' hR⟩
  · exact ⟨@table _ _ _ R, by unfold policy; simp, rel_table C R R' hR⟩

/-- **Both of logitForms.** -/
theorem rel_logitForms (hl : ∀ S0, Q (logits.left S0) (logits.left S0))
    (he : Q (logits.end_ 0).var (logits.end_ 0).var) : ListRel Q R R' logitForms := by
  intro f' hf'
  unfold logitForms at hf'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
  rcases hf' with rfl | rfl
  · exact ⟨_, by unfold logitForms; exact List.mem_cons_self, hl _⟩
  · refine ⟨_, by unfold logitForms; exact List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    refine C.sub he (C.sumTo _ _ _ fun k hk => C.smulE _ ?_)
    unfold FinalNorm.actAt
    exact C.add (hR _ _ (show k < 2 * d by omega))
      (C.smulN _ (hR _ _ (show d + k < 2 * d by omega)))

end Head

end VerifiableInference.Desc.Kinds.Head.Law
