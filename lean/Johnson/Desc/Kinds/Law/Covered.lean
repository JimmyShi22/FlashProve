-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Covered.lean: FOR THE SUB-ROW reads_covered_K06: EVERY ENTRY THAT THE HEAD's FORMS NAME IS A
READ's ENTRY BELOW THAT READ's LENGTH. `Covered f`: each entry (array, virtual row, index) in f's own
list of entries is one that `entry r i` names, for a read r of the head's five and an i < readLen r
(K06Statement.lean). Closed under the forms' arithmetic (all of it is Aff.addMul). Shown of
key (five), clip, table, mean, count and of logitForms' two. GENERIC IN THE READS' PLACES.
WHAT IT DOES NOT SAY: where `entry r i` lies (the seat's text: HeadSeatAt.lean: position = the read's
base in the plan's table + i); THAT THE PLAN's TABLE GIVES EACH READ A STRETCH OF AT LEAST readLen: not
compared. The normalization's forms: not here. The variables of what was heard (the claimed sum, the
end values) are asked to be covered: at a hearing's return they are bare slots.
-/
import Johnson.Desc.Kinds.Law.K06Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Ent)
open Norm (lt ls d lPd T S2)

theorem foldl_push_toList {α β : Type} (g : β → α) : ∀ (l : List β) (a : Array α),
    (l.foldl (fun acc x => acc.push (g x)) a).toList = a.toList ++ l.map g
  | [], a => by simp
  | x :: xs, a => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_push_toList g xs (a.push (g x))]
    simp

theorem addMul_ents (a b : Aff) (k : E) : (Aff.addMul a b k).ents.toList
    = a.ents.toList ++ b.ents.toList.map fun x => { x with coef := OnBytes.mulE x.coef k } := by
  show (b.ents.foldl (fun l x => l.push { x with coef := OnBytes.mulE x.coef k }) a.ents).toList = _
  rw [← Array.foldl_toList, foldl_push_toList]

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Heard] [Reads]

/-- Every entry that the form names is a read's entry below that read's length. -/
def Covered (f : Form) : Prop :=
  ∀ x, x ∈ f.ents.toList → ∃ (r : Read) (i : Nat), i < readLen r ∧
    ∃ y, y ∈ (entry r i).ents.toList ∧ y.tree = x.tree ∧ y.row = x.row ∧ y.idx = x.idx

theorem covered_addMul {a b : Form} (ha : Covered a) (hb : Covered b) (k : E) :
    Covered (Aff.addMul a b k) := by
  intro x hx
  rw [addMul_ents] at hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
    exact hb z hz

theorem covered_noEnts {f : Form} (h : f.ents = #[]) : Covered f := by
  intro x hx
  rw [h] at hx
  simp at hx

theorem covered_const (v : E) : Covered (Aff.ofConst v) := covered_noEnts rfl
theorem covered_slot (j : Nat) : Covered (Aff.slot j) := covered_noEnts rfl
theorem covered_entry {r : Read} {i : Nat} (h : i < readLen r) : Covered (entry r i) :=
  fun x hx => ⟨r, i, h, x, hx, rfl, rfl, rfl⟩

theorem covered_add {f g : Form} (hf : Covered f) (hg : Covered g) : Covered (f + g) :=
  covered_addMul hf hg _
theorem covered_sub {f g : Form} (hf : Covered f) (hg : Covered g) : Covered (f - g) :=
  covered_addMul hf hg _
theorem covered_smulE (k : E) {f : Form} (hf : Covered f) : Covered (k • f) :=
  covered_addMul (covered_noEnts rfl) hf _
theorem covered_smulN (n : Nat) {f : Form} (hf : Covered f) : Covered (n • f) :=
  covered_addMul (covered_noEnts rfl) hf _
theorem covered_addE {f : Form} (hf : Covered f) (x : E) :
    Covered (HAdd.hAdd (α := Form) (β := E) (γ := Form) f x) := covered_addMul hf (covered_const _) _
theorem covered_Eadd (x : E) {f : Form} (hf : Covered f) :
    Covered (HAdd.hAdd (α := E) (β := Form) (γ := Form) x f) := covered_addMul (covered_const _) hf _
theorem covered_subE {f : Form} (hf : Covered f) (x : E) :
    Covered (HSub.hSub (α := Form) (β := E) (γ := Form) f x) := covered_addMul hf (covered_const _) _
theorem covered_addN {f : Form} (hf : Covered f) (n : Nat) :
    Covered (HAdd.hAdd (α := Form) (β := Nat) (γ := Form) f n) :=
  covered_addMul hf (covered_const _) _
theorem covered_subN {f : Form} (hf : Covered f) (n : Nat) :
    Covered (HSub.hSub (α := Form) (β := Nat) (γ := Form) f n) :=
  covered_addMul hf (covered_const _) _
theorem covered_natCast (n : Nat) : Covered ((n : Nat) : Form) := covered_const _

theorem covered_sumTo (n : Nat) (f : Nat → Form) (h : ∀ i, i < n → Covered (f i)) :
    Covered (sumTo n f) := by
  unfold sumTo
  induction n with
  | zero => exact covered_const _
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact covered_add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n (Nat.lt_succ_self n))

/-! ## Counting (as in Clamp.lean; typed here without Mathlib) -/

theorem idx_lt0 {a n S N i : Nat} (hS : 0 < S) (hi : i < n / S) (h : a + n ≤ N) :
    a / S + i < N / S := by
  have h1 : (a / S + (i + 1)) * S ≤ N := by
    have e1 : a / S * S ≤ a := Nat.div_mul_le_self a S
    have e2 : (i + 1) * S ≤ n / S * S := Nat.mul_le_mul_right S hi
    have e3 : n / S * S ≤ n := Nat.div_mul_le_self n S
    rw [Nat.add_mul]
    omega
  have h2 := (Nat.le_div_iff_mul_le hS).mpr h1
  omega

theorem S2_pos0 : 0 < S2 := by unfold S2; exact Nat.pos_of_ne_zero (by simp)

theorem number_lt0 (n : Number) (l : Nat) (hl : l < n.digits.2) :
    NR + n.digits.1 + l < NR + 21 := by
  cases n <;> simp only [Number.digits] at hl ⊢ <;> omega

/-! ## The head's forms -/

theorem covered_atCosts (n : Number) : Covered (atCosts n) := by
  unfold atCosts
  exact covered_sumTo _ _ fun l hl => covered_smulN _
    (covered_addE (covered_entry (show _ < readLen .rowAtCosts from number_lt0 n l hl)) _)

theorem covered_summed (n : Number) : Covered (summed n) := by
  unfold summed
  exact covered_sumTo _ _ fun l hl => covered_smulN _
    (covered_addN (covered_entry (show _ < readLen .rowCount from number_lt0 n l hl)) _)

theorem covered_wideAt (k : Key) (f0 nl stride : Nat)
    (hb : ∀ l, l < nl → f0 + l * stride + len k ≤ 4 * d + 6 * JV) :
    Covered (wideAt k f0 nl stride) := by
  unfold wideAt
  exact covered_sumTo _ _ fun i hi => covered_sumTo _ _ fun l hl => covered_smulE _
    (covered_entry (show _ < readLen .wideAtKeys from idx_lt0 S2_pos0 hi (hb l hl)))

theorem covered_tableValuesAtCosts : Covered tableValuesAtCosts := by
  unfold tableValuesAtCosts
  refine covered_Eadd _ (covered_sumTo _ _ fun l hl => covered_sumTo _ _ fun i hi =>
    covered_smulN _ (covered_entry (show _ < readLen .wideAtCosts from idx_lt0 S2_pos0 hi ?_)))
  have : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  rcases this with rfl | rfl | rfl <;> omega

theorem covered_mid (k : Key) (v0 : Nat) (hv : v0 + len k ≤ JV) : Covered (mid k v0) := by
  unfold mid
  refine covered_Eadd _ (covered_wideAt k _ 2 JV fun l hl => ?_)
  have : l = 0 ∨ l = 1 := by omega
  rcases this with rfl | rfl <;> omega

theorem covered_low (k : Key) (hv : len k ≤ JV) : Covered (low k) := by
  unfold low
  refine covered_Eadd _ (covered_wideAt k _ 1 JV fun l hl => ?_)
  have : l = 0 := by omega
  subst this; omega

theorem covered_tableValue (k : Key) (v0 : Nat) (hv : v0 + len k ≤ JV) :
    Covered (tableValue k v0) := by
  unfold tableValue
  refine covered_Eadd _ (covered_wideAt k _ 3 JV fun l hl => ?_)
  have : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  rcases this with rfl | rfl | rfl <;> omega

theorem covered_clip : Covered clip := by
  unfold clip
  exact covered_subE (covered_add (covered_atCosts _) (covered_atCosts _)) _

theorem covered_table : Covered table := by
  unfold table
  exact covered_subE (covered_add (covered_atCosts _) covered_tableValuesAtCosts) _

theorem covered_mean : Covered mean := by
  unfold mean
  exact covered_subN (covered_add (covered_add (covered_summed _)
    (covered_smulN _ (covered_summed _))) (covered_summed _)) _

theorem covered_count : Covered count := by
  unfold count
  exact covered_sub (covered_add (covered_summed _) (covered_summed _)) (covered_natCast _)

theorem covered_top (hJ : len .marginTop ≤ JV) (hc : Covered logits.claimed.var) : Covered top := by
  unfold top
  exact covered_smulE _ (covered_sub (covered_sub (covered_subE (covered_add (covered_smulN _ hc)
    (covered_smulE _ (covered_add (covered_atCosts _) (covered_smulN _ (covered_atCosts _))))) _)
    (covered_smulN _ (covered_mid _ 0 (by omega)))) (covered_low _ hJ))

/-- **The five keys.** hJ: JVa ≤ JV (it holds as soon as V is not 0: Clamp.lean's JVa_le). -/
theorem covered_key (hJ : JVa ≤ JV) (hc : Covered logits.claimed.var) (k : Key) :
    Covered (key k) := by
  cases k with
  | marginTop => exact covered_top (Nat.le_refl _) hc
  | marginMid => exact covered_mid _ 0 (by simp only [len]; omega)
  | marginLow => exact covered_low _ (Nat.le_refl _)
  | tableA =>
    exact covered_add (covered_mid _ 0 (by simp only [len]; omega))
      (covered_smulN _ (covered_tableValue _ 0 (by simp only [len]; omega)))
  | tableB =>
    exact covered_add (covered_mid _ JVa (by simp only [len]; omega))
      (covered_smulN _ (covered_tableValue _ JVa (by simp only [len]; omega)))

/-- logitForms' second form. -/
theorem covered_actForm (he : Covered (logits.end_ 0).var) :
    Covered ((logits.end_ 0).var
      - sumTo d fun k => eq rs k • FinalNorm.actAt (entry .actAtLogits) k) := by
  refine covered_sub he (covered_sumTo _ _ fun k hk => covered_smulE _ ?_)
  unfold FinalNorm.actAt
  exact covered_add (covered_entry (show k < 2 * d by omega))
    (covered_smulN _ (covered_entry (show d + k < 2 * d by omega)))

/-! ## logitForms' first form: the sumcheck's own (rowForm) -/

theorem covered_onSlots : ∀ (u : List E) (first : Nat) (f : Form), Covered f →
    Covered (Part.MaskedSum.onSlots f first u) := by
  intro u
  induction u with
  | nil => intro first f hf; exact hf
  | cons x xs ih =>
    intro first f hf
    exact ih (first + 1) _ (covered_addMul hf (covered_slot _) _)

theorem covered_rowForm (h : Part.MaskedSum.Heard) (S0 : E) {kept : Form} (hs : Covered h.start)
    (hk : Covered kept) : Covered (Part.MaskedSum.rowForm h S0 kept) := by
  unfold Part.MaskedSum.rowForm
  exact covered_addMul (covered_addMul (covered_onSlots _ _ _ (covered_const _))
    (covered_sub (covered_const _) hs) _) hk _

theorem covered_left (S0 : E) (hs : ∀ h, logits.psc = some h → Covered h.start) :
    Covered (logits.left S0) := by
  unfold Sum.left
  cases hp : logits.psc with
  | none => exact covered_const _
  | some h => exact covered_rowForm h S0 (hs h hp) (covered_noEnts rfl)

/-- **Both of logitForms.** -/
theorem covered_logitForms (hs : ∀ h, logits.psc = some h → Covered h.start)
    (he : Covered (logits.end_ 0).var) : ∀ f, f ∈ logitForms → Covered f := by
  intro f hf
  unfold logitForms at hf
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl
  · exact covered_left _ hs
  · exact covered_actForm he

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.covered_key
#print axioms VerifiableInference.Desc.Kinds.Head.Law.covered_table
#print axioms VerifiableInference.Desc.Kinds.Head.Law.covered_logitForms
