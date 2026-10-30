-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PublicPart.lean.
WHAT IT DOES NOT SHOW. What a public part is worth. Nothing on soundness, probabilities or hiding.
WHAT IT IS. A FORM ALL OF WHOSE SLOTS ARE FILLED HAS A PUBLIC PART: the ledger's publicPart returns.
  SlotsFilled F f    every slot that the form f names is one of the ledger's numbers and is marked.
  publicPart_returns
  slotsFilled_...    the notion goes through HeadParts.lean's ways of making forms: a constant, a
                     slot, a + k b, the sum, the difference, k f, the sum over i < n.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE subE)
open OnBytes.Model (Aff Fork)
open Part.MaskedSum (shown_returns)

/-- Every slot that the form names is one of the ledger's numbers and is marked. -/
def SlotsFilled (F : Fork) (f : Form) : Prop :=
  ∀ x ∈ f.slots.toList, x.1 < F.ns ∧ F.gotF.getD x.1 false = true

theorem publicPart_returns (F : Fork) (f : Form) (h : SlotsFilled F f) :
    ∃ T, F.publicPart f = some T := by
  have gen : ∀ (l : List (Nat × E)) (v : E),
      (∀ x ∈ l, x.1 < F.ns ∧ F.gotF.getD x.1 false = true) →
      ∃ T, l.foldlM (fun (v : E) (x : Nat × E) =>
        (F.shown x.1).map fun y => addE v (mulE x.2 y)) v = some T := by
    intro l
    induction l with
    | nil => exact fun v _ => ⟨v, rfl⟩
    | cons x l ih =>
      intro v hl
      obtain ⟨h1, h2⟩ := hl x (by simp)
      rw [List.foldlM_cons, shown_returns h1 h2]
      exact ih _ fun y hy => hl y (by simp [hy])
  unfold Fork.publicPart
  rw [← Array.foldlM_toList]
  exact gen _ _ h

theorem slotsFilled_const (F : Fork) (x : E) : SlotsFilled F (Aff.ofConst x) := by
  intro y hy
  simp [Aff.ofConst] at hy

theorem slotsFilled_empty (F : Fork) : SlotsFilled F ({} : Aff) := by
  intro y hy
  simp at hy

theorem slotsFilled_slot {F : Fork} {j : Nat} (h1 : j < F.ns) (h2 : F.gotF.getD j false = true) :
    SlotsFilled F (Aff.slot j) := by
  intro y hy
  have e : y = (j, oneE) := by simpa [Aff.slot] using hy
  rw [e]
  exact ⟨h1, h2⟩

theorem slotsFilled_addMul {F : Fork} {a b : Form} (k : E) (ha : SlotsFilled F a)
    (hb : SlotsFilled F b) : SlotsFilled F (Aff.addMul a b k) := by
  intro y hy
  have e : (Aff.addMul a b k).slots.toList =
      a.slots.toList ++ b.slots.toList.map fun x => (x.1, mulE x.2 k) :=
    OnBytes.Model.foldl_push_toList _ _ _
  rw [e] at hy
  rcases List.mem_append.mp hy with h | h
  · exact ha y h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    exact hb x hx

theorem slotsFilled_add {F : Fork} {a b : Form} (ha : SlotsFilled F a) (hb : SlotsFilled F b) :
    SlotsFilled F (a + b) := slotsFilled_addMul oneE ha hb

theorem slotsFilled_sub {F : Fork} {a b : Form} (ha : SlotsFilled F a) (hb : SlotsFilled F b) :
    SlotsFilled F (a - b) := slotsFilled_addMul (subE zeroE oneE) ha hb

theorem slotsFilled_smul {F : Fork} {a : Form} (k : E) (ha : SlotsFilled F a) :
    SlotsFilled F (k • a) := slotsFilled_addMul k (slotsFilled_empty F) ha

theorem slotsFilled_sumTo {F : Fork} (n : Nat) (f : Nat → Form)
    (h : ∀ i, i < n → SlotsFilled F (f i)) : SlotsFilled F (sumTo n f) := by
  unfold sumTo
  induction n with
  | zero => exact slotsFilled_const F _
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    exact slotsFilled_add (ih fun i hi => h i (by omega)) (h n (by omega))

end VerifiableInference.Desc.Kinds.Head.Law
