-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoGood.lean.
Forms whose entries all lie in one array.

`InU t0 a`: every entry of a virtual row that the form a names lies in array number t0. It holds of
constants, of slots, of an entry of array t0, and passes through the forms' operations (addMul,
scale, sum, difference).
`HasGood α`: for a type α of values, what it is for a value to hold only such forms: `good t0 x`.
For a form it is InU; for a pair, an array, a list, an optional value, a step of a loop: that its
parts are good; for a type of which nothing else is said: nothing (the instance of low priority).
`Good t0 x`: the value x is good: a class, so that instance search carries it through the forms'
operations, pairs, arrays and lists. `Unasked α`: every value of the type is good.
`GoodCl t0 cl`: the claim's form is InU t0, and each of its runs lies in array t0.
InU, HasGood, Good and Unasked are after the words of the same names in a file EndGood.lean
; InU has that file's text.
Limit: for a type without an instance of HasGood of its own, a record that holds forms among them,
`good` says nothing. GoodCl is a plain definition and is never empty in that way.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixed

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model

/-- Every entry that the form names lies in array number t0. -/
def InU (t0 : ℕ) (a : Aff) : Prop := ∀ e ∈ a.ents.toList, e.tree = t0

theorem InU.ofConst (t0 : ℕ) (v : E) : InU t0 (Aff.ofConst v) := by
  intro e he
  simp [Aff.ofConst] at he

theorem InU.slot (t0 j : ℕ) : InU t0 (Aff.slot j) := by
  intro e he
  simp [Aff.slot] at he

theorem InU.empty (t0 : ℕ) : InU t0 ({} : Aff) := by
  intro e he
  simp at he

theorem InU.ent (t0 r i : ℕ) : InU t0 (Aff.ent t0 r i) := by
  intro e he
  simp [Aff.ent] at he
  rw [he]

private theorem foldl_push (t0 : ℕ) (k : E) : ∀ (l : List Ent) (acc : Array Ent),
    (∀ e ∈ acc.toList, e.tree = t0) → (∀ e ∈ l, e.tree = t0) →
    ∀ e ∈ (l.foldl (fun l x => l.push { x with coef := mulE x.coef k }) acc).toList, e.tree = t0
  | [], _, ha, _ => ha
  | x :: l, acc, ha, hl => by
    rw [List.foldl_cons]
    refine foldl_push t0 k l _ (fun e he => ?_) fun e he => hl e (List.mem_cons_of_mem _ he)
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ha e he
    · exact hl x List.mem_cons_self

theorem InU.addMul {t0 : ℕ} {a b : Aff} (ha : InU t0 a) (hb : InU t0 b) (k : E) :
    InU t0 (Aff.addMul a b k) := by
  unfold InU Aff.addMul
  simp only
  rw [← Array.foldl_toList]
  exact foldl_push t0 k _ _ ha hb

theorem InU.scale {t0 : ℕ} {a : Aff} (ha : InU t0 a) (k : E) : InU t0 (Aff.scale a k) :=
  InU.addMul (InU.empty t0) ha k

theorem InU.add {t0 : ℕ} {a b : Aff} (ha : InU t0 a) (hb : InU t0 b) : InU t0 (a + b) :=
  InU.addMul ha hb _

theorem InU.sub {t0 : ℕ} {a b : Aff} (ha : InU t0 a) (hb : InU t0 b) : InU t0 (a - b) :=
  InU.addMul ha hb _

theorem InU.u3Form (t0 K x : ℕ) : InU t0 (u3Form t0 K x) := InU.ent t0 _ _

/-- What it is for a value to hold only forms whose entries lie in array t0. -/
class HasGood (α : Type) where
  good : ℕ → α → Prop

export HasGood (good)

instance (priority := low) goodAny (α : Type) : HasGood α := ⟨fun _ _ => True⟩
instance goodAff : HasGood Aff := ⟨InU⟩
instance goodProd (α β : Type) [HasGood α] [HasGood β] : HasGood (α × β) :=
  ⟨fun t p => good t p.1 ∧ good t p.2⟩
instance goodMProd (α β : Type) [HasGood α] [HasGood β] : HasGood (MProd α β) :=
  ⟨fun t p => good t p.1 ∧ good t p.2⟩
instance goodList (α : Type) [HasGood α] : HasGood (List α) := ⟨fun t l => ∀ x ∈ l, good t x⟩
instance goodArray (α : Type) [HasGood α] : HasGood (Array α) :=
  ⟨fun t l => ∀ x ∈ l.toList, good t x⟩
instance goodOption (α : Type) [HasGood α] : HasGood (Option α) :=
  ⟨fun t o => ∀ x, o = some x → good t x⟩
instance goodStep (α : Type) [HasGood α] : HasGood (ForInStep α) :=
  ⟨fun t s => match s with
    | .done a => good t a
    | .yield a => good t a⟩

/-- The claim's form and runs lie in array t0. -/
def GoodCl (t0 : ℕ) (cl : Cl) : Prop := InU t0 cl.1 ∧ ∀ r ∈ cl.2.toList, r.tree = t0

/-- The value is good. A class, so that instance search carries it through the forms' operations. -/
class Good (t0 : ℕ) {α : Type} [HasGood α] (a : α) : Prop where
  out : good t0 a

/-- Every value of the type is good. -/
class Unasked (α : Type) [HasGood α] : Prop where
  all : ∀ (t : ℕ) (a : α), good t a

instance (priority := low) unaskedAny (α : Type) : @Unasked α (goodAny α) := ⟨fun _ _ => trivial⟩
instance {α : Type} [HasGood α] [Unasked α] : Unasked (Array α) := ⟨fun t _ x _ => Unasked.all t x⟩
instance {α : Type} [HasGood α] [Unasked α] : Unasked (List α) := ⟨fun t _ x _ => Unasked.all t x⟩
instance {α : Type} [HasGood α] [Unasked α] : Unasked (Option α) :=
  ⟨fun t _ x _ => Unasked.all t x⟩
instance {α β : Type} [HasGood α] [HasGood β] [Unasked α] [Unasked β] : Unasked (α × β) :=
  ⟨fun t a => ⟨Unasked.all t a.1, Unasked.all t a.2⟩⟩
instance {α β : Type} [HasGood α] [HasGood β] [Unasked α] [Unasked β] : Unasked (MProd α β) :=
  ⟨fun t a => ⟨Unasked.all t a.1, Unasked.all t a.2⟩⟩

section
variable {t0 : ℕ}

instance good_unasked {α : Type} [HasGood α] [Unasked α] (a : α) : Good t0 a :=
  ⟨Unasked.all t0 a⟩

/-! ### the forms' operations -/

instance good_ofConst (v : E) : Good t0 (Aff.ofConst v) := ⟨InU.ofConst t0 v⟩
instance good_slot (j : ℕ) : Good t0 (Aff.slot j) := ⟨InU.slot t0 j⟩
instance good_empty : Good t0 ({} : Aff) := ⟨InU.empty t0⟩
instance good_ent (r i : ℕ) : Good t0 (Aff.ent t0 r i) := ⟨InU.ent t0 r i⟩
instance good_u3Form (K x : ℕ) : Good t0 (u3Form t0 K x) := ⟨InU.u3Form t0 K x⟩
instance good_addMul (a b : Aff) (k : E) [ha : Good t0 a] [hb : Good t0 b] :
    Good t0 (Aff.addMul a b k) := ⟨InU.addMul ha.out hb.out k⟩
instance good_scale (a : Aff) (k : E) [ha : Good t0 a] : Good t0 (Aff.scale a k) :=
  ⟨InU.scale ha.out k⟩
instance good_add (a b : Aff) [ha : Good t0 a] [hb : Good t0 b] : Good t0 (a + b) :=
  ⟨InU.add ha.out hb.out⟩
instance good_sub (a b : Aff) [ha : Good t0 a] [hb : Good t0 b] : Good t0 (a - b) :=
  ⟨InU.sub ha.out hb.out⟩

/-! ### pairs, states of loops, arrays, lists -/

variable {α β : Type} [HasGood α] [HasGood β]

instance good_pair (a : α) (b : β) [ha : Good t0 a] [hb : Good t0 b] : Good t0 (a, b) :=
  ⟨⟨ha.out, hb.out⟩⟩
instance good_fst (a : α × β) [h : Good t0 a] : Good t0 a.1 := ⟨h.out.1⟩
instance good_snd (a : α × β) [h : Good t0 a] : Good t0 a.2 := ⟨h.out.2⟩
instance good_mk (a : α) (b : β) [ha : Good t0 a] [hb : Good t0 b] : Good t0 (MProd.mk a b) :=
  ⟨⟨ha.out, hb.out⟩⟩
instance good_mfst (a : MProd α β) [h : Good t0 a] : Good t0 a.fst := ⟨h.out.1⟩
instance good_msnd (a : MProd α β) [h : Good t0 a] : Good t0 a.snd := ⟨h.out.2⟩
instance good_yield (b : β) [h : Good t0 b] : Good t0 (ForInStep.yield b) := ⟨h.out⟩
instance good_done (b : β) [h : Good t0 b] : Good t0 (ForInStep.done b) := ⟨h.out⟩
instance good_emptyArr : Good t0 (#[] : Array α) := ⟨fun _ h => by simp at h⟩
instance good_nil : Good t0 ([] : List α) := ⟨fun _ h => absurd h List.not_mem_nil⟩

instance good_cons (x : α) (l : List α) [hx : Good t0 x] [hl : Good t0 l] : Good t0 (x :: l) :=
  ⟨fun y hy => by
    rcases List.mem_cons.1 hy with h | h
    · rw [h]
      exact hx.out
    · exact hl.out y h⟩

instance good_push (a : Array α) (x : α) [ha : Good t0 a] [hx : Good t0 x] :
    Good t0 (a.push x) :=
  ⟨fun y hy => by
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact ha.out y hy
    · exact hx.out⟩

instance good_getD (a : Array α) (i : ℕ) (d : α) [ha : Good t0 a] [hd : Good t0 d] :
    Good t0 (a.getD i d) :=
  ⟨by
    unfold Array.getD
    split
    · exact ha.out _ (by simp)
    · exact hd.out⟩

instance good_getElem? (a : Array α) (i : ℕ) [ha : Good t0 a] : Good t0 a[i]? :=
  ⟨fun x hx => ha.out x (Array.mem_toList_iff.2 (Array.mem_of_getElem? hx))⟩

instance good_toList (a : Array α) [h : Good t0 a] : Good t0 a.toList := ⟨h.out⟩
instance good_toArray (l : List α) [h : Good t0 l] : Good t0 l.toArray := ⟨h.out⟩

instance good_zipIdx (l : List α) (n : ℕ) [h : Good t0 l] : Good t0 (l.zipIdx n) :=
  ⟨fun _ hx => ⟨h.out _ (List.fst_mem_of_mem_zipIdx hx), trivial⟩⟩

instance good_set (a : Array α) (i : ℕ) (x : α) [ha : Good t0 a] [hx : Good t0 x] :
    Good t0 (a.setIfInBounds i x) :=
  ⟨fun y hy => by
    rcases Array.mem_or_eq_of_mem_setIfInBounds (Array.mem_toList_iff.1 hy) with h | rfl
    · exact ha.out y (Array.mem_toList_iff.2 h)
    · exact hx.out⟩

instance good_replicate (n : ℕ) (x : α) [h : Good t0 x] : Good t0 (Array.replicate n x) :=
  ⟨fun y hy => by
    have h2 : y ∈ List.replicate n x := by simpa using hy
    rw [List.eq_of_mem_replicate h2]
    exact h.out⟩

instance good_ite (p : Prop) [Decidable p] (a b : α) [ha : Good t0 a] [hb : Good t0 b] :
    Good t0 (if p then a else b) := by
  split
  · exact ha
  · exact hb

/-- A fold of good values, outside any routine. -/
theorem good_foldl (f : β → α → β) (hf : ∀ b a, Good t0 b → Good t0 a → Good t0 (f b a)) :
    ∀ (l : List α) (b : β), Good t0 l → Good t0 b → Good t0 (l.foldl f b)
  | [], _, _, hb => hb
  | a :: l, b, hl, hb => by
    rw [List.foldl_cons]
    exact good_foldl f hf l _ ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩
      (hf b a hb ⟨hl.out a List.mem_cons_self⟩)

theorem good_foldlArr (f : β → α → β) (hf : ∀ b a, Good t0 b → Good t0 a → Good t0 (f b a))
    (as : Array α) (b : β) (ha : Good t0 as) (hb : Good t0 b) : Good t0 (as.foldl f b) := by
  rw [← Array.foldl_toList]
  exact good_foldl f hf as.toList b ⟨ha.out⟩ hb

end
end Fo
