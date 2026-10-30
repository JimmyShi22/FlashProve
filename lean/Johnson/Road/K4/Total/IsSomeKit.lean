-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/IsSomeKit.lean: WHETHER AN OPTION's do-BLOCK RETURNS, STEP BY STEP: a kit of
small lemmas for the walks of Johnson/Road/K4/Total/: each says of one way of composing Options when
the whole returns, or that two wholes return together if their steps do. No routine of K4's is
walked here.

  `bind_same`: one first step, two continuations that return together.
  `bind_both`: two first steps that return together, two continuations that return together at
    whatever they are handed.
  `all_same`: List.all at two tests that agree on the members.
  `mapM_all`, `mapM_same`: List.mapM returns just where every step does.
  `amapM_all`, `amapM_same`: the like for Array.mapM.
  `foldlM_all`, `foldlM_same`: List.foldlM whose step is (f x).map (k a x) returns just where every
    f x does, from whatever value it starts.
  `sumForms_all`, `sumForms_same`: so for sumForms (OnBytes/Model/LayerForms.lean).
  `need_isSome`: need b (OnBytes/Desc/First/K4/Claims.lean) returns just where b is true.
  `hiTab_same`: hiTab (OnBytes/Model/Tensors.lean) returns at two points of one length together.
Kin in the library: mapM_isSome (Johnson/Desc/K14/Law/DotLaw.lean; OnBytes/TypedOracleCompiler/Slice/
Batch3SRead.lean) has one direction of mapM_all, in files of other kinds.
Limits. Lemmas on Option, List and Array; nothing on K4, on a plan or on soundness.


-/
import OnBytes.Desc.First.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model

variable {α α' β β' σ σ' : Type}

theorem bind_same (x : Option α) {f : α → Option β} {g : α → Option β'}
    (h : ∀ a, (f a).isSome = (g a).isSome) : (x.bind f).isSome = (x.bind g).isSome := by
  cases x with
  | none => rfl
  | some a => exact h a

theorem bind_both {x : Option α} {y : Option α'} {f : α → Option β} {g : α' → Option β'}
    (hx : x.isSome = y.isSome) (h : ∀ a b, (f a).isSome = (g b).isSome) :
    (x.bind f).isSome = (y.bind g).isSome := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b => cases hx
  | some a =>
    cases y with
    | none => cases hx
    | some b => exact h a b

theorem all_same {p q : α → Bool} : ∀ (l : List α), (∀ a ∈ l, p a = q a) → l.all p = l.all q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      all_same l fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem mapM_all (f : α → Option β) : ∀ l : List α,
    (l.mapM f).isSome = l.all fun a => (f a).isSome
  | [] => rfl
  | a :: l => by
    have ih := mapM_all f l
    rw [List.mapM_cons, List.all_cons, ← ih]
    cases f a with
    | none => rfl
    | some b =>
      cases l.mapM f with
      | none => rfl
      | some bs => rfl

theorem mapM_same {f : α → Option β} {g : α → Option β'} (l : List α)
    (h : ∀ a ∈ l, (f a).isSome = (g a).isSome) : (l.mapM f).isSome = (l.mapM g).isSome := by
  rw [mapM_all, mapM_all]
  exact all_same l h

theorem amapM_all (f : α → Option β) (xs : Array α) :
    (xs.mapM f).isSome = xs.toList.all fun a => (f a).isSome := by
  rw [Array.mapM_eq_mapM_toList, ← mapM_all]
  cases xs.toList.mapM f with
  | none => rfl
  | some bs => rfl

theorem amapM_same {f : α → Option β} {g : α → Option β'} (xs : Array α)
    (h : ∀ a ∈ xs.toList, (f a).isSome = (g a).isSome) :
    (xs.mapM f).isSome = (xs.mapM g).isSome := by
  rw [amapM_all, amapM_all]
  exact all_same _ h

theorem foldlM_all (f : α → Option β) (k : σ → α → β → σ) : ∀ (l : List α) (a : σ),
    (l.foldlM (fun a x => (f x).map (k a x)) a).isSome = l.all fun x => (f x).isSome
  | [], _ => rfl
  | x :: l, a => by
    rw [List.foldlM_cons, List.all_cons]
    cases f x with
    | none => rfl
    | some b => exact foldlM_all f k l (k a x b)

theorem foldlM_same {f : α → Option β} {g : α → Option β'} (k : σ → α → β → σ)
    (k' : σ' → α → β' → σ') (l : List α) (h : ∀ x ∈ l, (f x).isSome = (g x).isSome) (a : σ)
    (b : σ') :
    (l.foldlM (fun a x => (f x).map (k a x)) a).isSome =
      (l.foldlM (fun a x => (g x).map (k' a x)) b).isSome := by
  rw [foldlM_all, foldlM_all]
  exact all_same l h

theorem sumForms_all (n : Nat) (f : Nat → Option (Aff × E)) :
    (Layer.sumForms n f).isSome = (List.range n).all fun x => (f x).isSome := by
  unfold Layer.sumForms
  exact foldlM_all f (fun (a : Aff) (_ : Nat) (t : Aff × E) => a.addMul t.1 t.2) (List.range n)
    Layer.aff0

theorem sumForms_same (n : Nat) {f g : Nat → Option (Aff × E)}
    (h : ∀ x, x < n → (f x).isSome = (g x).isSome) :
    (Layer.sumForms n f).isSome = (Layer.sumForms n g).isSome := by
  rw [sumForms_all, sumForms_all]
  exact all_same _ fun x hx => h x (List.mem_range.mp hx)

theorem need_isSome (b : Bool) : (need b).isSome = b := by
  cases b <;> rfl

theorem hiTab_same {z z' : Array E} (h : z.size = z'.size) (la want : Nat) :
    (hiTab z la want).toOption.isSome = (hiTab z' la want).toOption.isSome := by
  unfold hiTab cutLast
  by_cases hk : la > z.size
  · have hk' : la > z'.size := h ▸ hk
    rw [if_pos hk, if_pos hk']
  · have hk' : ¬ la > z'.size := h ▸ hk
    rw [if_neg hk, if_neg hk']
    show (if ((z.extract 0 (z.size - la)).size != want) = true then
        (Except.error "plan-tensor-layout" : Except String (Array E))
      else .ok (eqTab (z.extract 0 (z.size - la)))).toOption.isSome =
      (if ((z'.extract 0 (z'.size - la)).size != want) = true then
        (Except.error "plan-tensor-layout" : Except String (Array E))
      else .ok (eqTab (z'.extract 0 (z'.size - la)))).toOption.isSome
    rw [Array.size_extract, Array.size_extract, h]
    split <;> rfl

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.bind_same
#print axioms OnBytes.Desc.First.K4.Total.bind_both
#print axioms OnBytes.Desc.First.K4.Total.all_same
#print axioms OnBytes.Desc.First.K4.Total.mapM_all
#print axioms OnBytes.Desc.First.K4.Total.mapM_same
#print axioms OnBytes.Desc.First.K4.Total.amapM_all
#print axioms OnBytes.Desc.First.K4.Total.amapM_same
#print axioms OnBytes.Desc.First.K4.Total.foldlM_all
#print axioms OnBytes.Desc.First.K4.Total.foldlM_same
#print axioms OnBytes.Desc.First.K4.Total.sumForms_all
#print axioms OnBytes.Desc.First.K4.Total.sumForms_same
#print axioms OnBytes.Desc.First.K4.Total.need_isSome
#print axioms OnBytes.Desc.First.K4.Total.hiTab_same
