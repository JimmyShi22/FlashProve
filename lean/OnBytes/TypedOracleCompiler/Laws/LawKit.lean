-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawKit.lean: a kit for laws that compare two runs of blocks.

A block is a routine of the verifier program (`Blk`, OnBytes/Iop/Ground.lean). A law of the kind
meant here says: this block does not hang on that part of the context, or on that argument. It is
said with a relation between two contexts that a pair of blocks carries on.

Why. A typed description of a file wants constant descriptions of its chains and a decision on views
alone. The program makes its descriptions by dry runs, and decides from contexts that hold roots,
run values and sealed digests. Two laws are wanted for that (OnBytes/TypedOracleCompiler/Laws/LawAlike.lean says
them).

Main names.
  `Out R Q`      two outcomes go together: both fail, with one and the same failure; or both
                 succeed, with values in the relation Q and contexts in the relation R
  `Carries R Q b b'`   from contexts in R, the outcomes of b and of b' go together
  `Same R b`     the class for the common case: `Carries R Eq b b` (one text, equal values)
  `Carries.pure`, `bind`, `bind_same`, `mono`, `ite`, `forIn_list`, `forIn_array`: rules for two
  texts
  `same_pure`, `Same.bind`, `same_map`, `same_ite`, `same_dite`, loops: rules for one text
  `same`         the tactic for one text: instances, else a binder, a bind, a match or an if, a let
  `StepAlike Q`  Q on what a loop's body returns

Not claimed. Nothing on any relation in particular, nor on any call of OnBytes/Iop/Ground.lean.
Nothing on what a block tests. A pair of blocks that both fail from every context carries every
relation.

-/
import OnBytes.Iop.GroundLaws

namespace OnBytes.TwoLaws

open OnBytes

/-- Two outcomes go together: one failure on both sides, or values in Q and contexts in R. -/
def Out {α : Type} (R : Ctx → Ctx → Prop) (Q : α → α → Prop) :
    Except Failure (α × Ctx) → Except Failure (α × Ctx) → Prop
  | .ok p, .ok q => Q p.1 q.1 ∧ R p.2 q.2
  | .error e, .error f => e = f
  | _, _ => False

theorem Out.ok {α : Type} {R : Ctx → Ctx → Prop} {Q : α → α → Prop} {x y : α} {c d : Ctx}
    (hq : Q x y) (hr : R c d) : Out R Q (.ok (x, c)) (.ok (y, d)) := ⟨hq, hr⟩

theorem Out.err {α : Type} {R : Ctx → Ctx → Prop} {Q : α → α → Prop} (e : Failure) :
    Out R Q (.error e : Except Failure (α × Ctx)) (.error e) := rfl

/-- From contexts in R the two blocks fail alike, or succeed with values in Q and leave contexts
in R. -/
def Carries {α : Type} (R : Ctx → Ctx → Prop) (Q : α → α → Prop) (b b' : Blk α) : Prop :=
  ∀ c c', R c c' → Out R Q (b c) (b' c')

/-- One text, equal values. -/
class Same {α : Type} (R : Ctx → Ctx → Prop) (b : Blk α) : Prop where
  out : Carries R Eq b b

/-! ## Rules for two texts -/

theorem Carries.of_same {α : Type} {R : Ctx → Ctx → Prop} {b : Blk α} (h : Same R b) :
    Carries R Eq b b := h.out

theorem Carries.mono {α : Type} {R : Ctx → Ctx → Prop} {P Q : α → α → Prop} {b b' : Blk α}
    (h : Carries R P b b') (hpq : ∀ x y, P x y → Q x y) : Carries R Q b b' := by
  intro c c' hc
  have h1 := h c c' hc
  cases e : b c with
  | error x =>
    cases e' : b' c' with
    | error y => rw [e, e'] at h1; exact h1
    | ok q => rw [e, e'] at h1; exact h1.elim
  | ok p =>
    cases e' : b' c' with
    | error y => rw [e, e'] at h1; exact h1.elim
    | ok q => rw [e, e'] at h1; exact ⟨hpq _ _ h1.1, h1.2⟩

theorem Carries.pure {α : Type} {R : Ctx → Ctx → Prop} {Q : α → α → Prop} {a a' : α}
    (h : Q a a') : Carries R Q (pure a : Blk α) (pure a') :=
  fun _ _ hc => Out.ok h hc

theorem Carries.bind {α β : Type} {R : Ctx → Ctx → Prop} {P : α → α → Prop} {Q : β → β → Prop}
    {b b' : Blk α} {f f' : α → Blk β} (hb : Carries R P b b')
    (hf : ∀ x x', P x x' → Carries R Q (f x) (f' x')) : Carries R Q (b >>= f) (b' >>= f') := by
  intro c c' hc
  have h1 := hb c c' hc
  show Out R Q (b c >>= fun p => f p.1 p.2) (b' c' >>= fun p => f' p.1 p.2)
  cases e : b c with
  | error x =>
    cases e' : b' c' with
    | error y => rw [e, e'] at h1; exact h1
    | ok q => rw [e, e'] at h1; exact h1.elim
  | ok p =>
    cases e' : b' c' with
    | error y => rw [e, e'] at h1; exact h1.elim
    | ok q => rw [e, e'] at h1; exact hf _ _ h1.1 _ _ h1.2

/-- A bind whose first call is one text on both sides, with equal values. -/
theorem Carries.bind_same {α β : Type} {R : Ctx → Ctx → Prop} {Q : β → β → Prop}
    {b : Blk α} {f f' : α → Blk β} [hb : Same R b]
    (hf : ∀ x, Carries R Q (f x) (f' x)) : Carries R Q (b >>= f) (b >>= f') :=
  Carries.bind hb.out fun x _ e => e ▸ hf x

theorem Carries.ite {α : Type} {R : Ctx → Ctx → Prop} {Q : α → α → Prop} {p p' : Prop}
    [Decidable p] [Decidable p'] {a b a' b' : Blk α} (hp : p ↔ p') (ha : Carries R Q a a')
    (hb : Carries R Q b b') : Carries R Q (if p then a else b) (if p' then a' else b') := by
  by_cases h : p
  · rw [if_pos h, if_pos (hp.1 h)]; exact ha
  · rw [if_neg h, if_neg (fun h' => h (hp.2 h'))]; exact hb

/-- Q on what a loop's body returns. -/
inductive StepAlike {β : Type} (Q : β → β → Prop) : ForInStep β → ForInStep β → Prop
  | done {a b : β} : Q a b → StepAlike Q (.done a) (.done b)
  | yield {a b : β} : Q a b → StepAlike Q (.yield a) (.yield b)

theorem Carries.forIn_list {α β : Type} {R : Ctx → Ctx → Prop} {Q : β → β → Prop} (l : List α)
    {i i' : β} {f f' : α → β → Blk (ForInStep β)} (hi : Q i i')
    (hf : ∀ a x x', Q x x' → Carries R (StepAlike Q) (f a x) (f' a x')) :
    Carries R Q (forIn l i f) (forIn l i' f') := by
  induction l generalizing i i' with
  | nil => rw [List.forIn_nil, List.forIn_nil]; exact Carries.pure hi
  | cons a l ih =>
    rw [List.forIn_cons, List.forIn_cons]
    refine Carries.bind (hf a i i' hi) fun r r' hr => ?_
    cases hr with
    | done h => exact Carries.pure h
    | yield h => exact ih h

theorem Carries.forIn_array {α β : Type} {R : Ctx → Ctx → Prop} {Q : β → β → Prop} (l : Array α)
    {i i' : β} {f f' : α → β → Blk (ForInStep β)} (hi : Q i i')
    (hf : ∀ a x x', Q x x' → Carries R (StepAlike Q) (f a x) (f' a x')) :
    Carries R Q (forIn l i f) (forIn l i' f') := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]; exact Carries.forIn_list _ hi hf

/-! ## Rules for one text -/

section one
variable {R : Ctx → Ctx → Prop}

instance same_pure {α : Type} (a : α) : Same R (pure a : Blk α) := ⟨Carries.pure rfl⟩

theorem Same.bind {α β : Type} {b : Blk α} {f : α → Blk β} (hb : Same R b)
    (hf : ∀ x, Same R (f x)) : Same R (b >>= f) :=
  ⟨Carries.bind hb.out fun x _ e => e ▸ (hf x).out⟩

instance same_bind {α β : Type} (b : Blk α) (f : α → Blk β) [hb : Same R b]
    [hf : ∀ x, Same R (f x)] : Same R (b >>= f) := Same.bind hb hf

instance same_map {α β : Type} (g : α → β) (b : Blk α) [hb : Same R b] : Same R (g <$> b) := by
  have e : g <$> b = b >>= fun x => pure (g x) := (bind_pure_comp g b).symm
  rw [e]; infer_instance

instance same_ite {α : Type} (p : Prop) [Decidable p] (a b : Blk α) [ha : Same R a]
    [hb : Same R b] : Same R (if p then a else b) := by
  split <;> assumption

instance same_dite {α : Type} (p : Prop) [Decidable p] (a : p → Blk α) (b : ¬p → Blk α)
    [ha : ∀ h, Same R (a h)] [hb : ∀ h, Same R (b h)] : Same R (dite p a b) := by
  split
  · exact ha _
  · exact hb _

instance same_forIn_list {α β : Type} (l : List α) (init : β)
    (f : α → β → Blk (ForInStep β)) [hf : ∀ a b, Same R (f a b)] : Same R (forIn l init f) := by
  induction l generalizing init with
  | nil => rw [List.forIn_nil]; infer_instance
  | cons a l ih =>
    rw [List.forIn_cons]
    refine Same.bind (hf a init) fun r => ?_
    cases r with
    | done b => exact same_pure b
    | yield b => exact ih b

instance same_forIn_array {α β : Type} (l : Array α) (init : β)
    (f : α → β → Blk (ForInStep β)) [hf : ∀ a b, Same R (f a b)] : Same R (forIn l init f) := by
  rw [← Array.forIn_toList]; infer_instance

instance same_foldlM_list {α β : Type} (l : List α) (init : β) (f : β → α → Blk β)
    [hf : ∀ b a, Same R (f b a)] : Same R (l.foldlM f init) := by
  induction l generalizing init with
  | nil => rw [List.foldlM_nil]; infer_instance
  | cons a l ih =>
    rw [List.foldlM_cons]
    exact Same.bind (hf init a) fun r => ih r

instance same_foldlM_array {α β : Type} (l : Array α) (init : β) (f : β → α → Blk β)
    [hf : ∀ b a, Same R (f b a)] : Same R (l.foldlM f init) := by
  rw [← Array.foldlM_toList]; infer_instance

instance same_forM_list {α : Type} (l : List α) (f : α → Blk PUnit) [hf : ∀ a, Same R (f a)] :
    Same R (l.forM f) := by
  induction l with
  | nil => exact same_pure _
  | cons a l ih => exact Same.bind (hf a) fun _ => ih

instance same_forM_array {α : Type} (l : Array α) (f : α → Blk PUnit) [hf : ∀ a, Same R (f a)] :
    Same R (l.forM f) := by
  unfold Array.forM; infer_instance

/-- A name for a block's failures changes nothing in what is carried. -/
theorem Carries.named {α : Type} {Q : α → α → Prop} {b b' : Blk α} (n : String)
    (h : Carries R Q b b') : Carries R Q (Blk.named n b) (Blk.named n b') := by
  intro c c' hc
  have h1 := h c c' hc
  unfold Blk.named
  cases e : b c with
  | error x =>
    cases e' : b' c' with
    | error y => rw [e, e'] at h1; cases h1; exact Out.err _
    | ok q => rw [e, e'] at h1; exact h1.elim
  | ok p =>
    cases e' : b' c' with
    | error y => rw [e, e'] at h1; exact h1.elim
    | ok q => rw [e, e'] at h1; exact h1

/-- A place for a block's failures changes nothing in what is carried. -/
theorem Carries.inPlace {α : Type} {Q : α → α → Prop} {b b' : Blk α} (n : String)
    (h : Carries R Q b b') : Carries R Q (Blk.inPlace n b) (Blk.inPlace n b') := by
  intro c c' hc
  have h1 := h c c' hc
  unfold Blk.inPlace
  cases e : b c with
  | error x =>
    cases e' : b' c' with
    | error y => rw [e, e'] at h1; cases h1; exact Out.err _
    | ok q => rw [e, e'] at h1; exact h1.elim
  | ok p =>
    cases e' : b' c' with
    | error y => rw [e, e'] at h1; exact h1.elim
    | ok q => rw [e, e'] at h1; exact h1

instance same_named {α : Type} (n : String) (b : Blk α) [hb : Same R b] :
    Same R (Blk.named n b) := ⟨Carries.named n hb.out⟩

instance same_inPlace {α : Type} (n : String) (b : Blk α) [hb : Same R b] :
    Same R (Blk.inPlace n b) := ⟨Carries.inPlace n hb.out⟩

end one

/-! ## The tactic for one text -/

/-- Instances where they reach; else one step: a binder, a bind, a let, a match or an if. -/
macro "same" : tactic =>
  `(tactic| repeat' first
      | infer_instance
      | intro _
      | with_reducible apply Same.bind
      | split
      | dsimp only)

end OnBytes.TwoLaws
