-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeCoef.lean: the step of the smallness test that sets the weights of every
virtual row on the rows of its array (`HTailF2.coefficientsF`, OnBytes/Model/Tail.lean), at two
states of a sub-proof's check that are alike and at two lists of tables. Statements and proofs.



Two states are alike (`ForkAlike`, OnBytes/Flat/LinksFreeFork.lean) if they agree in all but the
weights L on the columns, of which there are as many, and the constant of the one equation. By the
program's text the step reads of the state the batching element and, of an array, its kind and its
number of rows; it changes rows by `HTailF2.onRow`, and each change sets the weights on the rows and
their product form and leaves L as it is. The list of tables is not read.

Main theorems:
  `map_modify_comm`   a change at one place of an array, under a map that the change commutes with.
  `onRow_alike`       `onRow` keeps states alike, for a change f of a row with
                      eraseRow (f x) = f (eraseRow x).
  `tree_read`         what of an array does not look at L is the same in both states.
  `modify_rel`        `modify` at a step that keeps states alike.
  `id_bind`, `id_forIn`, `id_forIn_array`   two computations without effects, put together alike:
                      one after another; loops over one list or array whose bodies always go on.
  `coefficientsF_rel` the step at tl and at { tl with funs := f' }: from two states that are alike
                      both fail, or both return, with one context left and states alike.
Limits: nothing on what the weights are. Nothing on a run on a view. For proofs only; no module of
the program imports this file.
-/
import OnBytes.Flat.LinksFreeFork

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-! ## Arrays -/

/-- A change at one place, under a map with which the change commutes. -/
theorem map_modify_comm {α : Type} (e g : α → α) (h : ∀ x, e (g x) = g (e x)) (a : Array α)
    (i : Nat) : (a.modify i g).map e = (a.map e).modify i g := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_map, Array.getElem_modify]
    split
    · exact h _
    · rfl

/-! ## One row changed -/

/-- **`HTailF2.onRow` at two states that are alike**, for a change of the row that does not look at
the weights L and leaves them. -/
theorem onRow_alike {F F' : Fork} (h : ForkAlike F F') (t r : Nat) (f : HRow → HRow)
    (hf : ∀ x, eraseRow (f x) = f (eraseRow x)) :
    ForkAlike (HTailF2.onRow F t r f) (HTailF2.onRow F' t r f) := by
  obtain ⟨e, hT⟩ := h
  generalize F'.trees = T' at e hT
  generalize F'.c0 = c' at e
  subst e
  refine ⟨rfl, ?_⟩
  have k : ∀ X : HTree, eraseTree { X with rows := X.rows.modify r f } =
      { eraseTree X with rows := (eraseTree X).rows.modify r f } := by
    intro X
    unfold eraseTree
    dsimp only
    rw [map_modify_comm eraseRow f hf]
  unfold HTailF2.onRow
  dsimp only
  rw [map_modify_comm eraseTree (fun X => { X with rows := X.rows.modify r f }) k,
    map_modify_comm eraseTree (fun X => { X with rows := X.rows.modify r f }) k, hT]

/-- What of an array does not look at the weights is the same in two states that are alike. -/
theorem tree_read {F F' : Fork} (h : ForkAlike F F') {β : Type} (φ : HTree → β)
    (hφ : ∀ X, φ (eraseTree X) = φ X) (t : Nat) :
    φ (F.trees.getD t {}) = φ (F'.trees.getD t {}) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  exact trees_read h.2 (fun o => φ (o.getD {})) (fun o => by
    cases o with
    | none => rfl
    | some X => exact hφ X) t

/-- `modify` at a step that keeps states alike. -/
theorem modify_rel {Φ : Fork → Fork} (h : ∀ F F', ForkAlike F F' → ForkAlike (Φ F) (Φ F')) :
    cmpA.Rel Eq (modify Φ : SubM PUnit) (modify Φ) :=
  fun F F' hF _ _ => ⟨⟨rfl, h F F' hF⟩, rfl⟩

/-! ## Loops that compute -/

/-- One computation after another. -/
theorem id_bind {α β : Type} {S : α → α → Prop} {R : β → β → Prop} {x x' : Id α}
    {f f' : α → Id β} (hx : S x x') (hf : ∀ a a', S a a' → R (f a) (f' a')) :
    R (x >>= f) (x' >>= f') := hf _ _ hx

/-- Two loops over one list whose bodies always go on and keep the relation S. -/
theorem id_forIn {α β : Type} {S : β → β → Prop} {f f' : α → β → Id (ForInStep β)}
    (hf : ∀ a s s', S s s' →
      ∃ t t', f a s = ForInStep.yield t ∧ f' a s' = ForInStep.yield t' ∧ S t t') :
    ∀ (l : List α) (i i' : β), S i i' → S (forIn l i f : Id β) (forIn l i' f' : Id β)
  | [], _, _, h => h
  | a :: l, i, i', h => by
    obtain ⟨t, t', e, e', ht⟩ := hf a i i' h
    rw [List.forIn_cons, List.forIn_cons, e, e']
    exact id_forIn hf l t t' ht

/-- The same over one array. -/
theorem id_forIn_array {α β : Type} {S : β → β → Prop} {f f' : α → β → Id (ForInStep β)}
    (hf : ∀ a s s', S s s' →
      ∃ t t', f a s = ForInStep.yield t ∧ f' a s' = ForInStep.yield t' ∧ S t t')
    (l : Array α) (i i' : β) (h : S i i') : S (forIn l i f : Id β) (forIn l i' f' : Id β) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact id_forIn hf _ _ _ h

/-! ## The weights on the rows -/

/-- **`HTailF2.coefficientsF` at two states that are alike and two lists of tables.** -/
theorem coefficientsF_rel (tl : HTailF2) (f' : Array HFun) :
    cmpA.Rel Eq tl.coefficientsF (HTailF2.coefficientsF { tl with funs := f' }) := by
  unfold HTailF2.coefficientsF
  dsimp only
  refine cmpA.bind' (S := Eq) (by keeps)
    (Cmp.blk.lift ForkAlike (by show Over.K (m := Blk) _; keeps) (relB_refl _)) fun g g' e => ?_
  subst e
  refine modify_rel fun F F' hF => ?_
  have hθ : F'.theta = F.theta := by rw [hF.1]
  rw [hθ]
  show ForkAlike (_ >>= _ : Id Fork) (_ >>= _ : Id Fork)
  refine id_bind (S := ForkAlike) (id_forIn ?_ _ _ _ hF) fun r r' hr => ?_
  · intro n s s' hs
    split
    · rename_i t _
      rw [tree_read hs (fun X => X.kind) (fun _ => rfl) t]
      split
      · exact ⟨_, _, rfl, rfl, onRow_alike hs _ _ _ fun _ => rfl⟩
      · exact ⟨_, _, rfl, rfl, hs⟩
    · exact ⟨_, _, rfl, rfl, hs⟩
  refine id_bind (S := ForkAlike) (id_forIn ?_ _ _ _ hr) fun r r' hr => ?_
  · intro q s s' hs
    refine ⟨_, _, rfl, rfl, id_forIn_array ?_ _ _ _ hs⟩
    intro p s s' hs
    rw [tree_read hs (fun X => X.R) (fun _ => rfl) p.tree]
    exact ⟨_, _, rfl, rfl, onRow_alike hs _ _ _ fun _ => rfl⟩
  refine id_bind (S := ForkAlike) (id_forIn ?_ _ _ _ ?_) fun r r' hr => ?_
  · intro e s s' hs
    exact ⟨_, _, rfl, rfl, onRow_alike hs _ _ _ fun _ => rfl⟩
  · refine onRow_alike ?_ _ _ _ fun _ => rfl
    exact onRow_alike hr _ _ _ fun _ => rfl
  refine id_bind (S := ForkAlike) (id_forIn ?_ _ _ _ ?_) fun r r' hr => hr
  · intro mu s s' hs
    exact ⟨_, _, rfl, rfl, onRow_alike hs _ _ _ fun _ => rfl⟩
  · exact onRow_alike hr _ _ _ fun _ => rfl

end OnBytes.Flat
