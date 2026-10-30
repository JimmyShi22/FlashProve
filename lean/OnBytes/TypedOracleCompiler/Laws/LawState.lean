-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawState.lean: the kit's class `Same` carried up through one and two layers of
state over `Blk`.

The class (OnBytes/TypedOracleCompiler/Laws/LawKit.lean) says: one text, from contexts in R, fails alike or gives
equal values and leaves contexts in R. The model's checks (OnBytes/Model/) are written in layers of
state: SubM := StateT Fork Blk, PlaceM := StateT Placed Blk, LinkM := StateT LinkCtx SubM.

Main names.
  `SameS R x`   x : StateT σ Blk α: from every state s the block x s is `Same`. So the two runs that
                are compared start from one state s, and end in equal states (the state is part of
                the block's value).
  `SameL R x`   x : StateT σ (StateT τ Blk) α: from every state s, x s is `SameS`.
  For each of the two: pure, bind, map, if, dependent if, the six loops, mapM over a list or an
  array, a loop over a range, get, set, modify, modifyGet, the lift of a routine of the layer below
  (StateT.lift, monadLift), and run.

Not claimed. Nothing on two runs that start from two states that differ: law 1 ("the descriptions
are constants": OnBytes/TypedOracleCompiler/Laws/LawAlike.lean says the two laws) in the head's link (the link of
the head's sub-proof: `Verify.headPlanOf`, OnBytes/Model/VerifyLinks.lean) wants that (a relation
on Fork), and it is not here.

-/
import OnBytes.TypedOracleCompiler.Laws.LawKit

namespace OnBytes.TwoLaws

open OnBytes

variable {R : Ctx → Ctx → Prop}

/-! ## Three more loops for Blk itself (OnBytes/TypedOracleCompiler/Laws/LawKit.lean has the other six) -/

instance same_mapM_list {α β : Type} (l : List α) (f : α → Blk β) [hf : ∀ a, Same R (f a)] :
    Same R (l.mapM f) := by
  induction l with
  | nil => rw [List.mapM_nil]; infer_instance
  | cons a l ih =>
    rw [List.mapM_cons]
    exact Same.bind (hf a) fun b => Same.bind ih fun bs => same_pure _

instance same_mapM_array {α β : Type} (l : Array α) (f : α → Blk β) [hf : ∀ a, Same R (f a)] :
    Same R (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]; infer_instance

instance same_forIn_range {β : Type} (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → Blk (ForInStep β)) [hf : ∀ a b, Same R (f a b)] :
    Same R (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; infer_instance

instance same_discard {α : Type} (x : Blk α) [hx : Same R x] : Same R (discard x) := by
  have e : discard x = (fun _ => PUnit.unit) <$> x := by
    unfold Functor.discard
    rw [LawfulFunctor.map_const]
    rfl
  rw [e]; infer_instance

/-! The loops' rules as theorems, for a body that no instance reaches. -/

theorem Same.forIn_list' {α β : Type} {l : List α} {init : β} {f : α → β → Blk (ForInStep β)}
    (hf : ∀ a b, Same R (f a b)) : Same R (forIn l init f) :=
  have := hf; same_forIn_list l init f

theorem Same.forIn_array' {α β : Type} {l : Array α} {init : β} {f : α → β → Blk (ForInStep β)}
    (hf : ∀ a b, Same R (f a b)) : Same R (forIn l init f) :=
  have := hf; same_forIn_array l init f

theorem Same.forIn_range' {β : Type} {l : Std.Legacy.Range} {init : β} {f : Nat → β → Blk (ForInStep β)}
    (hf : ∀ a b, Same R (f a b)) : Same R (forIn l init f) :=
  have := hf; same_forIn_range l init f

theorem Same.foldlM_list' {α β : Type} {l : List α} {init : β} {f : β → α → Blk β}
    (hf : ∀ b a, Same R (f b a)) : Same R (l.foldlM f init) :=
  have := hf; same_foldlM_list l init f

theorem Same.foldlM_array' {α β : Type} {l : Array α} {init : β} {f : β → α → Blk β}
    (hf : ∀ b a, Same R (f b a)) : Same R (l.foldlM f init) :=
  have := hf; same_foldlM_array l init f

theorem Same.forM_list' {α : Type} {l : List α} {f : α → Blk PUnit}
    (hf : ∀ a, Same R (f a)) : Same R (l.forM f) :=
  have := hf; same_forM_list l f

theorem Same.forM_array' {α : Type} {l : Array α} {f : α → Blk PUnit}
    (hf : ∀ a, Same R (f a)) : Same R (l.forM f) :=
  have := hf; same_forM_array l f

theorem Same.mapM_list' {α β : Type} {l : List α} {f : α → Blk β}
    (hf : ∀ a, Same R (f a)) : Same R (l.mapM f) :=
  have := hf; same_mapM_list l f

theorem Same.mapM_array' {α β : Type} {l : Array α} {f : α → Blk β}
    (hf : ∀ a, Same R (f a)) : Same R (l.mapM f) :=
  have := hf; same_mapM_array l f

/-! ## One layer of state -/

class SameS (R : Ctx → Ctx → Prop) {σ α : Type} (x : StateT σ Blk α) : Prop where
  out : ∀ s, Same R (x s)

section S
variable {σ : Type}

instance sameS_pure {α : Type} (a : α) : SameS R (pure a : StateT σ Blk α) :=
  ⟨fun s => same_pure (a, s)⟩

theorem SameS.bind {α β : Type} {x : StateT σ Blk α} {f : α → StateT σ Blk β} (hx : SameS R x)
    (hf : ∀ a, SameS R (f a)) : SameS R (x >>= f) :=
  ⟨fun s => Same.bind (hx.out s) fun p => (hf p.1).out p.2⟩

instance sameS_bind {α β : Type} (x : StateT σ Blk α) (f : α → StateT σ Blk β) [hx : SameS R x]
    [hf : ∀ a, SameS R (f a)] : SameS R (x >>= f) := SameS.bind hx hf

instance sameS_map {α β : Type} (g : α → β) (x : StateT σ Blk α) [hx : SameS R x] : SameS R (g <$> x) := by
  have e : g <$> x = x >>= fun a => pure (g a) := (bind_pure_comp g x).symm
  rw [e]; infer_instance

instance sameS_ite {α : Type} (p : Prop) [Decidable p] (a b : StateT σ Blk α) [ha : SameS R a]
    [hb : SameS R b] : SameS R (if p then a else b) := by
  split <;> assumption

instance sameS_dite {α : Type} (p : Prop) [Decidable p] (a : p → StateT σ Blk α) (b : ¬p → StateT σ Blk α)
    [ha : ∀ h, SameS R (a h)] [hb : ∀ h, SameS R (b h)] : SameS R (dite p a b) := by
  split
  · exact ha _
  · exact hb _

instance sameS_forIn_list {α β : Type} (l : List α) (init : β)
    (f : α → β → StateT σ Blk (ForInStep β)) [hf : ∀ a b, SameS R (f a b)] :
    SameS R (forIn l init f) := by
  induction l generalizing init with
  | nil => rw [List.forIn_nil]; infer_instance
  | cons a l ih =>
    rw [List.forIn_cons]
    refine SameS.bind (hf a init) fun r => ?_
    cases r with
    | done b => exact sameS_pure b
    | yield b => exact ih b

instance sameS_forIn_array {α β : Type} (l : Array α) (init : β)
    (f : α → β → StateT σ Blk (ForInStep β)) [hf : ∀ a b, SameS R (f a b)] :
    SameS R (forIn l init f) := by
  rw [← Array.forIn_toList]; infer_instance

instance sameS_foldlM_list {α β : Type} (l : List α) (init : β) (f : β → α → StateT σ Blk β)
    [hf : ∀ b a, SameS R (f b a)] : SameS R (l.foldlM f init) := by
  induction l generalizing init with
  | nil => rw [List.foldlM_nil]; infer_instance
  | cons a l ih =>
    rw [List.foldlM_cons]
    exact SameS.bind (hf init a) fun r => ih r

instance sameS_foldlM_array {α β : Type} (l : Array α) (init : β) (f : β → α → StateT σ Blk β)
    [hf : ∀ b a, SameS R (f b a)] : SameS R (l.foldlM f init) := by
  rw [← Array.foldlM_toList]; infer_instance

instance sameS_forM_list {α : Type} (l : List α) (f : α → StateT σ Blk PUnit)
    [hf : ∀ a, SameS R (f a)] : SameS R (l.forM f) := by
  induction l with
  | nil => exact sameS_pure _
  | cons a l ih => exact SameS.bind (hf a) fun _ => ih

instance sameS_forM_array {α : Type} (l : Array α) (f : α → StateT σ Blk PUnit)
    [hf : ∀ a, SameS R (f a)] : SameS R (l.forM f) := by
  unfold Array.forM; infer_instance

instance sameS_get : SameS R (get : StateT σ Blk σ) := ⟨fun s => same_pure (s, s)⟩
instance sameS_set (s : σ) : SameS R (set s : StateT σ Blk PUnit) := ⟨fun _ => same_pure (PUnit.unit, s)⟩
instance sameS_modify (f : σ → σ) : SameS R (modify f : StateT σ Blk PUnit) :=
  ⟨fun s => same_pure (PUnit.unit, f s)⟩
instance sameS_modifyGet {α : Type} (f : σ → α × σ) : SameS R (modifyGet f : StateT σ Blk α) :=
  ⟨fun s => same_pure (f s)⟩

instance sameS_mapM_list {α β : Type} (l : List α) (f : α → StateT σ Blk β) [hf : ∀ a, SameS R (f a)] :
    SameS R (l.mapM f) := by
  induction l with
  | nil => rw [List.mapM_nil]; infer_instance
  | cons a l ih =>
    rw [List.mapM_cons]
    exact SameS.bind (hf a) fun b => SameS.bind ih fun bs => sameS_pure _

instance sameS_mapM_array {α β : Type} (l : Array α) (f : α → StateT σ Blk β) [hf : ∀ a, SameS R (f a)] :
    SameS R (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]; infer_instance

instance sameS_forIn_range {β : Type} (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → StateT σ Blk (ForInStep β)) [hf : ∀ a b, SameS R (f a b)] :
    SameS R (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; infer_instance

instance sameS_discard {α : Type} (x : StateT σ Blk α) [hx : SameS R x] : SameS R (discard x) := by
  have e : discard x = (fun _ => PUnit.unit) <$> x := by
    unfold Functor.discard
    rw [LawfulFunctor.map_const]
    rfl
  rw [e]; infer_instance

theorem SameS.forIn_list' {α β : Type} {l : List α} {init : β} {f : α → β → StateT σ Blk (ForInStep β)}
    (hf : ∀ a b, SameS R (f a b)) : SameS R (forIn l init f) :=
  have := hf; sameS_forIn_list l init f

theorem SameS.forIn_array' {α β : Type} {l : Array α} {init : β} {f : α → β → StateT σ Blk (ForInStep β)}
    (hf : ∀ a b, SameS R (f a b)) : SameS R (forIn l init f) :=
  have := hf; sameS_forIn_array l init f

theorem SameS.forIn_range' {β : Type} {l : Std.Legacy.Range} {init : β} {f : Nat → β → StateT σ Blk (ForInStep β)}
    (hf : ∀ a b, SameS R (f a b)) : SameS R (forIn l init f) :=
  have := hf; sameS_forIn_range l init f

theorem SameS.foldlM_list' {α β : Type} {l : List α} {init : β} {f : β → α → StateT σ Blk β}
    (hf : ∀ b a, SameS R (f b a)) : SameS R (l.foldlM f init) :=
  have := hf; sameS_foldlM_list l init f

theorem SameS.foldlM_array' {α β : Type} {l : Array α} {init : β} {f : β → α → StateT σ Blk β}
    (hf : ∀ b a, SameS R (f b a)) : SameS R (l.foldlM f init) :=
  have := hf; sameS_foldlM_array l init f

theorem SameS.forM_list' {α : Type} {l : List α} {f : α → StateT σ Blk PUnit}
    (hf : ∀ a, SameS R (f a)) : SameS R (l.forM f) :=
  have := hf; sameS_forM_list l f

theorem SameS.forM_array' {α : Type} {l : Array α} {f : α → StateT σ Blk PUnit}
    (hf : ∀ a, SameS R (f a)) : SameS R (l.forM f) :=
  have := hf; sameS_forM_array l f

theorem SameS.mapM_list' {α β : Type} {l : List α} {f : α → StateT σ Blk β}
    (hf : ∀ a, SameS R (f a)) : SameS R (l.mapM f) :=
  have := hf; sameS_mapM_list l f

theorem SameS.mapM_array' {α β : Type} {l : Array α} {f : α → StateT σ Blk β}
    (hf : ∀ a, SameS R (f a)) : SameS R (l.mapM f) :=
  have := hf; sameS_mapM_array l f

instance sameS_lift {α : Type} (b : Blk α) [hb : Same R b] :
    SameS R (StateT.lift b : StateT σ Blk α) :=
  ⟨fun s => Same.bind hb fun a => same_pure (a, s)⟩

instance sameS_monadLift {α : Type} (b : Blk α) [hb : Same R b] :
    SameS R (monadLift b : StateT σ Blk α) :=
  ⟨fun s => Same.bind hb fun a => same_pure (a, s)⟩

instance same_runS {α : Type} (x : StateT σ Blk α) (s : σ) [hx : SameS R x] :
    Same R (StateT.run x s) := hx.out s

end S

/-! ## Two layers of state -/

class SameL (R : Ctx → Ctx → Prop) {σ τ α : Type} (x : StateT σ (StateT τ Blk) α) : Prop where
  out : ∀ s, SameS R (x s)

section L
variable {σ τ : Type}

instance sameL_pure {α : Type} (a : α) : SameL R (pure a : StateT σ (StateT τ Blk) α) :=
  ⟨fun s => sameS_pure (a, s)⟩

theorem SameL.bind {α β : Type} {x : StateT σ (StateT τ Blk) α}
    {f : α → StateT σ (StateT τ Blk) β} (hx : SameL R x) (hf : ∀ a, SameL R (f a)) :
    SameL R (x >>= f) :=
  ⟨fun s => SameS.bind (hx.out s) fun p => (hf p.1).out p.2⟩

instance sameL_bind {α β : Type} (x : StateT σ (StateT τ Blk) α) (f : α → StateT σ (StateT τ Blk) β) [hx : SameL R x]
    [hf : ∀ a, SameL R (f a)] : SameL R (x >>= f) := SameL.bind hx hf

instance sameL_map {α β : Type} (g : α → β) (x : StateT σ (StateT τ Blk) α) [hx : SameL R x] : SameL R (g <$> x) := by
  have e : g <$> x = x >>= fun a => pure (g a) := (bind_pure_comp g x).symm
  rw [e]; infer_instance

instance sameL_ite {α : Type} (p : Prop) [Decidable p] (a b : StateT σ (StateT τ Blk) α) [ha : SameL R a]
    [hb : SameL R b] : SameL R (if p then a else b) := by
  split <;> assumption

instance sameL_dite {α : Type} (p : Prop) [Decidable p] (a : p → StateT σ (StateT τ Blk) α) (b : ¬p → StateT σ (StateT τ Blk) α)
    [ha : ∀ h, SameL R (a h)] [hb : ∀ h, SameL R (b h)] : SameL R (dite p a b) := by
  split
  · exact ha _
  · exact hb _

instance sameL_forIn_list {α β : Type} (l : List α) (init : β)
    (f : α → β → StateT σ (StateT τ Blk) (ForInStep β)) [hf : ∀ a b, SameL R (f a b)] :
    SameL R (forIn l init f) := by
  induction l generalizing init with
  | nil => rw [List.forIn_nil]; infer_instance
  | cons a l ih =>
    rw [List.forIn_cons]
    refine SameL.bind (hf a init) fun r => ?_
    cases r with
    | done b => exact sameL_pure b
    | yield b => exact ih b

instance sameL_forIn_array {α β : Type} (l : Array α) (init : β)
    (f : α → β → StateT σ (StateT τ Blk) (ForInStep β)) [hf : ∀ a b, SameL R (f a b)] :
    SameL R (forIn l init f) := by
  rw [← Array.forIn_toList]; infer_instance

instance sameL_foldlM_list {α β : Type} (l : List α) (init : β) (f : β → α → StateT σ (StateT τ Blk) β)
    [hf : ∀ b a, SameL R (f b a)] : SameL R (l.foldlM f init) := by
  induction l generalizing init with
  | nil => rw [List.foldlM_nil]; infer_instance
  | cons a l ih =>
    rw [List.foldlM_cons]
    exact SameL.bind (hf init a) fun r => ih r

instance sameL_foldlM_array {α β : Type} (l : Array α) (init : β) (f : β → α → StateT σ (StateT τ Blk) β)
    [hf : ∀ b a, SameL R (f b a)] : SameL R (l.foldlM f init) := by
  rw [← Array.foldlM_toList]; infer_instance

instance sameL_forM_list {α : Type} (l : List α) (f : α → StateT σ (StateT τ Blk) PUnit)
    [hf : ∀ a, SameL R (f a)] : SameL R (l.forM f) := by
  induction l with
  | nil => exact sameL_pure _
  | cons a l ih => exact SameL.bind (hf a) fun _ => ih

instance sameL_forM_array {α : Type} (l : Array α) (f : α → StateT σ (StateT τ Blk) PUnit)
    [hf : ∀ a, SameL R (f a)] : SameL R (l.forM f) := by
  unfold Array.forM; infer_instance

instance sameL_get : SameL R (get : StateT σ (StateT τ Blk) σ) := ⟨fun s => sameS_pure (s, s)⟩
instance sameL_set (s : σ) : SameL R (set s : StateT σ (StateT τ Blk) PUnit) := ⟨fun _ => sameS_pure (PUnit.unit, s)⟩
instance sameL_modify (f : σ → σ) : SameL R (modify f : StateT σ (StateT τ Blk) PUnit) :=
  ⟨fun s => sameS_pure (PUnit.unit, f s)⟩
instance sameL_modifyGet {α : Type} (f : σ → α × σ) : SameL R (modifyGet f : StateT σ (StateT τ Blk) α) :=
  ⟨fun s => sameS_pure (f s)⟩

instance sameL_mapM_list {α β : Type} (l : List α) (f : α → StateT σ (StateT τ Blk) β) [hf : ∀ a, SameL R (f a)] :
    SameL R (l.mapM f) := by
  induction l with
  | nil => rw [List.mapM_nil]; infer_instance
  | cons a l ih =>
    rw [List.mapM_cons]
    exact SameL.bind (hf a) fun b => SameL.bind ih fun bs => sameL_pure _

instance sameL_mapM_array {α β : Type} (l : Array α) (f : α → StateT σ (StateT τ Blk) β) [hf : ∀ a, SameL R (f a)] :
    SameL R (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]; infer_instance

instance sameL_forIn_range {β : Type} (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → StateT σ (StateT τ Blk) (ForInStep β)) [hf : ∀ a b, SameL R (f a b)] :
    SameL R (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; infer_instance

instance sameL_discard {α : Type} (x : StateT σ (StateT τ Blk) α) [hx : SameL R x] : SameL R (discard x) := by
  have e : discard x = (fun _ => PUnit.unit) <$> x := by
    unfold Functor.discard
    rw [LawfulFunctor.map_const]
    rfl
  rw [e]; infer_instance

theorem SameL.forIn_list' {α β : Type} {l : List α} {init : β} {f : α → β → StateT σ (StateT τ Blk) (ForInStep β)}
    (hf : ∀ a b, SameL R (f a b)) : SameL R (forIn l init f) :=
  have := hf; sameL_forIn_list l init f

theorem SameL.forIn_array' {α β : Type} {l : Array α} {init : β} {f : α → β → StateT σ (StateT τ Blk) (ForInStep β)}
    (hf : ∀ a b, SameL R (f a b)) : SameL R (forIn l init f) :=
  have := hf; sameL_forIn_array l init f

theorem SameL.forIn_range' {β : Type} {l : Std.Legacy.Range} {init : β} {f : Nat → β → StateT σ (StateT τ Blk) (ForInStep β)}
    (hf : ∀ a b, SameL R (f a b)) : SameL R (forIn l init f) :=
  have := hf; sameL_forIn_range l init f

theorem SameL.foldlM_list' {α β : Type} {l : List α} {init : β} {f : β → α → StateT σ (StateT τ Blk) β}
    (hf : ∀ b a, SameL R (f b a)) : SameL R (l.foldlM f init) :=
  have := hf; sameL_foldlM_list l init f

theorem SameL.foldlM_array' {α β : Type} {l : Array α} {init : β} {f : β → α → StateT σ (StateT τ Blk) β}
    (hf : ∀ b a, SameL R (f b a)) : SameL R (l.foldlM f init) :=
  have := hf; sameL_foldlM_array l init f

theorem SameL.forM_list' {α : Type} {l : List α} {f : α → StateT σ (StateT τ Blk) PUnit}
    (hf : ∀ a, SameL R (f a)) : SameL R (l.forM f) :=
  have := hf; sameL_forM_list l f

theorem SameL.forM_array' {α : Type} {l : Array α} {f : α → StateT σ (StateT τ Blk) PUnit}
    (hf : ∀ a, SameL R (f a)) : SameL R (l.forM f) :=
  have := hf; sameL_forM_array l f

theorem SameL.mapM_list' {α β : Type} {l : List α} {f : α → StateT σ (StateT τ Blk) β}
    (hf : ∀ a, SameL R (f a)) : SameL R (l.mapM f) :=
  have := hf; sameL_mapM_list l f

theorem SameL.mapM_array' {α β : Type} {l : Array α} {f : α → StateT σ (StateT τ Blk) β}
    (hf : ∀ a, SameL R (f a)) : SameL R (l.mapM f) :=
  have := hf; sameL_mapM_array l f

instance sameL_lift {α : Type} (x : StateT τ Blk α) [hx : SameS R x] :
    SameL R (StateT.lift x : StateT σ (StateT τ Blk) α) :=
  ⟨fun s => SameS.bind hx fun a => sameS_pure (a, s)⟩

instance sameL_monadLift {α : Type} (x : StateT τ Blk α) [hx : SameS R x] :
    SameL R (monadLift x : StateT σ (StateT τ Blk) α) :=
  ⟨fun s => SameS.bind hx fun a => sameS_pure (a, s)⟩

instance sameL_monadLift2 {α : Type} (b : Blk α) [hb : Same R b] :
    SameL R (monadLift b : StateT σ (StateT τ Blk) α) :=
  ⟨fun s => SameS.bind (sameS_monadLift b) fun a => sameS_pure (a, s)⟩

instance sameS_runL {α : Type} (x : StateT σ (StateT τ Blk) α) (s : σ) [hx : SameL R x] :
    SameS R (StateT.run x s) := hx.out s

end L

end OnBytes.TwoLaws
