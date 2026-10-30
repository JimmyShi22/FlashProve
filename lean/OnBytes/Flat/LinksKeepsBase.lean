-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksKeepsBase.lean: "leaves the two flags of a run as they are", for blocks and for
the routines that run above blocks.

A block (`Blk`, OnBytes/Iop/Ground.lean) runs in a context with two flags: whether the run is dry,
and whether intermediate values are kept. `Blk.Keeps b` (OnBytes/Iop/DrySizes.lean) says that b
leaves both as they are. The checks of the model's sub-proofs are not blocks: they run in a state
above `Blk` (`SubM`, OnBytes/Model/Hide.lean) or in two (`LinkM`, OnBytes/Model/Trees.lean). This
file says the same of them, once for all such layers, and shows the laws by which the property
passes through the ways in which a routine is put together.

Main definition: `Over m`: m is `Blk`, or a state above such an m. `Over.K x`: for a block,
`Blk.Keeps`; for a routine in a state, that it is so from every state.
Main theorems: `k_pure`, `k_bind`, `k_map`, `k_ite`, `k_dite`, the loops (`k_forIn_list`,
`k_forIn_array`, `k_forIn_range`, `k_foldlM_list`, `k_foldlM_array`, `k_forM_list`, `k_mapM_list`,
`k_mapM_array`), `k_fun`, the lifts (`k_lift`, `k_monadLift`, `k_liftT_refl`,
`k_liftT_step`), the reading and writing of the upper state (`k_get`, `k_set`, `k_modify`,
`k_modifyGet`), `k_run`.

Not claimed: anything on what a routine decides. For proofs only; no module of the program imports
this file.


-/
import OnBytes.Iop.DrySizes

set_option autoImplicit false

namespace OnBytes.Flat

/-- m is `Blk` or a state above such a monad; `K x`: x leaves the two flags of a run as they are. -/
class Over (m : Type → Type) [Monad m] where
  /-- the routine leaves the two flags as they are -/
  K : {α : Type} → m α → Prop
  /-- a routine that only returns a value -/
  pure' : ∀ {α : Type} (a : α), K (pure a : m α)
  /-- one routine after another -/
  bind' : ∀ {α β : Type} {x : m α} {f : α → m β}, K x → (∀ a, K (f a)) → K (x >>= f)

instance overBlk : Over Blk where
  K := Blk.Keeps
  pure' := Blk.keeps_pure
  bind' := Blk.keeps_bind

instance overState {σ : Type} {m : Type → Type} [Monad m] [Over m] : Over (StateT σ m) where
  K x := ∀ s, Over.K (x s)
  pure' a s := Over.pure' (a, s)
  bind' {_ _ x f} hx hf s := by
    show Over.K (x s >>= fun p => f p.1 p.2)
    exact Over.bind' (hx s) fun p => hf p.1 p.2

section laws

variable {m : Type → Type} [Monad m] [Over m] {α β σ : Type}

theorem k_pure (a : α) : Over.K (pure a : m α) := Over.pure' a

theorem k_bind {x : m α} {f : α → m β} (hx : Over.K x) (hf : ∀ a, Over.K (f a)) :
    Over.K (x >>= f) := Over.bind' hx hf

theorem k_map [LawfulMonad m] {f : α → β} {x : m α} (hx : Over.K x) : Over.K (f <$> x) := by
  rw [← bind_pure_comp]
  exact k_bind hx fun _ => k_pure _

theorem k_ite {c : Prop} [Decidable c] {x y : m α} (hx : Over.K x) (hy : Over.K y) :
    Over.K (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem k_dite {c : Prop} [Decidable c] {x : c → m α} {y : ¬c → m α} (hx : ∀ h, Over.K (x h))
    (hy : ∀ h, Over.K (y h)) : Over.K (dite c x y) := by
  split
  · exact hx _
  · exact hy _

/-- A loop over a list. -/
theorem k_forIn_list {f : α → β → m (ForInStep β)} (hf : ∀ a s, Over.K (f a s)) :
    ∀ {l : List α} {init : β}, Over.K (forIn l init f)
  | [], init => by
      rw [List.forIn_nil]
      exact k_pure init
  | a :: l, init => by
      rw [List.forIn_cons]
      refine k_bind (hf a init) fun r => ?_
      cases r with
      | done s => exact k_pure s
      | yield s => exact k_forIn_list hf

/-- A loop over an array. -/
theorem k_forIn_array {f : α → β → m (ForInStep β)} (hf : ∀ a s, Over.K (f a s))
    {l : Array α} {init : β} : Over.K (forIn l init f) := by
  rw [← Array.forIn_toList]
  exact k_forIn_list hf

/-- A loop over a range of numbers. -/
theorem k_forIn_range {f : Nat → β → m (ForInStep β)} (hf : ∀ a s, Over.K (f a s))
    {r : Std.Legacy.Range} {init : β} : Over.K (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact k_forIn_list hf

/-- A fold over a list. -/
theorem k_foldlM_list {f : β → α → m β} (hf : ∀ s a, Over.K (f s a)) :
    ∀ {l : List α} {init : β}, Over.K (List.foldlM f init l)
  | [], init => by
      rw [List.foldlM_nil]
      exact k_pure init
  | a :: l, init => by
      rw [List.foldlM_cons]
      exact k_bind (hf init a) fun _ => k_foldlM_list hf

/-- A fold over an array. -/
theorem k_foldlM_array {f : β → α → m β} (hf : ∀ s a, Over.K (f s a)) {l : Array α} {init : β} :
    Over.K (Array.foldlM f init l) := by
  rw [← Array.foldlM_toList]
  exact k_foldlM_list hf

/-- One routine for each member of a list. -/
theorem k_forM_list {f : α → m PUnit} (hf : ∀ a, Over.K (f a)) :
    ∀ {l : List α}, Over.K (List.forM l f)
  | [] => k_pure PUnit.unit
  | a :: _ => k_bind (hf a) fun _ => k_forM_list hf

/-- One routine for each member of a list, the values gathered. -/
theorem k_mapM_list [LawfulMonad m] {f : α → m β} (hf : ∀ a, Over.K (f a)) :
    ∀ {l : List α}, Over.K (List.mapM f l)
  | [] => by
      rw [List.mapM_nil]
      exact k_pure _
  | a :: l => by
      rw [List.mapM_cons]
      exact k_bind (hf a) fun _ => k_bind (k_mapM_list hf) fun _ => k_pure _

/-- One routine for each member of an array, the values gathered. -/
theorem k_mapM_array [LawfulMonad m] {f : α → m β} (hf : ∀ a, Over.K (f a)) {l : Array α} :
    Over.K (Array.mapM f l) := by
  rw [Array.mapM_eq_mapM_toList]
  exact k_map (k_mapM_list hf)

/-- A routine of the upper layer that is written as a function of the state. -/
theorem k_fun {x : StateT σ m α} (hx : ∀ s, Over.K (x s)) : Over.K x := hx

/-- A routine of the lower layer, run in the upper one. -/
theorem k_lift {x : m α} (hx : Over.K x) : Over.K (StateT.lift x : StateT σ m α) :=
  fun s => k_bind hx fun a => k_pure (a, s)

theorem k_monadLift {x : m α} (hx : Over.K x) :
    Over.K (MonadLift.monadLift x : StateT σ m α) := k_lift hx

theorem k_liftT_refl {x : m α} (hx : Over.K x) : Over.K (MonadLiftT.monadLift x : m α) := hx

omit [Monad m] [Over m] in
theorem k_liftT_step {n o : Type → Type} [Monad n] [Monad o] [Over o] [MonadLiftT m n]
    [MonadLift n o] {x : m α}
    (hx : Over.K (MonadLift.monadLift (MonadLiftT.monadLift x : n α) : o α)) :
    Over.K (MonadLiftT.monadLift x : o α) := hx

theorem k_get : Over.K (get : StateT σ m σ) := fun s => k_pure (s, s)

theorem k_set (s' : σ) : Over.K (set s' : StateT σ m PUnit) := fun _ => k_pure (PUnit.unit, s')

theorem k_modify (f : σ → σ) : Over.K (modify f : StateT σ m PUnit) :=
  fun s => k_pure (PUnit.unit, f s)

theorem k_modifyGet (f : σ → α × σ) : Over.K (modifyGet f : StateT σ m α) :=
  fun s => k_pure (f s)

/-- A routine of the upper layer, run from a state. -/
theorem k_run {x : StateT σ m α} (hx : Over.K x) (s : σ) : Over.K (StateT.run x s) := hx s

end laws

end OnBytes.Flat
