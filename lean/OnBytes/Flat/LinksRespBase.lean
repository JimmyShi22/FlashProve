-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksRespBase.lean: "gives the same from two states that are alike", for the routines
of a sub-proof's check.

Two states of a sub-proof's check are alike (`ForkAlike`, OnBytes/Flat/LinksFreeFork.lean) if they
agree in all but the coefficients of the one equation. `Resp.K x` says of a routine x: it leaves the
two flags of a run as they are, and from two such states and one dry context it fails both times, or
returns both times, with ONE value, one context left, and states that are alike again. It is a
property of one routine, and it passes through the ways in which a routine is put together as
`Over.K` does (OnBytes/Flat/LinksKeepsBase.lean); the laws here are that file's, said of it.

Main definition: `Resp m`: m is `Blk`, or `SubM`, or a state above such an m. `Resp.K x`: for a
block, `Blk.Keeps` (a block does not see the state); for a routine of `SubM`, what is said above;
for a routine in a further state, that it is so from every value of that state. Main theorems:
`r_pure`, `r_bind`, `r_map`, `r_ite`, `r_dite`, the loops, `r_fun`, the lifts (`r_lift`,
`r_lift_sub`, `r_monadLift`, `r_monadLift_sub`, `r_liftT_refl`, `r_liftT_step`), the reading and
writing of a further state (`r_get`, `r_set`, `r_modify`, `r_modifyGet`), `r_run`; `resp_sub`,
`resp_link`: what the property gives in the words of OnBytes/Flat/DryRel.lean; `cmpA_same`,
`cmpLA_same`: two continuations after one and the same such routine.

Not claimed: that a routine which returns the state of `SubM` itself, or a coefficient, has the
property: it has not. Nothing on a run on a view. For proofs only; no module of the program imports
this file.


-/
import OnBytes.Flat.LinksFreeFork

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-- m is `Blk`, `SubM`, or a state above such a monad; `K x`: x gives the same from two states of a
sub-proof's check that are alike. -/
class Resp (m : Type → Type) [Monad m] where
  /-- the routine gives the same from two states that are alike -/
  K : {α : Type} → m α → Prop
  /-- a routine that only returns a value -/
  pure' : ∀ {α : Type} (a : α), K (pure a : m α)
  /-- one routine after another -/
  bind' : ∀ {α β : Type} {x : m α} {f : α → m β}, K x → (∀ a, K (f a)) → K (x >>= f)

instance respBlk : Resp Blk where
  K := Blk.Keeps
  pure' := Blk.keeps_pure
  bind' := Blk.keeps_bind

instance respState {σ : Type} {m : Type → Type} [Monad m] [Resp m] : Resp (StateT σ m) where
  K x := ∀ s, Resp.K (x s)
  pure' a s := Resp.pure' (a, s)
  bind' {_ _ x f} hx hf s := by
    show Resp.K (x s >>= fun p => f p.1 p.2)
    exact Resp.bind' (hx s) fun p => hf p.1 p.2

/-- The layer of a sub-proof's check. It goes before the general one. -/
instance (priority := high) respSub : Resp (StateT Fork Blk) where
  K x := Over.K x ∧ cmpA.Rel Eq x x
  pure' a := ⟨k_pure a, cmpA.pure' rfl⟩
  bind' hx hf := ⟨k_bind hx.1 fun a => (hf a).1,
    cmpA.bind' hx.1 hx.2 fun a a' e => by subst e; exact (hf a).2⟩

section laws

variable {m : Type → Type} [Monad m] [Resp m] {α β σ : Type}

theorem r_pure (a : α) : Resp.K (pure a : m α) := Resp.pure' a

theorem r_bind {x : m α} {f : α → m β} (hx : Resp.K x) (hf : ∀ a, Resp.K (f a)) :
    Resp.K (x >>= f) := Resp.bind' hx hf

theorem r_map [LawfulMonad m] {f : α → β} {x : m α} (hx : Resp.K x) : Resp.K (f <$> x) := by
  rw [← bind_pure_comp]
  exact r_bind hx fun _ => r_pure _

theorem r_ite {c : Prop} [Decidable c] {x y : m α} (hx : Resp.K x) (hy : Resp.K y) :
    Resp.K (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem r_dite {c : Prop} [Decidable c] {x : c → m α} {y : ¬c → m α} (hx : ∀ h, Resp.K (x h))
    (hy : ∀ h, Resp.K (y h)) : Resp.K (dite c x y) := by
  split
  · exact hx _
  · exact hy _

/-- A loop over a list. -/
theorem r_forIn_list {f : α → β → m (ForInStep β)} (hf : ∀ a s, Resp.K (f a s)) :
    ∀ {l : List α} {init : β}, Resp.K (forIn l init f)
  | [], init => by
      rw [List.forIn_nil]
      exact r_pure init
  | a :: l, init => by
      rw [List.forIn_cons]
      refine r_bind (hf a init) fun r => ?_
      cases r with
      | done s => exact r_pure s
      | yield s => exact r_forIn_list hf

/-- A loop over an array. -/
theorem r_forIn_array {f : α → β → m (ForInStep β)} (hf : ∀ a s, Resp.K (f a s))
    {l : Array α} {init : β} : Resp.K (forIn l init f) := by
  rw [← Array.forIn_toList]
  exact r_forIn_list hf

/-- A loop over a range of numbers. -/
theorem r_forIn_range {f : Nat → β → m (ForInStep β)} (hf : ∀ a s, Resp.K (f a s))
    {r : Std.Legacy.Range} {init : β} : Resp.K (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact r_forIn_list hf

/-- A fold over a list. -/
theorem r_foldlM_list {f : β → α → m β} (hf : ∀ s a, Resp.K (f s a)) :
    ∀ {l : List α} {init : β}, Resp.K (List.foldlM f init l)
  | [], init => by
      rw [List.foldlM_nil]
      exact r_pure init
  | a :: l, init => by
      rw [List.foldlM_cons]
      exact r_bind (hf init a) fun _ => r_foldlM_list hf

/-- A fold over an array. -/
theorem r_foldlM_array {f : β → α → m β} (hf : ∀ s a, Resp.K (f s a)) {l : Array α} {init : β} :
    Resp.K (Array.foldlM f init l) := by
  rw [← Array.foldlM_toList]
  exact r_foldlM_list hf

/-- One routine for each member of a list. -/
theorem r_forM_list {f : α → m PUnit} (hf : ∀ a, Resp.K (f a)) :
    ∀ {l : List α}, Resp.K (List.forM l f)
  | [] => r_pure PUnit.unit
  | a :: _ => r_bind (hf a) fun _ => r_forM_list hf

/-- One routine for each member of a list, the values gathered. -/
theorem r_mapM_list [LawfulMonad m] {f : α → m β} (hf : ∀ a, Resp.K (f a)) :
    ∀ {l : List α}, Resp.K (List.mapM f l)
  | [] => by
      rw [List.mapM_nil]
      exact r_pure _
  | a :: l => by
      rw [List.mapM_cons]
      exact r_bind (hf a) fun _ => r_bind (r_mapM_list hf) fun _ => r_pure _

/-- One routine for each member of an array, the values gathered. -/
theorem r_mapM_array [LawfulMonad m] {f : α → m β} (hf : ∀ a, Resp.K (f a)) {l : Array α} :
    Resp.K (Array.mapM f l) := by
  rw [Array.mapM_eq_mapM_toList]
  exact r_map (r_mapM_list hf)

/-- A routine of the upper layer that is written as a function of the state. -/
theorem r_fun {x : StateT σ m α} (hx : ∀ s, Resp.K (x s)) : Resp.K x := hx

/-- A routine of the lower layer, run in the upper one. -/
theorem r_lift {x : m α} (hx : Resp.K x) : Resp.K (StateT.lift x : StateT σ m α) :=
  fun s => r_bind hx fun a => r_pure (a, s)

theorem r_monadLift {x : m α} (hx : Resp.K x) :
    Resp.K (MonadLift.monadLift x : StateT σ m α) := r_lift hx

theorem r_liftT_refl {x : m α} (hx : Resp.K x) : Resp.K (MonadLiftT.monadLift x : m α) := hx

omit [Monad m] [Resp m] in
theorem r_liftT_step {n o : Type → Type} [Monad n] [Monad o] [Resp o] [MonadLiftT m n]
    [MonadLift n o] {x : m α}
    (hx : Resp.K (MonadLift.monadLift (MonadLiftT.monadLift x : n α) : o α)) :
    Resp.K (MonadLiftT.monadLift x : o α) := hx

theorem r_get : Resp.K (get : StateT σ m σ) := fun s => r_pure (s, s)

theorem r_set (s' : σ) : Resp.K (set s' : StateT σ m PUnit) := fun _ => r_pure (PUnit.unit, s')

theorem r_modify (f : σ → σ) : Resp.K (modify f : StateT σ m PUnit) :=
  fun s => r_pure (PUnit.unit, f s)

theorem r_modifyGet (f : σ → α × σ) : Resp.K (modifyGet f : StateT σ m α) :=
  fun s => r_pure (f s)

/-- A routine of the upper layer, run from a state. -/
theorem r_run {x : StateT σ m α} (hx : Resp.K x) (s : σ) : Resp.K (StateT.run x s) := hx s

end laws


/-! ## The layer of a sub-proof's check -/

/-- A block, run in a sub-proof's check. -/
theorem r_lift_sub {α : Type} {x : Blk α} (hx : Resp.K x) :
    Resp.K (StateT.lift x : StateT Fork Blk α) :=
  ⟨k_lift (m := Blk) hx, Cmp.blk.lift ForkAlike (x := x) (x' := x) hx (relB_refl x)⟩

theorem r_monadLift_sub {α : Type} {x : Blk α} (hx : Resp.K x) :
    Resp.K (MonadLift.monadLift x : StateT Fork Blk α) := r_lift_sub hx

/-- What the property gives of a routine of a sub-proof's check. -/
theorem resp_sub {α : Type} {x : SubM α} (h : Resp.K x) : Over.K x ∧ cmpA.Rel Eq x x := h

/-- What it gives of a routine of a link. -/
theorem resp_link {α : Type} {x : LinkM α} (h : Resp.K x) : Over.K x ∧ cmpLA.Rel Eq x x :=
  ⟨fun C => (h C).1, fun C C' e => by
    subst e
    exact cmpA.mono' (fun p p' k => by subst k; exact ⟨rfl, rfl⟩) (h C).2⟩

/-- After one and the same routine of a sub-proof's check that gives the same from two states that
are alike. -/
theorem cmpA_same {α β : Type} {R : β → β → Prop} {x : SubM α} {f f' : α → SubM β} (h : Resp.K x)
    (hf : ∀ a, cmpA.Rel R (f a) (f' a)) : cmpA.Rel R (x >>= f) (x >>= f') :=
  cmpA.bind' (resp_sub h).1 (resp_sub h).2 fun a a' e => by subst e; exact hf a

/-- The same for a routine of a link. -/
theorem cmpLA_same {α β : Type} {R : β → β → Prop} {x : LinkM α} {f f' : α → LinkM β}
    (h : Resp.K x) (hf : ∀ a, cmpLA.Rel R (f a) (f' a)) : cmpLA.Rel R (x >>= f) (x >>= f') :=
  cmpLA.bind' (resp_link h).1 (resp_link h).2 fun a a' e => by subst e; exact hf a

end OnBytes.Flat
