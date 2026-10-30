-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/FlGrows.lean: THE PLAIN FUNCTIONS ON A LEDGER AND A TAPE LEAD TO A LATER LEDGER.
For the functions of OnBytes/K/Kc/Flat.lean and the merge's of OnBytes/K/Kc/QuietLink.lean: wherever
such a function returns, the ledger that it leaves is LATER than the one that it was handed
(`OnBytes.PscRun.Later`, OnBytes/Tie/Pv/Psc/PscLater.lean): as many slots; no fewer taken; if the
three arrays had their size they have it still; every slot that was filled is filled and holds the
same shown value and the same factor. Definitions, statements and proofs.

Why. A form names a hidden value by its slot, and what lies under the slot is read at the end. So
every law on a form's value that is stated at one ledger must last to the last one.

`Grows x`: a class: wherever x returns, its ledger is later. It is closed under `pure`, `bind`,
`if`, a map, a fold and a `mapM` over a list or an array. A function on the tape alone, a test and a
reading leave the ledger as it is. The ledger turns at four things alone: slots are taken
(`later_next`); a run of values is put under slots (`PscRun.hideRun_keeps`, WHICH WANTS NO
PREMISE ON THE ARRAYS' SIZES); a claim is added (`PscRun.lin_later`); an owed claim is marked
(`paid_later`).

`grows`: a tactic: it walks a do-block: bind by bind, into each `if` and each pattern.

Also: `Fl` is a lawful monad (wanted for `mapM` over an array).

Limits. One direction: from a return. Nothing is said where a function refuses; nothing on WHICH
values are put under the slots, on the claims, on soundness or on hiding.
-/
import OnBytes.K.Kc.QuietLink
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.Grow
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.PscRun (Later)

variable {α β γ : Type}

/-! ### What a step returns -/

theorem some_triple {a b : α} {F G : Fork} {t u : Tape} :
    (some (a, F, t) : Option (α × Fork × Tape)) = some (b, G, u) ↔ a = b ∧ F = G ∧ t = u := by
  constructor
  · intro h
    injection h with h
    injection h with h1 h2
    injection h2 with h2 h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem bind_some {x : Fl α} {f : α → Fl β} {F : Fork} {t : Tape} {r : β × Fork × Tape} :
    (x >>= f) F t = some r ↔ ∃ a G u, x F t = some (a, G, u) ∧ f a G u = some r := by
  show Fl.andThen x f F t = some r ↔ _
  unfold Fl.andThen
  cases h : x F t with
  | none => simp
  | some y =>
    obtain ⟨a, G, u⟩ := y
    constructor
    · intro h'
      exact ⟨a, G, u, rfl, h'⟩
    · rintro ⟨a', G', u', e, h'⟩
      obtain ⟨rfl, rfl, rfl⟩ := some_triple.mp e
      exact h'

/-! ### The monad's laws -/

instance : LawfulMonad Fl := LawfulMonad.mk'
  (id_map := by
    intro α x
    funext F t
    show Fl.andThen x (fun a => Fl.ret (id a)) F t = x F t
    unfold Fl.andThen
    cases x F t with
    | none => rfl
    | some y =>
      obtain ⟨a, G, u⟩ := y
      rfl)
  (pure_bind := by
    intros
    rfl)
  (bind_assoc := by
    intro α β γ x f g
    funext F t
    show Fl.andThen (Fl.andThen x f) g F t = Fl.andThen x (fun a => Fl.andThen (f a) g) F t
    unfold Fl.andThen
    cases x F t with
    | none => rfl
    | some y =>
      obtain ⟨a, G, u⟩ := y
      rfl)

/-! ### The class -/

/-- Wherever x returns, the ledger that it leaves is later than the one that it was handed. -/
class Grows (x : Fl α) : Prop where
  later : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape}, x F t = some (a, G, u) → Later F G

/-- A function that leaves the ledger as it is. -/
theorem Grows.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    Grows x :=
  ⟨fun {F t a G u} e => by
    obtain rfl := h F t a G u e
    exact Later.refl F⟩

instance grows_pure (a : α) : Grows (pure a : Fl α) :=
  Grows.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

/-- One function after another. -/
theorem Grows.bind {x : Fl α} {f : α → Fl β} (hx : Grows x) (hf : ∀ a, Grows (f a)) :
    Grows (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    exact (hx.later h1).trans ((hf a).later h2)⟩

instance grows_bind (x : Fl α) (f : α → Fl β) [Grows x] [∀ a, Grows (f a)] : Grows (x >>= f) :=
  Grows.bind inferInstance inferInstance

instance grows_map (g : α → β) (x : Fl α) [Grows x] : Grows (g <$> x) := by
  rw [map_eq_pure_bind]
  infer_instance

instance grows_ite (p : Prop) [Decidable p] (x y : Fl α) [Grows x] [Grows y] :
    Grows (if p then x else y) := by
  split <;> infer_instance

/-- The function that always refuses. -/
instance grows_none : Grows (fun _ _ => none : Fl α) := ⟨fun e => by simp at e⟩

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
macro "grows" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine Grows.bind ?_ ?_
    | intro _
    | split)

/-! ### Folds -/

theorem grows_foldlM {f : β → γ → Fl β} (hf : ∀ s a, Grows (f s a)) :
    ∀ (l : List γ) (s : β), Grows (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact Grows.bind (hf s a) fun s' => grows_foldlM hf l s'

theorem grows_mapM_list {f : α → Fl β} (hf : ∀ a, Grows (f a)) : ∀ l : List α, Grows (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact Grows.bind (hf a) fun _ => Grows.bind (grows_mapM_list hf l) fun _ => inferInstance

theorem grows_mapM_array {f : α → Fl β} (hf : ∀ a, Grows (f a)) (l : Array α) :
    Grows (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := grows_mapM_list hf l.toList
  infer_instance

/-! ### The steps -/

instance grows_must (b : Bool) : Grows (Fl.must b) :=
  Grows.of_same fun F t a G u e => by
    unfold Fl.must at e
    split at e
    · exact (some_triple.mp e).2.1
    · simp at e

instance grows_need (x : Option α) : Grows (Fl.need x) :=
  Grows.of_same fun F t a G u e => by
    unfold Fl.need at e
    cases x with
    | none => simp at e
    | some y => exact (some_triple.mp e).2.1

instance grows_ask (f : Fork → Option α) : Grows (Fl.ask f) :=
  Grows.of_same fun F t a G u e => by
    unfold Fl.ask at e
    cases h : f F with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

instance grows_onTape (g : Tape → Option (α × Tape)) : Grows (Fl.onTape g) :=
  Grows.of_same fun F t a G u e => by
    unfold Fl.onTape at e
    cases h : g t with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

/-- A step on the ledger that leads to a later one. -/
theorem Grows.change {f : Fork → Option Fork} (h : ∀ F G, f F = some G → Later F G) :
    Grows (Fl.change f) :=
  ⟨fun {F t a G u} e => by
    unfold Fl.change at e
    cases hf : f F with
    | none => simp [hf] at e
    | some H =>
      rw [hf] at e
      obtain rfl := (some_triple.mp e).2.1
      exact h F H hf⟩

/-- Taking slots leads to a later ledger. -/
theorem later_next (F : Fork) (n : Nat) : Later F { F with next := F.next + n } :=
  ⟨Nat.le_add_right _ _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩

instance grows_takeSlots (n : Nat) : Grows (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e => by
    obtain rfl := (some_triple.mp e).2.1
    exact later_next F n⟩

instance grows_hideRun (j : Nat) (v : Array E) (c : E) :
    Grows (Fl.change fun F => F.hideRun j v c) :=
  Grows.change fun _ _ h => OnBytes.PscRun.hideRun_keeps h

instance grows_lin (a : Aff) : Grows (Fl.change fun F => F.lin a) :=
  Grows.change fun _ _ h => OnBytes.PscRun.lin_later h

instance grows_read (n : Nat) : Grows (Fl.read n) := by unfold Fl.read; infer_instance
instance grows_readSum : Grows Fl.readSum := by unfold Fl.readSum; infer_instance
instance grows_answer (r : RoundName) : Grows (Fl.answer r) := by unfold Fl.answer; infer_instance
instance grows_point (r : RoundName) (n : Nat) : Grows (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance grows_batch (n : Nat) : Grows (Fl.batch n) := by unfold Fl.batch; infer_instance
instance grows_empty (r : RoundName) : Grows (Fl.empty r) := by unfold Fl.empty; infer_instance
instance grows_shown (j : Nat) : Grows (Fl.shown j) := by unfold Fl.shown; infer_instance
instance grows_publicPart (a : Aff) : Grows (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance

/-! ### Hidden values and the masked sumcheck -/

instance grows_claimsIn (n : Nat) : Grows (Fl.claimsIn n) := by unfold Fl.claimsIn; grows
instance grows_pscBeginAt (x : E) : Grows (Fl.pscBeginAt x) := by unfold Fl.pscBeginAt; grows
instance grows_pscBegin (C : Aff) : Grows (Fl.pscBegin C) := by unfold Fl.pscBegin; grows

instance grows_pscRound (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    Grows (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; grows

instance grows_roundIn (form : RoundForm) (p : Psc) (z : E) (d : Nat) :
    Grows (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; grows

instance grows_pscEnds (p : Psc) (d n : Nat) : Grows (Fl.pscEnds p d n) := by
  unfold Fl.pscEnds; grows

instance grows_pscRow (p : Psc) (S0 : E) (kept : Aff) : Grows (Fl.pscRow p S0 kept) := by
  unfold Fl.pscRow; grows

theorem grows_levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p : Psc),
    Grows (Fl.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Fl.levelRounds
    infer_instance
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine Grows.bind inferInstance fun _ => ?_
    refine Grows.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact grows_levelRounds mu rho order _ p'

instance (mu : Nat) (rho : Array E) (order : List Nat) (r : Array E) (p : Psc) :
    Grows (Fl.levelRounds mu rho order r p) := grows_levelRounds mu rho order r p

instance grows_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Grows (Fl.levelIn mu rho C order) := by
  unfold Fl.levelIn; grows

theorem grows_tscLoop : ∀ (zs : List E) (r : Array E) (p : Psc), Grows (Fl.tscLoop zs r p)
  | [], r, p => by
    unfold Fl.tscLoop
    infer_instance
  | z :: zs, r, p => by
    unfold Fl.tscLoop
    refine Grows.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact grows_tscLoop zs _ p'

instance (zs : List E) (r : Array E) (p : Psc) : Grows (Fl.tscLoop zs r p) := grows_tscLoop zs r p

instance grows_tscRounds (P : Array E) (lt : Nat) : Grows (Fl.tscRounds P lt) := by
  unfold Fl.tscRounds; grows

instance grows_tscIn (P : Array E) (lt n d : Nat) : Grows (Fl.tscIn P lt n d) := by
  unfold Fl.tscIn; grows

/-! ### The merge of the claims on the weights -/

theorem grows_wsForkRounds : ∀ (n : Nat) (rm : Array E) (p : Psc), Grows (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    infer_instance
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine Grows.bind inferInstance fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact grows_wsForkRounds n _ p'

instance (n : Nat) (rm : Array E) (p : Psc) : Grows (Fl.wsForkRounds n rm p) :=
  grows_wsForkRounds n rm p

instance grows_wsForkMerge (lk : Nat) (sv : Array Nat) : Grows (Fl.wsForkMerge lk sv) := by
  unfold Fl.wsForkMerge; grows

instance grows_flatForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    Grows (flatForkEnd lay cl sv) := by
  unfold flatForkEnd; grows

end OnBytes.Desc.First.Grow
