-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/ShapeKit.lean: basic definitions and lemmas for a list of rounds s ++ t.

The definitions `Tr.app`, `Tr.fst`, `Tr.snd`, `Rho.app`, `Strat.bind`, ... are in Iop/Shape.lean.
Here, for s ++ t: the verifier's randomness and the plain parts are pairs (for transcripts this is
in Iop/Shape.lean); runs of two strategies in a row; the positions of the prover's oracles and the
symbols there; and, for a single list s, rounds whose oracles are strings. Partial transcripts (at
the prover, at the verifier) are in Iop/State.lean.
-/
import Iop.Shape
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum

namespace Iop

/-! ## Verifier randomness, transcripts and strategies for s ++ t -/

namespace Rho

theorem app_fst_snd : ∀ {s t : Shape} (ρ : Rho (s ++ t)), app (fst ρ) (snd (s := s) ρ) = ρ
  | [], _, _ => rfl
  | _ :: s, _, (c, a) => by
      show (c, app (fst a) (snd (s := s) a)) = (c, a)
      rw [app_fst_snd a]

theorem fst_app : ∀ {s t : Shape} (a : Rho s) (b : Rho t), fst (app a b) = a
  | [], _, (), _ => rfl
  | _ :: _, _, (c, a), b => by
      show (c, fst (app a b)) = (c, a)
      rw [fst_app a b]

theorem snd_app : ∀ {s t : Shape} (a : Rho s) (b : Rho t), snd (s := s) (app a b) = b
  | [], _, _, _ => rfl
  | _ :: s, _, (_, a), b => snd_app (s := s) a b

/-- The verifier's randomness for s ++ t is a pair. -/
def appEquiv (s t : Shape) : Rho s × Rho t ≃ Rho (s ++ t) where
  toFun p := app p.1 p.2
  invFun ρ := (fst ρ, snd (s := s) ρ)
  left_inv p := Prod.ext (fst_app p.1 p.2) (snd_app p.1 p.2)
  right_inv ρ := app_fst_snd ρ

/-- The set of all ρ for s ++ t whose first part is in S. -/
def cylFst {s : Shape} (t : Shape) (S : Set (Rho s)) : Set (Rho (s ++ t)) := {ρ | fst ρ ∈ S}

/-- The set of all ρ for s ++ t whose second part is in S. -/
def cylSnd (s : Shape) {t : Shape} (S : Set (Rho t)) : Set (Rho (s ++ t)) :=
  {ρ | snd (s := s) ρ ∈ S}

end Rho

namespace Tr

theorem rho_app : ∀ {s t : Shape} (a : Tr s) (b : Tr t), rho (app a b) = Rho.app (rho a) (rho b)
  | [], _, _, _ => rfl
  | _ :: _, _, (_, c, a), b => by
      show (c, rho (app a b)) = (c, Rho.app (rho a) (rho b))
      rw [rho_app a b]

theorem rho_fst : ∀ {s t : Shape} (τ : Tr (s ++ t)), rho (fst τ) = Rho.fst (rho τ)
  | [], _, _ => rfl
  | _ :: _, _, (_, c, a) => by
      show (c, rho (fst a)) = (c, Rho.fst (rho a))
      rw [rho_fst a]

theorem rho_snd : ∀ {s t : Shape} (τ : Tr (s ++ t)), rho (snd (s := s) τ) = Rho.snd (s := s) (rho τ)
  | [], _, _ => rfl
  | _ :: s, _, (_, _, a) => rho_snd (s := s) a

end Tr

namespace Strat

/-- A run of two strategies in a row: the first runs on the first part of ρ; its result starts the
second, which runs on the second part; the transcripts are concatenated. -/
theorem run_bind :
    ∀ {s t : Shape} {β γ : Type} (σ : Strat s β) (g : β → Strat t γ) (ρ : Rho (s ++ t)),
      run (bind σ g) ρ =
        (Tr.app (run σ (Rho.fst ρ)).1 (run (g (run σ (Rho.fst ρ)).2) (Rho.snd (s := s) ρ)).1,
          (run (g (run σ (Rho.fst ρ)).2) (Rho.snd (s := s) ρ)).2)
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, _, _, _, (m, k), g, (c, ρ) => by
      have h := run_bind (k c) g ρ
      show ((m, c, (run (bind (k c) g) ρ).1), (run (bind (k c) g) ρ).2) =
        ((m, c,
            Tr.app (run (k c) (Rho.fst ρ)).1
              (run (g (run (k c) (Rho.fst ρ)).2) (Rho.snd (s := s) ρ)).1),
          (run (g (run (k c) (Rho.fst ρ)).2) (Rho.snd (s := s) ρ)).2)
      rw [h]

theorem run_map : ∀ {s : Shape} {β γ : Type} (g : β → γ) (σ : Strat s β) (ρ : Rho s),
    run (map g σ) ρ = ((run σ ρ).1, g (run σ ρ).2)
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, _, g, (m, k), (c, ρ) => by
      have h := run_map g (k c) ρ
      show ((m, c, (run (map g (k c)) ρ).1), (run (map g (k c)) ρ).2) =
        ((m, c, (run (k c) ρ).1), g (run (k c) ρ).2)
      rw [h]

/-- The challenges in the transcript of a run are the given ones. -/
theorem rho_run : ∀ {s : Shape} {β : Type} (σ : Strat s β) (ρ : Rho s), Tr.rho (run σ ρ).1 = ρ
  | [], _, _, () => rfl
  | _ :: _, _, (_, k), (c, ρ) => by
      show (c, Tr.rho (run (k c) ρ).1) = (c, ρ)
      rw [rho_run (k c) ρ]

end Strat


/-! ## The number of values of the verifier's randomness -/

theorem card_rho_app (s t : Shape) :
    Fintype.card (Rho (s ++ t)) = Fintype.card (Rho s) * Fintype.card (Rho t) := by
  rw [← Fintype.card_prod]
  exact (Fintype.card_congr (Rho.appEquiv s t)).symm

/-! ## Plain parts for s ++ t -/

namespace Plains

def app : {s t : Shape} → Plains s → Plains t → Plains (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (m, a), b => (m, app a b)

def fst : {s t : Shape} → Plains (s ++ t) → Plains s
  | [], _, _ => ()
  | _ :: _, _, (m, a) => (m, fst a)

def snd : {s t : Shape} → Plains (s ++ t) → Plains t
  | [], _, b => b
  | _ :: s, _, (_, a) => snd (s := s) a

theorem app_fst_snd : ∀ {s t : Shape} (π : Plains (s ++ t)), app (fst π) (snd (s := s) π) = π
  | [], _, _ => rfl
  | _ :: s, _, (m, a) => by
      show (m, app (fst a) (snd (s := s) a)) = (m, a)
      rw [app_fst_snd a]

theorem fst_app : ∀ {s t : Shape} (a : Plains s) (b : Plains t), fst (app a b) = a
  | [], _, (), _ => rfl
  | _ :: _, _, (m, a), b => by
      show (m, fst (app a b)) = (m, a)
      rw [fst_app a b]

theorem snd_app : ∀ {s t : Shape} (a : Plains s) (b : Plains t), snd (s := s) (app a b) = b
  | [], _, _, _ => rfl
  | _ :: s, _, (_, a), b => snd_app (s := s) a b

end Plains

namespace Tr

theorem plains_app :
    ∀ {s t : Shape} (a : Tr s) (b : Tr t), plains (app a b) = Plains.app (plains a) (plains b)
  | [], _, _, _ => rfl
  | _ :: _, _, (m, _, a), b => by
      show (m.2, plains (app a b)) = (m.2, Plains.app (plains a) (plains b))
      rw [plains_app a b]

theorem plains_fst : ∀ {s t : Shape} (τ : Tr (s ++ t)), plains (fst τ) = Plains.fst (plains τ)
  | [], _, _ => rfl
  | _ :: _, _, (m, _, a) => by
      show (m.2, plains (fst a)) = (m.2, Plains.fst (plains a))
      rw [plains_fst a]

theorem plains_snd :
    ∀ {s t : Shape} (τ : Tr (s ++ t)), plains (snd (s := s) τ) = Plains.snd (s := s) (plains τ)
  | [], _, _ => rfl
  | _ :: s, _, (_, _, a) => plains_snd (s := s) a

end Tr

/-! ## Positions of the prover's oracles for s ++ t, and what is there

A position of s ++ t is a position of s or a position of t. The alphabet at a position of the whole
is the alphabet at the position of the part, but only after the list has been taken apart; so
symbols are carried over by the maps OSym.ofLeft and OSym.ofRight, which are the identity at every
concrete position, and no cast appears in a statement. -/

namespace OPos

/-- A position of the first part, as a position of the whole. -/
def left : {s t : Shape} → OPos s → OPos (s ++ t)
  | _ :: _, _, .inl p => .inl p
  | _ :: _, _, .inr p => .inr (left p)

/-- A position of the second part, as a position of the whole. -/
def right : {s t : Shape} → OPos t → OPos (s ++ t)
  | [], _, p => p
  | _ :: s, _, p => .inr (right (s := s) p)

/-- To which part a position belongs. -/
def split : {s t : Shape} → OPos (s ++ t) → OPos s ⊕ OPos t
  | [], _, p => .inr p
  | _ :: _, _, .inl p => .inl (.inl p)
  | _ :: s, _, .inr p => (split (s := s) p).map .inr id

theorem split_left : ∀ {s t : Shape} (p : OPos s), split (left (t := t) p) = .inl p
  | _ :: _, _, .inl _ => rfl
  | r :: s, t, .inr p => by
      show (split (s := s) (left (t := t) p)).map (Sum.inr (α := r.Pos)) id = Sum.inl (Sum.inr p)
      rw [split_left p]
      rfl

theorem split_right : ∀ {s t : Shape} (p : OPos t), split (right (s := s) p) = .inr p
  | [], _, _ => rfl
  | r :: s, _, p => by
      show (split (s := s) (right (s := s) p)).map (Sum.inr (α := r.Pos)) id = Sum.inr p
      rw [split_right (s := s) p]
      rfl

theorem elim_split :
    ∀ {s t : Shape} (p : OPos (s ++ t)), Sum.elim left (right (s := s)) (split (s := s) p) = p
  | [], _, _ => rfl
  | _ :: _, _, .inl _ => rfl
  | r :: s, t, .inr p => by
      have h := elim_split (s := s) p
      show Sum.elim left (right (s := r :: s)) ((split (s := s) p).map (Sum.inr (α := r.Pos)) id) =
        Sum.inr p
      cases hp : split (s := s) p with
      | inl q =>
          rw [hp] at h
          show (Sum.inr (left q) : r.Pos ⊕ OPos (s ++ t)) = .inr p
          exact congrArg Sum.inr h
      | inr q =>
          rw [hp] at h
          show (Sum.inr (right (s := s) q) : r.Pos ⊕ OPos (s ++ t)) = .inr p
          exact congrArg Sum.inr h

theorem left_injective {s t : Shape} : Function.Injective (left (s := s) (t := t)) := fun p q h =>
  Sum.inl.inj ((split_left (t := t) p).symm.trans
    ((congrArg (split (s := s)) h).trans (split_left q)))

theorem right_injective {s t : Shape} : Function.Injective (right (s := s) (t := t)) := fun p q h =>
  Sum.inr.inj ((split_right (s := s) p).symm.trans
    ((congrArg (split (s := s)) h).trans (split_right q)))

theorem left_ne_right {s t : Shape} (p : OPos s) (q : OPos t) :
    left (t := t) p ≠ right (s := s) q := fun h => by
  have h' :=
    (split_left (t := t) p).symm.trans ((congrArg (split (s := s)) h).trans (split_right q))
  cases h'

end OPos

namespace OSym

/-- A symbol at a position of the first part, read in the whole, as a symbol of the first part. -/
def ofLeft : {s t : Shape} → (p : OPos s) → OSym (s ++ t) (OPos.left p) → OSym s p
  | _ :: _, _, .inl _, a => a
  | _ :: _, _, .inr p, a => ofLeft p a

/-- A symbol at a position of the second part, read in the whole, as a symbol of the second part. -/
def ofRight : {s t : Shape} → (p : OPos t) → OSym (s ++ t) (OPos.right (s := s) p) → OSym t p
  | [], _, _, a => a
  | _ :: s, _, p, a => ofRight (s := s) p a

theorem ofLeft_injective : ∀ {s t : Shape} (p : OPos s), Function.Injective (ofLeft (t := t) p)
  | _ :: _, _, .inl _ => fun _ _ h => h
  | _ :: _, _, .inr p => ofLeft_injective p

theorem ofRight_injective : ∀ {s t : Shape} (p : OPos t), Function.Injective (ofRight (s := s) p)
  | [], _, _ => fun _ _ h => h
  | _ :: s, _, p => ofRight_injective (s := s) p

end OSym

namespace Tr

/-- What is in the whole transcript at a position of the first part is what is there in the first
part. -/
theorem read_left :
    ∀ {s t : Shape} (τ : Tr (s ++ t)) (p : OPos s),
      OSym.ofLeft p (read τ (OPos.left p)) = read (fst τ) p
  | _ :: _, _, (_, _, _), .inl _ => rfl
  | _ :: _, _, (_, _, a), .inr p => read_left a p

/-- What is in the whole transcript at a position of the second part is what is there in the second
part. -/
theorem read_right : ∀ {s t : Shape} (τ : Tr (s ++ t)) (p : OPos t),
    OSym.ofRight (s := s) p (read τ (OPos.right (s := s) p)) = read (snd (s := s) τ) p
  | [], _, _, _ => rfl
  | _ :: s, _, (_, _, a), p => read_right (s := s) a p

/-- Two transcripts agree at a position of the first part if and only if their first parts agree
there. -/
theorem read_left_eq_iff {s t : Shape} (τ τ' : Tr (s ++ t)) (p : OPos s) :
    read τ (OPos.left p) = read τ' (OPos.left p) ↔ read (fst τ) p = read (fst τ') p := by
  rw [← read_left τ p, ← read_left τ' p]
  exact (OSym.ofLeft_injective p).eq_iff.symm

/-- Two transcripts agree at a position of the second part if and only if their second parts agree
there. -/
theorem read_right_eq_iff {s t : Shape} (τ τ' : Tr (s ++ t)) (p : OPos t) :
    read τ (OPos.right (s := s) p) = read τ' (OPos.right (s := s) p) ↔
    read (snd (s := s) τ) p = read (snd (s := s) τ') p := by
  rw [← read_right τ p, ← read_right τ' p]
  exact (OSym.ofRight_injective p).eq_iff.symm

end Tr

/-! ## Rounds all of whose oracles are strings -/

namespace Shape.IsPoint



/-- Rounds whose oracles are strings have finitely many positions. -/
@[reducible] def fintypeOPos : {s : Shape} → s.IsPoint → Fintype (OPos s)
  | [], _ => inferInstanceAs (Fintype Empty)
  | r :: s, (h, a) => by
      haveI := h.finPos
      haveI := fintypeOPos a
      exact inferInstanceAs (Fintype (r.Pos ⊕ OPos s))

/-- Equality of their positions can be decided. -/
@[reducible] def decEqOPos : {s : Shape} → s.IsPoint → DecidableEq (OPos s)
  | [], _ => inferInstanceAs (DecidableEq Empty)
  | r :: s, (h, a) => by
      haveI := h.decPos
      haveI := decEqOPos a
      exact inferInstanceAs (DecidableEq (r.Pos ⊕ OPos s))

end Shape.IsPoint

end Iop
