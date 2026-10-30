-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeRep.lean: several codes of different lengths, read at common positions ("under a
repetition").

Coding theory: distance, list size and mutual correlated agreement of several linear codes whose
words a verifier queries at common positions. Definitions and statements (in `Cb.Spec`); the proofs
are in Cb/Gen/CodeRepProofs.lean; hiding is in Cb/Gen/CodeRepHides.lean.

A group is a plain family of codes with encoder C a (a : A), each with its own length, and for each
a table with its own rows R a. The prover encodes in each code by itself. The verifier reads them
together: there is one set P of long positions, and the long position x is read in the component a
at the position pos a x. Nothing new is encoded: the reading is a transformation of the oracles.
Distance, lists and mutual correlated agreement of the group are taken under the reading: they count
long positions.

Main names:
  `Reading C`: the data P, pos, mult. `Reading.Even`: every position of a is read exactly
    mult a > 0 times.
  `Reading.rep`: repetition, the reading with P = the numbers below a common multiple N of the
    lengths and pos a x = x mod (length of a). It is even for 0 < N (`Spec.rep_even`);
    `Reading.one` is even (`Spec.one_even`).
  `Reading.Off` to `Reading.Prox`: the notions under a reading T. Guard (`Spec.one_decodesTo` to
    `Spec.one_mcaAt`): for one code read as it stands four of them, `Reading.DecodesTo`, `OnCode`,
    `ListAt`, `MCAat`, are `Blocks.DecodesTo`, `Code.Enc.OnCode`, `Code.Enc.ListAt`,
    `Code.Enc.MCAat`.
  The lemmas, each for an even reading T. A long radius e is, as a fraction, the radius e / mult a
  of the component a (rounded down: radii count positions).
  `Spec.list_le_prod`: the list under T at e has at most the product of the components' list sizes
    at e / mult a.
  `Spec.mca_le_sum`: the number of exceptional θ under T at e is at most the sum of the components'
    at e / mult a; no further term.
  `Spec.dist_under`: two different families of messages differ under T at D long positions or more,
    if each code has its distance d (`HasDist`) and D ≤ mult a * (distance of a) for all a.
  `Spec.list_le_johnson`: so, under the hypotheses of its statement, the Johnson bound of
    Cb/Gen/JohnsonList.lean holds for the group, with the number of long positions and D: a second
    bound on the same list, which does not multiply.
  `Spec.prox_of_comps`, `Spec.prox_johnson_of_comps`: under the hypotheses of their statements, from
    `Enc.Prox` of the components (Cb/Gen/CodeList.lean) to `Reading.Prox` of the group.

Limits: a declared difference. In the paper that this protocol builds on (lean/CREDITS.md), an
oracle transformation is ANY local map from the family of words to one long word, and repetition is
one of them. Here a reading is a family of maps of positions: the long symbol at x is the family of
the
components' columns at pos a x. Repetition, the identity, and any pairing of such maps are covered;
a transformation that computes on symbols is not.
This file says nothing on erasure correction, on running times, on decoding functions or samples. No
proximity gap is proved, and none is assumed but as a hypothesis written in a statement:
`Spec.mca_le_sum`, `Spec.prox_of_comps` and `Spec.prox_johnson_of_comps` pass on what the components
have. This file says nothing on protocols. It says nothing on numerals.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.CodeList

set_option autoImplicit false

namespace Cb
open Prob

/-- A reading of a family of codes at common positions: the data. -/
structure Reading {F A : Type} (C : A → Code.Enc F) where
  /-- the long positions -/
  P : Type
  [finP : Fintype P]
  /-- where the long position x is read in the component a -/
  pos : ∀ a, P → Fin (C a).n
  /-- how often a position of the component a is read -/
  mult : A → ℕ

attribute [instance] Reading.finP

namespace Reading
variable {F A : Type} {C : A → Code.Enc F}

/-- Every position of the component a is read exactly mult a times, and mult a > 0. -/
def Even (T : Reading C) : Prop := ∀ a, 0 < T.mult a ∧ ∀ y, cnt (fun x => T.pos a x = y) = T.mult a

/-- One code, read as it stands. -/
def one (C₀ : Code.Enc F) : Reading (fun _ : Unit => C₀) where
  P := Fin C₀.n
  pos _ x := x
  mult _ := 1

/-- Repetition: N is a common multiple of the lengths; the long position x is read at x mod the
length. -/
def rep (C : A → Code.Enc F) (N : ℕ) (h : ∀ a, (C a).n ∣ N) : Reading C where
  P := Fin N
  pos a x := ⟨x.val % (C a).n, Nat.mod_lt _ (Nat.pos_of_dvd_of_pos (h a) x.pos)⟩
  mult a := N / (C a).n

variable [Field F] (T : Reading C) (E : Type) [Field E] [Algebra F E]

section
variable {R : A → Type}

/-- The long position x is off: in some component, the column read there is off. -/
def Off (f : ∀ a, R a → Fin (C a).n → E) (M : ∀ a, R a → Fin (C a).k → E) (x : T.P) : Prop :=
  ∃ a, Blocks.Off ((C a).GE E) (f a) (M a) (T.pos a x)

/-- Decoding under the reading: at most e long positions are off. -/
def DecodesTo (e : ℕ) (f : ∀ a, R a → Fin (C a).n → E) (M : ∀ a, R a → Fin (C a).k → E) : Prop :=
  cnt (T.Off E f M) ≤ e

/-- On the set S of long positions all rows of all components agree with codewords. -/
def OnCode (f : ∀ a, R a → Fin (C a).n → E) (S : Finset T.P) : Prop :=
  ∃ M : ∀ a, R a → Fin (C a).k → E,
    ∀ x ∈ S, ∀ a r, f a r (T.pos a x) = ((C a).GE E).mulVec (M a r) (T.pos a x)

end

variable [Finite A] [Finite E] (R : A → Type) [∀ a, Finite (R a)]

/-- A list under the reading: every family of tables decodes at e to at most L families of messages.
-/
def ListAt (e L : ℕ) : Prop :=
  ∀ f : ∀ a, R a → Fin (C a).n → E,
    cnt (fun M : ∀ a, R a → Fin (C a).k → E => T.DecodesTo E e f M) ≤ L

omit [Finite A] [∀ a, Finite (R a)] in
/-- Mutual correlated agreement on lines under the reading: one θ for all components. -/
def MCAat (e bad : ℕ) : Prop :=
  ∀ f₀ f₁ : ∀ a, R a → Fin (C a).n → E,
    cnt (fun θ : E =>
        ∃ S : Finset T.P,
          Fintype.card T.P ≤ S.card + e ∧
          T.OnCode E (fun a r j => f₀ a r j + θ * f₁ a r j) S ∧
          ¬ (T.OnCode E f₀ S ∧ T.OnCode E f₁ S)) ≤ bad

/-- List size and count of exceptional θ of the group as functions of the long radius, at the radii
with ok. -/
structure Prox (ok : ℕ → Prop) (L bad : ℕ → ℕ) : Prop where
  list : ∀ e, ok e → T.ListAt E R e (L e)
  mca  : ∀ e, ok e → T.MCAat E R e (bad e)

end Reading

namespace Spec
open Blocks

def one_even : Prop := ∀ (F : Type) (C₀ : Code.Enc F), (Reading.one C₀).Even

def rep_even : Prop :=
  ∀ (F A : Type) (C : A → Code.Enc F) (N : ℕ) (h : ∀ a, (C a).n ∣ N),
    0 < N → (Reading.rep C N h).Even

section
variable (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]

/-! The guard: one code, read as it stands. -/

def one_decodesTo : Prop :=
  ∀ (C₀ : Code.Enc F) (R₀ : Type) (e : ℕ) (f : R₀ → Fin C₀.n → E) (M : R₀ → Fin C₀.k → E),
    (Reading.one C₀).DecodesTo E (R := fun _ => R₀) e (fun _ => f) (fun _ => M) ↔
    DecodesTo (C₀.GE E) e f M

def one_onCode : Prop :=
  ∀ (C₀ : Code.Enc F) (R₀ : Type) (f : R₀ → Fin C₀.n → E) (S : Finset (Fin C₀.n)),
    (Reading.one C₀).OnCode E (R := fun _ => R₀) (fun _ => f) S ↔ C₀.OnCode E f S

def one_listAt [Finite E] : Prop :=
  ∀ (C₀ : Code.Enc F) (R₀ : Type) [Finite R₀] (e L : ℕ),
    (Reading.one C₀).ListAt E (fun _ => R₀) e L ↔ C₀.ListAt E R₀ e L

def one_mcaAt [Finite E] : Prop :=
  ∀ (C₀ : Code.Enc F) (R₀ : Type) [Finite R₀] (e bad : ℕ),
    (Reading.one C₀).MCAat E (fun _ => R₀) e bad ↔ C₀.MCAat E R₀ e bad

/-! The lemmas. -/

/-- What decodes under an even reading at e decodes in each component at e / mult a: at the same
fraction of its length. -/
def decodesTo_comp : Prop :=
  ∀ (A : Type) (C : A → Code.Enc F) (T : Reading C), T.Even →
    ∀ (R : A → Type) (e : ℕ) (f : ∀ a, R a → Fin (C a).n → E) (M : ∀ a, R a → Fin (C a).k → E),
      T.DecodesTo E e f M → ∀ a, DecodesTo ((C a).GE E) (e / T.mult a) (f a) (M a)

/-- For an even reading, the list of a group is at most the product of the components' lists. -/
def list_le_prod [Finite E] : Prop :=
  ∀ (A : Type) [Fintype A] (C : A → Code.Enc F) (T : Reading C), T.Even →
    ∀ (R : A → Type) [∀ a, Finite (R a)] (e : ℕ) (L : A → ℕ),
      (∀ a, (C a).ListAt E (R a) (e / T.mult a) (L a)) → T.ListAt E R e (∏ a, L a)

/-- For an even reading, the exceptional θ of a group are at most the sum of the components'. -/
def mca_le_sum [Finite E] : Prop :=
  ∀ (A : Type) [Fintype A] (C : A → Code.Enc F) (T : Reading C), T.Even →
    ∀ (R : A → Type) [∀ a, Finite (R a)] (e : ℕ) (bad : A → ℕ),
      (∀ a, (C a).MCAat E (R a) (e / T.mult a) (bad a)) → T.MCAat E R e (∑ a, bad a)

/-- The distance of a group under the reading. -/
def dist_under : Prop :=
  ∀ (A : Type) (C : A → Code.Enc F) (T : Reading C), T.Even → (∀ a, HasDist (C a).G (C a).d) →
    ∀ D : ℕ, (∀ a, D ≤ T.mult a * (C a).d) →
      ∀ (R : A → Type) (M M' : ∀ a, R a → Fin (C a).k → E), M ≠ M' →
        D ≤ cnt fun x =>
            ∃ a r,
              ((C a).GE E).mulVec (M a r) (T.pos a x) ≠ ((C a).GE E).mulVec (M' a r) (T.pos a x)

/-- The Johnson bound for a group, from its distance under the reading alone. (not all hypotheses
are named here: see the statement below) -/
def list_le_johnson [Finite E] : Prop :=
  ∀ (A : Type) [Finite A] (C : A → Code.Enc F) (T : Reading C), T.Even →
    (∀ a, HasDist (C a).G (C a).d) →
    ∀ D : ℕ, (∀ a, D ≤ T.mult a * (C a).d) →
      ∀ e : ℕ, InJohnson (Fintype.card T.P) D e →
        ∀ (R : A → Type) [∀ a, Finite (R a)], T.ListAt E R e (listMax (Fintype.card T.P) D e)

/-- From the components' functions to the group's. -/
def prox_of_comps [Finite E] : Prop :=
  ∀ (A : Type) [Fintype A] (C : A → Code.Enc F) (T : Reading C), T.Even →
    ∀ (R : A → Type) [∀ a, Finite (R a)] (ok : A → ℕ → Prop) (L bad : A → ℕ → ℕ → ℕ),
      (∀ a, (C a).Prox E (ok a) (L a) (bad a)) →
      T.Prox E R (fun e => ∀ a, ok a (e / T.mult a))
        (fun e => ∏ a, L a (e / T.mult a) (Nat.card (R a)))
        (fun e => ∑ a, bad a (e / T.mult a) (Nat.card (R a)))

/-- The same with the list bounded by the Johnson bound of the group. -/
def prox_johnson_of_comps [Finite E] : Prop :=
  ∀ (A : Type) [Fintype A] (C : A → Code.Enc F) (T : Reading C), T.Even →
    (∀ a, HasDist (C a).G (C a).d) →
    ∀ D : ℕ, (∀ a, D ≤ T.mult a * (C a).d) →
      ∀ (R : A → Type) [∀ a, Finite (R a)] (ok : A → ℕ → Prop) (L bad : A → ℕ → ℕ → ℕ),
        (∀ a, (C a).Prox E (ok a) (L a) (bad a)) →
        T.Prox E R (fun e => InJohnson (Fintype.card T.P) D e ∧ ∀ a, ok a (e / T.mult a))
          (fun e => listMax (Fintype.card T.P) D e)
          (fun e => ∑ a, bad a (e / T.mult a) (Nat.card (R a)))

end
end Spec
end Cb
