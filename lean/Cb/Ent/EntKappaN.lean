-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Ent/EntKappaN.lean: the link with a closing whose whole test is a tower: "each round's error is
within 1 / X, with w bits of work credited at the rounds that draw locations", from a plain record
of natural numbers: a check that can be decided. X is a natural number other than 0; it need not be
a power of 2 (why: the head of Cb/Ent/EntKappaX.lean).

Definitions (records of natural numbers with their checks; "the link has these numbers") and four
statements. For variable links, closings and towers: none is built here; nothing is evaluated. The
tower's records of numbers are Cb/Ld/LdKappaTowN.lean's (`StN`, `BsN`, `LdTowG.At`), their checks at
X are Cb/Ent/EntKappaX.lean's; this file adds the link's own five rounds and the bridge, in the same
manner. "At most 1 / X with the bits B" is `Err.BelowB` (Cb/Ld/LdKappaBits.lean): in each round
e ≤ X⁻¹ · (2^b · v), with e the error that the link lists for the round (a count), b the round's
entry of B, v the number of all values of the round's verifier message.

Main names:
  `LkN`: the numbers of the link's own rounds: nP positions of an encoded index; e₀, e₁ the radii
    and t₀, t₁ the numbers of locations of the two folds' tests; v fold variables; l coordinates of
    the last point; q = |E|; f₀, f₁ bounds from above for the two folds' error numbers; sE a bound
    from above for the sending's error number, sD the number of its seeds.
  `c.Ok w X`: four inequalities between natural numbers, with 2^w at the round of the locations.
  `c.Is P S ε₀ ε₁`: the link P with the sending S and the folds' numbers ε₀, ε₁ has these numbers:
    equations for cardinalities, radii and numbers of locations; bounds from above for the rest.
  `BrN`, `b.Ok X`, `b.Is K`: the bridge: a list L, exceptional seeds zE of zD: L · zE · X ≤ zD.
  `LinkN`: all numbers of a link: core, bridge, one `StN` for each stage that folds, a `BsN`.
  `N.Ok w X` (decidable), `N.Is P S ε₀ ε₁ K T`.
  `Spec.linkN_ok_mono`: Y ≤ X → `N.Ok w X` → `N.Ok w Y`.
  `Spec.entKappaN_core`: X ≠ 0 → `c.Is P S ε₀ ε₁` → `c.Ok w X` → `P.KapCW S ε₀ ε₁ w X⁻¹`.
  `Spec.entKappaN_seat`: X ≠ 0 → `N.Is P S ε₀ ε₁ K T` → `N.Ok w X` → that record and
    `K.run.KapTW T w X⁻¹`: the two fields on the link of `LdObjZ.KapW` (Cb/Ld/LdKappaW.lean).
  `Spec.entKappaN_link`: X ≠ 0, the closing's whole test is the tower T, `N.Is P S ε₀ ε₁ K T`,
    `N.Ok w X` → the errors that the link with that closing lists are at most 1 / X with the bits
    0 0 0 w 0, then 0 for the bridge, then the tower's (`T.bits w`).
Proofs: Cb/Ent/EntKappaNProofs.lean [not in this library; so here read: not proved in this library].

Limits: not that a link is sound at the numbers that it lists: these are data fields of a link. Not
that a link with given numbers exists. Nothing on the value of any number. Not that proof of work is
worth its bits, or that work belongs at these rounds. The bound is one round's: it is no bound on
the chance of a false proof and no sum over the rounds.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ent.EntKappaX
import Cb.Ld.LdKappaW

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR
open scoped ENNReal

/-- The numbers of the link's own five rounds. -/
structure LkN where
  /-- the positions of an encoded index -/
  nP : ℕ
  /-- the radius at which the first index's fold is tested, and the number of its locations -/
  e₀ : ℕ
  t₀ : ℕ
  /-- the same for the further index -/
  e₁ : ℕ
  t₁ : ℕ
  /-- the fold variables -/
  v : ℕ
  /-- the coordinates of the last point -/
  l : ℕ
  /-- the number of elements of the field -/
  q : ℕ
  /-- bounds from above for the error numbers of the two folds -/
  f₀ : ℕ
  f₁ : ℕ
  /-- a bound from above for the error number of the sending; the number of its seeds -/
  sE : ℕ
  sD : ℕ

/-- The check of the link's own rounds at the bound 1 / X: the fold's point; the sending's seed; the
locations, with 2^w; the last point. The sending's second round draws nothing. -/
def LkN.Ok (c : LkN) (w X : ℕ) : Prop :=
  (c.f₀ + c.f₁ + c.v * c.q ^ (c.v - 1)) * X ≤ c.q ^ c.v ∧
  c.sE * X ≤ c.sD ∧
  max ((c.nP - c.e₀ - 1) ^ c.t₀ * c.nP ^ c.t₁) (c.nP ^ c.t₀ * (c.nP - c.e₁ - 1) ^ c.t₁) * X ≤
    2 ^ w * (c.nP ^ c.t₀ * c.nP ^ c.t₁) ∧
  c.l * c.q ^ (c.l - 1) * X ≤ c.q ^ c.l

/-- The check of the link's own rounds can be decided. -/
instance LkN.decOk (c : LkN) (w X : ℕ) : Decidable (c.Ok w X) := by unfold LkN.Ok; infer_instance

/-- The bridge's numbers: a list; the exceptional seeds of its zero-evader, among all seeds. -/
structure BrN where
  /-- a bound from above for the list -/
  lst : ℕ
  /-- a bound from above for the exceptional seeds -/
  zE : ℕ
  /-- the number of seeds -/
  zD : ℕ

/-- The check of the bridge at the bound 1 / X. No work. -/
def BrN.Ok (b : BrN) (X : ℕ) : Prop := b.lst * b.zE * X ≤ b.zD

/-- The check of the bridge can be decided. -/
instance BrN.decOk (b : BrN) (X : ℕ) : Decidable (b.Ok X) := by unfold BrN.Ok; infer_instance

/-- All numbers of a link whose closing's whole test is a tower. -/
structure LinkN where
  /-- the link's own rounds -/
  core : LkN
  /-- the bridge -/
  br : BrN
  /-- the stages that fold, in order -/
  st : List StN
  /-- the base case -/
  base : BsN

/-- The check of all rounds at the bound 1 / X. -/
def LinkN.Ok (N : LinkN) (w X : ℕ) : Prop :=
  N.core.Ok w X ∧ N.br.Ok X ∧ (∀ s ∈ N.st, s.OkX w X) ∧ N.base.OkX w X

/-- The check of all rounds can be decided. -/
instance LinkN.decOk (N : LinkN) (w X : ℕ) : Decidable (N.Ok w X) := by
  unfold LinkN.Ok; infer_instance

section
variable {E ι κ' J Λ : Type} [Field E] [Fintype E] [Fintype ι] [Fintype κ'] [Fintype J]
  [Fintype Λ]

/-- The link P, with the sending S and the folds' error numbers ε₀, ε₁, has the numbers c. -/
structure LkN.Is (c : LkN) (P : LdLkP E ι κ' J Λ) (S : P.Snd) (ε₀ ε₁ : ℕ) : Prop where
  nP : Fintype.card ι = c.nP
  e₀ : P.e₀ = c.e₀
  t₀ : P.t₀ = c.t₀
  e₁ : P.e₁ = c.e₁
  t₁ : P.t₁ = c.t₁
  v  : P.D.X.v = c.v
  l  : P.D.l = c.l
  q  : Fintype.card E = c.q
  f₀ : ε₀ ≤ c.f₀
  f₁ : ε₁ ≤ c.f₁
  sE : ldSendFamErr P.N S.Sd S.L ≤ c.sE
  sD : Fintype.card S.Sd.D = c.sD

/-- The closing K has the bridge's numbers b. -/
structure BrN.Is (b : BrN) {P : LdLkP E ι κ' J Λ} (K : P.Cl) : Prop where
  lst : K.L ≤ b.lst
  zE  : K.Z.err ≤ b.zE
  zD  : Fintype.card K.Z.D = b.zD

/-- The link P with the closing K, whose tower is T, has the numbers N. -/
structure LinkN.Is (N : LinkN) (P : LdLkP E ι κ' J Λ) (S : P.Snd) (ε₀ ε₁ : ℕ) (K : P.Cl)
    (T : LdTowG K.G P.RowS (P.rows K.G K.all) K.Z) : Prop where
  core : N.core.Is P S ε₀ ε₁
  br   : N.br.Is K
  tow  : T.At N.st N.base

end

namespace Spec

/-- The check at X gives the check at every smaller number. -/
def linkN_ok_mono : Prop := ∀ (N : LinkN) (w X Y : ℕ), Y ≤ X → N.Ok w X → N.Ok w Y

/-- The link's own rounds: from the numbers to the record of Cb/Ld/LdKappaWorkObj.lean. -/
def entKappaN_core : Prop :=
  ∀ (E ι κ' J Λ : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ'] [Fintype J]
      [Fintype Λ] (P : LdLkP E ι κ' J Λ) (S : P.Snd) (ε₀ ε₁ : ℕ) (c : LkN) (w X : ℕ),
    X ≠ 0 → c.Is P S ε₀ ε₁ → c.Ok w X → P.KapCW S ε₀ ε₁ w (X : ℝ≥0∞)⁻¹

/-- The two records in which the library's record with work (`LdObjZ.KapW`, Cb/Ld/LdKappaW.lean)
speaks of the link: its own rounds; the closing's bridge and tower. -/
def entKappaN_seat : Prop :=
  ∀ (E ι κ' J Λ : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ'] [Fintype J]
      [Fintype Λ] (P : LdLkP E ι κ' J Λ) (S : P.Snd) (ε₀ ε₁ : ℕ) (K : P.Cl)
      (T : LdTowG K.G P.RowS (P.rows K.G K.all) K.Z) (N : LinkN) (w X : ℕ),
    X ≠ 0 → N.Is P S ε₀ ε₁ K T → N.Ok w X →
    P.KapCW S ε₀ ε₁ w (X : ℝ≥0∞)⁻¹ ∧ K.run.KapTW T w (X : ℝ≥0∞)⁻¹

/-- The whole link: every error that it lists is at most 1 / X with its bits. -/
def entKappaN_link : Prop :=
  ∀ (E ι κ' J Λ : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ'] [Fintype J]
      [Fintype Λ] (P : LdLkP E ι κ' J Λ)
      (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (S : P.Snd) (ε₀ ε₁ : ℕ) (K : P.Cl)
      (T : LdTowG K.G P.RowS (P.rows K.G K.all) K.Z) (d₂ : P.W2) (d : P.W0) (N : LinkN)
      (w X : ℕ),
    X ≠ 0 → K.T = T.toEnd → N.Is P S ε₀ ε₁ K T → N.Ok w X →
    Err.BelowB (P.linkC on0 on1 S ε₀ ε₁ (K.cZ d₂) d).P.err
      (lkBits w ++ ((0 :: T.bits w) ++ [])) (X : ℝ≥0∞)⁻¹

end Spec
end Cb
