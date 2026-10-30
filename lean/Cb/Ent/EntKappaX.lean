-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Ent/EntKappaX.lean: a whole test as a tower, "each round's error is within 1 / X, with w
bits of work credited at the rounds that draw locations", for a natural number X that need not be a
power of 2; and what is gained by an X above 2^x.

Definitions and statements. Cb/Ld/LdKappaTowN.lean has the checks `StN.Ok w x`, `BsN.Ok w x` of a
tower's numbers, with the bound 2^-x. This file has the same checks with X in the place of 2^x, and
the same five steps from the checks to the tower's record `T.KapW w κ`
(Cb/Ld/LdKappaWorkObj.lean), at κ = 1 / X. The records of numbers (`StN`, `BsN`) and "the tower has
these numbers" (`StN.Is`, `BsN.Is`, `LdTowC.At`, `LdTowG.At`) are that file's, unchanged. For
variable towers: none is built here; nothing is evaluated. Here the check is said on a tower's
record of numbers.

Why. Where the verifier's messages are made from hash blocks, the library's pass multiplies the
bound c of every round by a factor above 1: `Err.BelowG.pull` gives κ · c and `grindDrawsSound`
gives κ₀^K · c (Iop/GrindPull.lean), with K the largest number of blocks of a round and
κ₀ = 1 + 2^-sl = `Iop.kapSl sl` (Iop/DrawOf.lean). From c = 2^-x one gets κ₀^K · 2^-x, which is more
than 2^-x. If the numbers pass their check at an X above 2^x, then from c = 1 / X one gets
κ₀^K / X, and that is at most 2^-x as long as κ₀^K ≤ X / 2^x.

Main names:
  `Spec.kapX`: X ≠ 0 → e · X ≤ 2^w · v → e ≤ X⁻¹ · (2^w · v), in the extended nonnegative reals;
    `Spec.kapX0`: the same without 2^w.
  `s.OkX w X`, `B.OkX w X`: the checks of a stage and of the base case (decidable).
  `Spec.okX_pow`: at X = 2^x they are the library's checks `s.Ok w x`, `B.Ok w x`.
  `Spec.okX_mono`: Y ≤ X → the checks at X give the checks at Y.
  `Spec.ldKappaX_fold`, `Spec.ldKappaX_sw`, `Spec.ldKappaX_base`: one fold, one code switch, the
    base case. `Spec.ldKappaX_towC`, `Spec.ldKappaX_towG`: X ≠ 0 → `T.At L B` → every s in L has
    `s.OkX w X` → `B.OkX w X` → `T.KapW w X⁻¹`.
  `Spec.room_spend`: 2^x · (2^e + 1) ≤ X · 2^e (that is, X ≥ 2^x · (1 + 2^-e)) → c ≤ 1 + 2^-e →
    c · X⁻¹ ≤ 2^-x.
  `Spec.room_blocks`: the same X, K · 2^(e + 1) ≤ 2^sl → (1 + 2^-sl)^K · X⁻¹ ≤ 2^-x.
Proofs: Cb/Ent/EntKappaXProofs.lean [not in this library; so here read: not proved in this library].

Limits: not that a tower with given numbers exists, or that it is sound at the numbers that it
lists. Nothing on the value of any number. Not that proof of work is worth its bits. The bound is
one round's: it is no bound on the chance of a false proof and no sum over the rounds.
`room_spend` and `room_blocks` are inequalities between numbers: no sampler and no pass stands
here, and nothing says how many blocks a round of any protocol has. The library's pass has one bound
c for all its lists of errors: the room of one list can be spent only if the others are at a bound
c with κ₀^K · c ≤ 2^-x too.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaTowN
import Iop.DrawKap

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR
open scoped ENNReal

/-- The check of one stage at the bound 1 / X: the fold's first round; its further rounds; the code
switch's two rounds, with 2^w at the second, which draws locations. -/
def StN.OkX (s : StN) (w X : ℕ) : Prop :=
  s.lst * X ≤ s.nCh ∧
  (s.bC + (s.bZ + s.bW) + s.lst * s.deg) * X ≤ s.nCh ∧
  s.lNext.choose 2 * s.zoE * X ≤ s.zoD ∧
  ((s.nP - s.e - 1) ^ s.ts * s.zbD + s.nP ^ s.ts * (s.lNext * s.zbE)) * X ≤
    2 ^ w * (s.nP ^ s.ts * s.zbD)

/-- The check of one stage can be decided. -/
instance StN.decOkX (s : StN) (w X : ℕ) : Decidable (s.OkX w X) := by
  unfold StN.OkX; infer_instance

/-- The check of the base case at the bound 1 / X: its first round; its second, which draws
locations, with 2^w. -/
def BsN.OkX (B : BsN) (w X : ℕ) : Prop :=
  (B.bad + B.l2) * X ≤ B.q ∧ (B.nP - B.e - 1) ^ B.t * X ≤ 2 ^ w * B.nP ^ B.t

/-- The check of the base case can be decided. -/
instance BsN.decOkX (B : BsN) (w X : ℕ) : Decidable (B.OkX w X) := by
  unfold BsN.OkX; infer_instance

namespace Spec

/-- From an inequality between natural numbers to the bound 1 / X, with 2^w. -/
def kapX : Prop :=
  ∀ (e v X w : ℕ), X ≠ 0 → e * X ≤ 2 ^ w * v →
    (e : ℝ≥0∞) ≤ (X : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) ^ w * (v : ℝ≥0∞))

/-- The same without 2^w. -/
def kapX0 : Prop :=
  ∀ (e v X : ℕ), X ≠ 0 → e * X ≤ v → (e : ℝ≥0∞) ≤ (X : ℝ≥0∞)⁻¹ * (v : ℝ≥0∞)

/-- At X = 2^x the checks are the library's. -/
def okX_pow : Prop :=
  (∀ (s : StN) (w x : ℕ), s.OkX w (2 ^ x) ↔ s.Ok w x) ∧
  ∀ (B : BsN) (w x : ℕ), B.OkX w (2 ^ x) ↔ B.Ok w x

/-- The checks at X give the checks at every smaller number. -/
def okX_mono : Prop :=
  (∀ (s : StN) (w X Y : ℕ), Y ≤ X → s.OkX w X → s.OkX w Y) ∧
  ∀ (B : BsN) (w X Y : ℕ), Y ≤ X → B.OkX w X → B.OkX w Y

/-- A fold with the numbers s. -/
def ldKappaX_fold : Prop :=
  ∀ (E P P' : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (s : StN) (Y : SumPar E P) (S : LdSwD Y P') (e : ℕ) (Lst mC mS mW : ℕ → ℕ) (L w X : ℕ),
    X ≠ 0 → s.Is Y S e Lst mC mS mW L → s.OkX w X → Y.Kap Lst mC mS mW (X : ℝ≥0∞)⁻¹

/-- The code switch after it. -/
def ldKappaX_sw : Prop :=
  ∀ (E P P' : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (s : StN) (Y : SumPar E P) (S : LdSwD Y P') (e : ℕ) (Lst mC mS mW : ℕ → ℕ) (L w X : ℕ),
    X ≠ 0 → s.Is Y S e Lst mC mS mW L → s.OkX w X → (S.D e).KapW e L w (X : ℝ≥0∞)⁻¹

/-- The base case. -/
def ldKappaX_base : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (B : BsN) (a : LdJoint E) (t bad L2 w X : ℕ),
    X ≠ 0 → B.Is a t bad L2 → B.OkX w X → a.KapBW t bad L2 w (X : ℝ≥0∞)⁻¹

/-- A tower. -/
def ldKappaX_towC : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (w X : ℕ) (B : BsN), X ≠ 0 → B.OkX w X →
    ∀ (a : LdJoint E) (T : LdTowC a) (Ls : List StN),
      T.At Ls B → (∀ s ∈ Ls, s.OkX w X) → T.KapW w (X : ℝ≥0∞)⁻¹

/-- A tower on a group's complex. -/
def ldKappaX_towG : Prop :=
  ∀ (E B' : Type) [Field E] [Fintype E] [Fintype B'] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sb : B' → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B')) (w X : ℕ)
      (B : BsN), X ≠ 0 → B.OkX w X →
    ∀ (T : LdTowG G Sb sl Z) (Ls : List StN),
      T.At Ls B → (∀ s ∈ Ls, s.OkX w X) → T.KapW w (X : ℝ≥0∞)⁻¹

/-- What an X above 2^x is good for: the bound 1 / X, times a factor of at most 1 + 2^-e, is at most
2^-x. -/
def room_spend : Prop :=
  ∀ (X x e : ℕ) (c : ℝ≥0∞), 2 ^ x * (2 ^ e + 1) ≤ X * 2 ^ e → c ≤ 1 + ((2 : ℝ≥0∞) ^ e)⁻¹ →
    c * (X : ℝ≥0∞)⁻¹ ≤ ((2 : ℝ≥0∞) ^ x)⁻¹

/-- The factor of K hash blocks with the bias 1 + 2^-sl each is such a factor. -/
def room_blocks : Prop :=
  ∀ (X x e sl K : ℕ), 2 ^ x * (2 ^ e + 1) ≤ X * 2 ^ e → K * 2 ^ (e + 1) ≤ 2 ^ sl →
    kapSl sl ^ K * (X : ℝ≥0∞)⁻¹ ≤ ((2 : ℝ≥0∞) ^ x)⁻¹

end Spec
end Cb
