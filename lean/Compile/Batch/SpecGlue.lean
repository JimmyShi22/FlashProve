-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecGlue.lean: privacy at the level of challengers, for batches of any size and any
scheme (`[Inhabited IVK]`, `[Inhabited Pf]`). Definitions and statements. Proofs:
Compile/Batch/GluePrivacy.lean. (Words of this library: lean/GLOSSARY.md.)

The step from the privacy experiment of the definition [ZKCP/Defs.lean;
ZKCP/Gen.lean] to one adversary that interacts with a challenger (`World`). No hashing and no
protocol occurs here: everything is generic in the family S of oracles, in the argument system A =
(C, P, V) and in the bound B on the size of a batch.

  `GCall`, `GIn`   the calls and replies of the real experiment: "setup", which returns ivk, and
                   "batch b", with the batch as the environment names it (instance, witness, own
                   flag), which returns the proofs of the adversary's own slots, in order
  `realW`, `GAdm`   the real challenger; admissible adversaries: see their doc comments
  `SCall`   the calls that a simulating challenger receives: "setup", and "prove xs", where xs are
            the instances of the adversary's own slots. So a simulating challenger is blind by type:
            it is never given the other slots, their number, or a witness
  `asW`   a simulating challenger with the calls of the real experiment: "batch b" becomes "prove
          b.ownX"
  `Spec.gluePrivacyWith`   if Sm is consistent (`World.Consistent`) (IVK and Pf inhabited),
                           closeness to `asW Sm` for all admissible adversaries (`Close`) gives
                           `Gen.HasIndexPrivacyWith` for the named simulator `simOf Sm s₀`

Counts. A batch is one call, whatever its size, and "setup" is one call: an adversary with n batches
has `TotalBound t (n + 1)`. So the number N of batches in the experiment of ZKCP/Gen.lean is the n
of `Close`, and ζ t n is that experiment's ζ tV N.

Notation: `s₀`: in `Sm.σ` (in `Close`: `G.σ`): a state of the challenger (`World`, Rom/World.lean);
`t`, `n`: natural numbers: in `Close`: `D.TotalBound t (n + 1)`; `tV`, `N`: natural numbers, binders
of `Gen.PrivacyFor` (ZKCP/Gen.lean): `(Vt ivk).QueryBound tV`; "N counts batches"; pp: in `PP`: the
first argument of `Gen.Simulator.init` (ZKCP/Gen.lean); the environment: a `Gen.ViewEnv`
(ZKCP/Gen.lean).
-/
import ZKCP.Gen
import Rom.World

noncomputable section

namespace Compile.GlueB

open Rom Prob ZKCP
open scoped ENNReal

variable {S : OSpec} {I X Wn PP IVK ISK Pf : Type}

/-! ## The real experiment as a challenger -/

/-- the calls of the real experiment -/
inductive GCall (X Wn : Type) : Type
  | setup : GCall X Wn
  | batch (b : Gen.Batch X Wn) : GCall X Wn

/-- the replies: ivk, or the proofs of the adversary's own slots, in order -/
abbrev GIn (IVK Pf : Type) : Type := IVK ⊕ List Pf

/-- the proofs of the adversary's own slots, in order -/
def ownPf (b : Gen.Batch X Wn) (πs : List Pf) : List Pf :=
  ((b.zip πs).filter fun s => s.1.2.2).map fun s => s.2

/-- The real challenger. Its private state is isk. Before "setup" a batch releases nothing. -/
def realW (A : Gen.Arg S I X Wn IVK ISK Pf) (i : I) : World S (GCall X Wn) (GIn IVK Pf) :=
  World.ofOComp (τ := Option ISK) fun s c => match c, s with
    | .setup, _ => (A.C i).bind fun o => pure (.inl o.1, some o.2)
    | .batch _, none => pure (.inr [], none)
    | .batch b, some k => (A.P k b.pairs).bind fun πs => pure (.inr (ownPf b πs.val), some k)

/-- Admissible: one "setup", first (the flag says whether it has been made); then at most n batches,
each allowed. -/
def GAdm {α : Type} (ok : Gen.Batch X Wn → Prop) :
    Adv S (GCall X Wn) (GIn IVK Pf) α → Bool → ℕ → Prop
  | .halt _, _, _ => True
  | .sample _ k, b, n => ∀ r, GAdm ok (k r) b n
  | .query _ _ k, b, n => ∀ r, GAdm ok (k r) b n
  | .call .setup k, b, n => b = false ∧ ∀ a, GAdm ok (k a) true n
  | .call (.batch _) _, _, 0 => False
  | .call (.batch c) k, b, n + 1 => b = true ∧ ok c ∧ ∀ a, GAdm ok (k a) b n

/-! ## Simulating challengers -/

/-- the calls that a simulating challenger receives -/
inductive SCall (X : Type) : Type
  | setup : SCall X
  | prove (xs : List X) : SCall X

/-- what a simulating challenger is told of a call -/
def forget : GCall X Wn → SCall X
  | .setup => .setup
  | .batch b => .prove b.ownX

/-- A simulating challenger with the calls of the real experiment. -/
def asW (Wn : Type) (Sm : World S (SCall X) (GIn IVK Pf)) : World S (GCall X Wn) (GIn IVK Pf) where
  σ := Sm.σ
  answer := Sm.answer
  reply := fun s c => Sm.reply s (forget c)

/-- Fixed values replace replies that do not have the expected form. The real challenger never gives
such a reply. -/
def ivkOf [Inhabited IVK] : GIn IVK Pf → IVK
  | .inl v => v
  | .inr _ => default

def listOf : GIn IVK Pf → List Pf
  | .inl _ => []
  | .inr l => l

/-- one proof for each instance: the list, cut or filled up with a fixed value -/
def fit [Inhabited Pf] (xs : List X) (l : List Pf) : Gen.Slots Pf xs :=
  ⟨(List.range xs.length).map fun n => l.getD n default, by simp⟩

/-- The simulator of the definition: its state is the state of the challenger; ivk is the
challenger's reply to "setup"; oracle queries are answered by the challenger; for a batch it passes
the instances that it is given to the challenger. It uses neither pp nor N. -/
def simOf [Inhabited IVK] [Inhabited Pf] (PP : Type)
    (Sm : World S (SCall X) (GIn IVK Pf)) (s₀ : Sm.σ) :
    Gen.Simulator S PP IVK X Pf where
  St := Sm.σ
  init := fun _ _ => (Sm.reply s₀ .setup).map fun a => (ivkOf a.1, a.2)
  answer := Sm.answer
  prove := fun s xs => (Sm.reply s (.prove xs)).map fun a => (fit xs (listOf a.1), a.2)


/-! ## The statements -/

/-- every admissible adversary (`GAdm`, each batch a `Gen.ValidBatch R B i`) with at most t queries
and n batches has, up to ζ t n, the same output with the real challenger on i and with G, for every
i -/
def Close (R : Gen.RelPair I X Wn PP) (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ)
    (G : World S (GCall X Wn) (GIn IVK Pf)) (s₀ : G.σ) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (i : I) (α : Type) (D : Adv S (GCall X Wn) (GIn IVK Pf) α) (t n : ℕ), D.TotalBound t (n + 1) →
    GAdm (fun b => Gen.ValidBatch R B i b.pairs) D false n →
    tv ((interact (realW A i) D (none, Table.empty _)).map Prod.fst)
        ((interact G D s₀).map Prod.fst) ≤ ζ t n

/-- From challengers to the definition, simulator named, if Sm is consistent.
(not all hypotheses are named here: see the statement below) -/
def Spec.gluePrivacyWith : Prop :=
  ∀ (S : OSpec) (I X Wn PP IVK ISK Pf : Type) [Inhabited IVK] [Inhabited Pf]
      (R : Gen.RelPair I X Wn PP) (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ)
      (Sm : World S (SCall X) (GIn IVK Pf)) (s₀ : Sm.σ) (ζ : ℕ → ℕ → ℝ≥0∞),
    Sm.Consistent → Close R A B (asW Wn Sm) s₀ ζ → Gen.HasIndexPrivacyWith R A B (simOf PP Sm s₀) ζ

end Compile.GlueB
