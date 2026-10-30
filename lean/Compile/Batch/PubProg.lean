-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubProg.lean: the first experiments of zero-knowledge compilation for batches, for any
program in the place of the prover's. Definitions only, but for one equality by rfl (words of this
library: lean/GLOSSARY.md).

Compile/Batch/PubChall.lean has the experiments for the scheme whose committer publishes pw ivk
(keyOf isk) and whose prover is the program `Pp` of Compile/Batch/Star.lean. Here the prover's
program is a parameter pq k fr xs (the key with tokens; for which requests a proof string is made;
the instances) so that the same definitions serve the prover with no query for an empty slot (`PpU`,
Compile/Batch/StarU.lean) and others.

  `MaskProg pq`  As far as the reply to a batch goes, the program that makes proof strings for the
                 adversary's own requests only is the same oracle algorithm (`erase`) as the
                 program that makes all.
  `argBPG pw pq Vf`  The scheme: the committer of `argB` followed by pw; the prover that pq gives,
                     after `realQ` (Compile/Batch/Oracles.lean: queries to the ghost names `fbw`
                     become queries to `fb`); any verifier.
  `argBPGT pw pq Vf`  Its token form, the same without `realQ`: C and P query the ghost names, as
                      the programs do. An object of the analysis only; the experiments below are
                      compared with the real experiment of `argBPGT` (under `MaskProg`, for
                      `VCBPG` also `GAdm`: Compile/Batch/PubProgReal.lean).
  `RealBPG'`, `VCBPG`  The real experiment in which what is not shown is not made; the challenger
                       whose steps are programs with tokens. With pq = `Pp` it is that of
                       Compile/Batch/PubChall.lean (`VCBPG_Pp`: by rfl).

After Compile/Batch/PubChall.lean with the prover's program replaced (of `VCBPG`; that file defines
no scheme and no real experiment).
-/
import Compile.Batch.PubChall
import Compile.Batch.ChallU

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.GlueB (GCall ownPf)
open Compile.Life2 (virt)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- a prover's program with flags: the key with tokens, for which requests a proof string is made,
the instances -/
abbrev FProg (lam : ℕ) (L : BatchProtocol I X) (K : ℕ) : Type :=
  IskH lam L → (ℕ → Bool) → List X → St lam K L (List (Prf lam L))

/-- The condition on pq: what is not shown is not made (exactly: for all γ, k, b, vs, st:
`(erase (pq k (ownFlag b) (reqs b)) vs).bind fun o => OComp.pure (replyOf b o.1, st)`
is equal to the same term with `fun _ => true` for `ownFlag b`). -/
def MaskProg {K : ℕ} (pq : FProg lam L K) : Prop :=
  ∀ (γ : Type) (k : IskH lam L) (b : Gen.Batch X Unit) (vs : List Bits) (st : γ),
    ((erase (pq k (ownFlag b) (reqs b)) vs).bind fun o => OComp.pure (replyOf b o.1, st))
      = (erase (pq k (fun _ => true) (reqs b)) vs).bind fun o => OComp.pure (replyOf b o.1, st)

variable {V : Type} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (pw : IVK lam L → WKey lam L → V)
  (pq : FProg lam L W.K) (i : I)

/-- The scheme. Its prover is the erased program with the ghost names written back (`realQ`,
Compile/Batch/Oracles.lean), as P of Compile/Batch/Star.lean (there every attempt with a nonce is a
query to the Fiat-Shamir oracle fb t, which is what V of that file queries). (progP W .. is the form
without `realQ`: Compile/Batch/ChallU.lean.) For a program that never queries a ghost name, `realQ`
changes nothing. -/
def argBPG (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool) :
    Gen.Arg (spec lam W.K L) I X Unit V (ISK lam L) (Prf lam L) where
  C := fun i => (C W WP p i).bind fun o => .pure (pw o.1 (keyOf o.2.1), o.2)
  P := fun k b => realQ (progP W (fun k xs => pq k (fun _ => true) xs) k b)
  V := Vf

/-- Its token form, the same without `realQ`: C and P are the erased programs as they are, queries
to the ghost names included. An object of the analysis of privacy only: the experiments below are
compared with the real experiment of argBPGT (under `MaskProg`, for `VCBPG` also `GAdm`:
Compile/Batch/PubProgReal.lean). -/
def argBPGT (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool) :
    Gen.Arg (spec lam W.K L) I X Unit V (ISK lam L) (Prf lam L) where
  C := fun i => (Ctok W WP p i).bind fun o => .pure (pw o.1 (keyOf o.2.1), o.2)
  P := progP W fun k xs => pq k (fun _ => true) xs
  V := Vf

/-- the steps of RealBPG' (the programs as they are, queries to the ghost names included) -/
def stepRealBPG' :
    Option (ISK lam L) → GCall X Unit →
    TypedOracleComputation lam W.K L (BInP V lam L × Option (ISK lam L)) := fun s c =>
  match c, s with
  | .setup, _ => (Ctok W WP p i).bind fun o => pure (.inl (pw o.1 (keyOf o.2.1)), some o.2)
  | .batch _, none => pure (.inr [], none)
  | .batch b, some k =>
      if hasOwn b then
        (erase (pq k.1 (ownFlag b) (reqs b)) k.2).bind fun o => pure (replyOfP V b o.1, some k)
      else pure (.inr [], some k)

/-- The real experiment without what is not shown. -/
abbrev RealBPG' : World (spec lam W.K L) (GCall X Unit) (BInP V lam L) :=
  World.ofOComp (stepRealBPG' W WP p pw pq i)

/-- The challenger. -/
abbrev VCBPG : Chall (spec lam W.K L) (split lam W.K L) (GCall X Unit) (BInP V lam L) where
  τ := Option (IskH lam L × ℕ)
  step := fun s c => match c, s with
    | .setup, none =>
      (Cp W WP p i).bind fun o =>
        Step.fresh 0 fun t => Step.pure (.inl (pw o.1 (keyOf o.2)), some (o.2, t))
    | .setup, some k => Step.pure (.inr [], some k)
    | .batch _, none => Step.pure (.inr [], none)
    | .batch b, some (k, N₀) =>
        if hasOwn b then
          Step.fresh 0 fun t₀ => (virt N₀ (t₀ + 1 - N₀) (pq k (ownFlag b) (reqs b))).bind fun πs =>
            Step.pure (replyOfP V b πs, some (k, N₀))
        else Step.pure (.inr [], some (k, N₀))

theorem VCBPG_Pp : VCBPG W WP p pw (Pp W WP p) i = VCBP W WP p pw i := rfl

end Compile.Batch
