-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecLoop.lean: the search over nonces: the one lemma that each part of the analysis of
the compiled scheme needs for a Fiat-Shamir query with proof-of-work bits. Two definitions and five
statements only. The proofs: Compile/Batch/LoopEager.lean, Compile/Batch/LoopLazy.lean,
Compile/Batch/LoopLaw.lean. (Words of this library: lean/GLOSSARY.md.)

The search: in a round with proof-of-work bits the honest prover makes the round's Fiat-Shamir query
with the nonces 0, 1, 2, .., at most more + 1 of them, and goes on with the first answer whose
proof-of-work bits are all 0; if there is none, with the last (the header of
Compile/Batch/SpecGrind.lean). It is written three times: `fbG` (Compile/Batch/Prover.lean); `fbGL`,
in the language `LStep` (Compile/Batch/Mirror.lean); `askG`, on strings
(Compile/Batch/CompleteRefDefs.lean). The statements here are, for the search, what the lemmas on
`fbT`, `fbL` or `askTypedOracle` are; in `Spec.fbG_fibre`, at gr = none, the search is `fbL` by definition.

  `realF`, `Spec.realQ_eager`
      for fixed oracle functions f: an algorithm c with the ghost names written back (`realQ c`: its
      queries to `fbw t k` become queries to `fb t`), run under f, is c run under `realF f`, which
      answers `fbw t k` as `fb t`. (`fbw t k`: the ghost name under which a token program makes
      attempt k + 1, Compile/Batch/Oracles.lean.)
  `Spec.askW_law`   for lazily sampled oracles: if the queries of the n + 1 attempts are new and
                    differ from each other, the final answer has exactly the distribution
                    `Prob.retry` (sample until the check passes, at most n + 1 times)
  `Spec.ok_share`, `Spec.ok_indep`
      if `w.OKG`, `g.OK`: under uniform hash blocks all proof-of-work bits are 0 with probability
      exactly 2^-b, and the verifier message with these bits set to 0 is independent of the check
  `Spec.fbG_fibre`   under the same conditions, the distribution of the search in `LStep`: the
                     search with uniform answers is: a uniform verifier message c, and then the
                     reduction's search, which is given c, does not use its proof-of-work bits, and
                     samples those of each attempt itself

Lemmas that only carry a property through the search: Compile/Batch/ProverG.lean.

Limits: nothing about whole rounds, chains or executions.
-/
import Compile.Batch.Mirror
import Compile.Batch.CompleteRefDefs
import Compile.Batch.ProverG
import Compile.Step1_defc_L
import Prob.Retry

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.DefC (virtL)
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- the oracle functions that answer the ghost name fbw t k as fb t -/
def realF (f : Fam (spec lam K L)) : Fam (spec lam K L) := fun o => match o with
  | .fbw t _ => fun q => f (.fb t) q
  | .leaf => f .leaf
  | .node => f .node
  | .rleaf => f .rleaf
  | .rnode => f .rnode
  | .fb t => f (.fb t)
  | .g t => f (.g t)
  | .ann => f .ann
  | .other => f .other

/-- the verifier message with the proof-of-work bits of a record set to 0; itself if there is no
record. (WireRB.zero, Iop/BatchWire.lean, is this at the record that the round's kind reads:
Compile/Batch/FibreSupp.lean: zero_lo, zero_sh.) -/
def zeroG {C P : Type} (gr : Option (GrW C P)) (c : C) : C :=
  match gr with
  | none => c
  | some g => g.set (fun _ => false) c

namespace Spec

/-- The oracle functions fixed. -/
def realQ_eager : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (α : Type) (c : TypedOracleComputation lam K L α) (f : Fam (spec lam K L)),
    (realQ c).runEager f = c.runEager (realF f)

/-- Lazily sampled oracles, new and distinct queries q j, .., q (j + n): the final answer has the
distribution `retry` (sample until the check passes, at most n + 1 times). -/
def askW_law : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (C P : Type) (g : GrW C P) (chal : Blk lam K → C)
      (t : Tag) (q : ℕ → FbIn lam L t) (n j : ℕ) (T : Table (spec lam K L)),
    (∀ m, j ≤ m → m ≤ j + n → T (OracleName.fb t) (q m) = none) →
    (∀ m m', j ≤ m → m ≤ j + n → j ≤ m' → m' ≤ j + n → q m = q m' → m = m') →
    ((Ref.askW g chal t q n j).runLazy T).map Prod.fst =
      retry (fun x : (Fin K → Dig lam) × Dig lam => g.ok (chal x.1)) n

/-- under `w.OKG`, `g.OK`: under a uniform answer the check fails with probability exactly 1 - 2^-b
-/
def ok_share : Prop :=
  ∀ (lam K : ℕ) (r : Round) (a : RAnn r) (w : WireRB lam K r a) (P : Type) (g : GrW r.Chal P),
    w.OKG → g.OK →
    qFail (fun x : (Fin K → Dig lam) × Dig lam => g.ok (w.chal x.1)) = 1 - ((2 : ℝ≥0∞) ^ g.b)⁻¹

/-- under `w.OKG`, `g.OK`: under a uniform answer the verifier message with its proof-of-work bits
set to 0, and the chaining value, are independent of the check (in the form that Prob.map_retry
takes) -/
def ok_indep : Prop :=
  ∀ (lam K : ℕ) (r : Round) (a : RAnn r) (w : WireRB lam K r a) (P : Type) (g : GrW r.Chal P),
    w.OKG → g.OK →
    ∀ b : r.Chal × Dig lam,
      pr (unif ((Fin K → Dig lam) × Dig lam))
          {x | (g.set (fun _ => false) (w.chal x.1), x.2) = b ∧ g.ok (w.chal x.1) = false} =
        pr (unif ((Fin K → Dig lam) × Dig lam))
            {x | (g.set (fun _ => false) (w.chal x.1), x.2) = b} *
          qFail (fun x : (Fin K → Dig lam) × Dig lam => g.ok (w.chal x.1))

/-- Under `w.OKG`, `g.OK`: the distribution of the search, with token numbers shifted (`virtL N₀ δ`)
and from any state, as an equality of distributions of (result, state). -/
def fbG_fibre : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (N₀ δ : ℕ) (r : Round) (a : RAnn r)
      (w : WireRB lam K r a) (P β : Type) (gr : Option (GrW r.Chal P)),
    w.OKG → (∀ g, gr = some g → g.OK) →
    ∀ (t : Tag) (tk : Tok) (us : List Tok)
        (k : Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) (st : LSt (spec lam K L)),
      (virtL N₀ δ (fbGL w gr (ansB w) t tk us none k)).run st =
        (unif r.Chal).bind fun c => (virtL N₀ δ (fbGL w gr (ansB w) t tk us (some c) k)).run st

end Spec

end Compile.Batch
