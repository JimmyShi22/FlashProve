-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecFit.lean: when the proof-of-work records (`GrW`) in a wire record fit a record of
protocols. `GrFit`, `GrFitB` (for the three protocols) and their parts for privacy: hypotheses of
the compiler theorems with proof-of-work bits (Compile/Batch/SpecUGr.lean;
Compile/Batch/PubProgMainBGr.lean; the header of Compile/Batch/SpecGrind.lean says what they are
for) and of the steps of their proofs. A separate file, so that the steps of the proof of privacy
can name them without importing the bounds. (Words of this library: lean/GLOSSARY.md.)

  `GrFitP`, `GrFitPB`   (1) and (2) below alone: what privacy uses. At a wire record without
                        proof-of-work bits it is true for every record of protocols; that is not
                        proved in this library; with (Acc) (`Honest.Acc`, Iop/InteractiveOracleProof.lean) and
                        locality (`IsLocal`) it follows from `fit_ok`, Compile/Batch/GrOK.lean
  `GrFit`   for one `BatchInteractiveOracleProof` with its honest prover: (1) nothing on the honest side depends on
            the proof-of-work bits: withheld sets (`wh`), the honest prover's messages (`run`), the
            positions read (`reads`, `extReads`); (2) the positions read do not depend on nonces
            (`readsPut`); (3) (Acc) where all proof-of-work bits are 0 (`acc`). Only (3) names
            `valid`; privacy uses (1) and (2), completeness (1) and (3)

That they can be met with proof-of-work bits: Compile/Batch/FitGrind.lean (for `L.grind`). Without
them they follow from (Acc) and locality: `fit_ok`.

Notation: `ρ`: a `Rho ..`: "The verifier's randomness of a whole execution"; `pl`: a `Plains ..`:
"The plain parts of all prover messages"; `τ`: a `Tr ..`: "Full transcripts" (all three:
Iop/Shape.lean); `w`, `x`, `c`: in `Wt`, `Y`, `H.one.Coin`: the arguments of `H.one.strat`
(`Honest.strat`, Iop/InteractiveOracleProof.lean); `ph`: a `PhT` (Compile/Batch/Prover.lean), of which `.first` is a
constructor; `nJ`, `n0`: lists of natural numbers: "nJ: the numbers of the final attempts of the
slot, n0: those of the shared rounds" (`putB`, Compile/Batch/Prover.lean); `T`, `Lk`, `B`: the
fields for `L.offline`, `L.link`, `L.onlineBatch` (Test, Link, Batch: `BatchProtocol`, Iop/Batch.lean); withheld set:
`Honest.withheld` (Iop/InteractiveOracleProof.lean); wire record, record of protocols: lean/GLOSSARY.md.
-/
import Compile.Batch.Prover

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## The proof-of-work records fit the record of protocols -/

/-- Nothing on the honest side depends on the proof-of-work bits, and the positions read do not
depend on nonces. What privacy uses. -/
structure GrFitP {K : ℕ} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {Wt : Type}
    (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) : Prop where
  /-- the withheld set of a slot does not depend on the proof-of-work bits -/
  wh : ∀ w x ρ, ρ ∈ H.one.withheld w x ↔ RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ H.one.withheld w x
  /-- the honest prover's messages do not depend on the proof-of-work bits -/
  run : ∀ w x c ρ,
    ((H.one.strat w x c).run ρ).1.plains =
      ((H.one.strat w x c).run (RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ)).1.plains ∧
    ∀ p, ((H.one.strat w x c).run ρ).1.read p =
      ((H.one.strat w x c).run (RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ)).1.read p
  /-- the positions that the verifier reads do not depend on the proof-of-work bits (`reads`,
  `extReads`) -/
  reads : ∀ x ρ pl, Q.loc.reads x ρ pl = Q.loc.reads x (RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ) pl
  extReads : ∀ x ρ, Q.loc.extReads x ρ = Q.loc.extReads x (RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ)
  /-- nor do they depend on the nonces -/
  readsPut : ∀ x ρ pl ph nJ n0,
    Q.loc.reads x ρ (putB Q.loc.shape Q.ann wq.sh ph nJ n0 pl) = Q.loc.reads x ρ pl

/-- The proof-of-work records fit a `BatchInteractiveOracleProof` and its honest prover. -/
structure GrFit {K : ℕ} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {Wt : Type} (H : BatchHonestProver Q Wt)
    (wq : ProtocolQueryLayout lam K Q) (valid : Wt → Y → Prop) : Prop extends GrFitP H wq where
  /-- (Acc) where all proof-of-work bits are 0: for a valid input, outside the withheld set and at
  proof-of-work bits 0, the verifier accepts every transcript that has the honest prover's oracles
  and its plain parts with any numbers written in as nonces -/
  acc : ∀ w x c ρ, valid w x → ρ ∉ H.one.withheld w x →
    RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh ρ = true →
    ∀ (nJ n0 : List ℕ) (τ : Tr Q.loc.shape), τ.rho = ρ →
      τ.plains = putB Q.loc.shape Q.ann wq.sh .first nJ n0 ((H.one.strat w x c).run ρ).1.plains →
      (∀ p, τ.read p = ((H.one.strat w x c).run ρ).1.read p) → Q.loc.accept x (H.ext w) τ = true

/-- `GrFitP` for the three protocols of a record of protocols -/
structure GrFitPB (W : QueryLayout lam L) : Prop where
  T : GrFitP (BatchHonestProver.ofHonest L.honestOfflineProver) W.T
  Lk : GrFitP (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk
  B : GrFitP L.honestOnlineBatchProver W.B

/-- `GrFit` for the three protocols of a record of protocols -/
structure GrFitB (W : QueryLayout lam L) (Ryes : I → X → Prop) : Prop where
  T : GrFit (BatchHonestProver.ofHonest L.honestOfflineProver) W.T fun _ _ => True
  Lk : GrFit (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk fun _ _ => True
  B : GrFit L.honestOnlineBatchProver W.B fun w x => Ryes w.1 x

theorem GrFitB.toP {W : QueryLayout lam L} {Ryes : I → X → Prop} (h : GrFitB W Ryes) : GrFitPB W :=
  ⟨h.T.toGrFitP, h.Lk.toGrFitP, h.B.toGrFitP⟩

end Compile.Batch
