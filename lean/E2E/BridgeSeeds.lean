-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/BridgeSeeds.lean: THE CLAUSE `prZ` OF `OnBytes.Prover.HonFit` (the measure of the OOD seeds that
are set aside, under the wire's map from uniform digests), AND A TIE OF THE TWO SETS OF OOD SEEDS:
those set aside for acceptance (Zs) and those good for privacy (Gs). General in the object and the
wiring.

  `prZ_none`: where no seed is set aside the measure is 0.
  **`prZ_of_seeds`**: at one index and one committer's randomness: where every seed that is set
    aside there lies outside Gs, the measure of the seeds set aside there is at most δ, THE VERY
    NUMBER that the statement of index privacy asks for the chance of a seed outside Gs
    (`PremW.seeds`; E2E/PremisesAtFiles.lean's `NoProverSide.seeds`), AT THE SAME LETTERS S.
  `asideOf Gs`: the set "outside Gs", at every index and committer's randomness; `not_mem_asideOf`:
    a seed is not set aside just if it is in Gs. At Zs := `asideOf Gs` the clause `prZ` of
    `OnBytes.Prover.HonFit` and the clause `seeds` of `OnBytes.WholeKey.PremW` speak of the same
    seeds, and ζ := δ.

Limits. WHICH seeds must be set aside is not said here: it falls out of where the honest run cannot
go on. No δ is shown small here. THE CLAUSE `prZ` IS ASKED AT EVERY INDEX WITH A REQUEST OF Yes AND
EVERY COMMITTER's RANDOMNESS, ONE AT A TIME; Gs IS ONE SET: to pay it everywhere by this theorem Gs
must miss THE UNION of the sets that are set aside, over all indices and all committer's randomness:
δ is then at least that union's measure, which may be 1 where each single set's measure is small.
`asideOf Gs` reads neither the index nor the committer's randomness: a set that must read them is
not of this form. "The same seeds" is said of the two sets alone: the measures of the three provers'
own abort sets stay at all seeds.


-/
import Johnson.WholeKey.Premises

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Bridge
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {K : ℕ} (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL)

/-- Where no OOD seed is set aside the measure is 0. -/
theorem prZ_none (i : I) (r : L.EncodingRandomness) :
    pr (unif (Fin K → Dig lam))
      {a | S.seed a ∈ (fun (_ : I) (_ : L.EncodingRandomness) => (∅ : Set L.OutOfDomainSeed)) i r} = 0 := by
  have e : {a : Fin K → Dig lam |
      S.seed a ∈ (fun (_ : I) (_ : L.EncodingRandomness) => (∅ : Set L.OutOfDomainSeed)) i r} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ h => h
  rw [e, pr_empty]

/-- **At one index and one committer's randomness: where every OOD seed that is set aside there lies
outside Gs**, the measure of the seeds set aside there is at most the chance of a seed outside Gs,
at the same letters S. -/
theorem prZ_of_seeds {Zs : I → L.EncodingRandomness → Set L.OutOfDomainSeed} {Gs : L.OutOfDomainSeed → Prop} {δ : ℝ≥0∞} (i : I)
    (r : L.EncodingRandomness) (hsub : ∀ e, e ∈ Zs i r → ¬ Gs e)
    (hδ : pr (unif (Fin K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ δ) :
    pr (unif (Fin K → Dig lam)) {a | S.seed a ∈ Zs i r} ≤ δ :=
  le_trans (pr_mono _ fun a h => hsub (S.seed a) h) hδ

/-- The OOD seeds outside Gs, set aside at every index and committer's randomness. -/
def asideOf (Gs : L.OutOfDomainSeed → Prop) : I → L.EncodingRandomness → Set L.OutOfDomainSeed := fun _ _ => {e | ¬ Gs e}

/-- A seed is not set aside so just if it is in Gs. -/
theorem not_mem_asideOf (Gs : L.OutOfDomainSeed → Prop) (i : I) (r : L.EncodingRandomness) (e : L.OutOfDomainSeed) :
    e ∉ asideOf (I := I) Gs i r ↔ Gs e := not_not

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.prZ_none
#print axioms AtPublicFiles.Bridge.prZ_of_seeds
#print axioms AtPublicFiles.Bridge.not_mem_asideOf
