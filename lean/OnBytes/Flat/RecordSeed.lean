-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/RecordSeed.lean: the seed of a table's record, drawn from the first blocks of any K
blocks, with its law, at the configuration of the entry's link.

OnBytes/Flat/EntryRecord.lean has the seed of b + c blocks (`recSeedAt`), b the number of blocks
that the seeds' draws need, and its law. A wire of the compiler has its own number K of blocks. Here
the seed is given for every K that is at least b, so that no equation between numbers stands in a
type.

Main definition: `recSeedK T lg s K h`: `recSeedB` of the first b of K blocks; the others are not
read.
Main theorems: `RecFits.seedLawK`; `entryFull_seedLawK`, `entrySmall_seedLawK`: for every word,
fixed before the blocks, the seed is one with a collision with probability at most 2^-128. Nothing
is assumed.

Not claimed. All that the head of OnBytes/Flat/EntryRecord.lean does not claim.

-/
import OnBytes.Flat.EntryRecord

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb Cb.Ood Hiop _root_.Iop _root_.Run Rom
open scoped ENNReal

/-- **The seed of K blocks**: that of the first b; the others are not read. -/
def recSeedK (T : Fmt.M1.Code) (lg s K : ℕ) (h : (seedBS lg s).b ≤ K)
    (a : Fin K → Dig 256) : (recZ T.l lg s).D :=
  recSeedB T lg s fun i => a (Fin.castLE h i)

/-- **The seed's law at K blocks.** -/
theorem RecFits.seedLawK {T : Fmt.M1.Code} {v eM lg s : ℕ} (hz : RecFits T eM lg s) {X : Type}
    (A : (decRec T v eM lg s).Claims X) (R : (decRec T v eM lg s).RelationsAndEncoding A) (K : ℕ)
    (h : (seedBS lg s).b ≤ K) (y : Fin (2 ^ T.a) → Run.PQ.SgX) :
    pr (unif (Fin K → Dig 256)) {a | (DecR.configurationOfStoredTable A R).coll y (recSeedK T lg s K h a)} ≤
      recBound T eM lg s := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  exact hz.seedLaw A R c y

end OnBytes.Slice

namespace OnBytes.Flat
open Prob Cb Hiop _root_.Iop _root_.Run OnBytes.Slice
open scoped ENNReal

/-- At the full size: at most 2^-128. -/
theorem entryFull_seedLawK {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
    (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (K : ℕ) (h : (seedBS recLg recS).b ≤ K)
    (y : Fin (DecR.configurationOfStoredTable A R).n → (DecR.configurationOfStoredTable A R).Sg) :
    pr (unif (Fin K → Dig 256)) {a | (DecR.configurationOfStoredTable A R).coll y (recSeedK recT recLg recS K h a)} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 128 :=
  (fr_fits.seedLawK (v := recV) A R K h y).trans fr_bound

/-- At the small example: at most 2^-128. -/
theorem entrySmall_seedLawK {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
    (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (K : ℕ) (h : (seedBS 19 1).b ≤ K)
    (y : Fin (DecR.configurationOfStoredTable A R).n → (DecR.configurationOfStoredTable A R).Sg) :
    pr (unif (Fin K → Dig 256)) {a | (DecR.configurationOfStoredTable A R).coll y (recSeedK srT 19 1 K h a)} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 128 :=
  (sr_fits.seedLawK (v := 8) A R K h y).trans sr_bound

end OnBytes.Flat

#print axioms OnBytes.Flat.entryFull_seedLawK
#print axioms OnBytes.Flat.entrySmall_seedLawK
