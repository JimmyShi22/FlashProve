-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/Seeds.lean: the seeds of a committed table's out-of-domain (OOD) sample, for
an honest prover in Lean, which this file does not write: typed, spelled as the verifier's key holds
them, and as the stand-in committer on byte strings (`Bind.Twin.commitW`, Johnson/Bind/Twin.lean)
reads them.

Why. An honest prover will keep the seeds of a committed table's OOD sample. The library has a typed
form of such seeds: for each answer a point over the extension field and a factor other than 0
(`OnBytes.Slice.recZ`, OnBytes/Slice/RecordRead.lean). A key holds them as a list of
`OnBytes.SampleSeed` (OnBytes/Iop/Send.lean), and the description tests that list. With the typed
form as the prover's seed, and the list as its spelling, no law on the honest side has to take "the
seeds are in order" as a premise: it is proved once, here.

Main names (namespace `Bind.ForProver`).
  `Seed sh`   the typed seeds at a shape: sh.s of them, each a point of sh.cube coordinates and a
    factor other than 0. It is the type of seeds of `recZ sh.l sh.cube sh.s`.
  `spell`   the typed seeds as a list of `SampleSeed`: the library's `spellSeedL`
    (OnBytes/K/IdSeedSpell.lean), each pair laid into the structure. It has code. `getElem?_spell`:
    its member number i, written out.
  `wordsOf`   a list of `SampleSeed` as the committer's text reads seeds: triples of words.
  `seedsFit`   the test, with code: there are sh.s seeds; each point has sh.cube coordinates; every
    word is below the prime; no factor is the triple of zeros.
  `SeedsFit`   what it checks, as a proposition. `seedsFit_iff`: the two agree.
  **`fits_spell`**   a spelled seed passes the test, at every shape and every typed seed.
  `wordsOf_spell`   read by the committer's text, a spelled seed is the list of which
    `Bind.Twin.answers_spelled` (Johnson/Bind/TwinAnswers.lean) speaks.

Limits. Definitions and short laws. Nothing here says where seeds come from: that a committer makes
them of a table's name by a hash function is another file's matter. Nothing on how seeds are
distributed. This file writes no honest prover. sh.cube is, by its text, the least C with sh.l ≤
2^C: no theorem of this file says so; the library proves it of `OnBytes.ceilLog2`, which has the
same text (`le_two_pow_ceilLog2`, `ceilLog2_le`, OnBytes/Slice/ProgCodes.lean); that it is the
number of coordinates that the verifier's test on a key asks for is `cubeBits_indexOf`
(Johnson/Bind/ForProver/Key.lean). No correctness of extraction, no binding of the commitment (the
opening form, `BindsWith`, VerifiableInference/MoreStatements.lean), no soundness, no completeness,
no index privacy; nothing on any program. Terms: lean/TERMS.md.
-/
import Johnson.Bind.Twin
import OnBytes.K.IdSeedSpell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E SampleSeed okE isZeroE)

/-- **The typed seeds of a table's OOD sample at a shape.** -/
abbrev Seed (sh : Bind.Twin.Shape) : Type :=
  Fin sh.s → (Fin sh.cube → Cb.Gl.E) × OnBytes.Slice.NZ

/-- **The typed seeds, spelled as a key holds them.** -/
def spell (sh : Bind.Twin.Shape) (ρ : Seed sh) : List SampleSeed :=
  (OnBytes.K.IdTable.spellSeedL sh.cube sh.s ρ).map fun y => ⟨y.1, y.2⟩

/-- Seeds as the committer's text reads them. -/
def wordsOf (sd : List SampleSeed) : List (List Fmt.Ext × Fmt.Ext) :=
  sd.map fun y => (y.z.map E.triple, y.beta.triple)

/-- **The test on a list of seeds, with code.** -/
def seedsFit (sh : Bind.Twin.Shape) (sd : List SampleSeed) : Bool :=
  sd.length == sh.s && sd.all fun y =>
    y.z.length == sh.cube && okE y.beta && y.z.all okE && !isZeroE y.beta

/-- What the test checks. -/
def SeedsFit (sh : Bind.Twin.Shape) (sd : List SampleSeed) : Prop :=
  sd.length = sh.s ∧ ∀ y ∈ sd, y.z.length = sh.cube ∧ okE y.beta = true ∧
    (∀ x ∈ y.z, okE x = true) ∧ isZeroE y.beta = false

/-- The test passes exactly where the proposition holds. -/
theorem seedsFit_iff (sh : Bind.Twin.Shape) (sd : List SampleSeed) :
    seedsFit sh sd = true ↔ SeedsFit sh sd := by
  unfold seedsFit SeedsFit
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true', and_assoc]

/-- **A spelled seed passes the test.** -/
theorem fits_spell (sh : Bind.Twin.Shape) (ρ : Seed sh) : SeedsFit sh (spell sh ρ) := by
  obtain ⟨h1, h2⟩ := OnBytes.K.IdTable.shaped_spell sh.cube sh.s ρ
  refine ⟨?_, fun y hy => ?_⟩
  · unfold spell
    rw [List.length_map]
    exact h1
  · unfold spell at hy
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
    obtain ⟨l, p, q, z, -⟩ := h2 w hw
    exact ⟨l, q, p, z⟩

/-- The member number i of a spelled seed. -/
theorem getElem?_spell (sh : Bind.Twin.Shape) (ρ : Seed sh) (i : Fin sh.s) :
    (spell sh ρ)[i.val]? =
      some ⟨List.ofFn fun t : Fin sh.cube => OnBytes.Slice.writeE ((ρ i).1 t),
        OnBytes.Slice.writeE (ρ i).2.val⟩ := by
  unfold spell OnBytes.K.IdTable.spellSeedL
  rw [List.getElem?_map, List.getElem?_ofFn, dif_pos i.isLt]
  rfl

/-- Read by the committer's text, a spelled seed is the library's spelling in triples of words. -/
theorem wordsOf_spell (sh : Bind.Twin.Shape) (ρ : Seed sh) :
    wordsOf (spell sh ρ) =
      (OnBytes.K.IdTable.spellSeedL sh.cube sh.s ρ).map fun y =>
        (y.1.map E.triple, y.2.triple) := by
  unfold wordsOf spell
  rw [List.map_map]
  rfl

/-- As many as were handed. -/
theorem length_wordsOf (sd : List SampleSeed) : (wordsOf sd).length = sd.length := by
  unfold wordsOf
  rw [List.length_map]

end Bind.ForProver

#print axioms Bind.ForProver.seedsFit_iff
#print axioms Bind.ForProver.fits_spell
#print axioms Bind.ForProver.getElem?_spell
#print axioms Bind.ForProver.wordsOf_spell
#print axioms Bind.ForProver.length_wordsOf
#print axioms Bind.ForProver.Seed
#print axioms Bind.ForProver.spell
#print axioms Bind.ForProver.wordsOf
#print axioms Bind.ForProver.seedsFit
#print axioms Bind.ForProver.SeedsFit
