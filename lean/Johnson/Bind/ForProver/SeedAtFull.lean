-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/SeedAtFull.lean: A TYPED SEED AT A SHAPE, READ AT A NUMBER OF COORDINATES
THAT IS EQUAL TO THE SHAPE'S OWN; and `meant_ours` (Johnson/Bind/ForProver/MeantOurs.lean) and
`keys_ours` (Johnson/Bind/ForProver/KeyOfRecAt.lean) at seeds that are typed at the full size's
shape. A definition, statements and proofs.

Why. This folder types a seed of a table's OOD sample at a shape: its points have as many
coordinates as the shape reckons (`Seed sh`, Johnson/Bind/ForProver/Seeds.lean). The library's
sample map at the full size is written at the numeral 29. The two numbers are equal by a reckoning
(`cube_full`), not by the form of the two texts, and `meant_ours` and `keys_ours` take a seed that
is typed at the numeral. Whoever has a seed from this folder's laws on a run wants the way across.

Main names (namespace `Bind.ForProver`).
   `seedAs h σ`: the seed σ with each point's coordinates numbered below lg, where h says that lg is
      the shape's number. No value turns.
   `spell_seedAs`: spelled, it is the same list.
   `meant_seed`: `meant_ours` at two seeds typed at the full size's shape: an instance of it.
   **`keys_seed`**: `keys_ours` there, with this folder's own `spell shFull` on the right.
Limits. A WAY BETWEEN TWO TYPES THAT ARE EQUAL: nothing is said that `meant_ours` and `keys_ours` do
not say. The seeds are bare letters, as there: that a seed is sampled at a table's name is not said
here. The full size alone for the last two. No hash function, no query, no coin's law. This file
writes no honest prover. Nothing on completeness, on index privacy, on soundness or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.MeantOurs
import Johnson.Bind.ForProver.KeyOfRecAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open OnBytes.Slice (GE NZ frS frZ)
open ProofFile.Honest (TableRand)
open Bind.Twin (Shape)
open Bind.Column (shFull)

/-- **A typed seed, its points' coordinates numbered below lg**, where lg is the shape's number of
coordinates. -/
def seedAs {sh : Shape} {lg : ℕ} (h : sh.cube = lg) (σ : Seed sh) :
    Fin sh.s → (Fin lg → GE) × NZ :=
  fun a => (fun t => (σ a).1 (Fin.cast h.symm t), (σ a).2)

/-- Spelled, it is the same list. -/
theorem spell_seedAs (sh : Shape) (lg : ℕ) (h : sh.cube = lg) (σ : Seed sh) :
    OnBytes.K.IdTable.spellSeedL lg sh.s (seedAs h σ) =
      OnBytes.K.IdTable.spellSeedL sh.cube sh.s σ := by
  subst h
  rfl

/-- `meant_ours` at two seeds that are typed at the full size's shape. An instance of it. -/
theorem meant_seed (entry : ℕ → ℕ → UInt64) (ρ ρ' : TableRand) (σ σ' : Seed shFull) :
    Johnson.Prover.Link.Meant
      (recAt frS frZ shFull entry ρ (seedAs cube_full σ),
        recAt frS frZ shFull entry ρ' (seedAs cube_full σ'))
      (strAt frS shFull entry ρ, strAt frS shFull entry ρ')
      (polysAt frS shFull entry ρ) (polysAt frS shFull entry ρ') :=
  meant_ours entry ρ ρ' (seedAs cube_full σ) (seedAs cube_full σ')

/-- **The two keys, at seeds that are typed at the full size's shape**: with this folder's own
spelling on the right. -/
theorem keys_seed (entry : ℕ → ℕ → UInt64) (ρ ρ' : TableRand) (σ σ' : Seed shFull) :
    Johnson.Prover.Link.keysOf
        (recAt frS frZ shFull entry ρ (seedAs cube_full σ),
          recAt frS frZ shFull entry ρ' (seedAs cube_full σ')) =
      (oodAt shFull entry ρ (spell shFull σ),
        { oodAt shFull entry ρ' (spell shFull σ') with item := 1 }) := by
  have e : ∀ τ : Seed shFull,
      ((OnBytes.K.IdTable.spellSeedL 29 1 (seedAs cube_full τ)).map fun y => ⟨y.1, y.2⟩ :
        List OnBytes.SampleSeed) = spell shFull τ :=
    fun τ => congrArg
      (List.map fun y : List OnBytes.E × OnBytes.E => (⟨y.1, y.2⟩ : OnBytes.SampleSeed))
      (spell_seedAs shFull 29 cube_full τ)
  rw [keys_ours, e σ, e σ']

end Bind.ForProver

end

#print axioms Bind.ForProver.seedAs
#print axioms Bind.ForProver.spell_seedAs
#print axioms Bind.ForProver.meant_seed
#print axioms Bind.ForProver.keys_seed
