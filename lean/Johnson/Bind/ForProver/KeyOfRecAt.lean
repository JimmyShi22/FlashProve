-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/KeyOfRecAt.lean: THE LIBRARY'S KEY WRITTEN OF THE TYPED OOD SAMPLE `recAt`
(Johnson/Bind/ForProver/SevenAt.lean) IS THE KEY THAT THIS FOLDER MAKES OF THE SAME PLAIN ENTRIES,
COINS AND SEED (`oodAt`, Johnson/Bind/ForProver/Ood.lean). General in the sizes; then at the full
size, for the two keys that the library's theorem on the link's decision writes. Definitions,
statements and proofs.

Why. In `seven_at_ours` and `meant_ours` the clauses on the sample hold of every table of
coefficients, by `recAt`'s definition. What they are worth hangs on what `recAt` is. Here it is held
against a text that is not made for it: `oodAt` calls the answers of the stand-in committer on byte
strings (`Bind.Twin.answers`, Johnson/Bind/Twin.lean).

Main names (namespace `Bind.ForProver`).
   `oodAt_eq_keyOf`: at every shape, plain entries, coins and typed seed: `oodAt` at the spelled
      seed is the library's key (`OnBytes.Slice.keyOf`) written of the seed and the sample map's
      answers at `msgsAt`. It is `oodSh_eq_keyOf` (Johnson/Bind/ForProver/OodIsKeyOf.lean) with the
      plain entries as a letter.
   `shapeOfSz S s sigma`: the shape with the sizes' a, l, r, v; `agree_shapeOfSz`: it agrees with S.
   **`keyOf_recAt`**: at the sizes S, the shape `shapeOfSz S s sigma` and the sample map
      `recZ` of l entries, lg coordinates and s answers, where lg is the shape's number of
      coordinates: the key written of `recAt` is `oodAt` at the seed, spelled.
   `cube_full`: at the full size's shape that number is 29.
   **`keys_ours`**: at the full size: the two keys that `Johnson.Prover.Link.keysOf` writes of
      (`recAt`, `recAt`) are `oodAt` at (ρ, σ), and `oodAt` at (ρ', σ') with the item 1.
Limits. EQUATIONS BETWEEN THIS LIBRARY'S OWN TERMS. The seed is a letter: that it is sampled, or
derived from a hash, is not said. At the full size the seed is typed at the numeral 29 and spelled
by the library's `spellSeedL 29 1`, not by this folder's `spell shFull`, whose type names the
shape's own number: the two types are equal by `cube_full` and are not identified here; the way
across is `seedAs`, and the two keys at this folder's own spelling are `keys_seed`
(Johnson/Bind/ForProver/SeedAtFull.lean). THE TWO KEYS ARE ONE TEXT AT TWO PAIRS OF BARE LETTERS;
the second has the item set to 1, by `keysOf`'s text. (ρ, σ) stand where the link reads the
committed table (its item 0), (ρ', σ') where it reads a second table (its item 1). That ρ, σ are the
coins and the seed of the run that makes the commitment ID (its salts, tree, root and name; σ
sampled at that name), and that ρ', σ' are a copy's own, sampled apart, with a copy's tree, name and
root: NEITHER is said here. Nothing here says that each table's randomness has one seed, that the
two tables' randomness is sampled apart, or that the second table's is the one at which a session
runs. The plain entries are a letter. THE COINS ARE TOTAL FUNCTIONS HERE: where they are made of
coins on finite ranges (`AtPublicFiles.Key.padReader`, the library's E2E/KeyReaders.lean), the pads that the
answers read lie inside the range only under `Bind.Column.Agree`: whoever lays such coins brings
that premise. 3 s ≤ l is a premise of the general forms; at the full size it is 3 ≤ 402,653,184. No
hash function, no query, no coin's law. This file writes no honest prover. Nothing on completeness,
on index privacy, on soundness or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.SevenAt
import Johnson.Bind.ForProver.OodIsKeyOf
import Johnson.Prover.Link.LinkYesStm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open OnBytes (TableKey)
open OnBytes.Slice (Sz GF GE NZ keyOf RecP recZ frS frZ)
open ProofFile.Honest (TableRand)
open Bind.Twin (Shape)
open Bind.Column (Agree shFull)

/-- **The key made of plain entries, coins and a typed seed is the library's key written of the
typed OOD sample**: the plain entries are a letter. -/
theorem oodAt_eq_keyOf (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (σ : Seed sh)
    (h3 : 3 * sh.s ≤ sh.l) :
    oodAt sh entry ρ (spell sh σ) =
      keyOf (fun β : NZ => β.val)
        ((σ, ((recZ sh.l sh.cube sh.s).rows (Fin sh.v → Bool)).val σ (msgsAt sh entry ρ)) :
          RecP NZ sh.v sh.cube sh.s) := by
  refine tableKey_ext _ _ rfl ?_ (seeds_eq_keyOf sh
    (σ, ((recZ sh.l sh.cube sh.s).rows (Fin sh.v → Bool)).val σ (msgsAt sh entry ρ)))
  apply Array.ext'
  rw [answers_oodAt sh entry ρ h3 σ]
  unfold keyOf OnBytes.K.IdTable.spellAns
  rw [Array.toList_ofFn]

/-- The shape with the sizes' a, l, r and v. -/
abbrev shapeOfSz (S : Sz) (s sigma : ℕ) : Shape := ⟨S.P.T.a, S.P.T.l, S.P.T.r, S.P.v, s, sigma⟩

/-- It agrees with the sizes, the pads beginning at l - 3 s. -/
theorem agree_shapeOfSz (S : Sz) (s sigma : ℕ) (h3 : 3 * s ≤ S.P.T.l) :
    Agree (shapeOfSz S s sigma) S (S.P.T.l - 3 * s) :=
  ⟨rfl, rfl, rfl, rfl, Nat.sub_add_cancel h3⟩

/-- **The key written of `recAt` is `oodAt` at the seed, spelled.** By the texts, and by no theorem
of this file: of ρ the pads alone reach either side (`Bind.Twin.answers` reads the plain entries and
the pads; `recAt` reads the message part of `polysAt`); ρ's tails and the number sigma are read by
neither. -/
theorem keyOf_recAt (S : Sz) (s sigma lg : ℕ) (hlg : (shapeOfSz S s sigma).cube = lg)
    (h3 : 3 * s ≤ S.P.T.l) (entry : ℕ → ℕ → UInt64) (ρ : TableRand)
    (σ : Fin s → (Fin lg → GE) × NZ) :
    keyOf (fun β : NZ => β.val)
        (recAt S (recZ S.P.T.l lg s) (shapeOfSz S s sigma) entry ρ σ : RecP NZ S.P.v lg s) =
      oodAt (shapeOfSz S s sigma) entry ρ
        ((OnBytes.K.IdTable.spellSeedL lg s σ).map fun y => ⟨y.1, y.2⟩) := by
  subst hlg
  have e : (S.ixR (recZ S.P.T.l (shapeOfSz S s sigma).cube s)).view
      (polysAt S (shapeOfSz S s sigma) entry ρ) = msgsAt (shapeOfSz S s sigma) entry ρ :=
    funext fun n => view_polysAt S (agree_shapeOfSz S s sigma h3) entry ρ n
  exact (congrArg (fun u => keyOf (fun β : NZ => β.val)
    ((σ, ((recZ S.P.T.l (shapeOfSz S s sigma).cube s).rows (Fin S.P.v → Bool)).val σ u) :
      RecP NZ S.P.v (shapeOfSz S s sigma).cube s)) e).trans
    (oodAt_eq_keyOf (shapeOfSz S s sigma) entry ρ σ h3).symm

/-! ## At the full size -/

/-- The full size's shape has 29 coordinates in a seed's point. -/
theorem cube_full : shFull.cube = 29 := by decide +kernel

/-- **The two keys that the library's theorem on the link's decision writes of this folder's typed
samples**: the first is this folder's key; the second is the same text at the other letters, with
the item 1. -/
theorem keys_ours (entry : ℕ → ℕ → UInt64) (ρ ρ' : TableRand) (σ σ' : frZ.D) :
    Johnson.Prover.Link.keysOf
        (recAt frS frZ shFull entry ρ σ, recAt frS frZ shFull entry ρ' σ') =
      (oodAt shFull entry ρ ((OnBytes.K.IdTable.spellSeedL 29 1 σ).map fun y => ⟨y.1, y.2⟩),
        { oodAt shFull entry ρ' ((OnBytes.K.IdTable.spellSeedL 29 1 σ').map fun y => ⟨y.1, y.2⟩)
          with item := 1 }) := by
  have h3 : 3 * 1 ≤ frS.P.T.l := by
    show 3 * 1 ≤ 402653184
    omega
  have k0 := keyOf_recAt frS 1 40 29 cube_full h3 entry ρ σ
  have k1 := keyOf_recAt frS 1 40 29 cube_full h3 entry ρ' σ'
  exact Prod.ext k0 (congrArg (fun k : TableKey => { k with item := 1 }) k1)

end Bind.ForProver

end

#print axioms Bind.ForProver.oodAt_eq_keyOf
#print axioms Bind.ForProver.shapeOfSz
#print axioms Bind.ForProver.agree_shapeOfSz
#print axioms Bind.ForProver.keyOf_recAt
#print axioms Bind.ForProver.cube_full
#print axioms Bind.ForProver.keys_ours
