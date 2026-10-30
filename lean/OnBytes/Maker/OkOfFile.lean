-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Maker/OkOfFile.lean: the makers' tests `okAt` (OnBytes/Maker/Files.lean) at `dryKey` and
`dryProof`, as that file defines them, from a value that the verifier program's reader of a key
file or of a proof file has returned, and what is left (`LeftOf4`, OnBytes/Maker/OkOfRow.lean).

OnBytes/Maker/OkOfRow.lean has the statement at the record of a reading, whose public part holds
the real table's name. `dryKey` and `dryProof` are made at the empty name (`noTable`). The dry
runs do not read the name: Lean takes the one for the other by unfolding, as in
OnBytes/Maker/OwesAt.lean.

Main names:
  `okAt_of_readKey`: a key file. The three premises on the first chain's block are paid: `key_own`
    (OnBytes/Maker/SrcFitsOf.lean), `plain_oneTime` (OnBytes/Tie/Pv/Keeps/PlainOfBook.lean).
  `okAt_of_readProof`: a proof file, at the call's own block. Two premises on the block stay: it
    carries the relation "alike" where no given source is met (hb), and its rounds note no opening
    with the mark "stored" (pl₁). `okAt_of_readKey_at`, `okAt_of_readProof_at`: the same at a key
    that is alike to the reading's (`KeyAlike`; `dryKey_keyAlike`, `dryProof_keyAlike`,
    OnBytes/Maker/FilesFree.lean): so at the key of a description's sample.

Limits: `LeftOf4` is a premise, shown of no lists. At a proof file the block is the call's own:
that the dry run of another request's block states the same list is not shown here. That a
sample's key is alike to the reading's is a premise. `okAt` is one of the three tests of `testsB`
(Johnson/Top/ProofRounds.lean); the two others, `shapesFit` and `sealBare`, follow from it
(OnBytes/Maker/OkOfShapes.lean). No file of this library calls the four statements:
OnBytes/Maker/OkOfLeft.lean says them again with less left. Nothing on soundness.
-/
import OnBytes.Maker.OkOfRow
import OnBytes.Maker.OwesAt
import OnBytes.Maker.FilesFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK OnBytes.Tie.Pv.Keeps.Plain
open OnBytes.Params (Rounds)

variable (a : ℕ)

/-- **A key file.** Where the program's reader has returned r, the makers' tests pass at the dry
runs' lists at r's key, if what is left holds. -/
theorem okAt_of_readKey (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
    (j : ℕ) (r : TailRead) (h : (Key.readKey k table file j).fromStart = .ok r)
    (R : Rounds × Rounds × Rounds) (hR : dryKey k r.key = some R)
    (L : LeftOf4 a R.1 R.2.1 R.2.2) : okAt a (dryKey k r.key) = true := by
  obtain ⟨R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, hS₁, T⟩ :=
    threeRead_of_readKey k table file j r h
  have hS₁' : Params.describeWith k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₁ 0 = some S₁ := hS₁
  have hR' : ((Key.oneTime k.oneTime).dryRun (Key.startOf k.oneTime)).bind
      (Three.dry3 (Key.tailPublic k noTable) r.key) = some R := hR
  rw [T.first_dry] at hR'
  have hd : Three.dry3 (Key.tailPublic k table) r.key (R₁, dry) = some R := hR'
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨o₁, b₁⟩ := key_own k.oneTime T.first_dry
  rw [hR]
  exact okAt_of_read4 a T hS₁' o₁ (plain_oneTime _ _ _ _ T.first_dry) b₁ R₃ hd L

/-- **A proof file.** The same, for a first chain's block that carries the relation "alike" where no
given source is met, and whose rounds note no opening with the mark "stored". -/
theorem okAt_of_readProof (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r : TailRead)
    (h : (readProof c table copy request words block file).fromStart = .ok r)
    (hb : Carries (Alike NoGiven true) (FirstEndAlike NoGiven) block block)
    (R : Rounds × Rounds × Rounds) (hR : dryProof c r.key block = some R) (pl₁ : PlainRounds R.1)
    (L : LeftOf4 a R.1 R.2.1 R.2.2) : okAt a (dryProof c r.key block) = true := by
  obtain ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, -, hS₁, T⟩ :=
    threeRead_of_readProof c table copy request words block file r h
  have hS₁' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS₁
  have hR' : (block.dryRun (firstStart c.first)).bind
      (Three.dry3 (tailPublic c noTable) r.key) = some R := hR
  rw [T.first_dry] at hR'
  have hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some R := hR'
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨o₁, b₁⟩ := first_own hb (firstStart_alike c.first) T.first_dry
  rw [hR]
  exact okAt_of_read4 a T hS₁' o₁ pl₁ b₁ R₃ hd L

/-- **A key file, at another key.** The same at the dry runs' lists at a key that is alike to the
reading's: so at the key of a description's sample. -/
theorem okAt_of_readKey_at (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
    (j : ℕ) (r : TailRead) (h : (Key.readKey k table file j).fromStart = .ok r) (key₀ : TableKey)
    (hk : KeyAlike key₀ r.key) (R : Rounds × Rounds × Rounds) (hR : dryKey k key₀ = some R)
    (L : LeftOf4 a R.1 R.2.1 R.2.2) : okAt a (dryKey k key₀) = true := by
  rw [dryKey_keyAlike hk k] at hR ⊢
  exact okAt_of_readKey a k table file j r h R hR L

/-- **A proof file, at another key**, and at the call's own block. -/
theorem okAt_of_readProof_at (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r : TailRead)
    (h : (readProof c table copy request words block file).fromStart = .ok r)
    (hb : Carries (Alike NoGiven true) (FirstEndAlike NoGiven) block block) (key₀ : TableKey)
    (hk : KeyAlike key₀ r.key) (R : Rounds × Rounds × Rounds)
    (hR : dryProof c key₀ block = some R) (pl₁ : PlainRounds R.1)
    (L : LeftOf4 a R.1 R.2.1 R.2.2) : okAt a (dryProof c key₀ block) = true := by
  rw [dryProof_keyAlike hk c block] at hR ⊢
  exact okAt_of_readProof a c table copy request words block file r h hb R hR pl₁ L

end OnBytes.Maker

#print axioms OnBytes.Maker.okAt_of_readKey_at
#print axioms OnBytes.Maker.okAt_of_readProof_at
#print axioms OnBytes.Maker.okAt_of_readKey
#print axioms OnBytes.Maker.okAt_of_readProof
