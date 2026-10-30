-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/OneData.lean: the plain data made at a file's own key are the plain data made at
a fixed key.

Two families of laws speak of a file's plain data. Those on a reading stand at the three lists of
rounds that the dry runs state at the key IN THE READING (`dryKey k r.key`, `dryProof c r.key
block`, OnBytes/Maker/Files.lean). The makers lay their data once, at a FIXED key: the key of a
fixed record. This file joins the two: the key in a reading is the program's key of the reading's
table (`tableKey`), that key has the item 0 and fits the parameters' shape, and the dry runs do not
hang on which key with these two properties is laid (OnBytes/Maker/FilesFree.lean).

  `dryKey_one`, `dryProof_one`     the dry runs at a fixed key that fits are those at the program's
                                  key of any table
  `dryKey_read`, `dryProof_read`   the same at the key in a record of the three chains' reading
                                  (`ThreeRead`, OnBytes/Maker/ThreeRead.lean)
  `dataAt_read`, `dataAt_readP`    so the data that the makers lay at the fixed key are the data at
                                  the reading's key; and where the tests pass there, they are those
                                  of the three lists

What is asked of the fixed key: the item 0, and that it fits the shape of the shared chain's index.
At a proof file both sides stand at ONE block of the first chain: nothing is said on two requests.

Not claimed. That the tests pass. Nothing on soundness.


-/
import OnBytes.Maker.FilesFree
import OnBytes.Maker.ThreeRead
import OnBytes.TieK.PlaceOpen

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes.Proof OnBytes.TieK OnBytes.Maker
open OnBytes.Params (Rounds)

section
variable {fl : Fmt.Fld} {cfg : ByteArray} {s : Params.IndexShape} {table : Params.TableName}
  {key₀ κ : TableKey} (h0 : key₀.item = 0) (hf : key₀.fits s = true)
  (hκ : tableKey fl cfg s table 0 = some κ)
include h0 hf hκ

/-- A fixed key with the item 0 that fits is alike the program's key of any table. -/
theorem keyAlike_table : TwoLaws.KeyAlike key₀ κ := by
  obtain ⟨seeds, -, hk, hfit⟩ := tableKey_open _ _ _ _ _ _ hκ
  have hi : κ.item = 0 := by rw [hk]
  exact keyAlike_of_fits s (h0.trans hi.symm) hf hfit

/-- **A key file: the dry runs at the fixed key are those at the program's key of any table.** -/
theorem dryKey_one (k : Params.KeyChains) : dryKey k key₀ = dryKey k κ :=
  dryKey_keyAlike (keyAlike_table h0 hf hκ) k

/-- **A proof file**, at one block of the first chain. -/
theorem dryProof_one (c : Params.ProofChains) (block : Blk FirstEnd) :
    dryProof c key₀ block = dryProof c κ block :=
  dryProof_keyAlike (keyAlike_table h0 hf hκ) c block

end

section Read
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
  {key₀ : TableKey} (h0 : key₀.item = 0) (hf : key₀.fits p.lin.fold.index = true)
include T h0 hf

/-- A key file: the dry runs at the fixed key are those at the key in the reading. -/
theorem dryKey_read (k : Params.KeyChains) : dryKey k key₀ = dryKey k r.key :=
  dryKey_one h0 hf T.key_made k

/-- A proof file, at one block of the first chain. -/
theorem dryProof_read (c : Params.ProofChains) (block : Blk FirstEnd) :
    dryProof c key₀ block = dryProof c r.key block :=
  dryProof_one h0 hf T.key_made c block

/-- **A key file: the data that are laid at the fixed key are those of the three lists that the dry
runs state at the reading's key**, where the tests pass. -/
theorem dataAt_read (a : ℕ) (k : Params.KeyChains) {R : Rounds × Rounds × Rounds}
    (hR : dryKey k r.key = some R) (ok : okAt a (some R) = true) :
    dryKey k key₀ = some R ∧ dataAt a (dryKey k key₀) = Three.Whole.of R.1 R.2.1 R.2.2 := by
  have e := (dryKey_read T h0 hf k).trans hR
  refine ⟨e, ?_⟩
  rw [e]
  exact if_pos ok

/-- **A proof file**, the like. -/
theorem dataAt_readP (a : ℕ) (c : Params.ProofChains) (block : Blk FirstEnd)
    {R : Rounds × Rounds × Rounds} (hR : dryProof c r.key block = some R)
    (ok : okAt a (some R) = true) :
    dryProof c key₀ block = some R ∧
      dataAt a (dryProof c key₀ block) = Three.Whole.of R.1 R.2.1 R.2.2 := by
  have e := (dryProof_read T h0 hf c block).trans hR
  refine ⟨e, ?_⟩
  rw [e]
  exact if_pos ok

end Read

end OnBytes.Maker.Page
