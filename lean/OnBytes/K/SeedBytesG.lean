-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/SeedBytesG.lean: the seeds of a stored table's record as a function of the answers of ANY
oracle on byte strings at the strings that OnBytes/K/SeedBytes.lean writes out. For proofs only; the
program does not import this file.

OnBytes/K/SeedBytes.lean says it at the format's own hash `Fmt.formatHash` and the format's oracle
`Fmt.oracle`. Here the oracle is a letter O : ByteArray → ByteArray, and the hash that O induces
(`Fmt.HO O`, Fmt/Rules23.lean) stands in the place of `Fmt.formatHash`. The program's side is `Tie.seedsAt O`
(OnBytes/Tie/EntryAtRec.lean): the text of `recordSeeds`, generic in the hash, at `Fmt.HO O`.

Main definitions.
  `seedBlockO O`, `seedsAtNameO O`, `seedDigsO O`: `seedBlock`, `seedsAtName`, `seedDigs` with O in
    the place of `Fmt.oracle`. At `Fmt.oracle` they are the old definitions (`seedBlockO_oracle`,
    `seedsAtNameO_oracle`, `seedDigsO_oracle`).
Main theorems.
  `seedStr_blockStr`: the string of a block of the seeds' round is `Slice.blockStr`
    (OnBytes/Slice/SeedRow.lean): two spellings of the half's byte.
  `recordSeeds_blocksG`: `Tie.seedsAt O f name bits count = some (seedsAtNameO O f name bits
    count)`: the like of `recordSeeds_blocks`.
  `seedsOfDigs_seedDigsG`: the seeds of the K digests are these, if K is at least `nBlocks`: the
    like of `seedsOfDigs_seedDigs`.
  `seedsOfDigs_seedDigs_of_G`: the statement of `seedsOfDigs_seedDigs`, from that at O :=
    `Fmt.oracle`; the old theorem is not called.

Five laws of OnBytes/K/SeedBytes.lean have no like here: what they serve there is had, in other
shapes, from laws that the library has at a letter already:
  `fetch_size`, `fetch_get` (the loop over a round's calls, its size and its entries):
    `Fmt.fetchFrom_spec`, and for the whole row `Fmt.size_fetchW`, `Fmt.fetchW_getD`
    (Fmt/Rules5Row.lean), at every hash, with `Fmt.blockW` for a half of a call.
  `row_get` (the verifier's message, block by block): for the seeds' round `Slice.seedRound_HO`
    (OnBytes/Slice/SeedRow.lean), at every O with answers of 32 bytes.
  `half_oracle`: `Run.blockW_HO` (Run/ChainRow.lean), at every such O.
  `recordFirst_oracle`: `Run.recordFirstW_HO` (Run/PageXSpare.lean), at every O.

Asked of O: every answer has 32 bytes. The old bound on the name's length is not asked: it kept the
first string within the domain on which `Fmt.formatHash` and the hash over `Fmt.oracle` agree, and `Fmt.HO O`
is O at the written strings by its own text. For the same reason `recordSeeds_blocksG` at O :=
`Fmt.oracle` is not `recordSeeds_blocks` by unfolding: that one speaks of the program's
`recordSeeds`, at `Fmt.formatHash`, and the way there (`Slice.recordSeedsW_oracle`,
OnBytes/Slice/SeedsAtOracle.lean) brings a bound on the name back. By that way the old statement
does not come back to the letter: it asks a name of at most 2 ^ 31 bytes, and `recordSeeds_blocks`
covers names of up to 2 ^ 32 - 200 bytes. So no way back is written for it here. The name of a
stored table with a root and a digest of 32 bytes has 112 bytes (`size_nameOf`,
OnBytes/K/SeedBytes.lean).

What is not claimed. Nothing on how the seeds are distributed; nothing on any hash function; nothing
on soundness. That any program or any verifier computes `Tie.seedsAt O`.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.SeedBytes
import OnBytes.Tie.EntryAtRec
import OnBytes.Slice.SeedRow

set_option autoImplicit false

namespace OnBytes.K

/-- The string of a block of the seeds' round, with the half as a byte of the block's number modulo
2. -/
theorem seedStr_blockStr (ρ0 : ByteArray) (b : ℕ) : seedStr ρ0 b = Slice.blockStr ρ0 b := by
  unfold seedStr Slice.blockStr
  rcases Nat.mod_two_eq_zero_or_one b with e | e
  · rw [e, if_pos rfl]
    rfl
  · rw [e, if_neg (by decide)]
    rfl

variable (O : ByteArray → ByteArray)

/-- Block t of the verifier's message in the seeds' round, at the oracle O. -/
def seedBlockO (name : ByteArray) (t : ℕ) : ByteArray :=
  O (seedStr (O (seedFirst name)) (t + 1))

/-- The seeds as a function of the table's name, at the oracle O. -/
def seedsAtNameO (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ) : List (List E × E) :=
  seedsOf f bits count ((Array.range (nBlocks bits count)).map (seedBlockO O name))

/-- The first K blocks of the verifier's message in the seeds' round at O, as digests. -/
def seedDigsO (name : ByteArray) (K : ℕ) : Fin K → Iop.Dig 256 :=
  fun t => Run.bytesToDig (seedBlockO O name t.val)

variable (hO : ∀ s, (O s).size = 32)

include hO in
/-- **The seeds at O are the program's draws on O's answers at the written strings.** -/
theorem recordSeeds_blocksG (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ) :
    Tie.seedsAt O f name bits count = some (seedsAtNameO O f name bits count) := by
  obtain ⟨c, vb, hq, hv⟩ := Slice.seedRound_HO O hO (O (seedFirst name)) (hO _)
    (nBlocks bits count)
  have hr : Fmt.rowOf vb =
      Fmt.rowOf ((Array.range (nBlocks bits count)).map (seedBlockO O name)) := by
    refine Slice.rowOf_congr _ _ fun j => ?_
    rw [hv j, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    by_cases hj : j < nBlocks bits count
    · rw [if_pos hj, if_pos hj, ← seedStr_blockStr]
      rfl
    · rw [if_neg hj, if_neg hj]
      rfl
  unfold Tie.seedsAt
  rw [Slice.recordSeedsW_pure]
  show (Fmt.Chain.queryW (m := Id) (Fmt.HO O) ⟨Fmt.recordLabel, O (seedFirst name), 0⟩
    ByteArray.empty .seeds 0 0 (nBlocks bits count)).map _ = _
  rw [hq]
  show some (seedsOf f bits count vb) = _
  unfold seedsAtNameO seedsOf
  rw [hr]

include hO in
/-- The seeds of the K digests of the seeds' round at O are the seeds at the name, if K is at least
the number of blocks that the program fetches. -/
theorem seedsOfDigs_seedDigsG (f : Fmt.Fld) (name : ByteArray) (bits count K : ℕ)
    (hK : nBlocks bits count ≤ K) :
    seedsOfDigs f bits count (seedDigsO O name K) = seedsAtNameO O f name bits count := by
  have e : ((Array.range (nBlocks bits count)).map fun t =>
      if h : t < K then Run.digToBytes (seedDigsO O name K ⟨t, h⟩) else ByteArray.empty) =
      (Array.range (nBlocks bits count)).map (seedBlockO O name) := by
    refine Array.map_congr_left fun k hk => ?_
    have hk' : k < nBlocks bits count := Array.mem_range.1 hk
    have hb : Run.digToBytes (Run.bytesToDig (seedBlockO O name k)) = seedBlockO O name k :=
      Run.TieTree.dig_bytes (seedBlockO O name k) (hO _)
    rw [dif_pos (show k < K by omega)]
    exact hb
  unfold seedsOfDigs seedsAtNameO
  rw [e]

omit O in
/-- The text of `seedBlockO`, at a letter for the oracle. -/
theorem seedBlockO_text (O : ByteArray → ByteArray) (name : ByteArray) (t : ℕ) :
    seedBlockO O name t = O (seedStr (O (seedFirst name)) (t + 1)) := rfl

omit O in
/-- The text of `seedBlock`. -/
theorem seedBlock_text (name : ByteArray) (t : ℕ) :
    seedBlock name t = Fmt.oracle (seedStr (Fmt.oracle (seedFirst name)) (t + 1)) := by
  rw [seedBlock]

omit O in
/-- At the format's oracle it is `seedBlock`. The two texts are unfolded first, so that no checker
need unfold the oracle. -/
theorem seedBlockO_oracle : seedBlockO Fmt.oracle = seedBlock := by
  funext name t
  exact (seedBlockO_text Fmt.oracle name t).trans (seedBlock_text name t).symm

omit O in
/-- At the format's oracle it is `seedsAtName`. -/
theorem seedsAtNameO_oracle : seedsAtNameO Fmt.oracle = seedsAtName := by
  funext f name bits count
  unfold seedsAtNameO seedsAtName
  rw [seedBlockO_oracle]

omit O in
/-- At the format's oracle it is `seedDigs`. -/
theorem seedDigsO_oracle : seedDigsO Fmt.oracle = seedDigs := by
  funext name K
  unfold seedDigsO seedDigs
  rw [seedBlockO_oracle]

omit O in
/-- The statement of `seedsOfDigs_seedDigs`, from `seedsOfDigs_seedDigsG` at O := `Fmt.oracle`. -/
theorem seedsOfDigs_seedDigs_of_G (f : Fmt.Fld) (name : ByteArray) (bits count K : ℕ)
    (hK : nBlocks bits count ≤ K) :
    seedsOfDigs f bits count (seedDigs name K) = seedsAtName f name bits count := by
  rw [← seedDigsO_oracle, ← seedsAtNameO_oracle]
  exact seedsOfDigs_seedDigsG Fmt.oracle Fmt.size_oracle f name bits count K hK

end OnBytes.K
