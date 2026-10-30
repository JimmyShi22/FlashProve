-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedRow.lean: the seed of a key's table under an oracle g is `toSeed` of the value of
the library's block sampler on g's answers at the strings of the seeds' round.

OnBytes/Slice/SeedTie.lean ties the program's draw to the library's sampler on a row of words. Here
the row is the one that the program reads: the words of a block of 256 bits, as the library cuts
them, are the words that the format reads off the block's 32 bytes (the library's `word_tie`,
Run/ToyChalLaw.lean); and the blocks of the seeds' round at the hash over a function are that
function's values at written strings (the library's `fetchW_getD`, Fmt/Rules5Row.lean, and
`blockW_HO`, Run/ChainRow.lean).

Main definitions.
 `blockBytes u`         b blocks of 256 bits as an array of b strings of 32 bytes.
 `blockStr ρ0 j`        the string of block j of the seeds' round at the start ρ0: half (j mod 2) of
                        call (j div 2).
 `blocksUnder g name b` g's answers at the strings of the blocks 1, 2, .., b, at the start that g
                        gives at the string of the table's name.
Main theorems.
 `rowOf_blocks`         THE WORDS OF A BLOCK: `Fmt.rowOf` of the blocks' bytes is the library's row
                        of the blocks' words.
 `seedTie_bytes`        the expression of `recordSeeds` behind its round's query, on the bytes of u,
                        is `toSeed` of the sampler's value on u.
 `coll_pr_bytes`, `coll_pr_bytes_full`   the bound of OnBytes/Slice/SeedBias.lean with that
                        expression; at the sizes of OnBytes/Slice/RecordFull.lean: sizes, bytes and
                        bound in one theorem.
 `recordSeedsW_Id`, `seedRound_HO`   the text of `recordSeeds` at the hash over a function, unfolded
                        to its one round; that round's message, block by block. A tool:
                        `rowOf_congr`.
 `seedUnder_eq`         THE SEED UNDER g (`seedUnder`, OnBytes/Slice/SeedWhich.lean), for every key
                        and every g.

WHAT IS NOT SHOWN. lg and s are arguments: that they are the numbers of the key's shape is shown at
the sizes of OnBytes/Slice/RecordFull.lean alone (`recShape_cubeBits`, `recShape_sizes`); the field
is the second, where the program takes its plan's. THAT g's ANSWERS AT THESE STRINGS ARE UNIFORM AND
INDEPENDENT OF THE TABLE IS NOT SHOWN HERE; for one name fixed beforehand:
OnBytes/Slice/SeedOracle.lean. Of the rest: of limit (3) of OnBytes/Slice/SeedBias.lean the first
sentence is paid here (which strings and which blocks are read, and that block 0 is not); the rest
stands. The strings are pairwise different and different from the name's string
(OnBytes/Slice/SeedStrings.lean; false beyond 2^49 blocks). A committer chooses its table, and so
the name, after questions of its own, and can ask strings of the round at starts of its choice
before it asks the name's string. So no probability over g is stated here. One table; no number
evaluated. Nothing on any hash function.

-/
import OnBytes.Slice.SeedTie
import Run.ToyChalLaw
import Run.ChainRow
import OnBytes.Slice.SeedWhich

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb Cb.Ood _root_.Iop _root_.Run Rom
open OnBytes.Tie (IdKey)

/-- b blocks of 256 bits as an array of b strings of 32 bytes. -/
def blockBytes {b : ℕ} (u : Fin b → Dig 256) : Array ByteArray :=
  Array.ofFn fun i => digToBytes (u i)

/-- **THE WORDS OF A BLOCK**: the row of words that the format reads off the blocks' bytes
(`Fmt.rowOf`) is the row of words into which the library cuts the blocks' bits; 0 beyond the last
block in both. -/
theorem rowOf_blocks {b : ℕ} (u : Fin b → Dig 256) :
    Fmt.rowOf (blockBytes u) = rowFn 0 (rowOf e64 b u) := by
  funext t
  unfold Fmt.rowOf rowFn blockBytes
  by_cases ht : t < 4 * b
  · have h4 : t / 4 < b := by omega
    rw [dif_pos ht]
    have e : (Array.ofFn fun i => digToBytes (u i)).getD (t / 4) ByteArray.empty =
        digToBytes (u ⟨t / 4, h4⟩) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos h4]
      rfl
    rw [e]
    exact word_tie (u ⟨t / 4, h4⟩) ⟨t % 4, Nat.mod_lt _ (by decide)⟩
  · have h4 : ¬ t / 4 < b := by omega
    rw [dif_neg ht]
    have e : (Array.ofFn fun i => digToBytes (u i)).getD (t / 4) ByteArray.empty =
        ByteArray.empty := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_neg h4]
      rfl
    have hb : ∀ i, Fmt.byteAt ByteArray.empty i = 0 := fun i => dif_neg (Nat.not_lt_zero i)
    rw [e]
    unfold Fmt.wordAt
    simp only [hb]
    decide

/-- **The program's seeds off the blocks' bytes are `toSeed` of the library's sampler on the
blocks**: the expression of `recordSeeds` behind its round's query, with `vb` the bytes of u. -/
theorem seedTie_bytes (lg s : ℕ) (u : Fin (seedBS lg s).b → Dig 256) :
    seedOf lg s ((timesT (Fmt.drawSeed .two lg) s (Fmt.rowOf (blockBytes u)) 0).1.map fun x =>
        (x.1.map E.ofTriple, E.ofTriple x.2)) =
      toSeed lg s ((seedBS lg s).φ u) := by
  rw [rowOf_blocks]
  exact seedTie lg s u

/-- **The bound of OnBytes/Slice/SeedBias.lean on the blocks' bytes**: for ONE stored table f, fixed
before the blocks, within the Johnson bound: over uniform blocks, the seeds that the expression of
`recordSeeds` behind its round's query draws from the blocks' bytes are such that the record does
not single one table out with probability at most the bound of `coll_pr`. -/
theorem coll_pr_bytes (T : Fmt.M1.Code) (v eM lg s : ℕ) (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (f : Fin (2 ^ T.a) → Run.PQ.SgX) :
    pr (unif (Fin (seedBS lg s).b → Dig 256))
        {u | (decRec T v eM lg s).coll f (seedOf lg s
          ((timesT (Fmt.drawSeed .two lg) s (Fmt.rowOf (blockBytes u)) 0).1.map fun x =>
            (x.1.map E.ofTriple, E.ofTriple x.2)))} ≤
      kapSl 128 ^ (seedBS lg s).b *
        ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
          ENNReal) / Fintype.card (recZ T.l lg s).D) := by
  have h := coll_pr_toSeed T v eM lg s ha hk he hJ h3 hl f
  simp only [← seedTie_bytes] at h
  exact h

/-- **SIZES, BYTES AND BOUND IN ONE THEOREM**: the same at the sizes of
OnBytes/Slice/RecordFull.lean; the radius eM is an argument, within the Johnson bound. ONE table f,
fixed before the blocks. Uniform blocks, not an oracle's answers. No number on the right is
evaluated. -/
theorem coll_pr_bytes_full (eM : ℕ) (he : eM < 3848273922)
    (hJ : InJohnson (2 ^ 32) 3848273922 eM) (f : Fin (2 ^ recT.a) → Run.PQ.SgX) :
    pr (unif (Fin (seedBS recLg recS).b → Dig 256))
        {u | (decRecFull eM).coll f (seedOf recLg recS
          ((timesT (Fmt.drawSeed .two recLg) recS (Fmt.rowOf (blockBytes u)) 0).1.map fun x =>
            (x.1.map E.ofTriple, E.ofTriple x.2)))} ≤
      kapSl 128 ^ 140 *
        ((((listMax (2 ^ 32) 3848273922 eM).choose 2 * (recZ recT.l recLg recS).err : ℕ) :
          ENNReal) / Fintype.card (recZ recT.l recLg recS).D) := by
  have h := coll_pr_bytes recT recV eM recLg recS (by decide) (by decide) he hJ recT_room.1
    recT_room.2 f
  have e : kapSl 128 ^ (seedBS recLg recS).b = kapSl 128 ^ 140 := by rw [seedBS_b_full]
  rwa [e] at h

/-! ## The seed under an oracle -/

/-- The string of block j of the seeds' round, at the start ρ0: half (j mod 2) of call (j div 2). -/
def blockStr (ρ0 : ByteArray) (j : ℕ) : ByteArray :=
  Fmt.oStr (UInt8.ofNat (j % 2)) 162 Fmt.recordLabel 1 ρ0
    (ByteArray.empty ++ Fmt.tail .seeds 0 0 (j / 2))

/-- **The blocks that the draw reads, off the oracle g**: g's answers at the strings of the blocks
1, 2, .. of the seeds' round, at the start that g gives at the string of the table's name. Block 0
is the chain's next value, and the draw does not read it. -/
def blocksUnder (g : Fam (rom 256)) (name : ByteArray) (b : ℕ) : Fin b → Dig 256 :=
  fun i => g () (bytesToBits (blockStr (oB (g ()) (seedFirst name)) (i.val + 1)))

/-- Two arrays with the same members give the same row of words. -/
theorem rowOf_congr (a c : Array ByteArray)
    (h : ∀ j, a.getD j ByteArray.empty = c.getD j ByteArray.empty) : Fmt.rowOf a = Fmt.rowOf c := by
  funext t
  unfold Fmt.rowOf
  rw [h]

/-- The text of `recordSeeds` at the hash over a function O, unfolded to its one round. -/
theorem recordSeedsW_Id (O : ByteArray → ByteArray) (name : ByteArray) (lg s : ℕ) :
    recordSeedsW (m := Id) (Fmt.HO O) .two name lg s =
      (Fmt.Chain.queryW (m := Id) (Fmt.HO O) ⟨Fmt.recordLabel, O (seedFirst name), 0⟩
        ByteArray.empty .seeds 0 0 (Fmt.blocksFor (s * (lg * 18 + 36)))).map fun x =>
          (timesT (Fmt.drawSeed .two lg) s (Fmt.rowOf x.2) 0).1.map fun y =>
            (y.1.map E.ofTriple, E.ofTriple y.2) := rfl

/-- **The seeds' round at the hash over a function O with answers of 32 bytes**: the verifier's
message is, block by block, O at the strings of the blocks 1, 2, .. . -/
theorem seedRound_HO (O : ByteArray → ByteArray) (hO : ∀ x, (O x).size = 32) (ρ0 : ByteArray)
    (h0 : ρ0.size = 32) (K : ℕ) :
    ∃ c vb, Fmt.Chain.queryW (m := Id) (Fmt.HO O) ⟨Fmt.recordLabel, ρ0, 0⟩ ByteArray.empty
        .seeds 0 0 K = some (c, vb) ∧
      ∀ j, vb.getD j ByteArray.empty =
        if j < K then O (blockStr ρ0 (j + 1)) else ByteArray.empty := by
  have hf : Fmt.firstBlock 0 = 1 := rfl
  have ha : Fmt.askOK Fmt.recordLabel ρ0 (0 + 1) ByteArray.empty .seeds 0 0 = true := by
    unfold Fmt.askOK
    rw [h0]
    decide
  have hsz := Fmt.size_fetchW (Fmt.HO O) Fmt.recordLabel ρ0 (0 + 1) ByteArray.empty .seeds 0 0
    (Fmt.firstBlock 0 + K)
  refine ⟨⟨Fmt.recordLabel, Fmt.nextA 0 (Fmt.fetchW (m := Id) (Fmt.HO O) Fmt.recordLabel ρ0 (0 + 1)
    ByteArray.empty .seeds 0 0 (Fmt.firstBlock 0 + K)), 0 + 1⟩,
    Fmt.msgA 0 (Fmt.fetchW (m := Id) (Fmt.HO O) Fmt.recordLabel ρ0 (0 + 1)
    ByteArray.empty .seeds 0 0 (Fmt.firstBlock 0 + K)), ?_, fun j => ?_⟩
  · unfold Fmt.Chain.queryW
    rw [if_pos ha]
    rfl
  · unfold Fmt.msgA
    by_cases hj : j < K
    · have hg := Fmt.fetchW_getD (Fmt.HO O) Fmt.recordLabel ρ0 (0 + 1) ByteArray.empty .seeds 0 0
        (Fmt.firstBlock 0 + K) (Fmt.firstBlock 0 + j) (by omega)
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsz]; omega)] at hg
      rw [if_pos hj, Array.getD_eq_getD_getElem?, Array.getElem?_extract_of_lt
        (by rw [hsz]; omega), hg, blockW_HO _ hO, hf, Nat.add_comm 1 j]
      rfl
    · rw [if_neg hj, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
        rw [Array.size_extract, hsz]
        omega)]
      rfl

/-- **THE SEED UNDER g IS `toSeed` OF THE LIBRARY'S SAMPLER ON g'S ANSWERS AT THE STRINGS OF THE
SEEDS' ROUND.** -/
theorem seedUnder_eq (lg s : ℕ) (k : IdKey) (g : Fam (rom 256)) :
    seedUnder lg s k g = some (toSeed lg s ((seedBS lg s).φ
      (blocksUnder g (Key.nameOf k.1 k.2.1 k.2.2) (seedBS lg s).b))) := by
  have hO : ∀ x, (oB (g ()) x).size = 32 := fun _ => size_digToBytes _
  obtain ⟨c, vb, hq, hv⟩ := seedRound_HO (oB (g ())) hO
    (oB (g ()) (seedFirst (Key.nameOf k.1 k.2.1 k.2.2))) (hO _)
    (Fmt.blocksFor (s * (lg * 18 + 36)))
  have hr : Fmt.rowOf vb =
      Fmt.rowOf (blockBytes (blocksUnder g (Key.nameOf k.1 k.2.1 k.2.2) (seedBS lg s).b)) := by
    refine rowOf_congr _ _ fun j => ?_
    rw [hv j, ← seedBS_b lg s]
    unfold blockBytes
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    by_cases hj : j < (seedBS lg s).b
    · rw [if_pos hj, dif_pos hj]
      rfl
    · rw [if_neg hj, dif_neg hj]
      rfl
  rw [← seedTie_bytes, ← hr]
  unfold seedUnder
  rw [recordSeedsW_Id, hq]
  rfl

end OnBytes.Slice
