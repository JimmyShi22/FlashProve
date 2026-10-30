-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/LeafWrites.lean: where the code of leaf queries over strings of bits
(`KeyLeaves.leafCode`, OnBytes/TypedOracleCompiler/Run/KeyLeaves.lean) writes.

That code is partial. OnBytes/TypedOracleCompiler/Run/KeyLeaves.lean says what its strings are where it writes
(`leafCode_str`). Here stands the other half: three tests on a leaf query are enough for it to
write, and they hold at the format's spelling of a leaf of a run's tree and of a stored table's
symbol, whichever file the tree is of. For proofs only; the program does not import this file.

Main theorems.
 `leafCode_some`   it writes at a query whose typed salt has 256 + nb bits, whose body passes `ok2`,
                  and which passes `leafOK2 cfg`.
 `leafCode_own`    so it writes at the bits of a label under 164 and of any bytes, under a typed
                  salt "32 bytes of start, then k bytes", if nb = 8 k, the label's place is below
                  2^48 and its index below 2^64.
 `leafCode_sto`    and at the string `TypedOracleCompiler.Run.storedStr a k y` of a stored table's symbol
                  (OnBytes/TypedOracleCompiler/Run/Tag174.lean), under the typed salt "cfg, then k bytes", where
                  `storedOK a k y` holds and cfg has 32 bytes.

Not claimed. That it writes nowhere else. At a salt of another length than k bytes it writes
nothing: that all trees of three files have salts of one length is said nowhere here. Under 174 it
writes at no other start than cfg. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.KeyLeaves

set_option autoImplicit false

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Strings
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I0 X0 : Type} (L0 : _root_.Iop.BatchProtocol I0 X0) (nb : ℕ) (cfg : ByteArray)

/-- **Three tests are enough for the code of leaf queries to write.** -/
theorem leafCode_some (q : LeafIn (strung L0)) (hl : q.salt.length = 256 + nb)
    (hk : ok2 q.body = true) (ho : leafOK2 L0 cfg q = true) :
    ∃ s, (KeyLeaves.leafCode L0 nb cfg).put q = some s := by
  obtain ⟨y0, sa⟩ := q
  obtain ⟨y, rfl⟩ : ∃ y : List Bool, y = y0 := ⟨y0, rfl⟩
  refine ⟨pre33 ++ (sa.take 256 ++ (y ++ sa.drop 256)), ?_⟩
  show (if leafOK2 L0 cfg ⟨y, sa⟩ = true then
      (pLeaf (L := strung L0) nb (pBody ok2)).put ⟨y, sa⟩ else none) = _
  rw [if_pos ho]
  show (if sa.length = 256 + nb then
      ((pBody ok2).put y).map (fun m => pre33 ++ (sa.take 256 ++ (m ++ sa.drop 256)))
    else none) = _
  rw [if_pos hl]
  show ((if ok2 y then some y else none : Option (List Bool))).map
    (fun m => pre33 ++ (sa.take 256 ++ (m ++ sa.drop 256))) = _
  rw [if_pos hk]
  rfl

/-- The typed salt "32 bytes of start, then k bytes" has 256 + 8 k bits. -/
theorem salt_len (k : ℕ) (start s0 : ByteArray) (hs : start.size = 32) (h0 : s0.size = k) :
    (bytesToBits start ++ bytesToBits s0).length = 256 + 8 * k := by
  rw [List.length_append, length_bytesToBits, length_bytesToBits, hs, h0]

/-- **At the format's spelling of a leaf of a run's tree.** -/
theorem leafCode_own (k : ℕ) (hn : nb = 8 * k) (place ix : ℕ) (z start s0 : ByteArray)
    (hp : place < 2 ^ 48) (hi : ix < 2 ^ 64) (hs : start.size = 32) (h0 : s0.size = k) :
    ∃ s, (KeyLeaves.leafCode L0 nb cfg).put
      ⟨spell2 164 (place, ix, z), bytesToBits start ++ bytesToBits s0⟩ = some s :=
  leafCode_some L0 nb cfg _ (by rw [hn]; exact salt_len k start s0 hs h0)
    (ok2_spell 164 place ix z (Or.inl rfl) hp hi)
    (leafOK2_own L0 cfg _ (spell2_take 164 _).2)

/-- **At the string of a stored table's symbol.** -/
theorem leafCode_sto (k : ℕ) (hn : nb = 8 * k) (a : ℕ) (y : ℕ × List UInt64)
    (hy : TypedOracleCompiler.Run.storedOK a k y) (s0 : ByteArray) (hc : cfg.size = 32)
    (h0 : s0.size = k) :
    ∃ s, (KeyLeaves.leafCode L0 nb cfg).put
      ⟨TypedOracleCompiler.Run.storedStr a k y, bytesToBits cfg ++ bytesToBits s0⟩ = some s := by
  have hp : _root_.Fmt.leafPlace 0 y.2.length (k / 8) < 2 ^ 48 := by
    have := hy.2.1
    omega
  refine leafCode_some L0 nb cfg _ (by rw [hn]; exact salt_len k cfg s0 hc h0)
    (ok2_spell 174 _ _ _ (Or.inr rfl) hp hy.2.2) ?_
  unfold leafOK2
  split
  · show (bitsToBytes ((bytesToBits cfg ++ bytesToBits s0).take 256) == cfg) = true
    rw [List.take_left' (by rw [length_bytesToBits, hc]), bitsToBytes_bytesToBits]
    rcases cfg with ⟨d⟩
    exact beq_self_eq_true d
  · rfl

end OnBytes.K.Arm
