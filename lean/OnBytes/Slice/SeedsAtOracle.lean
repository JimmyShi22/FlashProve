-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedsAtOracle.lean: at the hash over the realised oracle the generic text of the
program's `recordSeeds` is the program's `recordSeeds`, for names of at most 2^31 bytes; so at the
name of every stored table with a root and a configuration digest of 32 bytes.

`recordSeedsW` (OnBytes/Slice/RecordRead.lean) is the text of `recordSeeds`, generic in the hash; at
the format's own hash `Fmt.formatHash` it is `recordSeeds` (`recordSeedsW_H`). The library's `Fmt.HO_oracle`
says that on the domain of the hash, the hash over the realised oracle `Fmt.oracle` is `Fmt.formatHash`. The
text asks one call number 160, on the name, and calls number 162 of one round at the value of that
call; their data are in the domain (`seedFirst_dom`; `blockStr_dom`,
OnBytes/Slice/SeedStrings.lean).

How it is proved. The congruence is shown for two hashes that are VARIABLES. What speaks of the
format's own hash is written as terms, in named pieces, so that no checker need unfold a hash.

Main theorems.
 `queryW_congr`, `recordSeedsW_congr`   one step of a chain, and the text of `recordSeeds`, at two
                        plain hashes that agree where they ask.
 `seedFirst_dom`, `size_first_H`   the call number 160 on a name of at most 2^31 bytes is in the
                        domain; its value has 32 bytes.
 `recordSeedsW_oracle_H`   the text at `Fmt.HO Fmt.oracle` is the text at `Fmt.formatHash`.
 `recordSeedsW_oracle`  AT THE HASH OVER THE REALISED ORACLE THE TEXT IS THE PROGRAM'S
                        `recordSeeds`.
 `tableName_le`, `recordSeedsW_oracle_table`   so at `Fmt.tableName root cfg ..`, for a root and a
                        digest of 32 bytes. The numbers of coordinates and of seeds are free.

What is not claimed. Nothing on what the hash is: `Fmt.formatHash`, `Fmt.oracle` and `Fmt.HO_oracle` are
taken from the library by name. Nothing on an oracle that is drawn at random: this file has no
probability. That any checker runs this text. That the name is a key's (`nameOf_tableName`,
OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean, by unfolding). Names of more than 2^31
bytes.

-/
import OnBytes.Slice.SeedStrings
import Fmt.Rules23Laws

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Run

/-! ## Two plain hashes that agree where the text asks -/

section
variable (h h' : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)

/-- One step of a chain at two plain hashes that agree at the round's calls. Both hashes are
variables. -/
theorem queryW_congr (msg : ByteArray) (kind : Fmt.Kind) (w nonce : ℕ) (c : Fmt.Chain) (K : ℕ)
    (hc : ∀ j, j < (Fmt.firstBlock w + K + 1) / 2 →
      h 162 c.label (c.round + 1) c.rho (msg ++ Fmt.tail kind w nonce j) =
        h' 162 c.label (c.round + 1) c.rho (msg ++ Fmt.tail kind w nonce j)) :
    Fmt.Chain.queryW (m := Id) h c msg kind w nonce K =
      Fmt.Chain.queryW (m := Id) h' c msg kind w nonce K :=
  Option.some.inj
    ((queryW_some (fun n t i s b => some (h n t i s b)) h msg kind w nonce c K
        fun _ _ => rfl).symm.trans
      (queryW_some (fun n t i s b => some (h n t i s b)) h' msg kind w nonce c K
        fun j hj => congrArg some (hc j hj)))

/-- **The text of `recordSeeds` at two plain hashes that agree at the call number 160 on the name
and at every call number 162 at that start gives one value.** Both hashes are variables. -/
theorem recordSeedsW_congr (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ)
    (e0 : h 160 0 Fmt.recordLabel Fmt.zero32
        (Fmt.firstBytes Fmt.zero32 name ByteArray.empty none) =
      h' 160 0 Fmt.recordLabel Fmt.zero32 (Fmt.firstBytes Fmt.zero32 name ByteArray.empty none))
    (e1 : ∀ j, h 162 Fmt.recordLabel 1
        (h' 160 0 Fmt.recordLabel Fmt.zero32 (Fmt.firstBytes Fmt.zero32 name ByteArray.empty none))
        (ByteArray.empty ++ Fmt.tail .seeds 0 0 j) =
      h' 162 Fmt.recordLabel 1
        (h' 160 0 Fmt.recordLabel Fmt.zero32 (Fmt.firstBytes Fmt.zero32 name ByteArray.empty none))
        (ByteArray.empty ++ Fmt.tail .seeds 0 0 j)) :
    recordSeedsW (m := Id) h f name bits count = recordSeedsW (m := Id) h' f name bits count := by
  have a0 : Fmt.recordFirstW (m := Id) h name = Fmt.recordFirstW (m := Id) h' name := e0
  rw [recordSeedsW_pure, recordSeedsW_pure, a0,
    queryW_congr h h' ByteArray.empty .seeds 0 0
      ⟨Fmt.recordLabel, Fmt.recordFirstW (m := Id) h' name, 0⟩ _ fun j _ => e1 j]

end

/-! ## At the realised oracle -/

/-- The data of the call number 160 on a name of at most 2^31 bytes are in the domain of the
format's hash. -/
theorem seedFirst_dom (name : ByteArray) (hn : name.size ≤ 2 ^ 31) :
    Fmt.hDom 160 0 Fmt.recordLabel Fmt.zero32
      (Fmt.firstBytes Fmt.zero32 name ByteArray.empty none) = true :=
  dom0 160 Fmt.recordLabel _ (by decide) (by decide) (by decide) (by
    rw [size_seedBytes]
    omega)

/-- The first value of the seeds' chain at the format's own hash has 32 bytes. -/
theorem size_first_H (b : ByteArray) : (Fmt.formatHash 160 0 Fmt.recordLabel Fmt.zero32 b).size = 32 :=
  Fmt.size_H 160 0 Fmt.recordLabel Fmt.zero32 b

/-- **The text at the hash over the realised oracle is the text at the format's own hash**, for a
name of at most 2^31 bytes; bits and count are free. By `Fmt.HO_oracle`, call by call. -/
theorem recordSeedsW_oracle_H (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ)
    (hn : name.size ≤ 2 ^ 31) :
    recordSeedsW (m := Id) (Fmt.HO Fmt.oracle) f name bits count =
      recordSeedsW (m := Id) Fmt.formatHash f name bits count :=
  recordSeedsW_congr (Fmt.HO Fmt.oracle) Fmt.formatHash f name bits count
    (Fmt.HO_oracle 160 0 Fmt.recordLabel Fmt.zero32 _ (seedFirst_dom name hn))
    fun j => Fmt.HO_oracle 162 Fmt.recordLabel 1 _ _ (blockStr_dom _ (size_first_H _) j)

/-- **AT THE HASH OVER THE REALISED ORACLE THE TEXT IS THE PROGRAM'S `recordSeeds`**, for a name of
at most 2^31 bytes. -/
theorem recordSeedsW_oracle (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ)
    (hn : name.size ≤ 2 ^ 31) :
    recordSeedsW (m := Id) (Fmt.HO Fmt.oracle) f name bits count = recordSeeds f name bits count :=
  (recordSeedsW_oracle_H f name bits count hn).trans (recordSeedsW_H f name bits count)

/-- The name of a stored table with a root and a configuration digest of 32 bytes has at most 2^31
bytes (it has 112). -/
theorem tableName_le (root cfg : ByteArray) (hr : root.size = 32) (hc : cfg.size = 32)
    (a message tail logRows answers saltBytes : ℕ) :
    (Fmt.tableName root cfg a message tail logRows answers saltBytes).size ≤ 2 ^ 31 := by
  rw [Tie.size_tableName, hr, hc]
  decide

/-- **So at the name of a stored table**, for a root and a configuration digest of 32 bytes. -/
theorem recordSeedsW_oracle_table (f : Fmt.Fld) (root cfg : ByteArray) (hr : root.size = 32)
    (hc : cfg.size = 32) (a message tail logRows answers saltBytes bits count : ℕ) :
    recordSeedsW (m := Id) (Fmt.HO Fmt.oracle) f
        (Fmt.tableName root cfg a message tail logRows answers saltBytes) bits count =
      recordSeeds f (Fmt.tableName root cfg a message tail logRows answers saltBytes) bits count :=
  recordSeedsW_oracle f _ bits count
    (tableName_le root cfg hr hc a message tail logRows answers saltBytes)

end OnBytes.Slice

#print axioms OnBytes.Slice.queryW_congr
#print axioms OnBytes.Slice.recordSeedsW_congr
#print axioms OnBytes.Slice.seedFirst_dom
#print axioms OnBytes.Slice.size_first_H
#print axioms OnBytes.Slice.recordSeedsW_oracle_H
#print axioms OnBytes.Slice.recordSeedsW_oracle
#print axioms OnBytes.Slice.tableName_le
#print axioms OnBytes.Slice.recordSeedsW_oracle_table
