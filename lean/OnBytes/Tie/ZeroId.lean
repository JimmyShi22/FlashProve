-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/ZeroId.lean: the tables' shape, the digest of the public files and the table of a whole
call that returned 0, as one key in the sense of OnBytes/Tie/IdKey.lean.

Main definition: `idKeyOf`.
Main theorem.
- `zero_idOk`: under `ZeroFacts`, `idKeyOf w` is within `idOk`. The six numbers: `Key.readTable`
  refuses a shape that fails `Params.IndexShape.ok`. The digest's 32 bytes:
  `Params.configurationDigest_size`. The root's: `zero_table_root`. The size: the answers were read
  from the key file, which is within the files' limit (`readTable_size`).

What is not claimed. Nothing in this file ties `idKeyOf w` to the ID in the call's options:
OnBytes/Tie/IdKey.lean speaks of the string without the record's seeds, and the program hashes
another string. Under `ZeroFacts` the ID in the options, in lower-case digits, is the hexadecimal
form of `idAtS Fmt.oracle (idKeySOf w)`: the string with the seeds, whose base is `idKeyOf w`, at
the format's own oracle (`zero_idS`, OnBytes/K/Oracle/ZeroIdS.lean [not in this library]). No
probability and nothing on soundness. Nothing says that some
files make a call return 0. All limits in the heads of OnBytes/Tie/ZeroFacts.lean and
OnBytes/Tie/IdKey.lean hold here too. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.IdKey
import OnBytes.Tie.ZeroAt
import Fmt.Rules1Only

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Shell (World fileLimit)
open OnBytes.Model

/-- What enters the ID without seeds of a whole call: the tables' shape and the digest in p, and the
table that `Key.check` returned. A key in the sense of OnBytes/Tie/IdKey.lean, not the key file. -/
def idKeyOf (w : WholeSeen) : IdKey := (w.p.chains.tableShape, w.p.cfg, w.table)

/-- The answers that `OnBytes.readTable` returns, in the field in which the program computes, are,
as the format spells them, not longer than the bytes that they were read from. -/
theorem readTable_size {count : Nat} {b : ByteArray} {i : Nat} {t : Params.TableName} {j : Nat}
    (h : OnBytes.readTable .two count b i = .ok (t, j)) :
    (Fmt.cat ((t.answers.map E.triple).map Fmt.ext)).size ≤ b.size := by
  unfold OnBytes.readTable at h
  split at h
  · cases h
  · rename_i root j1 hd
    split at h
    · cases h
    · rename_i ys k hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      rw [rdManyT_eq] at hm
      have h1 := (Fmt.only_digest b i root j1 hd).2.2.1
      obtain ⟨_, _, e, hk, _⟩ := Fmt.only_many (Fmt.only_ext .two) count b j1 ys k h1 hm
      have e2 : (ys.map E.ofTriple).map E.triple = ys := by
        rw [List.map_map]
        exact List.map_id' ys
      show (Fmt.cat (((ys.map E.ofTriple).map E.triple).map Fmt.ext)).size ≤ b.size
      rw [e2]
      omega

/-- Under `ZeroFacts`, `idKeyOf w` is within `idOk`: it has a code. -/
theorem zero_idOk {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) : idOk (idKeyOf w) = true := by
  obtain ⟨j, hj⟩ := Verify.keyCheck_table h.keyYes
  have hroot := zero_table_root h
  have hcfg : w.p.cfg.size = 32 := by
    rw [h.same.1.1]
    exact Params.configurationDigest_size _
  unfold Key.readTable at hj
  split at hj
  · cases hj
  · rename_i hs
    split at hj
    · cases hj
    · rename_i i hi
      split at hj
      · cases hj
      · rename_i table j2 ht
        split at hj
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hj)
          have hz := readTable_size ht
          have hk := h.keySize
          have hok : w.p.chains.tableShape.ok = true := by
            simpa using hs
          unfold Params.IndexShape.ok Code.ok Params.IndexShape.pads Fmt.saltLenOK mostLogN at hok
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, c2⟩, _⟩, c4⟩, c5⟩, _⟩, _⟩, c8⟩, c9⟩, ⟨_, c11⟩⟩ := hok
          have p60 : 2 ^ w.p.chains.tableShape.code.logN ≤ 2 ^ 60 :=
            Nat.pow_le_pow_right (by decide) c2
          have hsz : (idBytes (idKeyOf w)).size ≤ 2 ^ 32 - 144 := by
            unfold idBytes idKeyOf Fmt.text Fmt.list Key.nameOf
            simp only [ByteArray.size_append, Fmt.size_u64n, size_tableName, hroot, hcfg]
            unfold fileLimit at hk
            omega
          unfold idOk
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hcfg⟩, hroot⟩, hsz⟩ <;>
            simp only [idKeyOf] <;> omega
        · cases hj

end OnBytes.Tie
