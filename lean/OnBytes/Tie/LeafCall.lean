-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/LeafCall.lean: from the exit code 3 of the command `verify -leaf` to a yes of
`Entry.check`.

OnBytes/Shell/AtPart.lean leads from the command to a yes of `Entry.check`.
OnBytes/Model/VerifyDerives.lean says how the parameter bytes under which that check ran follow from
the three configuration files. OnBytes/Tie/EntryClosedRec.lean leads from a yes of `Entry.check` at
given parameter bytes to a yes of the compiled verifier, a term of the library's theory and not
machine code. Here the first two are joined.

Main theorems.
- `leaf_call_check`: if the entry function `main`, called with
  `verify -leaf <config folder> <key file> <entry file>` and any options, returns 3, then the
  program's operations gave five reads that were answered with bytes, and then further steps;
  `Verify.planned` on the three configuration files' bytes returned a value p; `Params.entryBytesOf`
  of these bytes is some string; `Key.readTable`, under the tables' shape and the digest in p, read
  a first table, whose root has 32 bytes, from the key file's bytes; the entry file's bytes are at
  most 2^32 - 160; and `Entry.check` said yes on them, under that string and against that table.

What is not claimed. Nothing on soundness: of the compiled verifier's yes nothing is proved here. A
part that passed is no verification, and `verify -leaf` looks at none of the key's proofs: the first
table is read from the key file on its form alone, so nothing is known of it. It is read under the
shape in the key's one-time chain and checked under the shape in the entry's chain; that the two
agree is not stated.
No file proves of any files that `Params.entryBytesOf` of these files is a given string.

The limits in the heads of
OnBytes/Shell/AtPart.lean and OnBytes/Model/VerifyDerives.lean hold here too. The converse is not
stated, and nothing says that some files make the call pass. The bytes are the answers of the
program's reads in Lean's model of IO (OnBytes/Shell/AtOps.lean), and nothing says that they are a
file's content. Nothing about compiled code, Lean's run-time or the operating system. The program is
the Lean text `verify-on-bytes`; nothing here is said of the C++ program `cp_verify` or of how its
results compare. For proofs only; the program does not import this file.
-/
import OnBytes.Shell.AtPart
import OnBytes.Model.VerifyDerives
import OnBytes.Tie.SpecXBase

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Shell (Steps opsIO World Event fileLimit leafReads)

/-- The root of a table that `Key.readTable` has read has 32 bytes. -/
theorem keyTable_root {s : Params.IndexShape} {cfg file : ByteArray} {t : Params.TableName} {j : ℕ}
    (h : Key.readTable s cfg file = .ok (t, j)) : t.root.size = 32 := by
  unfold Key.readTable at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i table k ht
        split at h
        · injection h with h'
          have e : table = t := congrArg (·.1) h'
          rw [← e]
          exact readTable_root _ _ _ _ _ _ ht
        · cases h

/-- The command `verify -leaf`. If the entry function returns 3, the program's operations gave the
five reads, answered with bytes, and then the steps t. `Verify.planned` on the three configuration
files' bytes returned p, and `Params.entryBytesOf` of these bytes is the string `params`.
`Key.readTable`, under the tables' shape and the digest in p, read the table `first` from the key
file's bytes, and its root has 32 bytes. The entry file's bytes are at most 2^32 - 160, and
`Entry.check` said yes on them, under `params` and against `first`. -/
theorem leaf_call_check {config key entry : String} {options : List String} {s s' : World}
    (h : Shell.Run (_root_.main ("verify" :: "-leaf" :: config :: key :: entry :: options))
      s 3 s') :
    ∃ (pol kl lay kb ent params : ByteArray) (p : Model.Verify.Planned)
      (first further : Params.TableName) (j : ℕ) (t : List Event),
      Steps opsIO (leafReads config key entry pol kl lay kb ent ++ t) s s' ∧
      Model.Verify.planned pol kl (some lay) = .ok p ∧
      Params.entryBytesOf pol lay kl = some params ∧
      Key.readTable p.chains.tableShape p.cfg kb = .ok (first, j) ∧
      first.root.size = 32 ∧ ent.size + 16 ≤ 2 ^ 32 - 144 ∧
      Entry.check params first ent = .ok further := by
  obtain ⟨_, pol, kl, lay, kb, ent, cl, p, first, further, j, _, _, h1, _, _, _, _, h2, _, _, h3,
    h4, h5⟩ := Shell.main_leaf h
  refine ⟨pol, kl, lay, kb, ent, _, p, first, further, j, _, h1, h3,
    Model.Verify.planned_entryBytes h3, h4, keyTable_root h4, ?_, h5⟩
  have : fileLimit = 268435456 := rfl
  omega

end OnBytes.Tie

#print axioms OnBytes.Tie.leaf_call_check
