-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/IdOff.lean: the string of a call of the format's hash under a number that is not 179
modulo 65536 is no code of what enters the commitment ID's string without the record's seed, and the
search for the first key of an ID in a query log does not see entries whose queries are no codes.

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed.

OnBytes/Tie/IdKey.lean codes a shape, 32 bytes for the digest of the public files, and a table as
one bit string (`idCode`): the string of the format's call 179 on their bytes. The three together
are a key (`IdKey`): the library's word for what a digest stands for, not the key file.
OnBytes/Tie/IdRom.lean looks in a query log for the first key of a digest (`firstId`). A bound under
a random oracle may leave the entries at some fixed strings out of a log, such as the strings at
which digests of public bytes are asked for (the number 169). This file has the two lemmas from
which it follows that this changes nothing for `firstId`; no theorem here joins them.

Main theorems.
- `idCode_ne_call`, `idRead_call`: the bits of `Fmt.oStr half n t i st bs` are no key's code, and
  `idRead` refuses them, if n is not 179 modulo 65536. No other condition on the arguments: by
  `oStr_number` (OnBytes/Tie/DigestPoint.lean).
- `firstId_filter`: a log from which entries are left out whose queries `idRead` refuses has the
  same `firstId`, for every digest.

What is not claimed. Nothing on soundness and no probability. `idCode_ne_call` and `idRead_call`
speak of calls' strings alone. All limits in the heads of the files named above, and of
OnBytes/Tie/IdRead.lean, hold here too. Nothing is said of the program, which is the Lean port built
from OnBytes/. For proofs only; the program does not import this file.

-/
import OnBytes.Tie.IdRom
import OnBytes.Tie.DigestPoint

set_option autoImplicit false

namespace OnBytes.Tie

open ZKCP
open Rom (rom)

/-- The string of a call under a number that is not 179 modulo 65536 is, as bits, no key's code. -/
theorem idCode_ne_call {n : ℕ} (hn : n % 65536 ≠ 179) (half : UInt8) (t i : ℕ)
    (st bs : ByteArray) (k : IdKey) :
    idCode k ≠ some (Run.bytesToBits (Fmt.oStr half n t i st bs)) := by
  intro h
  unfold idCode at h
  split at h
  · have e := Run.bytesToBits_inj (Option.some.inj h)
    unfold idStr at e
    have h1 := oStr_number 0 179 0 0 Fmt.zero32 (idBytes k)
    have h2 := oStr_number half n t i st bs
    rw [e, h2] at h1
    exact hn (by omega)
  · cases h

/-- `idRead` refuses the bits of the string of a call under a number that is not 179 modulo 65536.
-/
theorem idRead_call {n : ℕ} (hn : n % 65536 ≠ 179) (half : UInt8) (t i : ℕ)
    (st bs : ByteArray) : idRead (Run.bytesToBits (Fmt.oStr half n t i st bs)) = none := by
  cases h : idRead (Run.bytesToBits (Fmt.oStr half n t i st bs)) with
  | none => rfl
  | some k => exact absurd ((idRead_iff k _).1 h) (idCode_ne_call hn half t i st bs k)

/-- `firstId` does not see entries whose queries `idRead` refuses: for every test p on entries, if
`idRead` refuses the query of every entry of the log that fails p, the log's entries that pass p
have the same first key of d as the log. -/
theorem firstId_filter (d : Digest 256) (p : Rom.QA (rom 256) → Bool) :
    ∀ σ : Rom.Trace (rom 256), (∀ e ∈ σ, p e = false → idRead e.2.1 = none) →
      firstId d (σ.filter p) = firstId d σ
  | [], _ => rfl
  | e :: σ, h => by
    have ih := firstId_filter d p σ fun x hx => h x (List.mem_cons_of_mem _ hx)
    unfold firstId at ih ⊢
    cases hp : p e with
    | true =>
      rw [List.filter_cons_of_pos (by rw [hp]), List.findSome?_cons, List.findSome?_cons, ih]
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true), List.findSome?_cons,
        h e List.mem_cons_self hp, ih, ite_self]

end OnBytes.Tie
