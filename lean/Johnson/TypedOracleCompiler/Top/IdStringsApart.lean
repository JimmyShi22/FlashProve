-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/IdStringsApart.lean: the commitment ID's string without the record's seed and its
string with the seed and an empty list of further digests are never equal: no bit string is a code
of both kinds.

Why. OnBytes/Tie/IdKey.lean has the string of the format's call 179 without the record's seed: the
configuration's digest, the table's name, the record's answers. OnBytes/Tie/IdKeySeed.lean has it
with the seed in front of the answers and a list of further digests behind them. A verifier that
compares one commitment with the hash function's answers at a string of each kind says yes only
where the function gives one answer at two different strings. This file has the "different".

Main names (namespace `OnBytes.K.Arm`):
  `idBytes_ne`: within `idOk` and `idOkS`, and where the list of further digests is empty, the bytes
    of a key without a seed (`IdKey`) are not the bytes of a key with a seed (`IdKeyS`): WHATEVER
    THE TWO KEYS HOLD. By lengths: 160 + 24 a bytes against 176 + 24 (m + a') bytes, and 16 is no
    multiple of 24.
  `idStr_ne`: so the two strings at which an oracle is asked differ. `idCode_ne`: so no bit string
    is the code of a key without a seed and of a key with a seed.
What is not claimed. Nothing where the list of further digests is not empty: with one digest of 32
bytes the lengths can meet (16 + 32 is twice 24), and this proof does not go through; the statement
may hold there all the same, by the count word behind the name: not proved here. Nothing outside
`idOk` and `idOkS`. WHOSE STRINGS: `idBytes` and `idBytesS` are this library's texts of two strings;
which of them a program or its twin hashes is not said here. Nothing on any verifier: that a given
one asks at both strings is not said here. No hash function, no probability, nothing on soundness.
For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.Top.IdSeedBytes

set_option autoImplicit false

namespace OnBytes.K.Arm
open OnBytes.Tie (IdKey idBytes idOk idStr idCode idOk_dom IdKeyS idBytesS idOkS idStrS idCodeS
  idOkS_dom)
open OnBytes.K.IdTable (size_idBytes)

/-- **The bytes without a seed are never the bytes with a seed**, where the list of further digests
is empty. By lengths. -/
theorem idBytes_ne (k : IdKey) (K : IdKeyS) (h : idOk k = true) (h' : idOkS K = true)
    (hT : K.told = []) : idBytes k ≠ idBytesS K := by
  intro e
  have s := congrArg ByteArray.size e
  rw [size_idBytes, size_idBytesS K hT] at s
  unfold idOk at h
  unfold idOkS at h'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h h'
  obtain ⟨⟨⟨-, ac⟩, ar⟩, -⟩ := h
  obtain ⟨⟨⟨⟨-, bc⟩, br⟩, -⟩, -⟩ := h'
  omega

/-- So the two strings at which an oracle is asked differ. -/
theorem idStr_ne (k : IdKey) (K : IdKeyS) (h : idOk k = true) (h' : idOkS K = true)
    (hT : K.told = []) : idStr k ≠ idStrS K := by
  intro e
  unfold idStr idStrS at e
  exact idBytes_ne k K h h' hT
    (Fmt.oStr_inj 0 0 179 179 0 0 0 0 _ _ _ _ (Or.inl rfl) (Or.inl rfl) (idOk_dom h)
      (idOkS_dom h') e).2.2.2.2.2

/-- **No bit string is the code of a key without a seed and of a key with a seed and no further
digest.** -/
theorem idCode_ne (k : IdKey) (K : IdKeyS) (hT : K.told = []) (c : ZKCP.Str)
    (hc : idCode k = some c) : idCodeS K ≠ some c := by
  intro hc'
  unfold idCode at hc
  unfold idCodeS at hc'
  split at hc
  · rename_i h
    split at hc'
    · rename_i h'
      exact idStr_ne k K h h' hT
        (_root_.Run.bytesToBits_inj ((Option.some.inj hc).trans (Option.some.inj hc').symm))
    · cases hc'
  · cases hc

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.idBytes_ne
#print axioms OnBytes.K.Arm.idStr_ne
#print axioms OnBytes.K.Arm.idCode_ne
