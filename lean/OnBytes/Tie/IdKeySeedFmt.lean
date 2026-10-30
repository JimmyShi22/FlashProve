-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/IdKeySeedFmt.lean: the commitment ID's string as OnBytes/Tie/IdKeySeed.lean writes it is
`Fmt.publishedBytes` (Fmt/Rules4.lean), at all five arguments, and the ID at a function O is
`Fmt.publishedIDW` at the hash over O. No hypothesis.

What this file states. `publishedBytesS_fmt`: `publishedBytesS` is `Fmt.publishedBytes`, at all five
arguments. `idBytesS_fmt`: the bytes at a key are `Fmt.publishedBytes` at the key's digest, its
table's name, its seed's and its answers' elements as triples of words, and its further digests.
`idAtS_fmt`: the ID at O (`idAtS`) is `Fmt.publishedIDW` at the hash over O (`Fmt.HO O`).
`Fmt.publishedBytes` is Lean's text of the format's rule R4.11; that rule's string is the one at the
empty last list, at a seed list that holds the elements of the record's seeds, seed by seed the
point's coordinates and then the factor. OnBytes/Tie/IdKeySeed.lean proves that no bit string is the
code of two keys for the string that it writes out itself (`publishedBytesS`); this file links that
string to `Fmt.publishedBytes`.

Under which hypotheses. None: the three equations hold at all arguments.

What it does not show. A statement on strings and on one definition of Fmt/Rules4.lean: an equation
between two Lean texts, which checks nothing against the format's page or the programs. That a
program calls that rule at a key's own parts, and which seed it puts in, is not said here. Nor that
the last list is empty, which the format requires (its closing word 0), or that a digest in it is
the digest of anything: both arguments are unconstrained here, as in `Fmt.publishedBytes`. No
probability. For proofs only; the program does not import this file.


-/
import OnBytes.Tie.IdKeySeed

set_option autoImplicit false

namespace OnBytes.Tie

/-- The string that OnBytes/Tie/IdKeySeed.lean writes out is `Fmt.publishedBytes`. -/
theorem publishedBytesS_fmt (cfg name : ByteArray)
    (seed answers : List (UInt64 × UInt64 × UInt64)) (told : List ByteArray) :
    publishedBytesS cfg name seed answers told = Fmt.publishedBytes cfg name seed answers told :=
  publishedBytesS_eq cfg name seed answers told

/-- The bytes at a key, as `Fmt.publishedBytes` at its parts. -/
theorem idBytesS_fmt (k : IdKeyS) :
    idBytesS k = Fmt.publishedBytes k.base.2.1 (Key.nameOf k.base.1 k.base.2.1 k.base.2.2)
      (k.seed.map E.triple) (k.base.2.2.answers.map E.triple) k.told :=
  publishedBytesS_fmt _ _ _ _ _

/-- The ID at O is `Fmt.publishedIDW` at the hash over O. -/
theorem idAtS_fmt (O : ByteArray → ByteArray) (k : IdKeyS) :
    idAtS O k = Fmt.publishedIDW (m := Id) (Fmt.HO O) k.base.2.1
      (Key.nameOf k.base.1 k.base.2.1 k.base.2.2) (k.seed.map E.triple)
      (k.base.2.2.answers.map E.triple) k.told := by
  unfold idAtS Fmt.publishedIDW
  rw [idBytesS_fmt]

end OnBytes.Tie

#print axioms OnBytes.Tie.publishedBytesS_fmt
#print axioms OnBytes.Tie.idBytesS_fmt
#print axioms OnBytes.Tie.idAtS_fmt
