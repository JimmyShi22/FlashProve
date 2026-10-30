-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/CoinsAnchor.lean: THE COINS' ALGORITHM OF THE HONEST COMMITTER, AS FAR AS IT ASKS THE
HASH FUNCTION: the two strings that the rule on the programs' private randomness
(docs/format/COIN-KEYS.md, sections 1 and 2, the row "the anchor's commit run") has hashed, written;
what is made of the second answer and the secret seed is a letter. Definitions, statements and
proofs.

Why. Binding (Johnson/Top/DescribeTerms.lean, `BindLaws.coinsWithin`) lets the told committer's
number come by an algorithm that asks the hash function at most q times, and reads of that algorithm
q alone. By that page the anchor's pads, random entries and salts come by a generator, which asks no
hash, from a key K = take(take(child(1, 0), zeros), I), where I = H(176, 0, 0; four items) and one
item holds c, the configuration's digest. So the algorithm asks twice. Here it is written in that
form, so that q := 2 is a theorem about a term, and the strings can be read against the page.

Main names (namespace `VerifierAndGoals.Fit`).
  `coinItem name bytes`: an item: the length of its name in 8 bytes, the name, the length of its
    bytes in 8 bytes, the bytes (`Fmt.textS`, then `Fmt.text`, Fmt/Rules1.lean).
  `anchorItems c S`: the four items of the anchor's commit run: the title `a stored table's making`;
    `the configuration`: c; `the shape`: S; `the first table`. The first and the last have no bytes.
  `anchorString c S`: the oracle's string of H(176, 0, 0; these items), at half 0, as
    `VerifierAndGoals.configString` has it for c.
  `coinsAnchor Z S gen`: ask `VerifierAndGoals.configString Z`; at its answer c ask `anchorString c S`; at its
    answer I return gen ρ I.
  **`queryBound_coinsAnchor`**: it asks at most 2 queries. `evaluate_coinsAnchor`: its value at a
    hash function.

WHO READS EACH LETTER. Z: the first string (the three public files). S (the stored table's shape, as
bytes): the second string. gen (from the randomness and I to the result): the result alone; under
"for all". ρ: gen alone. No verifier reads anything here.

Limits.
- gen IS A LETTER: ChaCha20's block function, child, take, the paths of section 2a of the page, and
  the way from the values so made to the told committer's one number (the inverse of its two
  enumerations) are not written. Nothing says that a program's values are gen's.
- S IS A LETTER: that it is the words which the table's name holds after its two digests (R4.10) is
  not said.
- THE STRINGS ARE HELD AGAINST THE PAGE BY READING ALONE, at an edition not held against what ships;
  against no program's bytes and no test vector. By its own head that page is no part of
  the format and has not been independently reviewed.
- The hash function is the random oracle of the library: an answer is a digest of 256 bits at the
  string of half 0. That the programs' H at these bytes is that answer is the library's modelling of
  H, as for c.
- Nothing on hiding.
Terms: lean/GLOSSARY.md.

-/
import Ladder

set_option autoImplicit false

namespace VerifierAndGoals.Fit
open VerifiableInference

/-- An item of a key's list. -/
def coinItem (name : String) (bytes : ByteArray) : ByteArray := Fmt.textS name ++ Fmt.text bytes

/-- The four items of the anchor's commit run. -/
def anchorItems (c S : ByteArray) : ByteArray :=
  coinItem "a stored table's making" ByteArray.empty ++ coinItem "the configuration" c ++
    coinItem "the shape" S ++ coinItem "the first table" ByteArray.empty

/-- The oracle's string of H(176, 0, 0; the four items). -/
def anchorString (c : Digest) (S : ByteArray) : BitString :=
  _root_.Run.bytesToBits (Fmt.oStr 0 176 0 0 Fmt.zero32 (anchorItems (_root_.Run.digToBytes c) S))

/-- **The coins' algorithm**: the configuration's digest; the key's digest; then gen. -/
def coinsAnchor {Rand α : Type} (Z : PublicFiles) (S : ByteArray) (gen : Rand → Digest → α) (ρ : Rand) :
    DeterministicAlgorithm α :=
  .query (configString Z) fun c => .query (anchorString c S) fun I => .done (gen ρ I)

/-- **It asks at most twice.** -/
theorem queryBound_coinsAnchor {Rand α : Type} (Z : PublicFiles) (S : ByteArray) (gen : Rand → Digest → α)
    (ρ : Rand) : (coinsAnchor Z S gen ρ).toRandomized.QueryBound 2 :=
  fun _ _ => trivial

/-- Its value at a hash function. -/
theorem evaluate_coinsAnchor {Rand α : Type} (Z : PublicFiles) (S : ByteArray) (gen : Rand → Digest → α)
    (ρ : Rand) (hash : Hash) :
    (coinsAnchor Z S gen ρ).evaluate hash =
      gen ρ (hash (anchorString (hash (configString Z)) S)) := rfl

/- An item without bytes is its name's length, its name and the length 0: 8 + 15 + 8 bytes. -/
#guard (coinItem "the first table" ByteArray.empty).size == 31
/- The lengths stand lowest byte first. -/
#guard (coinItem "copy" (Fmt.zeroBytes 3)).data ==
  #[4, 0, 0, 0, 0, 0, 0, 0, 99, 111, 112, 121, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/- The four items at a digest of 32 bytes and a shape of two words. -/
#guard (anchorItems (Fmt.zeroBytes 32) (Fmt.zeroBytes 16)).size ==
  (8 + 23 + 8) + (8 + 17 + 8 + 32) + (8 + 9 + 8 + 16) + (8 + 15 + 8)
/- The call lies in H's domain. -/
#guard Fmt.hDom 176 0 0 Fmt.zero32 (anchorItems (Fmt.zeroBytes 32) (Fmt.zeroBytes 16))

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.queryBound_coinsAnchor
#print axioms VerifierAndGoals.Fit.evaluate_coinsAnchor
