-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/BigOf.lean: what the makers of the key file's and the proof file's protocol take (`FilesParameters
X R`, OnBytes/Flat/FilesAt.lean), with the proof file's first block in the frame of the verifier
program's own first block.

Definitions. The makers `keyIOR` and `proofIOR` (OnBytes/Maker/Files.lean) take the data of a file's
rounds, by definition, from three dry runs at a sample record and instance, call the tests on them,
and stand at the empty data where a test fails. For a proof file they take the first chain's block
as a letter. Here that block is `Proof.firstBlock U.c.first (U.links x) (U.reply x)`: THE FRAME
`Proof.firstBlock` (OnBytes/Proof/File.lean) IS THE PROGRAM'S; THE LINKS' BLOCK `U.links`, THE REPLY
`U.reply` AND THE CHAINS `U.k`, `U.c` ARE LETTERS: any block is typed at `U.links`, also one that
fails at once or that states no round.

Main names:
  `Pub X`: the two files' chains' parameters (`k`, `c`: two free fields; no planner and no public
    file is named here), a table's name, the links' block and the reply as functions of an instance;
    an instance and a key; the most roots in one message; the number of slots; which part of an
    instance is fixed first.
  `Pub.block U x`: the first chain's block at an instance, as above.
  `bigOf U rec₀ : FilesParameters X R`: the first chain's block is `U.block`; the dry runs are made at the
    record rec₀ and at the instance `U.x₀`.
  `wholeOf`: kept for OnBytes/Flat/NotesToRounds.lean [not in this library].

Limits: nothing is proved here. AMONG THE STATEMENTS THAT NAME `bigOf` (no full list: later files
add to it): at a letter U: `innerCompiledVerifierSoundFromDryRunAtFullSize_dry`, `innerCompiledVerifierSoundFromDryRunAtSmallSize_dry` (Johnson/Flat/TwoSizes.lean) and
`early_bigOf` (Johnson/Flat/FilesLate.lean [not in this library]: which part of an instance is fixed
first). At values of
`Pub X`: `early_pubOf`, `early_pubReq` (the same file, the same field, at `pubOf` and `pubReq`), and
`bigReq_eq_bigOf` (Johnson/Flat/ThreeAtFiles.lean), at the full size: the data
made of a planner's answer, `bigReq p`, are `bigOf (pubReq p) recZeroFull`: by that equation the
theorems of that file at `bigReq p` stand at a value of `bigOf`. `bigReq p` is laid by `bigAt`
(OnBytes/Flat/BigAt.lean), a second way to lay a `FilesParameters`: that equation ties the two at the full size.
At the small size Johnson/Flat/SmallAtFiles.lean types no such equation, and says so. The
tops (Johnson/Top/KeyTop.lean [not in this library], ProofTop.lean [not in this library]) take G as
a letter under `AtPlan Z G`; the theorems at a letter p of the planner's type of answers
(Johnson/Flat/TwoAtPlan.lean) stand at `bigAt`; that the makers' tests pass is shown at no U. The
number of slots is 2 ^ (Nat.log2 U.N): it is `U.N` where that is a power of two, the greatest power
of two below it where it is another positive number, and 1 at `U.N` = 0: by reading; no theorem says
it. `bigOf` DROPS FOUR FIELDS OF `Pub X`: `late` (nothing comes late in the values), `table` (the
makers lay a table's name of their own, which no decision reads), `key₀` (the key is written of the
record rec₀, by `keyOf`, in
OnBytes/Flat/FilesAt.lean), `maxRt` (2 with the makers): the four fields stay, since other files
give values of `Pub X` (Johnson/Flat/PubOf.lean, PubReq.lean). That the dry runs give the same
rounds at every instance and every key that fits is not said here.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.FilesAt
import OnBytes.Key.File
import OnBytes.Proof.File

set_option autoImplicit false

namespace OnBytes.Flat
open OnBytes.Maker

/-- What is public about the two big files. -/
structure Pub (X : Type) where
  k     : Params.KeyChains
  c     : Params.ProofChains
  table : Params.TableName
  /-- the links' block at an instance -/
  links : X → Blk Proof.LinksResult
  /-- the reply that an instance names -/
  reply : X → E
  /-- the instance at which the dry runs are made; a key -/
  x₀    : X
  key₀  : TableKey
  /-- the most roots in one message -/
  maxRt : Nat
  N     : ℕ
  early : X → X
  late  : Option ℕ

/-- The data of a whole file, from the three dry runs, behind three tests (`Three.Whole.fits` at the
letter maxRt, `storedFit`, `countsFit`). The makers of OnBytes/Flat/FilesAt.lean do not call it:
they test by `okAt` (OnBytes/Maker/Files.lean), which holds eight tests, these three among them, and
make another object; it stays for OnBytes/Flat/NotesToRounds.lean [not in this library]. -/
def wholeOf (a maxRt : Nat) (p : Proof.TailPublic) (key : TableKey) (b : Blk Proof.FirstEnd)
    (s : Start) : Option Three.Whole := do
  let x₁ ← b.dryRun s
  let r ← Three.dry3 p key x₁
  let W := Three.Whole.of r.1 r.2.1 r.2.2
  if Three.Whole.fits r.1 r.2.1 r.2.2 maxRt && storedFit a W && countsFit a W then some W else none

/-- The first chain's block of a proof file at an instance: the program's own frame
`Proof.firstBlock` at the letters `U.c`, `U.links`, `U.reply`. -/
def Pub.block {X : Type} (U : Pub X) (x : X) : Blk Proof.FirstEnd :=
  Proof.firstBlock U.c.first (U.links x) (U.reply x)

/-- What the two makers take, at the letter U. rec₀: the record at which the dry runs are made. -/
def bigOf {X R : Type} (U : Pub X) (rec₀ : R) : FilesParameters X R :=
  ⟨U.k, U.c, U.block, rec₀, (U.x₀, rec₀), Nat.log2 U.N, U.early⟩

end OnBytes.Flat
