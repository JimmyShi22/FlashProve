-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/Coins.lean: THE COMPILED PROVER's COINS (Coins, OnBytes/Prover/Defs.lean) IN
THE FORM IN WHICH A PARSED FILE CAN HOLD THEM. Definitions only, each with code, and one predicate
on lengths.

Why. The parser of a whole file (File.toBPrf, OnBytes/Maker/CarrierTyping.lean) lays the first
query's salt as the bits of the field run1; a leaf's typed salt as the bits of the run value of the
chain that sent its tree, then the bits of the file's own salt; and what stands behind the slot's
value as the bits of a salt, then the leaf's index as one word. Coins of any other form make a proof
string that no parsed file holds.

Main names.
  ByteCoins L     the three run values, each leaf's own salt, the filling, the place in the binding
    tree with its siblings and its salt: ALL LETTERS. Nothing here draws or fixes one.
  ByteCoins.runAt the run value of the chain of round number i (nJ: the joining round's number; n3:
    the seam's: Chains.nJ, Chains.n3, Compile/Joined/Types.lean).
  coinsOf         the coins.
  ByteCoins.Fit   the lengths.

Limits. DEFINITIONS ONLY. Whether the run values are drawn or written is not chosen here. That none
of them is 32 zero bytes (a test in front of the verifier: Johnson/Top/Fire/Code/FileInOf.lean) is
asked where that test is met, not here. The strategy must send run2 and run3 in the joining round's
and the seam's plain parts: nothing here makes it do so. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Defs
import OnBytes.Maker.CarrierTyping

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open _root_.Run
open _root_.Iop (Dig)
open TypedOracleCompiler.Iop (BatchProtocolWithLeafBody)
open TypedOracleCompiler.Compile.Batch (Body)
open OnBytes.Maker (rsOf)

variable {I X : Type}

/-- The coins of one whole file, as bytes. -/
structure ByteCoins (L : BatchProtocolWithLeafBody I X) where
  run1 : ByteArray
  run2 : ByteArray
  run3 : ByteArray
  /-- a leaf's own salt: round, own component?, tree, leaf -/
  leaf : ℕ → Bool → ℕ → ℕ → ByteArray
  /-- the body of a leaf at which no position stands -/
  pad : Body L
  /-- the place in the binding tree, its siblings' digests, its leaf's salt -/
  place : ℕ
  slotPath : List (Dig 256)
  slotSalt : ByteArray

variable {L : BatchProtocolWithLeafBody I X}

/-- The run value of the chain of round number i. -/
def ByteCoins.runAt (bc : ByteCoins L) (nJ n3 i : ℕ) : ByteArray :=
  if i < nJ then bc.run1 else if i < n3 then bc.run2 else bc.run3

/-- **The coins.** depth: the binding tree's. -/
def coinsOf (nJ n3 depth : ℕ) (bc : ByteCoins L) : Coins 256 L where
  salt := bytesToBits bc.run1
  leaf := fun i b k j => leafSalt (bc.runAt nJ n3 i) (bc.leaf i b k j)
  pad := bc.pad
  slot := bc.place
  path := bc.slotPath
  rsalt := rsOf (2 ^ depth + bc.place) bc.slotSalt

/-- The lengths. salt: the bytes of a leaf's own salt; s: the binding tree's shape. -/
structure ByteCoins.Fit (bc : ByteCoins L) (salt : ℕ) (s : Params.LinBindingShape) : Prop where
  run1 : bc.run1.size = 32
  run2 : bc.run2.size = 32
  run3 : bc.run3.size = 32
  leaf : ∀ i b k j, (bc.leaf i b k j).size = salt
  place : bc.place < 2 ^ s.logLeaves
  slotPath : bc.slotPath.length = s.logLeaves
  slotSalt : bc.slotSalt.size = s.saltBytes

end OnBytes.Prover.Print
