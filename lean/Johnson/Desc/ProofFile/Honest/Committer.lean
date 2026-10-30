-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Committer.lean: the index committer's part in the honest side of a
session (one request), as one structure, `Committer`, beside `Prover` (Honest/Frame.lean). Four
things that the other files of this folder take as separate parameters are read from it: the stored
table's columns (`Prover.stored`), the external string of the library's `Iop.BatchHonestProver` (the argument
`ext` of `honestB`, Honest/Record.lean), the key computed without an instance (`KeyAndJoiningRoundMessages.keyOf`,
Honest/Strat.lean) and the key inside the explicit input (`Prover.key`). Definitions only;
no theorem.

  1  `Isk`, `Isk.wt`, `Isk.ofWt`   what the prover keeps of the index committer's run, as one value
  2  `Committer`   the whole encoded index; the out-of-domain sample; the function that builds the
     explicit input
  3  `Committer.prover`, `Committer.ext`, `Committer.seam`, `Committer.rel`   what is read from it
  4  `Run32`, `Committer.seamFile`, `honestC`   the same at the proof file's three types; the
     library's `Iop.BatchHonestProver`, filled

The fields and their arguments follow the library's own structure `Iop.HolographicProtocol`
(Hiop/RecInterface.lean). There the encoding is computed from the index and the coins, and the
honest answer from the index, the coins and the seed. A session's explicit input is the instance
with the seed and the answer. The honest side's private input is the index, the coins and the seed.

What it is not. `Committer` is the information-theoretic part of the index committer, for one
encoded index. The index verification key, ivk, is wider. It holds the commitment ID; the key file,
with its root, its out-of-domain answers and its one-time proof; and a file for each copy. The index
committer makes these one-time proofs once. None of that is in `Committer`: no root, no ID, no
honest side for the key file or for a copy's file.
One stored table. The library's external string is a single string, and `enc` has no argument that
says which stored table of the statement is meant (its item, a number from 0). A file that ties two
encoded indices needs two such structures.

Limits.
  * `tie` is a field: a hypothesis, which each caller has to prove.
  * Nothing compares `enc` with a code, `ood` with `enc`, or `xi` with a description's test on
    the instance.
  * What ties the two type parameters of `honestC`'s coins (R2, R3) to the compiler's randomness is
    not stated.
  * Nothing is proved about `honestC`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Record
import Run.CodingBits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (WholeD FrontMsg)
open Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK SgX)

variable {W₀ Rc Sd X Xi Ky Tr X₀ Xh TF TJ T3 : Type}

/-! ## 1 isk -/

/-- **What the prover keeps of the index committer's run**, for one encoded index. This is isk, as
far as a session's honest side reads it. -/
structure Isk (W₀ Rc Sd : Type) where
  /-- the index -/
  index : W₀
  /-- the pads and encoding randomness with which this encoded index's stored table was encoded -/
  coins : Rc
  /-- the seed of the out-of-domain sample -/
  seed : Sd

/-- The same value as a triple: the form of the private input of the library's `Iop.BatchHonestProver`. -/
def Isk.wt (k : Isk W₀ Rc Sd) : W₀ × Rc × Sd := (k.index, k.coins, k.seed)

/-- The inverse: the structure from such a triple. -/
def Isk.ofWt (w : W₀ × Rc × Sd) : Isk W₀ Rc Sd := ⟨w.1, w.2.1, w.2.2⟩

/-! ## 2 The structure `Committer` -/

/-- **The index committer's part, for one encoded index.** `X` is the type of the instance, `Xi`
that of the explicit input, `Ky` that of the part of ivk that the shared chain reads. -/
structure Committer (W₀ Rc Sd X Xi Ky : Type) where
  /-- the whole encoded index: its column at a position, as a list of field elements; `none` beyond
  the encoded index -/
  enc : W₀ → Rc → Nat → Option (List Cb.Gl.F)
  /-- the out-of-domain seeds and answers -/
  ood : Isk W₀ Rc Sd → Ky
  /-- the function that builds the explicit input from isk and the instance -/
  xi : Isk W₀ Rc Sd → X → Xi
  /-- what the shared chain reads of the explicit input -/
  key : Xi → Ky
  /-- the explicit input that is built from isk holds isk's own sample: a hypothesis, which each
  caller has to prove -/
  tie : ∀ k x, key (xi k x) = ood k

/-! ## 3 What is read from it -/

section
variable (Cm : Committer W₀ Rc Sd X Xi Ky)

/-- **A prover whose stored table and key are the committer's.** The other fields of `H` are
unchanged. It lays the one table at every item of the statement: item 0 alone is meant
(`Committer.proverAt`, Honest/CommitterAt.lean). -/
def Committer.prover (H : Prover W₀ Rc Xi Ky Tr X₀ Xh) : Prover W₀ Rc Xi Ky Tr X₀ Xh :=
  { H with stored := fun w₀ rc _ x => Cm.enc w₀ rc x, key := Cm.key }

/-- **The library's external string.** At each position below 2 ^ a it holds the position itself and
the encoded index's column there, converted to words; it holds no word where `enc` returns `none`.
It uses the same `enc` as `Committer.prover`. So what a run reads of the stored table and what the
string holds come from one definition. -/
def Committer.ext (a : Nat) (w : W₀ × Rc × Sd) : (Iop.oneExternalString (2 ^ a) SgX).Str :=
  fun p => (p.val, ((Cm.enc w.1 w.2.1 p.val).getD []).map OnBytes.Slice.ofF)

/-- **The `KeyAndJoiningRoundMessages` (Honest/Strat.lean) that goes with the prover.** Its key is the committer's `ood`;
the three rounds without a challenge are the caller's arguments. -/
def Committer.seam (front : W₀ → Rc → Sd → Xi → TF) (join : W₀ → Rc → Sd → TJ)
    (seam : W₀ → Rc → Sd → Xi → T3) : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3 :=
  ⟨fun w₀ rc sd => Cm.ood ⟨w₀, rc, sd⟩, front, join, seam⟩

/-- **The inputs about which something is to be stated, in the form that is meant for the parameter
`Rel` of `Owed`** (Honest/Owed.lean). `R` is the relation proper, on the index and the instance (the
witness is computed from the index and the explicit input: `Prover.trace`). The explicit input is
the one that is built from the index, the stored tables' pads and encoding randomness, some seed,
and an instance x with R w₀ x. No other clause reads them. -/
def Committer.rel (R : W₀ → X → Prop) : W₀ → Rc → Xi → Prop :=
  fun w₀ rc ξ => ∃ sd x, ξ = Cm.xi ⟨w₀, rc, sd⟩ x ∧ R w₀ x

end

/-! ## 4 At the proof file's three types; the library's `Iop.BatchHonestProver` -/

/-- A chain's run value as a coin: 256 bits, a finite type that holds every value of 32 bytes
(`Iop.Dig`, Iop/Wire.lean; `Run.digToBytes`, Run/CodingBits.lean). -/
abbrev Run32 : Type := Iop.Dig 256

/-- **The `KeyAndJoiningRoundMessages` at the proof file's own three types** (OnBytes/Maker/SilentParts.lean). The seed
carries the copy's number: Sd := S × ℕ. `answers`: the sample's answers, computed from isk. `r2`,
`r3`: the run values of the second and the third chain, as coins. The front round and the joining
round send the answers; the front round also sends the copy's number; no field reads the instance.
-/
def Committer.seamFile {S : Type} (Cm : Committer W₀ Rc (S × ℕ) X Xi Ky)
    (answers : Isk W₀ Rc (S × ℕ) → List OnBytes.E) (r2 r3 : Run32) :
    KeyAndJoiningRoundMessages W₀ Rc (S × ℕ) Xi Ky (FrontMsg (List OnBytes.E)) (JoinMsg (List OnBytes.E) ByteArray)
      ByteArray :=
  Cm.seam (fun w₀ rc sd _ => ⟨answers ⟨w₀, rc, sd⟩, sd.2⟩)
    (fun w₀ rc sd => ⟨answers ⟨w₀, rc, sd⟩, _root_.Run.digToBytes r2⟩)
    fun _ _ _ _ => _root_.Run.digToBytes r3

/-- **The honest side of the file's protocol, with one committer**: `honestB` at the committer's
prover, external string and key. `front`, `join` and `seam`: the three rounds without a challenge,
as functions of the two coins (`join` of the first alone). -/
noncomputable def honestC (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
    (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (Cm : Committer W₀ Rc Sd X Xi Ky)
    (H : Prover W₀ Rc Xi Ky Tr X₀ Xh) {R2 R3 : Type} [Fintype R2] [Nonempty R2] [Fintype R3]
    [Inhabited R3] (front : R2 → R3 → W₀ → Rc → Sd → Xi → TF) (join : R2 → W₀ → Rc → Sd → TJ)
    (seam : R2 → R3 → W₀ → Rc → Sd → Xi → T3) :
    Iop.BatchHonestProver (batchOf C D tF tJ t3 F silent) (W₀ × Rc × Sd) :=
  honestB C D tF tJ t3 F silent B (Cm.prover H)
    (fun r2 r3 => Cm.seam (front r2 r3) (join r2) (seam r2 r3)) (Cm.ext D.a)

end ProofFile.Honest
