-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/CommitterFile.lean: `honestCAt` (Honest/CommitterAt.lean) at the proof
file's own three types (`honestCFile`). The three rounds without a challenge are filled in: what the
front round, the joining round and the seam send is what `Committer.seamFile`
(Honest/Committer.lean) gives; the two coins are each a chain's run value (`Run32`); the test on
these rounds' plain parts asks the two copies of the answers, as the library's own test for the
proof file does (`silP`, OnBytes/Flat/FilesAt.lean, which is at another type of instances).
Definitions, and statements with their proofs, by unfolding.

  `silentAns`   the test, at an explicit input of any type; `ans`: the answers as the explicit input
     has them
  `honestCFile`   the definition
  `silentAns_file`   where the explicit input's answers are the committer's own (a hypothesis), the
     test passes at what `Committer.seamFile` sends, at all coins
  `Committer.relW`   the relation on the whole private input, the seed too; `rel_of_relW`: it gives
     `Committer.rel`; `silentAns_relW`: under it the test passes at the private input's own seed

Parameters left: C (the coding); D (the data of the file's rounds: the library computes it from a
description: `FileDescription.data`, Johnson/Desc/BlockSlot.lean); ans; answers; a₀. Of the three fixed
messages that are inside the protocol's shape the copy's number is 0 and the two byte strings are
empty, as in the proof file's protocol of OnBytes/Flat/FilesAt.lean; the two lists of answers are
the parameter a₀.

Limits.
  * As those of Honest/Committer.lean and Honest/CommitterAt.lean.
  * Nothing compares `ans` with `answers`, or either with `Committer.ood`: these are hypotheses for
    a caller.
  * That the library's goals put the answers of their fixed sample at a₀ is a reading of the text,
    made in another part of this project; no statement here names that sample.
  * Nothing on a run, a coin or a measure.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.CommitterAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (WholeD FrontMsg)
open Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK)

variable {W₀ Rc X Xi Ky Tr X₀ Xh S : Type}

/-- **The test on the plain parts of the rounds without a challenge**, at an explicit input of any
type: both copies of the answers are the explicit input's; the copy's number, the joining round's
run value and the seam's message are not tested. -/
def silentAns (ans : Xi → List OnBytes.E) (ξ : Xi) (f : FrontMsg (List OnBytes.E))
    (j : JoinMsg (List OnBytes.E) ByteArray) (_ : ByteArray) : Bool :=
  decide (f.answers = ans ξ) && decide (j.answers = ans ξ)

/-- **The honest side of the file's protocol, with one committer, at the proof file's three types.**
`a₀`: the answers in the two fixed messages that are inside the protocol's shape where a round
without a challenge has sent nothing: the prover does not send them. The proof file's protocol
puts there the answers of one fixed sample (`front₀`, `join₀`,
OnBytes/Flat/FilesAt.lean). -/
noncomputable def honestCFile (C : CK) (D : WholeD) (F : FileDescription Xi) (B : ProverCoinCounts)
    (Cm : Committer W₀ Rc (S × ℕ) X Xi Ky) (item₀ : Nat) (H : Prover W₀ Rc Xi Ky Tr X₀ Xh)
    (ans : Xi → List OnBytes.E) (answers : Isk W₀ Rc (S × ℕ) → List OnBytes.E)
    (a₀ : List OnBytes.E) :
    Iop.BatchHonestProver
      (batchOf C D (⟨a₀, 0⟩ : FrontMsg (List OnBytes.E))
        (⟨a₀, ByteArray.empty⟩ : JoinMsg (List OnBytes.E) ByteArray) ByteArray.empty F
        (silentAns ans)) (W₀ × Rc × (S × ℕ)) :=
  honestCAt C D (⟨a₀, 0⟩ : FrontMsg (List OnBytes.E))
    (⟨a₀, ByteArray.empty⟩ : JoinMsg (List OnBytes.E) ByteArray) ByteArray.empty F (silentAns ans) B
    Cm item₀ H (R2 := Run32) (R3 := Run32)
    (fun r2 r3 => (Cm.seamFile answers r2 r3).front)
    (fun r2 => (Cm.seamFile answers r2 default).join)
    (fun r2 r3 => (Cm.seamFile answers r2 r3).seam)

/-- **The test passes at what is sent**, where the explicit input's answers are the committer's
own. -/
theorem silentAns_file (Cm : Committer W₀ Rc (S × ℕ) X Xi Ky) (ans : Xi → List OnBytes.E)
    (answers : Isk W₀ Rc (S × ℕ) → List OnBytes.E) (w₀ : W₀) (rc : Rc) (sd : S × ℕ) (ξ : Xi)
    (h : ans ξ = answers ⟨w₀, rc, sd⟩) (r2 r3 : Run32) :
    silentAns ans ξ ((Cm.seamFile answers r2 r3).front w₀ rc sd ξ)
      ((Cm.seamFile answers r2 r3).join w₀ rc sd) ((Cm.seamFile answers r2 r3).seam w₀ rc sd ξ) =
        true := by
  unfold silentAns
  rw [h]
  exact Bool.and_eq_true_iff.2 ⟨decide_eq_true rfl, decide_eq_true rfl⟩

/-! ## The relation on the whole private input -/

/-- **The inputs about which something is to be stated of `honestCFile`**: a relation on the
whole private input: the index, the stored tables' pads and encoding randomness, and the seed.
`Committer.rel` (Honest/Committer.lean) has the seed under ∃, in the form that the Rel of `Owed`
needs, which has no argument for a seed. But the key that the shared chain's prover's sides are
given, the front round and the joining round read the private input's own seed. So here the explicit
input is the one that is built from that index, that randomness and that seed, and an instance of R.
-/
def Committer.relW {Sd : Type} (Cm : Committer W₀ Rc Sd X Xi Ky) (R : W₀ → X → Prop) :
    W₀ × Rc × Sd → Xi → Prop :=
  fun w ξ => ∃ x, ξ = Cm.xi (Isk.ofWt w) x ∧ R w.1 x

/-- It gives `Committer.rel` at the first two components of the private input. -/
theorem Committer.rel_of_relW {Sd : Type} {Cm : Committer W₀ Rc Sd X Xi Ky} {R : W₀ → X → Prop}
    {w : W₀ × Rc × Sd} {ξ : Xi} (h : Cm.relW R w ξ) : Cm.rel R w.1 w.2.1 ξ := by
  obtain ⟨x, e, hR⟩ := h
  exact ⟨w.2.2, x, e, hR⟩

/-- **Under the relation the test passes at the private input's own seed**, at all coins. `hans`:
the explicit input that is built from k has k's own answers: a hypothesis for a caller. -/
theorem silentAns_relW {Cm : Committer W₀ Rc (S × ℕ) X Xi Ky} {ans : Xi → List OnBytes.E}
    {answers : Isk W₀ Rc (S × ℕ) → List OnBytes.E} (hans : ∀ k x, ans (Cm.xi k x) = answers k)
    {R : W₀ → X → Prop} {w : W₀ × Rc × (S × ℕ)} {ξ : Xi} (h : Cm.relW R w ξ) (r2 r3 : Run32) :
    silentAns ans ξ ((Cm.seamFile answers r2 r3).front w.1 w.2.1 w.2.2 ξ)
      ((Cm.seamFile answers r2 r3).join w.1 w.2.1 w.2.2)
      ((Cm.seamFile answers r2 r3).seam w.1 w.2.1 w.2.2 ξ) = true := by
  obtain ⟨x, rfl, -⟩ := h
  exact silentAns_file Cm ans answers w.1 w.2.1 w.2.2 _ (hans _ x) r2 r3

end ProofFile.Honest

#print axioms ProofFile.Honest.silentAns_file
#print axioms ProofFile.Honest.Committer.rel_of_relW
#print axioms ProofFile.Honest.silentAns_relW
