-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/ShutTied.lean: THE BATCHING KIND's FOURTH PLACE IN A LINK, THE SHUTTING,
TIED TO THE TABLE OF CONDITIONS BETWEEN BLOCKS: `TiedAt` (Johnson/Desc/Sound/ChainOfPromises.lean)
at the piece of the block that marks the link's record as closed, at the table's own conditions
(`onT`, LinkTiedAt.lean). A list of debts and a theorem.

Why. The table's row of this block is empty: it closes nothing, opens nothing, reads nothing. So the
kind's own two relations need say nothing; the law is the batching kind's `shut_goodIn_yes`
(Johnson/Desc/First/Batch/Law/ShutYes.lean) between «true» and «true»; the third tie is trivial; the
fourth asks «no mark» alone, which an unmarked statement has; «a mark stays» is
`shut_mark_yes`.

What is said.
  `ShutOwes`: what is left: that the piece holds a block each of whose yeses is the shutting's, with
    the identity for its extractor; that the table's row at k closes and reads nothing; that the
    table's promise and «no mark» ride over the block's yes; that what is open behind holds in front
    (t5); that «decodes» rides. `shut_tied`: **`ShutOwes` gives `TiedAt … k ps`.** The record is
    read beside a fixed public part z.

Limits. AN IMPLICATION: shown of no record of the protocol. Of TiedAt's eight clauses five are paid
here (the law; t1, t2 by the choice of `onT`; t3; t4; the mark: six with t1 and t2 counted apart);
`hands`, `t5` and `dec` are owed. k is free. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTiedAt
import Johnson.Desc.First.Batch.Law.ShutYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Where shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start)
open _root_.Run.PQ (CK)

variable {P W : Type} {C : CK} {F : Frame}

/-- **WHAT IS LEFT OF THE SHUTTING's TIE.** -/
structure ShutOwes (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k : ℕ) (pw : Where) (piece : ℕ) (b₅ : Block S Claim) (ps : Piece C F S Claim W) : Prop where
  /-- OWES the record of blocks: a yes of the block's step is a yes of the shutting's, with the same
  return -/
  hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
    (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x
  /-- OWES the maker of the pieces: the piece holds that block -/
  hps : ps.b = below b₅
  /-- OWES the caller of the rule of composition: the piece's extractor is the identity -/
  hext : ∀ a τ w, ps.ext a τ w = w
  /-- OWES the table of conditions between blocks: the row at k closes nothing -/
  hins : (rowQ links pl k).ins = []
  /-- OWES the table of conditions between blocks: the row at k reads nothing -/
  hctx : (rowQ links pl k).ctx = []
  /-- OWES the batching kind's law with the table of conditions: the table's promise and «no mark»
  ride over the block's yes -/
  hands : ∀ a τ b, onT Nm Mg links pl (fun s : S => (z, s)) k a → ps.ior.red.out a τ = some b →
    onT Nm Mg links pl (fun s : S => (z, s)) (k + 1) b
  /-- OWES what rides over the block: an item that is open behind the block holds in front -/
  t5 : ∀ a τ b w i, onQ Nm Mg links pl (fun s : S => (z, s)) k a → ¬ a.1.failed ≠ none →
    ps.ior.red.out a τ = some b → onQ Nm Mg links pl (fun s : S => (z, s)) (k + 1) b →
    relQ Nm Mg links pl (fun s : S => (z, s)) (k + 1) b w →
    openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i → ¬ insQ links pl k i →
    meansQ Nm Mg (fun s : S => (z, s)) i a (ps.ext a τ w)
  /-- OWES the block's own text: «the stored table decodes with the record» rides -/
  dec : ∀ a τ b, ps.ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf F a.2) →
    Mg.decodes (z, b.1) (strsOf F b.2)

/-- **THE SHUTTING, TIED TO THE TABLE.** -/
theorem shut_tied (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k : ℕ) (pw : Where) (piece : ℕ) (b₅ : Block S Claim) (ps : Piece C F S Claim W)
    (A : ShutOwes Nm Mg links pl z k pw piece b₅ ps) :
    TiedAt Nm Mg links pl (fun s : S => (z, s)) k ps := by
  have hl : ps.GoodIn (onT Nm Mg links pl (fun s : S => (z, s)) k)
      (onT Nm Mg links pl (fun s : S => (z, s)) (k + 1)) (fun _ _ => True) (fun _ _ => True) :=
    shut_goodIn_yes pw piece b₅ A.hb₅ ps A.hps A.hext _ _ _ _ A.hands
      fun _ _ _ _ _ _ _ _ _ _ => trivial
  refine tiedAt_of hl (tieOwes_of_rest
    ⟨fun _ _ _ _ _ _ _ _ _ => trivial, fun a τ b w _ hu _ _ _ _ => ?_, A.t5, ?_, A.dec⟩)
  · refine relAt_ins Nm Mg links pl _ k a _ hu (fun i hi => ?_) fun i hi => ?_
    · rw [A.hins] at hi
      exact nomatch hi
    · rw [A.hctx] at hi
      exact nomatch hi
  · exact fun a τ b hout hm => shut_mark_yes pw piece b₅ A.hb₅ ps A.hps a b τ hout hm

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.shut_tied
