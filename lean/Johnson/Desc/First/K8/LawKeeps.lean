-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawKeeps.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS LAW IN THE PLAIN FORM
OF THE RULE OF COMPOSITION.

The plain form (`Iop.Reduction.Leads`, Johnson/Desc/Plain/Leads.lean) has no extractor: on every
statement with the condition in front the prover has lost, at the block's errors, towards "whatever
the block puts out stands in Q to the statement in front". For a block with a promise Q is to say:
the promise behind is kept, and for every world w what stands behind at w gives what stands in front
at w.
  `hear_plain`: the kind's block at its own stretch has that form, between the two boundaries of
    Johnson/Desc/First/K8/LawPiece.lean; with, at no cost, what holds for certain of a yes: the
    record behind holds the list of a typed matrix, and the reading of the statement has not turned.
  `hear_keepsW`: the same at the rule's own name for a block with a promise (`Iop.Reduction.KeepsW`,
    Johnson/Desc/Plain/World.lean). `hear_plain_true`: so for the two languages "there is a world":
    `Iop.Reduction.Keeps`.
Statements and proofs: from `piece_good`; nothing is counted anew.
Limits: those of LawPiece.lean: THE CALLER AND THE LETTERS ARE PARAMETERS: no caller made of the
public record is named. NOT SHOWN: that the form fails at a block that says yes to all; that the
condition in front is met at the values that run; that the error is below the round's number of
challenges.

-/
import Johnson.Desc.First.K8.LawLost
import Johnson.Desc.Plain.World

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Prob Cb.Pv.Tail OnBytes.Maker OnBytes.Tie.Pv.Tail KObj VerifiableInference.OnPublicFiles
  VerifiableInference.Desc.Sound

section
variable {S Cl W : Type} {F : Frame} {seat : Seat S} {p : Par} {base e : ℕ} {d : TailCallerOn}

/-- **The kind's law in the plain form.** -/
theorem hear_plain (Q : Reads Cl W F seat p base e d) (hf : Fits p d.c.s) (hOK : d.c.s.OK)
    (he : (Fintype.card (Dr d.c.s) / 2 ^ d.c.s.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.red.Leads Q.onA
      (fun a b => (Q.onB b ∧ ∀ w, Q.relB b w → Q.relA a w) ∧
        (∃ β : Dr d.c.s, Q.cf b.1 = listOf β) ∧ Q.rd b = Q.rd a)
      (piece (Cl := Cl) (W := W) (F := F) seat p base e).err := by
  intro a ha
  refine Doomed.mono _ _ ?_ ((piece_good Q hf hOK he).know a ha)
  intro τ hτ b hb
  obtain ⟨m, c, ⟨⟩⟩ := τ
  obtain ⟨_, hcf, hrd⟩ := Q.of_out hf a b m c hb
  exact ⟨⟨hear_keeps Q hf a b m c ha hb, fun w hw => hτ b w hb (Or.inl hw)⟩,
    ⟨matrixOf hf c, hcf⟩, hrd⟩

/-- **The same at the rule's own name for a block with a promise**: at every world. -/
theorem hear_keepsW (Q : Reads Cl W F seat p base e d) (hf : Fits p d.c.s) (hOK : d.c.s.OK)
    (he : (Fintype.card (Dr d.c.s) / 2 ^ d.c.s.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.red.KeepsW Q.onA Q.onB Q.relA Q.relB
      (piece (Cl := Cl) (W := W) (F := F) seat p base e).err :=
  (hear_plain Q hf hOK he).conseq (fun _ h => h) fun _ _ _ _ _ hq => hq.1

/-- For the two languages "there is a world". -/
theorem hear_plain_true (Q : Reads Cl W F seat p base e d) (hf : Fits p d.c.s) (hOK : d.c.s.OK)
    (he : (Fintype.card (Dr d.c.s) / 2 ^ d.c.s.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.red.Keeps Q.onA Q.onB
      (fun a => ∃ w, Q.relA a w) (fun b => ∃ w, Q.relB b w)
      (piece (Cl := Cl) (W := W) (F := F) seat p base e).err :=
  (hear_plain Q hf hOK he).conseq (fun _ h => h)
    fun _ _ _ _ _ hq => ⟨hq.1.1, fun ⟨w, hw⟩ => ⟨w, hq.1.2 w hw⟩⟩

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.hear_plain
#print axioms VerifiableInference.Desc.First.K8.hear_keepsW
#print axioms VerifiableInference.Desc.First.K8.hear_plain_true
