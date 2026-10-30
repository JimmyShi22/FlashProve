-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K5/ItemAtFull.lean: at the three stored full-size public files (VerifierAndGoals.storedPublicFiles): the clause on the request's
item holds (the field "item" of "StartHeld", E2E/StartAtFiles.lean); so the proof file's first test on an instance,
okStart, accepts what the library writes for every instance of the full size's type, at every OOD sample; and so
some input meets the condition "ReadyInput" (Honest/Thread/ReadyInput.lean), at the prover that the frame's maker
returns at one written filling. With no premise but the library's head, which has a member at these files.

  clause_older        the closed fact of ItemClosed.lean, at the format's second hash function itself
  item_zFull          under the head at storedPublicFiles: the request's item is made at a string of the request file's length,
                      and the comparison with the head's own public part accepts it
  startHeld_zFull     under the head at storedPublicFiles: "StartHeld", whole
  okStart_zFull       under the head at storedPublicFiles: okStart accepts "instanceAsPlainRecord z" at every z
  okStart_at_zFull    no premise: there are letters that meet the head at storedPublicFiles, and at them okStart accepts at every z
  readyInput_at_zFull no premise: at such letters the frame's maker returns at the written filling
                      "widerFillAtC fullIn o' S O", and there are an index and a typed request at which, at every OOD
                      sample and every value of the field rc, the input is ready. The closed sentence on the written
                      book that the maker's return takes is bookWhole_returns_written
                      (AtFullSide/K14/BookWholeWritten.lean)

How. The public part at storedPublicFiles is known field by field where the comparison reads it: the scan's written value and the
three digests as terms (publicOfO_zFull_of_rest, Johnson/AtFull/Public/Join.lean, at lay_size); the head's public part
is that value, since both are what one maker returns. The rest is ItemLetters.lean's ties and the closed fact. From
one string to all of its length: item_free (E2E/StartAtFiles.lean).

Limits. One example, at the full size alone: at VerifierAndGoals.storedPublicFiles alone: not at other files in the goals' scope. All limits
of AtFullSide/Top/HeadMemberAtFull.lean hold: the three files are terms written in Ladder/Stored.lean; the example's
weights are synthetic; the member is what the makers return at these files. At the earlier hash OnBytes.secondHashFunction. The
closed facts beneath are evaluations in Lean's kernel; no independent checker has replayed them.
okStart is the first test on an instance: its yes is no sign that the verifier accepts any proof.
"ReadyInput" is a condition on an input: a value of a thread's parameter "valid". Nothing here says
that "ready" (Honest/Frame.lean) returns at that input, that any part plays, that a thread's border is reached, or that
a verifier accepts. The index and the request are the library's own member (by the Limits of
Johnson/FrontRoad/ServedExists.lean, by inspection: the all-zero weights, all tokens 0). All limits of ReadyInput.lean
and of K5/Law/ReadyInputOfItem.lean hold: the condition reads the private input; its first clause bears tests on the
table's key; a law whose end states a distribution over rc or the seed may not lean on it without more.
No property of the protocol is claimed: nothing on soundness, completeness or what anything reveals.
-/
import AtFullSide.K5.ItemClosed
import AtFullSide.Layout.Size
import AtFullSide.Top.HeadMemberAtFull
import AtFullSide.K14.BookWholeWritten
import E2E.StartInScope
import Johnson.Desc.ProofFile.Law.CarryAtLaw
import Johnson.Desc.ProofFile.Honest.K5.Law.ReadyInputOfItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K5.Item
open VerifierAndGoals
open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Flat (RecFull)
open LPFD.Full (XF)
open P5J (AtMgA F0T TS)
open ProofFile.Honest (ReadyInput onlineProverFromPublicFiles widerFillAtC fullIn IndexCommitterCoins OnlineProverArguments)

/-- The closed fact at the format's second hash function itself. -/
theorem clause_older : clauseBy secondHashFunction 4104 id = true := by
  rw [olderK_fun]
  exact clause_closed

variable {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head at the stored full-size files the clause on the request's item holds at one string of the request
file's length.** -/
theorem item_zFull (h : AtMgA secondHashFunction storedPublicFiles D r Zp Np cF x) :
    ∃ it, Fmt.requestItem secondHashFunction Zp.pol Zp.KL reqW = some it ∧
      statementHeld Zp.p.X it = .ok () := by
  obtain ⟨ePol, eKL⟩ := ProofFile.Law.pub_files h.laid.pub
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, -, -, ⟨hHL, -, hLaid⟩, hl, -, -, -, -, -,
    -, hX⟩ := AtFull.Public.publicOfO_zFull_of_rest Johnson.Unfolds.Layout.lay_size
  obtain ⟨Lh, calls, fs, kb, pub, hn, hc, -, -, -, -, -, eH⟩ := hLaid
  have eHL := Except.ok.inj (hHL.symm.trans eH)
  subst eHL
  have eX := Except.ok.inj (h.laid.publicO.symm.trans hX)
  have hC := clause_older
  unfold clauseBy at hC
  rw [digests_at hl hn hc] at hC
  cases hi : itemBy secondHashFunction 4104 with
  | none =>
    rw [hi] at hC
    cases hC
  | some it =>
    rw [hi] at hC
    refine ⟨it, by rw [ePol, eKL, requestItem_at, hi], ?_⟩
    have key : heldBy Zp.p.X.P Zp.p.X.digests it = true := by
      rw [eX]
      exact hC
    rw [statementHeld_by, key]
    rfl

/-- **Under the head at the stored full-size files: what the first test on an instance asks of the public files.** -/
theorem startHeld_zFull (h : AtMgA secondHashFunction storedPublicFiles D r Zp Np cF x) :
    AtPublicFiles.Start.StartHeld secondHashFunction ProofFile.pureRoad.links Zp :=
  AtPublicFiles.Start.startHeld_of_laid h.scope h.laid fun _ hq =>
    AtPublicFiles.Start.item_free
      (by rw [reqW_size, hq, (AtPublicFiles.Start.numbers_of_laid h.scope h.laid).1]; rfl) (item_zFull h)

/-- **Under the head at the stored full-size files the first test accepts what the library writes for every instance
of the type, at every OOD sample.** -/
theorem okStart_zFull (h : AtMgA secondHashFunction storedPublicFiles D r Zp Np cF x) (z : XF × RecFull) :
    (F0T secondHashFunction Zp Np cF).okStart (LPFD.Full.instanceAsPlainRecord z) = true :=
  AtPublicFiles.Start.okStart_of_public Np cF (startHeld_zFull h) z

/-- **No premise: there are letters that meet the head at the stored full-size files, and at them the first test
accepts at every instance of the type.** -/
theorem okStart_at_zFull :
    ∃ Zp Np cF x, AtMgA secondHashFunction storedPublicFiles (VerifierAndGoals.AtTheName.dpZ storedPublicFiles)
        (FlashProve.theProofRun (asDescriptionFiles storedPublicFiles)) Zp Np cF x ∧
      ∀ z : XF × RecFull, (F0T secondHashFunction Zp Np cF).okStart (LPFD.Full.instanceAsPlainRecord z) = true := by
  obtain ⟨-, -, Zp, Np, cF, x, h⟩ := AtFullSide.Top.headMember_zFull
  exact ⟨Zp, Np, cF, x, h, okStart_zFull h⟩

/-- **No premise: some input is ready at the stored full-size files**, at the prover that the frame's maker returns at
the written filling. -/
theorem readyInput_at_zFull (o' : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ Zp Np cF x A, AtMgA secondHashFunction storedPublicFiles (VerifierAndGoals.AtTheName.dpZ storedPublicFiles)
        (FlashProve.theProofRun (asDescriptionFiles storedPublicFiles)) Zp Np cF x ∧
      onlineProverFromPublicFiles secondHashFunction storedPublicFiles.pol storedPublicFiles.lay storedPublicFiles.KL (widerFillAtC fullIn o' S O) = .ok A ∧
      A.F = F0T secondHashFunction Zp Np cF ∧
      ∃ (i : Cm.Idx) (x' : XF), ∀ (rec : RecFull) (rc : IndexCommitterCoins),
        ReadyInput A.F A.H
          ⟨i, rc, LPFD.Full.instanceAsPlainRecord (x', rec),
            ⟨OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X i x'.val)⟩⟩ := by
  obtain ⟨hl, -, Zp, Np, cF, x, h⟩ := AtFullSide.Top.headMember_zFull
  obtain ⟨A, hA, hF, hR⟩ :=
    ProofFile.Honest.K5.readyInput_widerC_of_start h hl AtFullSide.K14.bookWhole_returns_written
      (okStart_zFull h) o' S O
  exact ⟨Zp, Np, cF, x, A, h, hA, hF, hR⟩

end AtFullSide.K5.Item

#print axioms AtFullSide.K5.Item.clause_older
#print axioms AtFullSide.K5.Item.item_zFull
#print axioms AtFullSide.K5.Item.startHeld_zFull
#print axioms AtFullSide.K5.Item.okStart_zFull
#print axioms AtFullSide.K5.Item.okStart_at_zFull
#print axioms AtFullSide.K5.Item.readyInput_at_zFull
