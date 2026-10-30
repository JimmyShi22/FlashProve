-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SharedSendsWritten.lean: kind K14: **THE FORM SharedSends
(Honest/K14/BookAtShared.lean) HOLDS AT THE LIBRARY's WRITTEN LIST OF THE SHARED CHAIN's SENDINGS**
(proofSendsFull.2.1 = proofSends1, Johnson/G/SendsWritten.lean), at the written sizes' codes and the
two sendings' notices as the linear claim's shape has them; AND SO, AT THE PROOF FILE's IOP AS
WRITTEN IN LEAN (below: the description), FOR ALL PUBLIC FILES Z THAT PASS InScope AND EVERY Zp OF
WHICH LaidAt HOLDS, WHERE THE FRAME's sharedAhead, bookRaw OR bookWhole RETURNS AT THAT LIST: the
fact on the order holds at the part at "send o_omega", and the test for that part accepts what is
returned. Statements with their proofs; no definition.

  sharedSends_written   **SharedSends at the written list**: the codes; the first two labels and
                  what is sent under them; isSwitch's nine verdicts (Honest/K14/SwitchLabels.lean)
  sharedSends_at_files   the same at the description's plan
  made_sends_at_files   the public part's own three lists (Zp.made.proof) are the written ones
  carriers_at_files   **where the short list returns l: at the owner ⟨"send o_omega", 0⟩ the split's
                  entry (what splitEntry returns) lies in l and spends, its spender the part s of
                  the round 7 ("SPLIT"); every other entry carries, to a part k with StandsBehind
                  (the description's order) s k**
  order_at_files  **there the short test, the test on the order and the owner's test accept l, laid
                  into any book**
  order_at_raw    **AT THE RAW BOOK, before any of its own tests is asked: the short test and the
                  owner's test accept, and at the part that holds "SPLIT" nothing else of the
                  owner's coins is known**
  spOwner_ok_at_written, spOwner_ok_at_made   so at every book that bookWhole returns at the written
                  list, and at the public part's own lists

What is assumed. That sharedAhead, bookRaw or bookWhole returns: OF THAT PREMISE IS USED: that a
book is there whose entries at the owner are the short list's, and that the short list's eight steps
that can reject have returned. (THE PREMISE "bookWhole RETURNS" CARRIES MORE: a book is handed on
only where it passes all eleven of its own tests, ProverCoinCounts.clauses, Honest/Frame.lean: none of that is
used) · InScope Z, LaidAt.
What is not claimed. That any of the three returns at any file. IN THIS FILE THE PREMISES ARE SHOWN
TO HOLD TOGETHER AT NO LETTERS, NOT AT A SMALL EXAMPLE: BY THIS FILE THE STATEMENTS MAY BE EMPTY.
(That the short list returns there: Honest/K14/SharedAheadAtHead.lean. That bookRaw and bookWhole
return at the goals' two named sets: bookRaw_returns_at_named,
AtFullSide/K14/RawReturnsAtNamed.lean, and bookWhole_returns_at_named,
AtFullSide/K14/WholeReturnsAtNamed.lean, in the side library (this library may not hold them):
compiled module by module so far: over the frame's segmentCarries as it lies beneath them alone; at
mergesByName, a guess; no Lake, no ride of record, no independent checker yet.) THAT THE RAW BOOK
PASSES ITS OWN TESTS: no lemma here leads to the eighth test's yes. That the lists which the frame's
maker onlineProverFromPublicFiles hands to bookWhole are the written ones: Honest/K14/BookAtPure.lean. The like at "send
o_u". All holds at the order orderOf F alone. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BookAtOmegaHead
import Johnson.Desc.ProofFile.Honest.K14.SwitchLabels
import Johnson.G.SendsWritten
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (proofSendsFull)
open VerifierAndGoals (InScope)
open P5J (LaidAt F0T TS)
open AtPublicFiles.TreeReads (sized_at written_proof)

/-- **SharedSends at the written list.** -/
theorem sharedSends_written :
    SharedSends proofSendsFull.2.1 proofSizedFull.codes
      ((Desc.K14.withU proofSizedFull.batch.shape).getD #[]).toList
      (Desc.K14.withOmega proofSizedFull.batch.shape).toList := by
  exact ⟨by decide +kernel, _, _, _, rfl, rfl, by decide +kernel, rfl, by decide +kernel,
    two_no_switch.1, two_no_switch.2, fun s hs => List.all_eq_true.1 rest_switches s hs⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The same at the description's plan. -/
theorem sharedSends_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    SharedSends proofSendsFull.2.1 (qAt Zp Np).codes
      ((Desc.K14.withU (qAt Zp Np).S).getD #[]).toList
      (Desc.K14.withOmega (qAt Zp Np).S).toList := by
  show SharedSends proofSendsFull.2.1 Zp.p.chains.made.sized.proof.codes
    ((Desc.K14.withU Zp.p.chains.made.sized.proof.batch.shape).getD #[]).toList
    (Desc.K14.withOmega Zp.p.chains.made.sized.proof.batch.shape).toList
  rw [sized_at scope L, written_proof]
  exact sharedSends_written

/-- The public part's own three lists of what the proof file's chains send are the written ones
(the library's sends_in_scope and pins_of_laid, joined). -/
theorem made_sends_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    Zp.made.proof = proofSendsFull :=
  VerifiableInference.PlanWritten.Joined.sends_in_scope scope L.pub (P5J.pins_of_laid scope L).1

/-- **AT THE DESCRIPTION: WHOEVER CARRIES A COIN OF THE PART AT "send o_omega" STANDS BEHIND THE
PART THAT SPENDS ONE**: carriers_all (Honest/K14/BookAtOmega.lean) there. -/
theorem carriers_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {l : List Ahead}
    (h : sharedAhead (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.2.1 = .ok l) :
    ∃ (s : Addr) (e₀ : Ahead),
      addrOfRound (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder 7 = some s ∧
      splitEntry (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder proofSendsFull.2.1 = some e₀ ∧ e₀ ∈ l ∧
      e₀.owner = { place := sendPlace 5, part := 0 } ∧
      e₀.start = ⟨0, spFirstCoin ⟨qAt Zp Np, 0⟩⟩ ∧ e₀.count = ⟨0, 1⟩ ∧ e₀.spender = s ∧
      e₀.once = true ∧ ∀ k ∈ l, k.owner = { place := sendPlace 5, part := 0 } →
        k = e₀ ∨ (k.once = false ∧
          StandsBehind (orderOf (F0T OnBytes.secondHashFunction Zp Np cF)) s k.spender) := by
  obtain ⟨-, hs, -⟩ := sendings_of_laid scope L
  obtain ⟨hN, -, -⟩ := headNumbers_give ⟨qAt Zp Np, 0⟩ hs (numbers_at_files scope L)
  exact carriers_all (form_at_files scope L)
    ((VerifiableInference.Desc.FileDescription.planOk_ok _).1 L.planOk).places
    (sharedSends_at_files scope L) hN h

/-- **AT THE DESCRIPTION: THE SHORT LIST PASSES ALL THREE TESTS.** -/
theorem order_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat) {l : List Ahead}
    (h : sharedAhead (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.2.1 = .ok l) (B₀ : ProverCoinCounts) :
    spWholeB ⟨qAt Zp Np, a⟩ { B₀ with ahead := l } = true ∧
      behindSpenderB (spFirstCoin ⟨qAt Zp Np, a⟩)
        (spEntries ⟨qAt Zp Np, a⟩ + 1 + (spMaskCode ⟨qAt Zp Np, a⟩).r) { B₀ with ahead := l }
        (orderOf (F0T OnBytes.secondHashFunction Zp Np cF)) { place := sendPlace 5, part := 0 } = true ∧
      (spOwner ⟨qAt Zp Np, a⟩).ok { B₀ with ahead := l } (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
        { place := sendPlace 5, part := 0 } = true := by
  obtain ⟨hfit, hs, -⟩ := sendings_of_laid scope L
  obtain ⟨hN, hn, hP⟩ := headNumbers_give ⟨qAt Zp Np, a⟩ hs (numbers_at_files scope L)
  have hX := form_at_files scope L
  have hpl := ((VerifiableInference.Desc.FileDescription.planOk_ok _).1 L.planOk).places
  have hS := sharedSends_at_files scope L
  exact ⟨whole_of_short hX hS hN h B₀, carriers_behind hX hpl hS hN h B₀ _ _,
    spOwner_ok_of_short hX hpl ⟨qAt Zp Np, a⟩ hS hN hn hfit hs hP h B₀⟩

/-- **AT THE DESCRIPTION, AT THE RAW BOOK**, at the written list. -/
theorem order_at_raw (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat)
    {p0 p2 : Johnson.G.ChainSends} {M : Merges} {W : ProverCoinCounts}
    (hW : bookRaw (F0T OnBytes.secondHashFunction Zp Np cF) p0 proofSendsFull.2.1 p2 M = .ok W) :
    spWholeB ⟨qAt Zp Np, a⟩ W = true ∧
      (∃ s, addrOfRound (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder 7 = some s ∧
        W.knownBy (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
          { place := sendPlace 5, part := 0 } s = []) ∧
      (spOwner ⟨qAt Zp Np, a⟩).ok W (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
        { place := sendPlace 5, part := 0 } = true := by
  obtain ⟨hfit, hs, -⟩ := sendings_of_laid scope L
  obtain ⟨hN, hn, hP⟩ := headNumbers_give ⟨qAt Zp Np, a⟩ hs (numbers_at_files scope L)
  exact spOwner_ok_of_raw hW (form_at_files scope L)
    ((VerifiableInference.Desc.FileDescription.planOk_ok _).1 L.planOk).places ⟨qAt Zp Np, a⟩
    (sharedSends_at_files scope L) hN hn hfit hs hP

/-- **AT THE DESCRIPTION: spWholeB AND THE OWNER's TEST ACCEPT EVERY BOOK THAT bookWhole RETURNS AT
THE WRITTEN LIST.** -/
theorem spOwner_ok_at_written (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat)
    {p0 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) p0 proofSendsFull.2.1 p2 M = .ok B) :
    spWholeB ⟨qAt Zp Np, a⟩ B = true ∧
      (spOwner ⟨qAt Zp Np, a⟩).ok B (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
        { place := sendPlace 5, part := 0 } = true := by
  obtain ⟨hfit, hs, -⟩ := sendings_of_laid scope L
  obtain ⟨hN, hn, hP⟩ := headNumbers_give ⟨qAt Zp Np, a⟩ hs (numbers_at_files scope L)
  exact spOwner_ok_of_book hB (form_at_files scope L)
    ((VerifiableInference.Desc.FileDescription.planOk_ok _).1 L.planOk).places ⟨qAt Zp Np, a⟩
    (sharedSends_at_files scope L) hN hn hfit hs hP

/-- **THE SAME AT THE PUBLIC PART's OWN LISTS.** -/
theorem spOwner_ok_at_made (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat) {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 M = .ok B) :
    spWholeB ⟨qAt Zp Np, a⟩ B = true ∧
      (spOwner ⟨qAt Zp Np, a⟩).ok B (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
        { place := sendPlace 5, part := 0 } = true := by
  rw [made_sends_at_files scope L] at hB
  exact spOwner_ok_at_written scope L a hB

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sharedSends_written
#print axioms ProofFile.Honest.K14.sharedSends_at_files
#print axioms ProofFile.Honest.K14.made_sends_at_files
#print axioms ProofFile.Honest.K14.carriers_at_files
#print axioms ProofFile.Honest.K14.order_at_files
#print axioms ProofFile.Honest.K14.order_at_raw
#print axioms ProofFile.Honest.K14.spOwner_ok_at_written
#print axioms ProofFile.Honest.K14.spOwner_ok_at_made
