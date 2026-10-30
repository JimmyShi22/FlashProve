-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLScriptStand.lean

It states no goal. No property of the protocol is claimed.

THE TIE OF THE WORDS AT A STAND IN FRONT
OF THE CLOSING PROXIMITY TEST, AT THE FIRST CHAIN's SCRIPT AS A VALUE: the premise hw of
acceptedS_stands_L (not beneath this file), in its own form, at
Q := `firstScriptAt I S Op A cF` (AtFullSide/K1/FirstScript.lean), H := A.H, the
share's own data, readers and closing. An assembly.

  `finish_border_written`   A CLOSED LINE: in the written list of places the written finish stands at
      number 353. With a control that says no
  `finish_border_first`   so under the head, where the maker returns: borderNo cF.blocksInOrder pl.place = 353
  `challenges_in_front_of_the_test`   the rounds in front of member 354 are those that the switch's
      lot reads, and two more
  `heard_at_closing_stand`   THE EQUATION OF LISTS at a stand: the challenges that the test's job
      reads, heardL (frontOf m), are the first so many of those that the witness is given as the
      switch's lot reads. By heardL_at_stand (ClosingWordsHeard.lean)
  `book_first`   the maker's book is what bookWhole returns at the written lists of sendings
  `wordsTied_at_closing_stand`   THE TOP: hw

By: `closingMemberSeat_at_stand` (LotLSeatAtStand.lean) ·
`switch_lot_returns_at_closing_stand` (LotLOwedAtStand.lean) · `wordsTied_first`
(LotLScriptFirst.lean).

Hypotheses of the top. h: the head. hA: the maker returns A. hf: pl is the finish. hok: the closing's
public test at the finish. hpub: the filling's public test at every valid input. hReach: a stand is
reached. hcarry: A NAMED PREMISE:
where the finish's part is handed cs and lays V at the challenges that the job reads, the
job's carrying rows at the stretches lent to the test's second part are V 0 (carryRows_at_lent,
carryRows_of_book: ClosingWordsJob.lean, ClosingWordsBook.lean; that the row's lending is the
part's is those files' too).

Limits. The full size and the format's second hash function alone. hok, hpub, hReach and hcarry are not paid
here. That a stand exists is not said: at no stand the top says nothing. Nothing on completeness,
soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `heard_at_closing_stand` and `wordsTied_at_closing_stand` bear
this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- hf and hok speak of the finish and of the closing's public test: they name no coin. hpub is bound
  over every input that meets Vd and reads its instance: it names no coin.
- hReach and hcarry are themselves bound over all coins and every stand: by themselves they pick
  among no coins.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- In `heard_at_closing_stand` k, st, m and E are the theorem's own binders, and the letters st, m
  and E (the verifier's state, the state of the prover's side, the available tables) stand under hT
  : `Thr … 354 k st m E`; in `wordsTied_at_closing_stand` they are bound inside the end, under `ThrS
  … 354 k st m E`: premises of the first kind: they name k; by their text, at fixed st, m and E they
  can hold at some values of the coins and fail at others.
- The end of the second binds besides c under `lendRow … (k.look …) … = .ok c` and Rr under
  `carryRows … (restCoins J' c.2.1).mem = .ok Rr`: of the first kind. J' under its equation, the
  record R under `enterFinish st = .ok R` and G under `R.st.groups[R.g]? = some G` name no coin.
- One clause of the invariant says that the input of m is w and meets Vd, a letter for a predicate
  on the input: what it reads of the input is not fixed here.
- The thread's other letters (test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, Said) stand under no
  premise in front that names a coin; the invariant reads them. The Script is no letter: it is the
  term `firstScriptAt`.
- The other theorems of this file name no coin: they bear none.
- What lifts the bar. For c and Rr the made terms are what `lendRow` and `carryRows` return:
  `carryRows_returns_at_input` (LReturnsClosing.lean) shows, from the head, the ground and the
  finish, at the rows of `Sz.ref` and at every input whose instance passes the description's test,
  that the second returns whatever is lent. For st, m and E the made terms would be those of the
  honest run at the border, as terms of w, k and the challenges, and the lemma would show the
  premises at them at every value of the coins. None is known to this file: so the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLScriptFirst
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLSeatAtStand
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLOwedAtStand
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingWordsHeard
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingStand
import Johnson.Desc.ProofFile.Honest.K12.AtProof.CutAtL
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below wordsFirst)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Means (layoutOf)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.FirstThread (lettersHead WtF roundsTo_succ)
open ProofFile.Honest.K1 (LocB firstScriptAt readersB)
open ProofFile.Honest.K2 (SwitchPlace)
open ProofFile.Honest.K2.Law (SwitchCoins)
open ProofFile.Honest.K12.Light (WordsTied)
open ProofFile.Honest.K12.AtProof (plainL finishAt finishW jobL doorAtL heardL heardL_at_stand
  places_at_L finish_two_rounds switch_lot_returns_at_closing_stand)
open P5J (AtMgA TS)

set_option maxRecDepth 1000000 in
/-- **A CLOSED LINE**: in the written list of places the written finish stands at number 353. The
control: asked for 354, the test's own number, the line says no. -/
theorem finish_border_written :
    finishW.any (fun pl => P5J.At.ps.findIdx (· == pl.place) == 353) = true ∧
      finishW.any (fun pl => P5J.At.ps.findIdx (· == pl.place) == 354) = false := by
  decide +kernel

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S₀ : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head, where the maker returns, the finish is member number 353.** -/
theorem finish_border_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S₀ Op) = .ok A)
    {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl) : borderNo cF.blocksInOrder pl.place = 353 := by
  have c := finish_border_written.1
  rw [← finish_is_written h hA, hf, Option.any_some, beq_iff_eq] at c
  rw [K1.borderNo_written h pl.place]
  exact c

/-- **The rounds in front of the test are those that the switch's lot reads, and two more.** -/
theorem challenges_in_front_of_the_test (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S₀ Op) = .ok A)
    {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl) :
    (declsTo cF.blocksInOrder 354).length = 0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder pl.place) + 2 := by
  obtain ⟨⟨b, hb, -⟩, -⟩ := places_at_L h.toAtMg
  have e := roundsTo_succ hb
  rw [finish_two_rounds h.toAtMg hb] at e
  rw [finish_border_first h hA hf, Nat.zero_add]
  exact e

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S₀ Op) = .ok A)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
  (Kp : Place → TS → TS → Prop) (w : LocB W₀)
include h hA

/-- **THE EQUATION OF LISTS AT A STAND.** -/
theorem heard_at_closing_stand {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl) {k : Coins A.B}
    {st : S} {m : Mid (LocB W₀) Unit} {E : Env}
    (hT : Thr (lettersHead h A.H (firstScriptAt I S₀ Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
      w).thread 354 k st m E) :
    heardL (frontOf m) =
      (m.st.heard ++ []).take (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder pl.place)) :=
  heardL_at_stand (lettersHead h A.H (firstScriptAt I S₀ Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
    w).thread hT.2.1 rfl (challenges_in_front_of_the_test h hA hf)

/-- **The maker's book is what bookWhole returns at the written lists of sendings.** -/
theorem book_first :
    bookWhole (P5J.F0T OnBytes.secondHashFunction A.Z Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (P5J.F0T OnBytes.secondHashFunction A.Z Np cF).first.blocksInOrder) = .ok A.B := by
  have e := K14.atPure_book_at_head h hA
  rw [VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
    (P5J.pins_of_laid h.scope h.laid).1] at e
  exact e

/-- hok, hpub, hReach AND hcarry ARE PREMISES. **THE TIE OF THE WORDS AT A STAND IN FRONT OF THE
CLOSING PROXIMITY TEST**: the premise hw of acceptedS_stands_L, at the first chain's Script. -/
theorem wordsTied_at_closing_stand (Said : ℕ → Coins A.B → Mid (LocB W₀) Unit → Prop)
    {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl)
    (hok : K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take pl.link) pl = true)
    (hpub : ∀ v, Vd v → K2.publicOk (widerRows S₀ A.Z A.G) A.G.first.layout pl
      ((K2.segmentsOf A.Z A.G).take pl.link) v.x = true)
    (hReach : ∀ k st m E, ThrS (lettersHead h A.H (firstScriptAt I S₀ Op A cF) test carryX item n₁
        n₂ b₀ Vd Rd Kp w).thread Said 354 k st m E →
      Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS A.Z) 354 (m.st.input.x.pub, st))
    (hcarry : ∀ k st m E R (J' : TestJob (LocB W₀) Unit),
      J' = atStand (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows S₀ A.Z A.G)
        (readersB I A.Z) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl) m.st.input
        (frontOf m) R →
      ∀ c : RowCoins [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'],
      ThrS (lettersHead h A.H (firstScriptAt I S₀ Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread Said 354 k st m E →
      enterFinish st = .ok R →
      lendRow A.B (A.B.rowsOf (lettersHead h A.H (firstScriptAt I S₀ Op A cF) test carryX item n₁ n₂
          b₀ Vd Rd Kp w).thread.chain)
        (k.look (lettersHead h A.H (firstScriptAt I S₀ Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
          w).thread.chain) J'.p.place
        [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'] 0 = .ok c →
      ∀ (cs : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries)
        (V : ℕ → Johnson.Prover.Send.Rows), K2.handed 0 pl k = some cs →
      K2.switchRowsLaid (widerRows S₀ A.Z A.G) (readersB I A.Z)
        (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl cs m.st.input
        (heardL (frontOf m)) = .ok V →
      AtProof.carryRows (widerRows S₀ A.Z A.G) (readersB I A.Z)
        (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl m.st.input
        (heardL (frontOf m)) (restCoins J' c.2.1).mem = .ok (V 0)) :
    ∀ k st m E R (J' : TestJob (LocB W₀) Unit),
      J' = atStand (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows S₀ A.Z A.G)
        (readersB I A.Z) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl) m.st.input
        (frontOf m) R →
      ∀ c : RowCoins [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'],
      ThrS (lettersHead h A.H (firstScriptAt I S₀ Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread Said 354 k st m E →
      enterFinish st = .ok R →
      lendRow A.B (A.B.rowsOf (lettersHead h A.H (firstScriptAt I S₀ Op A cF) test carryX item n₁ n₂
          b₀ Vd Rd Kp w).thread.chain)
        (k.look (lettersHead h A.H (firstScriptAt I S₀ Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
          w).thread.chain) J'.p.place
        [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'] 0 = .ok c →
      ∀ Rr : Johnson.Prover.Send.Rows,
      AtProof.carryRows (widerRows S₀ A.Z A.G) (readersB I A.Z)
        (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl m.st.input
        (heardL (frontOf m)) (restCoins J' c.2.1).mem = .ok Rr →
      ∀ G, R.st.groups[R.g]? = some G →
      WordsTied R.st R.g G
        (wordsFirst (P5J.At.arr A.Z) st.st st.book
          ((lettersHead h A.H (firstScriptAt I S₀ Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.wit k m.st.input (m.st.heard ++ [])))
        (layoutOf R.st G) (plainL Rr (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))) := by
  intro k st m E R J' hJ' c hT he hl Rr ho G hG
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hGd : ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G := by
    rw [eG]
    exact O.blank
  obtain ⟨est, -, hone, hmem⟩ := closingMemberSeat_at_stand h A.H (firstScriptAt I S₀ Op A cF) test
    carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1 (hReach k st m E hT) he hG hGd hf
  obtain ⟨hw, -, -, cs, hH, hrows⟩ := switch_lot_returns_at_closing_stand h A.H
    (firstScriptAt I S₀ Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w (book_first h hA) hGd hf
    (widerRows S₀ A.Z A.G) (readersB I A.Z) A.G.first.layout (K2.segmentsOf A.Z A.G) hok hpub hT.1
  obtain ⟨V, hV⟩ := hrows (heardL (frontOf m))
  have hc := hcarry k st m E R J' hJ' c hT he hl cs V hH hV
  obtain rfl : Rr = V 0 := Except.ok.inj (ho.symm.trans hc)
  rw [heard_at_closing_stand h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w hf hT.1] at hV
  have hcodes : st.st.codes = pl.sizes.codes :=
    (hmem 185 (by rw [hone]; exact List.mem_singleton.2 rfl)).codes
  rw [est]
  exact wordsTied_first h hA hf st.st st.book R.g G (layoutOf st.st G) hcodes
    (fun o ho' => ⟨(hmem o ho').seat, (hmem o ho').message, (hmem o ho').found⟩) hw k hH m.st.input
    (m.st.heard ++ []) hV _

end

end ProofFile.Honest.K12.LotL

end

#print axioms ProofFile.Honest.K12.LotL.finish_border_written
#print axioms ProofFile.Honest.K12.LotL.finish_border_first
#print axioms ProofFile.Honest.K12.LotL.challenges_in_front_of_the_test
#print axioms ProofFile.Honest.K12.LotL.heard_at_closing_stand
#print axioms ProofFile.Honest.K12.LotL.book_first
#print axioms ProofFile.Honest.K12.LotL.wordsTied_at_closing_stand
