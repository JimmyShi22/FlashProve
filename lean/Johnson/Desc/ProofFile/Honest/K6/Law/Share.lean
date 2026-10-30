-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/Share.lean.
WHAT IT IS NOT. CONDITIONAL: A SHELL. EVERY FIELD OF ITS TWO STRUCTURES IS A PREMISE: none is shown
here of a run, of a prover or of any values; no example is laid at which they hold together. NOT THE
DEBT `ExchangeS` AT THE SUB-PROTOCOL's BORDER: ITS SHARE AT THREE ITEMS; at the first chain's thread
that border's row owes seven (Honest/K6/Law/ShareAtHead.lean says which). The three fields of the
second structure hold all the content: that the relation `K6Out` holds behind the step at what
the law reads off the thread's witness, that what is due (`RecordDue`) stands there, and the table's
test on the forms at the head's four runs. That the verifier accepts is the debt's own premise:
nothing here shows it. Segment 24 and piece 4 are numerals, as in the library's lemma. Nothing
is claimed on soundness, completeness or hiding; none of the library's goals.
WHAT IT IS. The sub-protocol "the output head's own rounds": ITS SHARE OF THE DEBT `ExchangeS`
(Honest/Thread/PaysS.lean) AT THREE ITEMS OF THE TABLE OF JOINTS: formsT 24 4 "own", formsT 24 4
"join", formsT 24 4 "weights": two structures of named premises and one theorem that lays them into
the library's own lemma `opened_back` (Johnson/Desc/Kinds/Law/K6ItemsBack.lean); it ends in the
debt's share at one item, `ExchangeAtS` (Honest/Thread/SharesS.lean), three times.

  `k6_input`          the member's play leaves the input as it was (Honest/Law/Along.lean:
                      `play_mid`)
  `K6ShareLetters`    WHAT THE THREAD's LETTERS ARE ASKED TO MEET: what the three items mean follows
                      from the composed meaning's field; three facts on its data at valid inputs;
                      two on public numbers. No state of a run stands in it, and no border's number.
  `K6ShareDebts`      THIS SUB-PROTOCOL's OWN DEBTS behind the member's step, at lists of challenges
                      that fit: `due`, `pubTest`, `out`. No unfolding pays them.
  `k6_share`          under the two structures: the debt at the three items, from the thread with
                      any sentence Said beside it
  `k6_means_at`       the first three fields of `K6ShareLetters` AT THE FIRST CHAIN's THREAD
                      (Honest/Thread/First.lean: `Letters.thread`), where the letter for the items'
                      meaning is the composed meaning: by unfolding

WHO PAYS, AT THE FIRST CHAIN's THREAD AT THE LIBRARY's OWN LETTERS, BORDER 341. None of it is typed
here. `K6ShareLetters`: `k6_letters_full` (Honest/K6/Law/LettersFull.lean), under the library's one
hypothesis, at every Lk that is the first chain's link 24 (the library has one under that
hypothesis: `link24_at_head`, Johnson/Desc/Kinds/Law/K6StateAtHead.lean). `due`: `due_at_head`
(Honest/K6/Law/DueAtHead.lean), under the same two. `pubTest`: `k6_forms_behindS`
(Honest/K6/Law/FormsBehind.lean), under the hypothesis and a premise on the thread's letter for what
a step keeps. `out`: `k6_out_at_thread` (Honest/K6/Law/OutAtThread.lean), under three structures of
premises and the member's test on the plan; that test is paid under the hypothesis (`flat_ok`,
Johnson/P5J/FoldJ1.lean), two of the structures under it and a premise on the prover's halves; THE
THIRD, `K6Script`, IS SHOWN OF NO THREAD. The join: Honest/K6/Law/ShareAtHead.lean.
OF THE FOLDER Johnson/Goal/ it names Meaning.sizesOf, as an argument of the library's compCut;
nothing else of that folder is called, and no module of it is imported by name.

-/
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.Kinds.Law.K6ItemsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout ReqShape)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning Item)
open VerifiableInference.Desc.Sound (Mem MsgT Frame SeatsNamed GroupsSeated MgData mgAll namedOnce)
open ProofFile.Honest (Thread Thr ThrS ExchangeAtS ProverCoinCounts Coins Local Mid Env drawsFit play_mid)

/-- The member's play leaves the input as it was. -/
theorem k6_input {St Cl V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk St Cl V W X Pb}
    {blk : Block St Cl} {k : Coins Bk} {s s' : St} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn}
    {y : List ProofFile.Honest.Played × Mid W X} {cols : List OpenedColumn}
    (hS : T.Stepped blk k s m E ds y cols s') : y.2.st.input = m.st.input := by
  obtain ⟨⟨⟨l, _, hp⟩, _⟩, _⟩ := hS
  exact (play_mid l ds [] m y hp).1

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xj Tr X Pb Xi P Tok : Type} {rows cols nR : ℕ}
  {Wp : OnBytes.Model.Verify.Public}

/-- **WHAT THE THREAD's LETTERS ARE ASKED TO MEET.** Facts on letters, on the data and on public
numbers: no state of a run stands in them. -/
structure K6ShareLetters
    (T : Thread Bk S Claim (Local W₀ Rc Xj Tr) (Local W₀ Rc Xj Tr) X Pb)
    (i₁ i₂ i₃ : T.ι) (toP : T.P → P)
    (toW : T.Wt → Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (Dof : Local W₀ Rc Xj Tr → MgData Xi P Tok rows cols nR Wp)
    (Mg₀ : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ) (n rb l piece : ℕ)
    (states : ℕ → List (K9.RunOf S)) : Prop where
  /-- what the three items mean follows from the composed meaning's field -/
  own : ∀ w a y v, (mgAll (Dof w) Mg₀).formsT 24 4 "own" (toP a.1, a.2) y (toW v) →
    T.means w i₁ a y v
  join : ∀ w a y v, (mgAll (Dof w) Mg₀).formsT 24 4 "join" (toP a.1, a.2) y (toW v) →
    T.means w i₂ a y v
  weights : ∀ w a y v, (mgAll (Dof w) Mg₀).formsT 24 4 "weights" (toP a.1, a.2) y (toW v) →
    T.means w i₃ a y v
  /-- facts on the data, at valid inputs -/
  fits : ∀ w, T.valid w → ∃ tokV req dec hN hG tab tokH,
    MgFitsK6 (Dof w) lay6 num n rb tokV req dec hN hG tab tokH
  head : ∀ w, T.valid w → (Dof w).links[24]? = some .head
  once : ∀ w, T.valid w → namedOnce (Dof w).arr (Dof w).N 24 n = true
  /-- facts on public numbers -/
  runs : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l piece states 3
  plan : (parOf Wp.hS (workOf Wp)).ok = true

/-- **THIS SUB-PROTOCOL's OWN DEBTS, behind the member's step, at fitting lists.** No unfolding pays
them. -/
structure K6ShareDebts
    (T : Thread Bk S Claim (Local W₀ Rc Xj Tr) (Local W₀ Rc Xj Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xj Tr) X → Prop) (b : Nat)
    (toW : T.Wt → Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (Dof : Local W₀ Rc Xj Tr → MgData Xi P Tok rows cols nR Wp)
    (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ) (n rb : ℕ) (P8 : K8.ReadsQuiet.PH)
    (states : ℕ → List (K9.RunOf S)) : Prop where
  /-- what is due (`RecordDue`) stands at the state behind -/
  due : ∀ blk k s m E ds y cols s', T.bs[b]? = some blk → ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    ∃ aK cU, RecordDue (Dof m.st.input).arr (Dof m.st.input).N Wp lay6 num n
      rb P8 (Dof m.st.input).St states ((Dof m.st.input).Rd 24) s' aK cU
  /-- the table's test on the forms at the head's four runs, behind: the promise's own content at
  the next border -/
  pubTest : ∀ blk k s m E ds y cols s', T.bs[b]? = some blk → ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ r, K6Name r →
      K9.formsInT ((Dof m.st.input).Rd 24) ((Dof m.st.input).N.sent 24 0) 3 r s' = true
  /-- the elder relation `K6Out` behind the step, at what the law reads off the thread's witness, at
  every continuation -/
  out : ∀ blk k s m E ds y cols s', T.bs[b]? = some blk → ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds', K6Out Wp s'
      (compCut (Dof m.st.input).cs (Dof m.st.input).arr (Dof m.st.input).ms (Dof m.st.input).N
        (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp (plAt n rb)
        (toW (T.wit k m.st.input (y.2.st.heard ++ ds'))))

variable {T : Thread Bk S Claim (Local W₀ Rc Xj Tr) (Local W₀ Rc Xj Tr) X Pb}
  {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xj Tr) X → Prop} {b : Nat}
  {i₁ i₂ i₃ : T.ι} {toP : T.P → P} {toW : T.Wt → Wit (Fin rows → Fin cols → GE) Tok MsgT}
  {Dof : Local W₀ Rc Xj Tr → MgData Xi P Tok rows cols nR Wp}
  {Mg₀ : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
  {lay6 : ReqLayout} {num : ℕ → ℕ → ℕ} {n rb : ℕ} {P8 : K8.ReadsQuiet.PH} {l piece : ℕ}
  {states : ℕ → List (K9.RunOf S)}

/-- CONDITIONAL: **the shell**: under the two structures, the thread's debt at the three items. -/
theorem k6_share (L : K6ShareLetters T i₁ i₂ i₃ toP toW Dof Mg₀ lay6 num n rb l piece states)
    (H : K6ShareDebts T Said b toW Dof lay6 num n rb P8 states) :
    ExchangeAtS T Said b i₁ ∧ ExchangeAtS T Said b i₂ ∧ ExchangeAtS T Said b i₃ := by
  have core : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cs s', ThrS T Said b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cs s' → ∀ ds',
      (mgAll (Dof y.2.st.input) Mg₀).formsT 24 4 "own" (toP (T.seat k y.2 s').1, s')
          (T.strs (E.add y.1)) (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds'))) ∧
        (mgAll (Dof y.2.st.input) Mg₀).formsT 24 4 "join" (toP (T.seat k y.2 s').1, s')
          (T.strs (E.add y.1)) (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds'))) ∧
        (mgAll (Dof y.2.st.input) Mg₀).formsT 24 4 "weights" (toP (T.seat k y.2 s').1, s')
          (T.strs (E.add y.1)) (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds'))) := by
    intro blk hblk k s m E ds y cs s' hT hd hS ds'
    have hv : T.valid m.st.input := hT.1.2.2.2.2.2.2
    rw [k6_input hS]
    obtain ⟨tokV, req, dec, hN, hG, tab, tokH, F⟩ := L.fits _ hv
    obtain ⟨aK, cU, R⟩ := H.due blk k s m E ds y cs s' hblk hT hd hS
    exact opened_back Mg₀ F (L.head _ hv) P8 l piece states L.runs (toP (T.seat k y.2 s').1, s') _ _
      aK cU R L.plan (L.once _ hv) (H.pubTest blk k s m E ds y cs s' hblk hT hd hS)
      (H.out blk k s m E ds y cs s' hblk hT hd hS ds')
  refine ⟨?_, ?_, ?_⟩
  · intro blk hblk k s m E ds y cs s' hT hd hS ds' i hi
    rw [List.mem_singleton.1 hi]
    exact L.own _ _ _ _ (core blk hblk k s m E ds y cs s' hT hd hS ds').1
  · intro blk hblk k s m E ds y cs s' hT hd hS ds' i hi
    rw [List.mem_singleton.1 hi]
    exact L.join _ _ _ _ (core blk hblk k s m E ds y cs s' hT hd hS ds').2.1
  · intro blk hblk k s m E ds y cs s' hT hd hS ds' i hi
    rw [List.mem_singleton.1 hi]
    exact L.weights _ _ _ _ (core blk hblk k s m E ds y cs s' hT hd hS ds').2.2

end

/-! ## At the first chain's own letters -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xj Tr X Xi P Tok : Type} {rows cols nR : ℕ}
  {Wp : OnBytes.Model.Verify.Public}
  (L : ProofFile.Honest.FirstThread.Letters Bk Claim W₀ Rc Xj Tr X P (Fin rows → Fin cols → GE) Tok MsgT)
  {Dof : Local W₀ Rc Xj Tr → MgData Xi P Tok rows cols nR Wp}
  {Mg₀ : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)}

/-- CONDITIONAL: **the three premises on what the items mean, at the first chain's thread**: where
the letter for the items' meaning is the composed meaning. -/
theorem k6_means_at (hMg : ∀ w, L.Mg w = mgAll (Dof w) Mg₀) (r : String) :
    ∀ w a y v, (mgAll (Dof w) Mg₀).formsT 24 4 r (id a.1, a.2) y (id v) →
      L.thread.means w (Item.formsT 24 4 r) a y v := by
  intro w a y v h
  show Item.holds L.N (L.mg w) (Item.formsT 24 4 r) a y v
  unfold ProofFile.Honest.FirstThread.Letters.mg
  rw [hMg w]
  exact h

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_input
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_share
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_means_at
