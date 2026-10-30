-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the request's own test at a run, at the return's own book.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListWAtReturnsBook.lean: CONDITIONAL. Statements with their
proofs;
no definition.

Can the hypotheses be met together at a real run? NOT KNOWN: as at Sim2/ListWAtThread.lean.

What is here. `onAtRun_W_at_thread` (Sim2/ListWAtThread.lean) AT THE BOOK THAT THE MAKER RETURNS
WITH THE
PROVER: AMONG THE BINDERS NO PREMISE ON A BOOK IS LEFT. The book's return has moved into hAr: what
is
won is which book, not that the maker of books returns.

  `returns_book_written`   under the stronger head the return's book has the written entries and the
      written rows of the first chain.
  `omega_plan_written`   the shared sendings' plan has the written codes and shape.
  `onAtRun_W_at_the_returns_book`   **the statement.**

THE END IS `OnAtRun₃` ITSELF. OF THE SENDERS' 71 PREMISES NONE IS LEFT.

ALL THE PREMISES: h (`AtMgA`) · hAr · hL · hP · T · hρ · hR · hrun · hM · hq · Th, Said (letters) ·
hI₃ · hsix ·
hsays. What each is: Sim2/ListWAtThread.lean's head. hsays is a premise here; at the letters' names
(the thread `thread₃`, the companion `said₃`, the job P.ownMany) it is `rowsSay_at_the_letters`
(AtFullSide/K12/RowsSayAtTheLetters.lean), from the head at the return, the maker's return and the
last chain's open letters P, WHICH ARE A PREMISE THERE (`openLast`,
Honest/K12/AtFile/WAtTheLetters.lean, is a value of them); whether a stand of that thread is there
is not said.

By. THE TESTS ON THE BOOK ARE CALLED, NOT TYPED: `own_proof_at`
(Sim2/OwnProofBook.lean: the
five, by Lean's kernel at the written entries) and `ties_of_written`
(AtFullSide/K12/TiesForAtPure.lean). Which book: `atPure_book_at_head`
(Honest/K14/AtPureBookAtHead.lean) ·
`made_sends_at_files` (Honest/K14/SharedSendsWritten.lean) · `bookWhole_same_at_head`
(Honest/K14/BookWholeAtHead.lean) · `bookRaw_returns_written`, `bookWhole_returns_raw`,
`rawAhead_written`, `rawBookRows_written` (AtFullSide/K14/).

Limits. Those of the files named. It stands at the list of merges that the maker guesses
(AtPureBookAtHead.lean's own words). Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWAtThread
import Johnson.Desc.ProofFile.Honest.K12.Sim2.OwnProofBook
import AtFullSide.K12.TiesForAtPure
import AtFullSide.K14.WholeAheadAtHead
import AtFullSide.K14.RawBookRowsWritten
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K14.SharedSendsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.K1 (qFull likeFull_qFull)
open VerifiableInference.Desc.K13.Law (wMsgFull wMsg_written)
open H2K.Member (codesFull piWFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open ProofFile.Honest.K14 (jobOmega)
open AtFullSide.K14 (rawAheadW rawRowsFirstW)

attribute [local irreducible] P2Law.ProofPlan.WP

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- CONDITIONAL on the head and hA. **The return's book has the written entries and first rows.**
General in the filling. -/
theorem returns_book_written {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) {Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.B.ahead = rawAheadW ∧ A.B.first = rawRowsFirstW := by
  obtain ⟨W, hW⟩ := AtFullSide.K14.bookRaw_returns_written
  have hh := K14.bookWhole_same_at_head (AtFullSide.K14.bookWhole_returns_raw W hW) h
  have hb' := K14.atPure_book_at_head h hA
  rw [K14.made_sends_at_files h.scope h.laid] at hb'
  have e : W = A.B := Except.ok.inj (hh.symm.trans hb')
  rw [← e]
  exact ⟨AtFullSide.K14.rawAhead_written W hW, (AtFullSide.K14.rawBookRows_written _ W hW).1⟩

/-- CONDITIONAL on the head. The shared sendings' plan has the written codes and shape. -/
theorem omega_plan_written (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) :
    (VerifiableInference.Desc.K1.qAt Zp Np).codes = qFull.codes ∧
      (VerifiableInference.Desc.K1.qAt Zp Np).S = qFull.lin := by
  obtain ⟨x, -, Wr⟩ := written_at_head h
  rw [qAt_written Wr Np]
  refine ⟨likeFull_qFull.codes.symm, ?_⟩
  show x.shape = qFull.lin
  rw [← Wr.lin]
  exact (like_head h).1.lin.trans likeFull_qFull.lin.symm

/-- CONDITIONAL on all its premises. **The clause of the rule at the list that bears the lot's row,
at
the wide filling's return and its own book: no premise on a book.** -/
theorem onAtRun_W_at_the_returns_book {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) (I : WiderIn W₀)
    (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) =
      .ok Ar)
    (hL : secondW (X := Unit) I OnBytes.secondHashFunction S' O Ar.Z Ar.G ≠ [])
    {H : Prover W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B W₀ IndexCommitterCoins OnBytes.TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {w₀ : W₀} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins Ar.B} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k ρ = .ok r)
    (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hM : jobRealW S' (P5J.F0T OnBytes.secondHashFunction Zp Np cF) enterOwn O.pile (K1.lotNo OnBytes.secondHashFunction Zp)
      (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
      (fun P w => randAt P w.rc) Zp Ar.G = some M)
    (L : Lettered Ar.B (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
      (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (hq : L.bare = rowAtW Face.own OnBytes.secondHashFunction Zp Np cF M.toRun.toTest)
    -- the rule's invariant in front of the test is a thread's; two sentences at its stands
    (Th : Thread Ar.B (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
        (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (Said : ℕ → Coins Ar.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hI₃ : T.I₃ 2 = ThrS Th Said 2)
    (hsix : ∀ (st : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃) (m₀ : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
                    Unit) (E₀ : Env), ThrS Th Said 2 k st m₀ E₀ →
      frontFiveB M.toRun.toTest.p codesFull (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀ m₀.st.input
                (frontOf m₀))) = true ∧
      manyFitsS M.p (M.mems.map (·.shape)) M.trees
        (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀ m₀.st.input (frontOf m₀))))
            = true ∧
      tsLenOf M.toRun.toTest.p (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀
                      m₀.st.input (frontOf m₀)))) = 3 ∧
      ∃ Dp, FrontAsksD M.toRun.toTest m₀.st.input (frontOf m₀) codesFull Dp)
    (hsays : ∀ (st : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃) (m₀ : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
                    Unit) (E₀ : Env)
      (c : RowCoins [(firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀
                IndexCommitterCoins ProofFile.Inst Cells) Unit), restPart M.toRun.toTest]),
      ThrS Th Said 2 k st m₀ E₀ →
      lendRow Ar.B (Ar.B.rowsOf 2) (k.look 2) placeW
        [(firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst
                  Cells) Unit), restPart M.toRun.toTest] 0 = .ok c →
      SaysAt M m₀.st.input (frontOf m₀) (restCoins M.toRun.toTest c.2.1)) :
    OnAtRun₃ T ρ r L := by
  have h' := h.toAtMg
  obtain ⟨hAh, hFr⟩ := returns_book_written h hAr
  obtain ⟨hAc, hAS⟩ := omega_plan_written h'
  obtain ⟨b1, b2, b3, b4, b5⟩ := own_proof_at hAh hFr (PI := PIw) (PW := PWw) rfl rfl rfl rfl
    (⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩ : K14.SendPub) hAc hAS
  have e3 : M.toRun.toTest.members.length = 3 := by
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, hb⟩ := eight_blocks_at_head h'
    have hA := sendPub_at_head h' q1 q2 q3 q4 q5 q6 q7 q8 hb
    have hmsg : OnBytes.linMessageW Zp.first.lin = some wMsgFull :=
      (VerifiableInference.Desc.K1.wMsg_full (like_head h').1).trans wMsg_written
    rw [real_job_written h' S' O.pile (K1.lotNo OnBytes.secondHashFunction Zp) _ _ _ Ar.G hM hA hmsg]
    rfl
  exact onAtRun_W_at_thread h I S' O hAr hL hP T hρ hR hrun M hM L hq
    (by rw [e3]; exact (AtFullSide.K12.ties_of_written Ar.B hAh).2) b1 b2 b3 b4 b5 Th Said hI₃ hsix
    hsays

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.returns_book_written
#print axioms ProofFile.Honest.K12.Sim2.omega_plan_written
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_W_at_the_returns_book
