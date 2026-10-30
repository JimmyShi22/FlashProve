-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the request's own test at a run: the six tests on the state on entry are paid.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListWSixPaid.lean: CONDITIONAL. One statement with its proof;
no
definition.

Can the hypotheses be met together at a real run? NOT KNOWN: as at Sim2/ListWAtThread.lean.

What is here. `onAtRun_W_at_the_returns_book` (Sim2/ListWAtReturnsBook.lean) WITH hsix GONE: at the
last
chain's thread in the form (`lettersLast` … .thread, Honest/Thread/LastHead.lean, every letter but
the trees taken over free), the six tests on the state on entry are `lines_front_narrow`,
CALLED.

  `onAtRun_W_six_paid`   the statement.

THE END IS `OnAtRun₃` ITSELF.

ALL THE PREMISES: h (`AtMgA`) · hAr · hL · hP · T · hρ · hR · hrun · hM · hq · the thread's letters
· Said with
  hSaid   at border 2 the companion gives the field letter at the base that is tied to the two ends:
      `SaidField` Th (`BaseTied` F Th);
  hI₃   the rule's invariant at border 2 of the last chain is that thread's with that companion;
  hsays   `SaysAt` at every stand of the thread there and whatever the frame lends the pair: a
      premise here; at the letters' names (the thread `thread₃`, the companion `said₃`, the job
      P.ownMany) it is `rowsSay_at_the_letters` (AtFullSide/K12/RowsSayAtTheLetters.lean), from the
      head at the return, the maker's return and the last chain's open letters P, WHICH ARE A
      PREMISE THERE (`openLast`, Honest/K12/AtFile/WAtTheLetters.lean, is a value of them);
      whether a stand of that thread is there is not said.

By. `lines_front_narrow` (K12/AtFile/WLine.lean) · `enters_at_W` (K12/AtFile/WAccepted.lean) ·
`letter_at_filling` (K12/AtFile/WFilling.lean) · `field_of_said_W` (K12/AtFile/WField.lean) ·
`mems_lit`
(K12/AtFile/CoreMems.lean). THESE FILES BEAR "NOT IN FRONT OF A LAW OVER COINS": so does this
statement: its
letters are theirs.

Limits. Those of the files named. No stand is shown but the one that the rule's own hypothesis
hands.
Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWAtReturnsBook
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLine
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WField
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFilling
import Johnson.Desc.ProofFile.Honest.K12.AtFile.CoreMems

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃)
open H2K.Member (codesFull piWFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open ProofFile.Honest.LastThread (lettersLast)
open ProofFile.Honest.K12.AtFile (takenLast lines_front_narrow enters_at_W letter_at_filling
  field_of_said_W mems_lit linesB)

attribute [local irreducible] P2Law.ProofPlan.WP

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- CONDITIONAL on all its premises. **The clause of the rule at the list that bears the lot's row,
at
the wide filling's return and its own book: the six tests on the state on entry paid.** -/
theorem onAtRun_W_six_paid {x₀ : VerifiableInference.Desc.First.Look.Place}
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
    -- the last chain's thread, at letters; the trees taken over are the written list
    {Wt : Type} (N : VerifiableInference.Desc.Shared.NumbersS)
    (Mg : Local W₀ IndexCommitterCoins ProofFile.Inst Cells →
      VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × P5J.TS) Wt)
    (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
    (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × P5J.TS))
    (order : S₃ → Prop)
    (ends : Coins Ar.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn → (ProofFile.InstPub × P5J.TS) ×
        Desc.K14.St)
    (wit : Coins Ar.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn → Wt)
    (table : Fmt.TreeSource → Coins Ar.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn → Place ×
        Table)
    (fixed : Fmt.TreeSource → ℕ) (item n₁ n₂ : ℕ) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
    (Rd : ℕ → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → S₃ → Prop) (Kp : Place → S₃ → S₃ → Prop) (w : Local W₀
              IndexCommitterCoins ProofFile.Inst Cells)
    (Said : ℕ → Coins Ar.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ k m, Said 2 k m →
      SaidField (lettersLast Zp Np cF Ar.H N Mg ML PL order takenLast ends wit table fixed item n₁
          n₂ Vd Rd Kp w).thread
        (BaseTied (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (lettersLast Zp Np cF Ar.H N Mg ML PL order
                        takenLast ends wit table fixed item n₁ n₂ Vd Rd Kp w).thread) 2 k m)
    (hI₃ : T.I₃ 2 = ThrS (lettersLast Zp Np cF Ar.H N Mg ML PL order takenLast ends wit table fixed
        item n₁ n₂ Vd Rd Kp w).thread Said 2)
    (hsays : ∀ (st : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃) (m₀ : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
                    Unit) (E₀ : Env)
      (c : RowCoins [(firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀
                IndexCommitterCoins ProofFile.Inst Cells) Unit), restPart M.toRun.toTest]),
      ThrS (lettersLast Zp Np cF Ar.H N Mg ML PL order takenLast ends wit table fixed item n₁ n₂ Vd
          Rd Kp w).thread Said 2 k st m₀ E₀ →
      lendRow Ar.B (Ar.B.rowsOf 2) (k.look 2) placeW
        [(firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst
                  Cells) Unit), restPart M.toRun.toTest] 0 = .ok c →
      SaysAt M m₀.st.input (frontOf m₀) (restCoins M.toRun.toTest c.2.1)) :
    OnAtRun₃ T ρ r L := by
  obtain ⟨M', hM', hp, -, -, -, -, HL⟩ := letter_at_filling (Wt := Wt) h I S' O hAr
  have eMM : M' = M := Option.some.inj (hM'.symm.trans hM)
  subst eMM
  obtain ⟨hm, ht⟩ := mems_lit h I S' O hAr hM'
  have hF := field_of_said_W (F := (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) (lettersLast Zp Np cF Ar.H N
                  Mg ML PL order takenLast ends wit table fixed item n₁ n₂ Vd Rd Kp w).thread Said 2 hSaid
  refine onAtRun_W_at_the_returns_book h I S' O hAr hL hP T hρ hR hrun M' hM L hq
    (lettersLast Zp Np cF Ar.H N Mg ML PL order takenLast ends wit table fixed item n₁ n₂ Vd Rd Kp
        w).thread Said hI₃ (fun st m₀ E₀ u => ?_) hsays
  have hE := (enters_at_W (HL N Mg ML PL order ends wit table fixed item n₁ n₂ Vd Rd Kp w) hF u).1
  obtain ⟨hl, hfr⟩ := lines_front_narrow Zp Np cF Ar.H N Mg ML PL order takenLast ends wit table
      fixed item n₁ n₂ Vd Rd Kp w h Said M'
    (by rw [hp]; exact early_at_head_W h.toAtMg) hp hm ht hF u hE
  unfold linesB at hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
  exact ⟨hl.1.1, hl.1.2, hl.2, hfr⟩

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.onAtRun_W_six_paid
