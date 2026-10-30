-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WTable.lean: the clauses `trees` and `old` of `StandAtW`
(WAccepted.lean) at the last chain's thread whose table and counts are `lastTable` and `lastFixed`
(LastTerm.lean) with the test's own trees, and the five at the base prover at these terms.

  `roundsTo_at_F0T`   no round stands in front of the test in its own chain
  `trees_at_term`  the test's new trees are the thread's tables
  `WidthsAt`       the three taken trees' widths, at the two earlier threads' tables
  `old_at_term`    the taken trees are in hand at the declared widths
  `StandRest`      what a stand still owes, each under its name
  `five_at_filling`   the five at the base prover

The premises of `five_at_filling`, and where each is owed.
  hPL      the thread's promise is `fillAt`: the thread's letter
  WidthsAt the first and the shared thread's tables: theirs
  `StandRest.field`   the field and the ends: ProofFile's `SaidField` with `BaseTied`
  `StandRest.taken`   the job's trees are the tables taken over
  `StandRest.saysAt`  `SaysLeft` (WSays.lean): the item rows, the pins, the tie of the words
  hnext    the letters' order, rides and keeps behind the block

Limits.
- NOT IN FRONT OF A LAW OVER COINS: the thread's pair is a premise, the five its ends.
- AT THE FILLING, NOT READ THROUGH.
- `testTbl` is a text of a test's tree: the head of K12/ScriptLots.lean binds whoever lays it.
- That a stand is reached is not said; where none is, the five say nothing.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFilling
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFiveAt
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WHanded
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLine
import Johnson.Desc.ProofFile.Honest.K12.AtFile.CoreMems
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WSays
import AtFullSide.K12.LettersTwelve

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut start₃E firstOfS sharedOfEnd)
open VerifiableInference.Desc.Last (fillAt lastPlaces)
open ProofFile.Honest.K12.Light (ManyJob SaysAt)
open H2K.Member (piWFull)
open ProofFile.Honest.LastThread (lettersLast)
open ToldDesc (ownAt)
open P5J (F0T TS AtMgA)
open AtFullSide.K12 (jobAtFill)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- No round stands in front of the test in its own chain. -/
theorem roundsTo_at_F0T (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain P5J.TS ProofFile.Cl) : roundsTo (F0T o Zp Np cF).second.blocksInOrder 2 = 0 := by
  rw [second_flat]
  rfl

section
variable {Bk : ProverCoinCounts} {W₃ W₂ X : Type}

/-- **The three taken trees' widths**, at the two earlier threads' tables. -/
structure WidthsAt (r₁ : ℕ) (toCommon : W₃ → W₂)
    (tb₁ : Fmt.TreeSource → Coins Bk → W₃ → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins Bk → W₂ → List Fmt.Drawn → Place × Table) : Prop where
  masks : ∀ k w h, (tb₁ (.own 1) k w h).2.words = 3
  own : ∀ k w h, (tb₁ (.own 82) k w h).2.words = 12
  omega : ∀ k w h, (tb₂ (.own 1) k w h).2.words = 36

end

section
variable {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X Wt W₂ : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : Local W₀ Rc ProofFile.Inst Tr →
    VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × P5J.TS) Wt)
  (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
  (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × P5J.TS))
  (order : S₃ → Prop)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    (ProofFile.InstPub × P5J.TS) × Desc.K14.St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (r₁ n₀ : ℕ) (toCommon : Local W₀ Rc ProofFile.Inst Tr → W₂)
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
  (tb₂ : Fmt.TreeSource → Coins Bk → W₂ → List Fmt.Drawn → Place × Table)
  (fx₁ fx₂ : Fmt.TreeSource → ℕ)
  (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) X) (own₀ : X)
  (item n₁ n₂ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : ℕ → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop) (Kp : Place → S₃ → S₃ → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The thread at the tables and counts. -/
noncomputable abbrev lastAt : Thread Bk S₃ ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst :=
  (lettersLast Zp Np cF H N Mg ML PL order takenLast ends wit
    (lastTable r₁ toCommon tb₁ tb₂ (ownLast J own₀ n₀))
    (lastFixed r₁ fx₁ fx₂ fun τ => n₀ + seedRound J.p.nums.stages τ) item n₁ n₂ Vd Rd Kp w).thread

/-- **The clause `old` at the tables.** -/
theorem old_at_term (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hW : WidthsAt r₁ toCommon tb₁ tb₂) {k : Coins Bk} {s : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁
      tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w) 2 k s m E) :
    ∀ d ∈ (proximityTestKind guardedProximityTestParts (fourOf Np).W : Block T12 Unit).rounds, ∀ q ∈ d.opens,
      oldSrc E.sent q.2 = true → ∃ pt, E.tree q.2 = some pt ∧ pt.2.words = q.1.W := by
  refine old_at_W h _ rfl (sent_at_F0T OnBytes.secondHashFunction Zp Np cF) (fun σ hσ k' w' h' => ?_) u
  have e : takenLast = [.taken 0 1, .taken 0 82, .taken 1 1] := by decide
  rw [e] at hσ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl
  · exact hW.masks k' w' h'
  · exact hW.own k' w' h'
  · exact hW.omega _ _ _

/-- **The clause `trees` at the tables.** n₀: the rounds in front of the chain. -/
theorem trees_at_term (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hn : n₀ = (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon
      tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).front)
    (hseat : SeatOf ((ownAt Np).retype : Block S₃ ProofFile.Cl) J enterOwn leaveOwn)
    (hp : J.p = (fourOf Np).W) (hfresh : J.fresh.isNone = false) (hR : RowsOfHeard J)
    (hhalf : ((lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁
        tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).hs.find? fun g =>
        g.place == ((ownAt Np).retype : Block S₃ ProofFile.Cl).place) =
      some (proverSideOfProximityTest J : Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X).needsField)
    (hblk : (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁
      tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).bs[2]? =
        some ((ownAt Np).retype : Block S₃ ProofFile.Cl)) :
    ∀ k st m E ds y cols,
      Thr (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁
        tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w) 2 k st m E → m.opened.isSome = true →
      drawsFit ((ownAt Np).retype : Block S₃ ProofFile.Cl).rounds ds = true →
      (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁
        fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).Moved ((ownAt Np).retype : Block S₃ ProofFile.Cl) k m E ds y
          cols →
      (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁
        fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).Trees ((lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL
          order ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).fresh 2) k y.2
            (E.add y.1) := by
  refine trees_head_W h _ hblk J enterOwn leaveOwn hseat hp hfresh hR hhalf own₀ ?_ ?_
  · intro τ _
    have e₁ : treesTo (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀
        toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).bs 2 = 0 :=
      sent_at_F0T OnBytes.secondHashFunction Zp Np cF
    have e₂ : roundsTo (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀
        toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).bs 2 = 0 :=
      roundsTo_at_F0T OnBytes.secondHashFunction Zp Np cF
    rw [e₁, e₂, Nat.zero_add, Nat.add_zero, ← hn]
    rfl
  · intro τ _
    have e₁ : treesTo (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀
        toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).bs 2 = 0 :=
      sent_at_F0T OnBytes.secondHashFunction Zp Np cF
    have e₂ : roundsTo (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀
        toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).bs 2 = 0 :=
      roundsTo_at_F0T OnBytes.secondHashFunction Zp Np cF
    rw [e₁, e₂, Nat.zero_add, Nat.add_zero, ← hn]
    rfl

/-- **What a stand still owes, at the tables.** -/
structure StandRest (T : Thread Bk S₃ ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X
      ProofFile.Inst)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (A : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X) : Prop where
  field : FieldAtW (F0T OnBytes.secondHashFunction Zp Np cF) T Said 2
  taken : ∀ k st m E (c : RowCoins [(firstPart A.toRun.toTest :
      Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X), restPart A.toRun.toTest]),
    ThrS T Said 2 k st m E →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) A.p.place
      [(firstPart A.toRun.toTest : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
        restPart A.toRun.toTest] 0 = .ok c →
    ∀ i (hi : i < takenLast.length), TakenIs T k m
      (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
        (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1)))
      i takenLast[i]
  saysAt : ∀ k st m E (c : RowCoins [(firstPart A.toRun.toTest :
      Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X), restPart A.toRun.toTest]),
    ThrS T Said 2 k st m E →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) A.p.place
      [(firstPart A.toRun.toTest : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X),
        restPart A.toRun.toTest] 0 = .ok c →
    ∃ ws, SaysLeft A m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1) st ws

/-- **`StandAtW` at the tables, from what still stands open.** -/
theorem stand_of_rest {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Rr : List Fmt.DeclaredRound}
    (hPL : PL = fillAt (ToldDesc.p14At Zp) Rr handLast endedLast)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (A : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X) (hp : A.p = (fourOf Np).W)
    (hm : A.mems.map (·.shape) = memsW) (ht : A.trees = treesW piWFull)
    (hfresh : A.fresh.isNone = false) (hR : RowsOfHeard A.toRun.toTest)
    (hn : n₀ = (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon
      tb₁ tb₂ fx₁ fx₂ A.toRun.toTest own₀ item n₁ n₂ Vd Rd Kp w).front)
    (H₀ : LetterAtW (F0T OnBytes.secondHashFunction Zp Np cF)
      (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁
        fx₂ A.toRun.toTest own₀ item n₁ n₂ Vd Rd Kp w) 2 A enterOwn leaveOwn
      ((ownAt Np).retype : Block S₃ ProofFile.Cl) idleT12)
    (hW : WidthsAt r₁ toCommon tb₁ tb₂)
    (R : StandRest (Zp := Zp) (Np := Np) (cF := cF) (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML
      PL order ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ A.toRun.toTest own₀ item n₁ n₂ Vd Rd Kp w)
      Said A) :
    StandAtW (F0T OnBytes.secondHashFunction Zp Np cF) (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order
                  ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ A.toRun.toTest own₀ item n₁ n₂ Vd Rd Kp w) Said 2 A := by
  have he : A.p.early = true := (public_head_W h.toAtMg A hp hfresh).2.2.2.1
  have LF : ∀ k st m E, ThrS (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁
      n₀ toCommon tb₁ tb₂ fx₁ fx₂ A.toRun.toTest own₀ item n₁ n₂ Vd Rd Kp w) Said 2 k st m E →
      linesB A H2K.Member.codesFull 3 (ProofFile.Honest.Sh.testSh (A.rec₀ m.st.input (frontOf m))) = true ∧
        ∃ Dp, FrontAsksD A.toRun.toTest m.st.input (frontOf m) H2K.Member.codesFull Dp :=
    fun k st m E u => lines_front_narrow Zp Np cF H N Mg ML PL order takenLast ends wit _ _ item n₁ n₂
      Vd Rd Kp w h Said A he hp hm ht R.field u (enters_at_W H₀ R.field u).1
  exact
    { field := R.field
      taken := R.taken
      lines := fun k st m E u => (LF k st m E u).1
      front := fun k st m E u => (LF k st m E u).2
      saysAt := fun k st m E c u hc => by
        obtain ⟨ws, hL⟩ := R.saysAt k st m E c u hc
        exact saysAt_own A _ _ _ (enters_at_W H₀ R.field u).1
          (owe_of_says (tidy_at_stand Zp Np cF H N Mg ML PL order takenLast ends wit _ _ item n₁ n₂ Vd
            Rd Kp w hPL u.1) hL)
      old := fun k st m E u => by
        rw [hp]
        exact old_at_term H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ _ own₀ item n₁ n₂
          Vd Rd Kp w h.toAtMg hW u.1
      trees := fun blk hb k st m E ds y cols u hd hM => by
        obtain rfl : blk = ((ownAt Np).retype : Block S₃ ProofFile.Cl) :=
          Option.some.inj (hb.symm.trans H₀.member)
        exact trees_at_term H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ _ own₀ item n₁
          n₂ Vd Rd Kp w h.toAtMg hn H₀.seat hp hfresh hR H₀.half H₀.member k st m E ds y cols u.1
          (enters_at_W H₀ R.field u).2 hd hM }

end

section
variable {x : VerifiableInference.Desc.First.Look.Place} {W₀ Wt W₂ : Type}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
  (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
include h hA

/-- **The five at the base prover.** The job is the filling's, the thread's tables and counts are
the terms above, every other letter is free. -/
theorem five_at_filling :
    ∃ M, jobAtFill Zp Np cF I S O A.G = some M ∧
      ∀ (N : VerifiableInference.Desc.Shared.NumbersS)
        (Mg : Local W₀ IndexCommitterCoins ProofFile.Inst Cells →
          VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × P5J.TS) Wt)
        (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
        (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × P5J.TS))
        (ends : Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn →
          (ProofFile.InstPub × P5J.TS) × Desc.K14.St)
        (wit : Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn → Wt)
        (r₁ n₀ : ℕ) (toCommon : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → W₂)
        (tb₁ : Fmt.TreeSource → Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn →
          Place × Table)
        (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn → Place × Table)
        (fx₁ fx₂ : Fmt.TreeSource → ℕ) (own₀ : Unit) (item n₁ n₂ : ℕ)
        (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
        (Rd : ℕ → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → S₃ → Prop) (Kp : Place → S₃ → S₃ → Prop)
        (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
        {Rr : List Fmt.DeclaredRound},
        PL = fillAt (ToldDesc.p14At Zp) Rr handLast endedLast →
        n₀ = (lastAt (Zp := Zp) (Np := Np) (cF := cF) A.H N Mg ML PL (fun s => OnBytes.Means.InOrder s.st) ends wit r₁ n₀ toCommon
          tb₁ tb₂ fx₁ fx₂ M.toRun.toTest own₀ item n₁ n₂ Vd Rd Kp w).front →
        WidthsAt r₁ toCommon tb₁ tb₂ →
        StandRest (Zp := Zp) (Np := Np) (cF := cF) (lastAt (Zp := Zp) (Np := Np) (cF := cF) A.H N Mg
          ML PL (fun s => OnBytes.Means.InOrder s.st) ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ M.toRun.toTest own₀ item n₁ n₂ Vd Rd Kp
          w) Said M →
        (∀ k s m E ds y cols s',
          ThrS (lastAt (Zp := Zp) (Np := Np) (cF := cF) A.H N Mg ML PL (fun s => OnBytes.Means.InOrder s.st) ends wit r₁ n₀ toCommon
            tb₁ tb₂ fx₁ fx₂ M.toRun.toTest own₀ item n₁ n₂ Vd Rd Kp w) Said 2 k s m E →
          drawsFit ((ownAt Np).retype : Block S₃ ProofFile.Cl).rounds ds = true →
          (lastAt (Zp := Zp) (Np := Np) (cF := cF) A.H N Mg ML PL (fun s => OnBytes.Means.InOrder s.st) ends wit r₁ n₀ toCommon tb₁
            tb₂ fx₁ fx₂ M.toRun.toTest own₀ item n₁ n₂ Vd Rd Kp w).Stepped
            ((ownAt Np).retype : Block S₃ ProofFile.Cl) k s m E ds y cols s' →
          Rd 3 y.2.st.input s' ∧ ∀ q, lastPlaces[2]? = some q → Kp q s s') →
        ∀ fl : ℕ → S₃ → List Fmt.Drawn → Option String,
          FiveAt (lastAt (Zp := Zp) (Np := Np) (cF := cF) A.H N Mg ML PL (fun s => OnBytes.Means.InOrder s.st) ends wit r₁ n₀ toCommon
            tb₁ tb₂ fx₁ fx₂ M.toRun.toTest own₀ item n₁ n₂ Vd Rd Kp w) Said fl 2 := by
  obtain ⟨M, hM, hp, ⟨f, hf⟩, hl, hd, hR, hL⟩ := letter_at_filling (Wt := Wt) h I S O hA
  have hms := mems_lit h I S O hA hM
  refine ⟨M, hM, ?_⟩
  intro N Mg ML PL ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ own₀ item n₁ n₂ Vd Rd Kp w Said Rr
    hPL hn hW R hnext fl
  have H₀ := hL N Mg ML PL (fun s => OnBytes.Means.InOrder s.st) ends wit (lastTable r₁ toCommon tb₁ tb₂
    (ownLast M.toRun.toTest own₀ n₀))
    (lastFixed r₁ fx₁ fx₂ fun τ => n₀ + seedRound M.toRun.toTest.p.nums.stages τ) item n₁ n₂ Vd Rd Kp w
  have St := stand_of_rest A.H N Mg ML PL (fun s => OnBytes.Means.InOrder s.st) ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ own₀ item n₁
    n₂ Vd Rd Kp w h hPL Said M hp hms.1 hms.2 (by rw [hf]; rfl) hR hn H₀ hW R
  have hplan : (VerifiableInference.Desc.K12.proximityTestKind guardedProximityTestParts M.toRun.toTest.p : Block T12 Unit).planOk =
      true := (public_head_W h.toAtMg M hp (by rw [hf]; rfl)).2.2.1
  refine five_at_W A.H N Mg ML PL (fun s => OnBytes.Means.InOrder s.st) takenLast ends wit _ _ item n₁
    n₂ Vd Rd Kp w h.toAtMg (AtFullSide.K12.book_laid h hA) Said M hp f hf hl hd hPL H₀ St ?_ fl
  intro k s m E ds y cols s' u hd' hS
  obtain ⟨hr, hk⟩ := hnext k s m E ds y cols s' u hd' hS
  obtain ⟨⟨-, -, hform, -⟩, -⟩ := u
  obtain ⟨f', o', -, -, h2⟩ := shape_of_form _ hPL hform
  obtain ⟨-, -, -, hdec⟩ := VerifiableInference.Desc.step_inv _ _ _ _ _ _ _ hS.2
  exact ⟨(tidy_behind H₀.seat hplan h2 hdec).inOrder, hr, hk⟩

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.roundsTo_at_F0T
#print axioms ProofFile.Honest.K12.AtFile.WidthsAt
#print axioms ProofFile.Honest.K12.AtFile.lastAt
#print axioms ProofFile.Honest.K12.AtFile.old_at_term
#print axioms ProofFile.Honest.K12.AtFile.trees_at_term
#print axioms ProofFile.Honest.K12.AtFile.StandRest
#print axioms ProofFile.Honest.K12.AtFile.stand_of_rest
#print axioms ProofFile.Honest.K12.AtFile.five_at_filling
