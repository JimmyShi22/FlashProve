-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/RcAtStand.lean: AT A STAND OF THE FIRST THREAD AT THE CHAIN's END THE STATE PASSES THE LIBRARY's TESTS ON THE FIRST CHAIN's LAST STATE (ToldDesc.rcLastB): the two things left of hFirst under the threads: rcLastB says yes at the plan's values, and the state's codes are the statement's.

  rc_at_stand   from ThrS at SaidOk: rcLastB at the plan's values; the statement's codes

By calls: hRc_at_left_gen (ToldDescR/HRcAtLeftGen.lean) at the thread's own meaning of the promise; its EndAt₁ off reach_below (Thread/SaidOk.lean): the pair ThrS, not Thr alone: a stand may hold a word above the prime; the slot's condition is the thread's formP at the end; the closed facts as AtMgA.lastLeft_at_head_alone takes them.

This letter is for the honest run's own forms alone. NEVER ON SOUNDNESS's ROAD.
NO PROPERTY IS CLAIMED. -/
import Johnson.Desc.ProofFile.Honest.Thread.WordsBelow
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.Desc.ProofFile.Honest.Thread.BookFacts
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.P2LawR.LdAtLeft
import Johnson.P2LawR.SitsAtLeft
import Johnson.P2LawR.RestOfDoor
import Johnson.ToldDescR.HRcAtLeftGen
import Johnson.Desc.Last.OwnAtHead
import Johnson.P5J.L0.LastMq
import Johnson.P5J.CodesOne
import Johnson.Desc.Kinds.Law.RowLenAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ToldDesc (rcLastB p14At)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The tests on the last state at a stand at the chain's end.** -/
theorem rc_at_stand (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT' : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      cF.blocksInOrder.length k s m E) :
    rcLastB 0 (LLT25.vAt Zp h.𝔇.N) VerifiableInference.Desc.K13.Law.LFull s.st.codes s = true ∧
      s.st.codes = P5J.At.cs Zp := by
  have hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      cF.blocksInOrder.length k s m E := ⟨hT'.1, hSaid _ _ _ hT'.2⟩
  obtain ⟨-, -, -, hIdx, hNum, hcut, hmade⟩ := h.rest_of_door
  have hy : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first
      Zp.made = true :=
    VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [hmade, Bool.or_true])
  have hfull := P2Law.Left.ldAt_is_full h.toAtMg hy
  have hL := P2Law.Left.ld_at_head h.toAtMg hy
  have hS := P2Law.Left.sits_at_head h.toAtMg hy
  rw [hfull] at hL hS
  have hm : s.failed = none := head_noMark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1
  have hb : cF.blocksInOrder.length ≤ cF.blocksInOrder.length := le_rfl
  have hr := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT.1
  have hc : s.st.codes = P5J.At.cs Zp := (reach_facts h).codes _ _ hr hm
  have hN : h.𝔇.N = P5J.At.N Zp cF := rfl
  have hpc : (p14At Zp).codes = P5J.At.cs Zp := (P5J.At.codesOne h.laid).symm
  refine ⟨?_, hc⟩
  rw [hN, hc, ← hpc]
  have hEnd := reach_below (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (ProofFile.startS Zp) m.st.input.x.pub hb (fun _ h0 => h0)
    (fun v i p u hu => storedWords_lt H v.w₀ v.rc i p u hu) hT
  have hII : ∀ a, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub .indexIs a =
      K13.indexIsC 4 a.2 := by
    intro a
    have e1 : P5J.mgAtAll h = h.toAtMg.mq h.𝔇 := h.mq_is.symm
    show (P5J.mgAtAll h).pub .indexIs a = _
    rw [e1, VerifiableInference.Desc.Last.mq_indexIs h.toAtMg h.𝔇 a, hIdx]
  exact ToldDesc.hRc_at_left_gen h.toAtMg
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP hII hL (fun _ => True)
    ((ToldDesc.planSits_iff _ _ _ _ _).1 hS) hNum hcut hmade (m.st.input.x.pub, s) ProofFile.Honest.FirstThread.noStrs
    (by
      have f := hT.1.2.2.1.2
      have hl : P5J.At.ps.length = cF.blocksInOrder.length := by
        rw [head_len h]
        exact VerifiableInference.Desc.Kinds.Head.Law.ps_length
      have e0 : P5J.At.ps[cF.blocksInOrder.length]? = none := by
        rw [← hl]
        exact List.getElem?_length _
      have f' : VerifiableInference.Desc.First.onAt (P5J.At.N Zp cF)
          (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP P5J.At.links P5J.At.ps[cF.blocksInOrder.length]?
          (((VerifiableInference.Desc.First.openSets P5J.At.links P5J.At.ps
            (VerifiableInference.Desc.First.start P5J.At.links))[cF.blocksInOrder.length]?).getD [])
          (((VerifiableInference.Desc.First.pubSets
            (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more P5J.At.links
            P5J.At.ps)[cF.blocksInOrder.length]?).getD []) (m.st.input.x.pub, s) ProofFile.Honest.FirstThread.noStrs := f
      rw [e0] at f'
      show VerifiableInference.Desc.First.onAt _ _ _ none _ _ _ _
      rw [hl]
      exact f') ⟨hEnd, trivial⟩ hm

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.rc_at_stand
