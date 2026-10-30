-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the condition at a run, under the head.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/OnAtHead.lean: AT THE REAL JOB (`jobOmegaReal`) AND THE SIMULATORS' JOB (`simulatorJobAtOmega`), UNDER THE HEAD, AT A RUN: the condition `OnOmega` at a called second part behind the guard, from its clause `asks` alone: the door's equation is `door_head_omega`, the clause on the columns is `trees_head_omega`, the rest `onOmega_at_run`.

  `onOmega_at_head`   **the statement**

What is left. The clause `asks`: `ShapeAsksO` and `DataAsks`. On the run: hR, hrun, hc, S, h10. On the filling: hg, hgO, hlaid, hα. On the plan's letters: hb. On the book: hbk, e₂, hf, ho, hst, hmem: evaluated on no real book. Public: T, hk, hk', hrows, hfit.

Limits. A conditional. Of the walk (`runC`). Reads the input and the carried coins: no later law may take it as a hypothesis on a run and speak of the random values as sampled anew. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.AtRun
import Johnson.Desc.ProofFile.Honest.K12.SimO.TreesHead
import Johnson.Desc.ProofFile.Honest.K12.SimO.DoorHead
import Johnson.Desc.ProofFile.Honest.K12.SimO.SlotO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open VerifiableInference.Desc (Block K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12)
open Desc.K14 (St blocks)
open H2K.Pub (sgOf)
open H2K.Member (codesFull)
open Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open H2K.JointK H2K.First
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Common StandsAt ready runC midSharedAtW
  carriedAt storedShown Part Placed Member Weights TableRand carryE Ahead Face)
open ProofFile.Honest.K14 (jobOmega sendingPart liftSend sendPlace)
open ProofFile.Honest.K12.AtProof (fourOf simulatorJobAtOmega jobOmegaReal)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The condition at a run, under the head, from its clause on the verifier's state alone.** -/
theorem onOmega_at_head {W₀ Tr Y : Type} {pO : P12} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (hO : (fourOf Np).O = some pO) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ ProofFile.Honest.IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : ProofFile.Honest.IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ ProofFile.Honest.IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (wt : W₀ → Weights)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit TableKey) (hσ : σ.block.place = pO.place)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ
      (restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)
        (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) :
        Member Empty _ _ _).guarded pre t
      (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages))
    (h10 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 10)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : Placed Empty _ _).needsField)
    (hlaid : σ.block.rounds.zip σ.block.oracles = (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).laid)
    (hgO : (P.shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ (fun w : Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey => wt w.w₀)
          (fun w => ProofFile.Honest.K12.AtProof.randAt (K1.qAt Zp Np) w.rc)) (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit)]⟩)
    (hbk : bookCutsOmega Bk ⟨K1.qAt Zp Np, 0⟩ pO = true)
    (e₂ : Ahead)
    (hf : (carryE Bk ⟨(jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.place, 0 + 1⟩)[
      (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).members.length]? = some e₂)
    (ho : e₂.owner = ⟨(jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.place, 0⟩)
    (hst : e₂.start = ⟨0, 0⟩)
    (hmem : ∀ t, t < (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).members.length →
      ∃ a a', (carryE Bk ⟨(jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.place, 0⟩)[t]? = some a ∧
      (carryE Bk ⟨(jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.place, 0 + 1⟩)[t]? = some a' ∧
      a.owner = a'.owner ∧ a.start = a'.start ∧ a.count = a'.count)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dd : ℕ → Fmt.Drawn)
    (T : FirstTies (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) s next rest Dd
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take
        (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)))
    (hk : s.h ≤ s.k) (hk' : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ (w : Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) (fr : Front Unit) (mem mem' : ℕ → Stretch),
      (∀ t, t < (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).members.length → mem t = mem' t) →
      μOf (sgOf s) ((jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).rows₀ w fr mem) =
        μOf (sgOf s) ((jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).rows₀ w fr mem'))
    (hfit : drawsFit (((H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p).take
        (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)).map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take
        (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)) = true) :
    ∃ (c : ProofFile.Honest.RowCoins
        [(firstPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) :
          Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).needsField,
        (restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) :
          Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).needsField])
      (m : ProofFile.Honest.Mid (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit),
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      ProofFile.Honest.carriedAt Bk k 1 ⟨σ.block.place, 1⟩
        (restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : ProofFile.Honest.Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).needsField = .ok c.2.1.2.2 ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      drawsFit (((H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p).take (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)).map (·.1))
        (m.st.lately (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)) = true ∧
      ((∃ (Dp : H2K.First.Plain) (cc : ℕ → ℕ → List UInt64) (Rw : PlainRows),
          Dp.ts.length = firstListAtOmega.length ∧
          ProofFile.Honest.K12.Own.ShapeAsksO (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m.st.input
            (restFront (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m)
            (carriedCoins (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)
              (ProofFile.Honest.K12.stretches _ c.2.1.2.2))
            (heardIn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m) codesFull Dp ∧
          DataAsks (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m.st.input
            (restFront (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m)
            (carriedCoins (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)
              (ProofFile.Honest.K12.stretches _ c.2.1.2.2))
            (heardIn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m) Dp cc Rw) →
        OnOmega Face.shared (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)
          (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8])
          1 firstListAtOmega
          (restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)
            (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) :
            Member Empty _ _ _).guarded c.2.1.2.2 m
          (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked) ⟨σ.block.place, 1⟩)) := by
  obtain ⟨c, m, hm, hca, hin, hf3, hon⟩ := onOmega_at_run h.laid.planOk _ rfl
    (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) hR σ pre t S hg
    hlaid e₂ hf ho hst hmem s next rest Dd T hk' hrows hfit hrun hc
    (storedShown (P.storedWords w₀ rc) r.run.storedAsked) Face.shared 1 firstListAtOmega codesFull
  refine ⟨c, m, hm, hca, hin, hf3, fun hasks => hon ?_ ?_ hasks⟩
  · obtain ⟨m', hm', he⟩ := door_head_omega b1 b2 b3 b4 b5 b6 b7 b8 hb hα h.laid.planOk hR hrun σ _ pre t _ S h10 hc
      (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) rfl
    obtain rfl : m = m' := Option.some.inj (Except.ok.inj (hm.symm.trans hm'))
    have hkey : (Face.shared : Face Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) TableKey).pub m.st.input = P.key x := by
      rw [hin]
      rfl
    rw [hkey]
    exact he
  · exact trees_head_omega h hO b1 b2 b3 b4 b5 b6 b7 b8 hb _ _ _ _ rfl _ hR σ hσ pre t S h10 hrun hc hg hlaid hgO
      hbk e₂ hf ho hst hmem s next rest Dd T hk hrows _ m _ hm hca

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.onOmega_at_head
