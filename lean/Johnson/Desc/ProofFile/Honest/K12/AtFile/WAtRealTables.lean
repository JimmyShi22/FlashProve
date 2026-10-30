-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WAtRealTables.lean: the five statements at the last chain's proximity test
at the real tables: the first chain's Script's and `tableShared`.

  `five_at_real_tables`   at a return of the maker at `onlineProverPartsInUse`, at `lastAt` over these tables, from
                   the field, the clause `saysAt`, the two equations on `toCommon`, the rounds in front
                   and the two letters under the stand and the step. `taken` is part 4's
                   `takenAtTheRealTables`, `WidthsAt` its `widthsAtW`

Limits.
- NOT IN FRONT OF A LAW OVER COINS. AT THE FILLING, NOT READ THROUGH.
- `testTbl` is a text of a test's tree: the head of K12/ScriptLots.lean binds whoever lays it.
- That a stand is reached is not said; where none is, the five say nothing.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WTable
import AtFullSide.K12.Part4.TakenAtTheRealTables
import AtFullSide.K12.Part4.WidthsAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Chain Place Strs K1.qAt)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (fillAt lastPlaces)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.K12.AtProof (randAt)
open ProofFile.Honest.K1 (LocB firstScriptAt)
open ProofFile.Honest.FirstThread (lettersHead WtF)
open P2Law.ProofPlan (declProofFull)
open AtFullSide.K12 (jobAtFill)
open AtFullSide.K12.Part4 (takenAtTheRealTables)
open ProofFile.Honest.K12.Part4 (widthsAtW)
open ToldDesc (ownAt)
open P5J (TS AtMgA)

variable {W₀ Wt : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The five at the real tables.** -/
theorem five_at_real_tables (h : AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : ℕ → P5J.TS → Option String) (carryX : ℕ → ProofFile.InstPub × P5J.TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : LocB W₀ → Prop) (Rd : ℕ → LocB W₀ → P5J.TS → Prop)
    (Kp : Place → P5J.TS → P5J.TS → Prop) (w : LocB W₀)
    (testOnU testOnOmega : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit) :
    ∃ M, jobAtFill A.Z Np cF I S Op A.G = some M ∧
      ∀ (N : VerifiableInference.Desc.Shared.NumbersS)
        (Mg : LocB W₀ → VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × P5J.TS) Wt)
        (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
        (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × P5J.TS))
        (ends : Coins A.B → LocB W₀ → List Fmt.Drawn → (ProofFile.InstPub × P5J.TS) × Desc.K14.St)
        (wit : Coins A.B → LocB W₀ → List Fmt.Drawn → Wt)
        (r₁ n₀ : ℕ) (toCommon : LocB W₀ → Common W₀ IndexCommitterCoins TableKey)
        (itemL t₁ t₂ : ℕ) (VdL : LocB W₀ → Prop) (RdL : ℕ → LocB W₀ → S₃ → Prop)
        (KpL : Place → S₃ → S₃ → Prop) (wL : LocB W₀)
        (Said : ℕ → Coins A.B → Mid (LocB W₀) Unit → Prop) {Rr : List Fmt.DeclaredRound},
        r₁ = ((P5J.F0T OnBytes.secondHashFunction A.Z Np cF).first.blocksInOrder.flatMap (·.rounds)).length →
        (∀ v, (toCommon v).w₀ = v.w₀) → (∀ v, (toCommon v).rc = v.rc) →
        PL = fillAt (ToldDesc.p14At A.Z) Rr handLast endedLast →
        let T := lastAt (Zp := A.Z) (Np := Np) (cF := cF) A.H N Mg ML PL
          (fun s => OnBytes.Means.InOrder s.st) ends wit r₁ n₀ toCommon
          (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.table
          (tableShared (K1.qAt A.Z Np) (I.weights A.Z) (randAt (K1.qAt A.Z Np)) testOnU testOnOmega
            ())
          (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.fixed
          (fixedShared declProofFull.2.1) M.toRun.toTest () itemL t₁ t₂ VdL RdL KpL wL
        n₀ = T.front →
        FieldAtW (P5J.F0T OnBytes.secondHashFunction A.Z Np cF) T Said 2 →
        (∀ k st m E (c : RowCoins [(firstPart M.toRun.toTest : Part (LocB W₀) (LocB W₀) Unit),
            restPart M.toRun.toTest]),
          ThrS T Said 2 k st m E →
          lendRow A.B (A.B.rowsOf T.chain) (k.look T.chain) M.p.place
            [(firstPart M.toRun.toTest : Part (LocB W₀) (LocB W₀) Unit), restPart M.toRun.toTest] 0 =
              .ok c →
          ∃ ws, SaysLeft M m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1) st ws) →
        (∀ k s m E ds y cols s', ThrS T Said 2 k s m E →
          drawsFit ((ownAt Np).retype : Block S₃ ProofFile.Cl).rounds ds = true →
          T.Stepped ((ownAt Np).retype : Block S₃ ProofFile.Cl) k s m E ds y cols s' →
          RdL 3 y.2.st.input s' ∧ ∀ q, lastPlaces[2]? = some q → KpL q s s') →
        ∀ fl : ℕ → S₃ → List Fmt.Drawn → Option String, FiveAt T Said fl 2 := by
  obtain ⟨M, hM, key⟩ := five_at_filling (Wt := Wt) (W₂ := Common W₀ IndexCommitterCoins TableKey) h I S Op hA
  refine ⟨M, hM, ?_⟩
  intro N Mg ML PL ends wit r₁ n₀ toCommon itemL t₁ t₂ VdL RdL KpL wL Said Rr hr₁ hw hr hPL T hn hF hS
    hnext fl
  subst hr₁
  obtain ⟨M', hM', tk⟩ := takenAtTheRealTables A.H N Mg ML PL (fun s => OnBytes.Means.InOrder s.st) ends
    wit n₀ toCommon M.toRun.toTest itemL t₁ t₂ VdL RdL KpL wL h hA test carryX item n₁ n₂ b₀ Vd Rd Kp
    w testOnU testOnOmega () hw hr
  obtain rfl : M' = M := Option.some.inj (hM'.symm.trans hM)
  have hW := widthsAtW I S Op h hA (I.weights A.Z) (randAt (K1.qAt A.Z Np)) testOnU testOnOmega ()
    ((P5J.F0T OnBytes.secondHashFunction A.Z Np cF).first.blocksInOrder.flatMap (·.rounds)).length toCommon
  exact key N Mg ML PL ends wit _ n₀ toCommon _ _ _ _ () itemL t₁ t₂ VdL RdL KpL wL Said hPL hn hW
    ⟨hF, fun k st m E c u hc => tk Said k st m E c u hc, hS⟩ hnext fl

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.five_at_real_tables
