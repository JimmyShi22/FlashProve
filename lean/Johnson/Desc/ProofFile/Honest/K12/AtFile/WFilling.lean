-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFilling.lean: the letters of the last chain's proximity test
at the base prover: the job that the filling `onlineProverPartsInUse` lays, and `LetterAtW` (WAccepted.lean)
at the prover that `onlineProverFromPublicFiles` returns there.

  `job_facts`      of a job that `jobRealW` returns: the seated numbers, the fresh table, three
                   members, the trees' depths, the door
  `rows_heard_real`   its rows read of a front what was heard alone
  `half_at_filling`   the side at the test's place is the job's pair behind the guard, by `find?`
  `letter_at_filling`   `LetterAtW` at the base prover, at every letter of the thread but `taken`

By what. `job_at_filling` (AtFullSide/K12/LettersAtHead.lean); `letter_at_W` (WLetter.lean);
`stages_at_head`; `rows_heard_W` (WTrees.lean).

Limits.
- Under the head and at `onlineProverFromPublicFiles`'s return (hA): `atPure_returns_fillW_at` pays that return at the head.
- AT THE FILLING, NOT READ THROUGH: the base prover's half is `proverSideOfProximityTest` behind the guard.
- Of the thread's letters only what the test's block reads: the table, the counts, the witness, `ends`
  stay free here.
- Nothing on a run. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLetter
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WTrees
import AtFullSide.K12.LettersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.K12.Light (ManyJob doorW nums_head_W)
open ProofFile.Honest.LastThread (lettersLast)
open ToldDesc (ownAt)
open P5J (F0T TS AtMgA)
open AtFullSide.K12 (jobAtFill job_at_filling)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **Of a job that the maker returns.** -/
theorem job_facts {W₀ Rc Xi Tr X : Type} (h : P5J.AtMg o Z D r Zp Np cF)
    (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi) (enter : Fd.S₃ → Except String T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi) (no : Place → ℕ)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) (G : ProofFile.Ground)
    {M : ManyJob (Local W₀ Rc Xi Tr) X}
    (hM : jobRealW S Fd enter pile no readers weights rand Zp G = some M) :
    M.p = (fourOf Np).W ∧ (∃ f, M.fresh = some f) ∧ M.mems.length = 3 ∧
      M.trees.map (·.1) = [13, 22, 22] ∧ M.rec₀ = doorW Fd (·.x) enter placeW idleT12 := by
  unfold jobRealW at hM
  obtain ⟨F, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hM
  obtain rfl : F = fourOf Np :=
    Option.some.inj (hF.symm.trans (ProofFile.Honest.K12.Light.stages_at_head h).1)
  refine ⟨rfl, ⟨_, rfl⟩, rfl, ?_, rfl⟩
  show [ProofFile.Honest.K12.Light.depthOf (fourOf Np).W 0, ProofFile.Honest.K12.Light.depthOf (fourOf Np).W 1,
    ProofFile.Honest.K12.Light.depthOf (fourOf Np).W 2] = [13, 22, 22]
  unfold ProofFile.Honest.K12.Light.depthOf
  rw [nums_head_W h]
  rfl

/-- **The job's rows read the heard alone.** -/
theorem rows_heard_real {W₀ Rc Xi Tr X : Type} (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi)
    (enter : Fd.S₃ → Except String T12) (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi)
    (no : Place → ℕ) (readers : Local W₀ Rc Xi Tr → Readers)
    (weights : Local W₀ Rc Xi Tr → Weights) (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand)
    (G : ProofFile.Ground) {M : ManyJob (Local W₀ Rc Xi Tr) X}
    (hM : jobRealW S Fd enter pile no readers weights rand Zp G = some M) :
    RowsOfHeard M.toRun.toTest := by
  unfold jobRealW at hM
  obtain ⟨F, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hM
  refine rows_heard_W _ _ _ _ _ _ _ _ _ (fun x fr fr' he => ?_) (fun x fr fr' he => ?_)
  · funext k r j
    show (K1.firstFill S G.first).forSend x K1.firstAddr fr.heard k r j =
      (K1.firstFill S G.first).forSend x K1.firstAddr fr'.heard k r j
    rw [he]
  · funext k r j
    show (K13.wDataAt pile Zp G x.x).forSend x.R ⟨_, 0⟩ fr.heard k r j =
      (K13.wDataAt pile Zp G x.x).forSend x.R ⟨_, 0⟩ fr'.heard k r j
    rw [he]

section
variable {x : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
  (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
include h hA

/-- **The side at the test's place.** -/
theorem half_at_filling {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hs : A.H.second =
      [(proverSideOfProximityTest M.toRun.toTest : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) _ Unit).needsField])
    (hp : M.p = (fourOf Np).W) :
    (A.H.second.find? fun g => g.place == ((ownAt Np).retype : Block S₃ ProofFile.Cl).place) =
      some (proverSideOfProximityTest M.toRun.toTest :
        Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit).needsField := by
  have e : ((proverSideOfProximityTest M.toRun.toTest : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
      (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit).needsField.place ==
      ((ownAt Np).retype : Block S₃ ProofFile.Cl).place) = true := by
    show (M.p.place == (ownAt Np).place) = true
    have e' : (fourOf Np).W.place = placeW := p12At_place _ _
    rw [ownAt_place_W, hp, e']
    exact beq_self_eq_true _
  rw [hs]
  simp [List.find?, e]

end

variable {x : VerifiableInference.Desc.First.Look.Place} {W₀ Wt : Type}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
  (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
include h hA

/-- **`LetterAtW` at the base prover.** Every letter but the trees taken over stays free. -/
theorem letter_at_filling : ∃ M, jobAtFill Zp Np cF I S O A.G = some M ∧ M.p = (fourOf Np).W ∧
    (∃ f, M.fresh = some f) ∧ M.mems.length = 3 ∧ M.trees.map (·.1) = [13, 22, 22] ∧
    RowsOfHeard M.toRun.toTest ∧
    ∀ (N : VerifiableInference.Desc.Shared.NumbersS)
      (Mg : Local W₀ IndexCommitterCoins ProofFile.Inst Cells →
        VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt)
      (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
      (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × TS))
      (order : S₃ → Prop)
      (ends : Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn →
        (ProofFile.InstPub × TS) × Desc.K14.St)
      (wit : Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn → Wt)
      (table : Fmt.TreeSource → Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn →
        Place × Table)
      (fixed : Fmt.TreeSource → ℕ) (item n₁ n₂ : ℕ) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
      (Rd : ℕ → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → S₃ → Prop) (Kp : Place → S₃ → S₃ → Prop)
      (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells),
      LetterAtW (F0T OnBytes.secondHashFunction Zp Np cF)
        (lettersLast Zp Np cF A.H N Mg ML PL order takenLast ends wit table fixed item n₁ n₂ Vd Rd
          Kp w).thread 2 M enterOwn leaveOwn ((ownAt Np).retype : Block S₃ ProofFile.Cl) idleT12 := by
  obtain ⟨M, hM, hs⟩ := job_at_filling h I S O hA
  obtain ⟨hp, hf, hl, hd, hr⟩ := job_facts h.toAtMg S (F0T OnBytes.secondHashFunction Zp Np cF) enterOwn O.pile
    (K1.lotNo OnBytes.secondHashFunction Zp) (lettersW I Zp) (fun w => I.weights Zp w.w₀)
    (fun P w => randAt P w.rc) A.G hM
  refine ⟨M, hM, hp, hf, hl, hd, rows_heard_real S (F0T OnBytes.secondHashFunction Zp Np cF) enterOwn O.pile
    (K1.lotNo OnBytes.secondHashFunction Zp) (lettersW I Zp) (fun w => I.weights Zp w.w₀)
    (fun P w => randAt P w.rc) A.G hM, ?_⟩
  intro N Mg ML PL order ends wit table fixed item n₁ n₂ Vd Rd Kp w
  exact letter_at_W Zp Np cF A.H N Mg ML PL order takenLast ends wit table fixed item n₁ n₂ Vd Rd Kp
    w M hp (half_at_filling h I S O hA hs hp) hr rfl

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.job_facts
#print axioms ProofFile.Honest.K12.AtFile.rows_heard_real
#print axioms ProofFile.Honest.K12.AtFile.half_at_filling
#print axioms ProofFile.Honest.K12.AtFile.letter_at_filling
