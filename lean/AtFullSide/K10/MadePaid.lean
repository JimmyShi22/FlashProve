-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/MadePaid.lean: the closing of a segment (K10): the first of the three premises that the exchange at a closing
takes (`ThreeLeft.made`, Johnson/Desc/ProofFile/Honest/K10/Pay/Five.lean) is paid at the first thread: at the coins that the
book gives the part, the job's rows are made and pass the public test.

  `layersVec_at_stand`  under the head, at the head's thread, at a stand in front of the closing of segment l: the makers of the
                      layers' vectors of reads return at the challenges heard in front of their sendings (`LayersVec`,
                      AtFullSide/K10/VecJoin.lean), by `vec_lay_later` (AtFullSide/K1/VecAtLater.lean)
  **`made_first_paid`**   the field `made` of `ThreeLeftFirst` at the reference sizes at each of the 25 closings of the first
                      thread: premises: the return of `onlineProverFromPublicFiles` at the filling, the head at it, and `Tied`

Limits. The reference sizes alone. The head and the return of `onlineProverFromPublicFiles` are premises. Where the thread's invariant holds at no
stand of a border the field holds there for nothing. The full size and the older hash alone.
-/
import AtFullSide.K10.VecJoin
import AtFullSide.K1.VecAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (recOf)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open OnBytes.Model (Head.Covered)
open OnBytes.HonestTrace (Sz)
open OnBytes.HonestTrace.U3 (covOf)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. The option turns off one early look at a notation's text, which has no case for a
-- field access; it loosens nothing in what Lean checks of a theorem.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **At a stand in front of a closing the makers of the layers' vectors of reads return.** -/
theorem layersVec_at_stand {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : Nat}
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m E) (cov : Head.Covered) :
    LayersVec Zp G cov m.st.heard l := by
  intro a st g hst hseg hg hle V hV
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, -, -, hM, -, -⟩ := hT'
  have hB : 14 * (2 * g) + 4 < 14 * l + IM.nAt l + 5 := by
    unfold IM.nAt
    split <;> omega
  exact ProofFile.Honest.K1.vec_lay_later h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg hG hst hseg hB hM cov V hV

end

section
variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o Sz.ref O) = .ok A)
  (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

include hA in
/-- **The field `made` at each of the 25 closings of the first thread, paid**, at the reference sizes. -/
theorem made_first_paid (l : Nat) (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied h.firstChain A.Z l p Qc blk)
    {k : Coins A.B} {s : TS} {m : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit} {En : Env} {ds : _} {y : _} {cols : _}
    {s' : TS}
    (St : StepAt (firstThread h parts w) Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s')
    {D : BaseData} (Hb : CloseBase Qc (recOf s) D)
    (ca : CsAll (closeCarries (lotJob
      (fun v : Local W₀ IndexCommitterCoins Inst Cells => (⟨v.trace, I.weights A.Z v.w₀, v.rc⟩ : Readers)) (widerRows Sz.ref A.Z A.G)
      (stAtZero h.firstChain.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub) A.Z A.G Qc).pub)) :
    ∃ R, (lotJob (fun v : Local W₀ IndexCommitterCoins Inst Cells => (⟨v.trace, I.weights A.Z v.w₀, v.rc⟩ : Readers))
        (widerRows Sz.ref A.Z A.G) (stAtZero h.firstChain.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub) A.Z A.G Qc).rows
          m.st.input m.st.heard ca = .ok R ∧ rowsFit s.st D.G R = true :=
  made_first_of_layers I o O hA h parts w l Said Td
    (fun _ _ _ _ hT => layersVec_at_stand h.head A.H parts.script _ _ _ _ _ _ _ _ _ w (atPure_ok hA).2.1 hT _) St Hb ca

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.layersVec_at_stand
#print axioms ProofFile.Honest.K10.made_first_paid
