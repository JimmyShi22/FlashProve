-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeFirst.lean: the closing of a segment (K10): the first of the three premises that the
exchange at a closing still takes (`ThreeLeft.made`, Pay/Five.lean): at the coins that the book gives the part, the job's
rows are made and pass the public test. Here it is had from ONE named premise, on the reads alone.

  `ReadsReady`          the named premise: each own message of the segments up to the closing's that the filling of the reads
                      serves is ready at the list of challenges heard
  **`made_of_readsReady`**   at the head's thread, at a stand in front of a closing, at the filling `widerRows` at the reference
                      sizes and the opening's ground: the rows are made and fit, from `ReadsLight` at the input's instance and
                      `ReadsReady`
  **`made_first`**       the field `made` of `ThreeLeftFirst` at the reference sizes, at each of the 25 closings of the first thread,
                      from `ReadsReady` at its stands

What is paid beneath. That the code switch's public test accepts (Pay/MadeReads.lean, over the law that `ReadsLight` follows
from the start's test on the instance). Of the readiness of the own messages: the switches' own and the opening's
(Pay/MadeOwnAB.lean), the digits' (Pay/MadeOwnStand.lean, Pay/MadeDigitsAt.lean). That the rows then return and fit:
Pay/MadeThread.lean.

Limits. `ReadsReady` is a premise. The reference sizes alone. The head and the return of `onlineProverFromPublicFiles` are premises. Where the thread's
invariant holds at no stand of a border the field holds there for nothing.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.Five
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeThread
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeReads
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnABFit
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnStand
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeDigitsAt
import Johnson.Desc.ProofFile.Honest.AtBaseGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (recOf)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open OnBytes.HonestTrace.U3 (u3RowsOf)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (mineReads)
open ProofFile.Honest.K2.Law (ReadsLight)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **The named premise**: each own message of the segments up to the closing's that the filling of the reads serves is
ready at the list of challenges heard. A definition, meant as a premise. -/
def ReadsReady (Zp : ProofFile.Pub) (G : ProofFile.Ground) (Qc : Par) (x : ProofFile.Inst) (heard : List Fmt.Drawn) : Prop :=
  ∀ a, OwnAddr (addrsAt Zp G) (lotSegs Zp G Qc) a → mineReads Zp G a = true → (u3RowsOf Zp G x).readyAt heard a = true

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. The option turns off one early look at a notation's text, which has no case for a
-- field access; it loosens nothing in what Lean checks of a theorem.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **At a stand in front of a closing the job's rows are made and fit**, from the two premises on the reads. Gr: the
opening's ground, under a name of its own. -/
theorem made_of_readsReady {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {Gr : ProofFile.Ground} (hGr : Gr = Bs.G₀)
    {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m En) {D : BaseData} (Hb : CloseBase Qc (recOf s) D)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (stAt : StAtOf ProofFile.Inst)
    (ca : CsAll (closeCarries (lotJob readers (widerRows Sz.ref Zp Gr) stAt Zp Gr Qc).pub))
    (hReads : ReadsLight Zp Gr m.st.input.x) (h4 : ReadsReady Zp Gr Qc m.st.input.x m.st.heard) :
    ∃ R, (lotJob readers (widerRows Sz.ref Zp Gr) stAt Zp Gr Qc).rows m.st.input m.st.heard ca = .ok R ∧
      rowsFit s.st D.G R = true := by
  subst hGr
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hl : l < 25 := link_lt h (List.getElem?_eq_some_iff.1 hblk).1
  have hQ : Qc.link = l := (IM.k10Par_fields Td.2.1).1.trans (IM.k9Where_fields Td.1).2.1
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, hFit, -, -, -, -, -⟩ := hT'
  have hd : drawsFit (declsTo cF.blocksInOrder (14 * l + IM.nAt l + 5)) m.st.heard = true := hFit
  exact made_of_reads h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w O Td hT Hb readers stAt ca hReads
    (ownHeard_of_two (allFit_at_head h O)
      (digits_at_stand h O hl hQ (fun _ hm => digitsFit_at_head h O hm) hd) h4)

end

/-! ## At the first thread -/

section
variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o Sz.ref O) = .ok A)
  (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

include hA in
/-- **The field `made` at each of the 25 closings of the first thread**, at the reference sizes, from `ReadsReady` at its
stands. -/
theorem made_first (l : Nat) (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied h.firstChain A.Z l p Qc blk)
    (hR : ∀ k s m En, Thr (firstThread h parts w) (14 * l + IM.nAt l + 5) k s m En →
      ReadsReady A.Z A.G Qc m.st.input.x m.st.heard)
    {k : Coins A.B} {s : TS} {m : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit} {En : Env} {ds : _} {y : _} {cols : _}
    {s' : TS}
    (St : StepAt (firstThread h parts w) Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s')
    {D : BaseData} (Hb : CloseBase Qc (recOf s) D)
    (ca : CsAll (closeCarries (lotJob
      (fun v : Local W₀ IndexCommitterCoins Inst Cells => (⟨v.trace, I.weights A.Z v.w₀, v.rc⟩ : Readers)) (widerRows Sz.ref A.Z A.G)
      (stAtZero h.firstChain.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub) A.Z A.G Qc).pub)) :
    ∃ R, (lotJob (fun v : Local W₀ IndexCommitterCoins Inst Cells => (⟨v.trace, I.weights A.Z v.w₀, v.rc⟩ : Readers))
        (widerRows Sz.ref A.Z A.G) (stAtZero h.firstChain.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub) A.Z A.G Qc).rows
          m.st.input m.st.heard ca = .ok R ∧ rowsFit s.st D.G R = true := by
  obtain ⟨Bs, base, Op⟩ := h.head.laid.opened
  have eG : A.G = Bs.G₀ := (base_ground_atPure Op.made hA rfl).symm
  have hT : Thr (firstThread h parts w) (14 * l + IM.nAt l + 5) k s m En := St.thr.1
  have hReads : ReadsLight A.Z A.G m.st.input.x := by
    rw [eG]
    exact reads_at_first_stand h parts w Op hT
  exact made_of_readsReady h.head A.H parts.script _ _ _ _ _ _ _ _ _ w Op eG Td hT Hb _ _ ca hReads (hR k s m En hT)

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.ReadsReady
#print axioms ProofFile.Honest.K10.made_of_readsReady
#print axioms ProofFile.Honest.K10.made_first
