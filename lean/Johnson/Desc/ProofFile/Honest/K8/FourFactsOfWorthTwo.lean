-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FourFactsOfWorthTwo.lean: THE SMALLNESS TEST, THE HONEST PROVER's
SIDE: AT A STAND OF THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD, IN FRONT OF EACH OF THE 25
BATCHINGS: THE TWO DICTIONARIES `CellOkR` AND `MaskOkR` AT THE STATE's PART; AND SO `FourFacts`
FROM THE LIBRARY's TWO SENTENCES "WORTH" ALONE. Four theorems; no definition; none of the library's
goals.

  `wrap_and_mark_at_stand`   a stand's state is reached by the blocks with the test on words in
                   front, at the batching's cut, and bears no mark
  **`cellOkR_at_stand`**, **`maskOkR_at_stand`**   the head · l < 25 · what `digAt` returns at l ⊢
                   at every stand there, at the part a: the dictionary, at the data's list of what
                   is sent, radii and seats, at own := h.𝔇.N.group l. No witness stands in them
  **`fourFacts_of_worthTwo`**   besides an opening and its test on its plan ⊢ at every stand, part a
                   and witness v: `WorthTwo` gives `FourFacts` at the data of the reader `rdC`:
                   `fourFacts_of_worth_head` (FourFactsOfWorthHead.lean beside this file) at own :=
                   h.𝔇.N.group l, its two premises on the part laid in
HOW. A stand's state is reached by the blocks with the test on words in front (`wrapEnd_at_stand`,
ValuesOfChain.lean, at `chainThread_at_head`); it bears no mark: the thread's form at the head says
just that; then `cellOkR_at_wrap`, `maskOkR_at_wrap` (Johnson/Desc/K8/Honest/CellOkAtWrap.lean,
MaskOkAtWrap.lean).
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
TACTICS THAT SEARCH: omega, at the number of the batching's cut.
Limits. AN IMPLICATION: `WorthTwo` STAYS A PREMISE. NO MEMBER: that a stand is there is not said.
THE LIBRARY's HEAD IS A PREMISE. The full size and the format's second hash function alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.FourFactsOfWorthHead
import Johnson.Desc.K8.Honest.MaskOkAtWrap

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.OnPublicFiles (CellOkR MaskOkR)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.Sound (MsgT dataQ)
open VerifiableInference.Desc.K9L (fixed9)
open VerifiableInference.Desc.PhiAll (phiAll)
open VerifiableInference.Desc.LinkJoin (batchAt rdC)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open ProofFile.Honest.K9 (BatStand)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Desc.Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Lk : Link S Claim} {p : Desc.K9.Where}

/-- A stand's state: reached by the blocks with the test on words in front, at the batching's cut;
and without a mark. -/
theorem wrap_and_mark_at_stand {l : ℕ} (hl : l < 25) {κ s m En ds y cols s' x' z G₁}
    (hst : BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) κ s m En ds y cols s' x' z G₁) :
    (∃ zp, Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp)
      (batchAt P5J.fullLinks P5J.At.ps l) (zp, s)) ∧ s.failed = none := by
  obtain ⟨zp, hz⟩ := wrapEnd_at_stand
    (chainThread_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl) hst
  refine ⟨⟨zp, ?_⟩, Option.isNone_iff_eq_none.1 hst.thr.1.2.2.1.1⟩
  rw [LPFK9.batch_nAt l hl]
  have e : 14 * l + IM.nAt l + 2 = 14 * l + (if l = 24 then 11 else 9) := by
    unfold IM.nAt
    split <;> omega
  rw [e]
  exact hz

/-- **THE DICTIONARY ON THE DIGITS' CELLS AT A STAND.** -/
theorem cellOkR_at_stand {l : ℕ} (hl : l < 25) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : Look.digAt (P5J.At.X Zp) l = some (xx, tlD)) :
    ∀ κ s m En ds y cols s' x' z G₁,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps l) κ s m En ds y cols s' x' z G₁ →
      ∀ a, Desc.K9.atS.get? s = some a →
        CellOkR xx tlD h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1)
          (h.𝔇.N.group l) a := by
  intro κ s m En ds y cols s' x' z G₁ hst a ha
  obtain ⟨⟨zp, hw⟩, hu⟩ := wrap_and_mark_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hst
  exact cellOkR_at_wrap h hl hd hw hu ha

/-- **THE DICTIONARY ON THE MASK ROW AT A STAND.** -/
theorem maskOkR_at_stand {l : ℕ} (hl : l < 25) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : Look.digAt (P5J.At.X Zp) l = some (xx, tlD)) :
    ∀ κ s m En ds y cols s' x' z G₁,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps l) κ s m En ds y cols s' x' z G₁ →
      ∀ a, Desc.K9.atS.get? s = some a →
        MaskOkR xx h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1)
          (h.𝔇.N.group l) a := by
  intro κ s m En ds y cols s' x' z G₁ hst a ha
  obtain ⟨⟨zp, hw⟩, hu⟩ := wrap_and_mark_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hst
  exact maskOkR_at_wrap h hl (P5J.look_of_dig hd) hw hu ha

/-- **FROM THE TWO SENTENCES "WORTH" ALONE.** -/
theorem fourFacts_of_worthTwo {β : Type}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    {xx : First.Look.Place} {tlD : HTailF2}
    (hd : Look.digAt (P5J.At.X Zp) l = some (xx, tlD)) (ψ : S → β) :
    ∀ κ s m En ds y cols s' x' z G₁,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps l) κ s m En ds y cols s' x' z G₁ →
      ∀ a (v : Wit (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT),
        Desc.K9.atS.get? s = some a →
        LinkJoin.WorthTwo S.fork? LinkJoin.heardDig xx tlD h.𝔇.sent h.𝔇.l3.rad
          (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr s v →
        FourFacts tlD LinkJoin.pi8 (fixed9 (phiAll tlD ψ) s)
          (dataQ (h.𝔇.N.group l) a (rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) :=
  fun κ s m En ds y cols s' x' z G₁ hst a v ha hW =>
    fourFacts_of_worth_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hOk hl e3 hd
      (h.𝔇.N.group l) ψ κ s m En ds y cols s' x' z G₁ hst a v ha hW
      (cellOkR_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hd
        κ s m En ds y cols s' x' z G₁ hst a ha)
      (maskOkR_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hd
        κ s m En ds y cols s' x' z G₁ hst a ha)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.wrap_and_mark_at_stand
#print axioms ProofFile.Honest.K8.cellOkR_at_stand
#print axioms ProofFile.Honest.K8.maskOkR_at_stand
#print axioms ProofFile.Honest.K8.fourFacts_of_worthTwo
