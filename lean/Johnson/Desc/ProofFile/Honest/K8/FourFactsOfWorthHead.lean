-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FourFactsOfWorthHead.lean: THE SMALLNESS TEST, THE HONEST PROVER's
SIDE: `fourFacts_of_worth` (FourFactsOfWorthAtStand.lean beside this file) WITH THREE OF ITS FIVE
NAMED PREMISES STRUCK, EACH BY ONE CALL OF A LEMMA OF THE LIBRARY, AND ITS FREE LETTERS LAID AT THE
HEAD's OWN DATA. An instance of that theorem: narrower in its letters, lighter in its premises. No
definition; no new premise; none of the library's goals.

  **`fourFacts_of_worth_head`**   the library's head · an opening and its test on its plan · l < 25
                   · what `digAt` returns at l ⊢ at every stand of the first chain's thread in
                   front of the segment's batching, at the part a there and at every witness v: the
                   library's two sentences "worth" (`WorthTwo`), `CellOkR` and `MaskOkR` at a
                   give `FourFacts` at the data of the reader `rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v`
THE LETTERS: the seats := fun j => h.𝔇.l3.seat xx.link true j.1 · the arrays' numbers :=
h.𝔇.l3.arr · the reader := `rdC` (Johnson/Desc/First/Link/Law/ClampPin.lean) at the data's codes,
arrays and members · the witness's cells and tokens: the head's own types.
THE THREE CALLS: the test on the mask row's seat: `P5J.AtMgA.left_maskPub`
(Johnson/P5J/K09LeftPub.lean) · "the caller's reading of the witness's messages is the reader's", at
the read cells and at the mask row: `P5J.AtMgA.left_oneCells_head`, `left_oneMask_head`
(Johnson/P5J/K09LeftOnesHead.lean), with `P5J.look_of_dig`.
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
NO TACTIC THAT SEARCHES: a term.
Limits. AN IMPLICATION. `WorthTwo`, `CellOkR` AND `MaskOkR` STAY PREMISES: the library has the
last two at the states of the verifier's side's frame (`P5J.AtMgA.left_cells_at`,
`AtMgA.left_mask`), not at a stand. NO MEMBER: that a stand is there, or that the three hold
together at one, is not said. THE LIBRARY's HEAD IS A PREMISE. The full size and the format's
second hash function alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.FourFactsOfWorthAtStand
import Johnson.P5J.K09LeftPub
import Johnson.P5J.K09LeftOnesHead

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

/-- **AT THE HEAD's OWN DATA: TWO PREMISES ON THE PART, AND THE TWO SENTENCES "WORTH".** -/
theorem fourFacts_of_worth_head {β : Type}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    {xx : First.Look.Place} {tlD : HTailF2}
    (hd : Look.digAt (P5J.At.X Zp) l = some (xx, tlD)) (own : List (ℕ × ℕ)) (ψ : S → β) :
    ∀ κ s m En ds y cols s' x' z G₁,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps l) κ s m En ds y cols s' x' z G₁ →
      ∀ a (v : Wit (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT),
        Desc.K9.atS.get? s = some a →
        LinkJoin.WorthTwo S.fork? LinkJoin.heardDig xx tlD h.𝔇.sent h.𝔇.l3.rad
          (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr s v →
        CellOkR xx tlD h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1) own a →
        MaskOkR xx h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1) own a →
        FourFacts tlD LinkJoin.pi8 (fixed9 (phiAll tlD ψ) s)
          (dataQ own a (rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) :=
  fun κ s m En ds y cols s' x' z G₁ hst a v ha hW hC hM =>
    fourFacts_of_worth h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hOk hl e3 hd
      (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr own
      (fun v => rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v) (h.left_maskPub hl hd) ψ
      κ s m En ds y cols s' x' z G₁ hst a v ha hW
      (h.left_oneCells_head hl (P5J.look_of_dig hd) tlD v)
      (h.left_oneMask_head hl (P5J.look_of_dig hd) v) hC hM

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.fourFacts_of_worth_head
