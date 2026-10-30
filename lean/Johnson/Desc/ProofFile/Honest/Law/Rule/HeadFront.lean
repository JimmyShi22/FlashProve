-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/HeadFront.lean: THE PREMISE "hfront" (of
Honest/K9/TotalExchangeSeat.lean: `exchange_totalB_seat`) AT THE FIRST CHAIN's THREAD AT THE
LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean), AT ONE FILLING OF ITS LETTER Front:
what the table's item of an entry of the gatherer's order says at the laid letters. In that
statement Front is a letter. The three arrows: (i) the item is open in front of the batching
(Law/Rule/OpenForms.lean: `head_forms_open`) · (ii) from the entry to its item
(Honest/Law/NoHouse/EntryItem.lean: `item_of_entry`) · (iii) what the item says at these letters:
the library's own `mgAll_forms` (Johnson/Desc/Sound/MgAll.lean), by unfolding.

`frontAt` THE FILLING: at the entry o of segment m: the library's `formsQA` where the data say that
the run may name what is ahead, else `formsQ`: at the state and the witness's tables `head_hfront`
from "every item that is open in front of segment m's batching holds" to `frontAt` at every entry
of the sort's order `head_hfront_order` the same at a link's own order, where that is the sort's
`head_worths` the two items "worth" at the digits' piece hold there too `frontAt_link` at every
entry but "K8.equations" `frontAt` is `formsQ` at the link's own readers (`readersOfLink`), at the
holes that the head's data lay at the segment: by the seal's `k03_hlink`

Limits. THE FULL SIZE ALONE. The library's head has a member at the name under four premises on the
public files (the seal's `head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of our
files calls it; no member of the head TOGETHER WITH the thread's sentence is shown. SAID, NOT
PROVED, OF `frontAt` (said, not shown here): the Front at which ItemBack is to be proved, at every
entry but one a sort: at "K8.equations" it wants, beside `frontAt`, what the two items "worth" say:
IN WHICH FORM is part 1's and the lookups' to say: `head_worths` hands the two items' own
sentences. The pins and the item's second conjunct are not read here. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.EntryItem
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenForms
import Johnson.P5J.K03ObjTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item ModelPart shift)
open VerifiableInference.Desc.LinkJoin (batchAt sortItems)
open VerifiableInference.Desc.Sound (MsgT formsQ formsQA seatTab)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **What the table's item of the entry o of segment m says at the laid letters.** -/
def frontAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : Nat) (o : Nat × String) (s : TS)
    (v : WtF) : Prop :=
  if h.𝔇.ah o.1 o.2 = true then
    formsQA (h.𝔇.N.sent m) (h.𝔇.N.group m) (h.𝔇.Rd m) o.1 o.2 s (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)
  else formsQ (h.𝔇.Rd m) (h.𝔇.N.group m) o.1 o.2 s (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)

/-- **At every entry but "K8.equations" the filling is `formsQ` at the link's own readers**: the
    form that
the lookups' house asks for, at the holes that the head's data lay at
    the segment. By the
seal's `k03_hlink`. -/
theorem frontAt_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat}
    {Lk : VerifiableInference.Desc.Link TS VerifiableInference.Desc.Claim}
    (hl : cF.links[m]? = some Lk) {o : Nat × String} (ho : o.2 ≠ "K8.equations") (s : TS)
    (v : WtF) :
    frontAt h m o s v ↔
      formsQ (VerifiableInference.Desc.K9.readersOfLink
          (VerifiableInference.Desc.K9.holesAt (P5J.At.X Zp)
            (VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp)) m Lk) Lk)
        (h.𝔇.N.group m) o.1 o.2 s (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) := by
  have ea : h.𝔇.ah o.1 o.2 = false := by
    show (o.2 == "K8.equations") = false
    exact beq_false_of_ne ho
  have eR : h.𝔇.Rd m = VerifiableInference.Desc.K9.readersOfLink
      (VerifiableInference.Desc.K9.holesAt (P5J.At.X Zp)
        (VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp)) m Lk) Lk := P5J.k03_hlink h m Lk hl
  unfold frontAt
  rw [ea, if_neg (by simp), eR]

end

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

theorem head_hfront {m : Nat} (hm : m < 25) {sub : ModelPart} (hs : P5J.At.links[m]? = some sub)
    (wI : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS) (st : Strs) (v : WtF)
    (hall : ∀ j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
        (batchAt P5J.At.links P5J.At.ps m),
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means wI j a st v) :
    ∀ o ∈ sortItems sub, frontAt h m o a.2 v := by
  intro o ho
  obtain ⟨kk, rr, hi, hr⟩ := item_of_entry P5J.At.links m sub hs o ho
  have e := hall _ (head_forms_open h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm hs hi)
  exact e.1 o hr

theorem head_hfront_order {m : Nat} (hm : m < 25) {sub : ModelPart}
    (hs : P5J.At.links[m]? = some sub) {order : List (Nat × String)}
    (hord : ∀ o ∈ order, o ∈ sortItems sub) :
    ∀ wI a st v, (∀ j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
        (batchAt P5J.At.links P5J.At.ps m),
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means wI j a st v) →
      ∀ o ∈ order, frontAt h m o a.2 v :=
  fun wI a st v hall o ho =>
    head_hfront h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm hs wI a st v hall o (hord o ho)

/-- The two items "worth" at the digits' piece hold there too: for whoever fixes what the entry
"K8.equations" wants beside `frontAt`. -/
theorem head_worths {m : Nat} (hm : m < 25) {sub : ModelPart} (hs : P5J.At.links[m]? = some sub)
    (wI : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS) (st : Strs) (v : WtF)
    (hall : ∀ j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
        (batchAt P5J.At.links P5J.At.ps m),
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means wI j a st v) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means wI
        (Item.worth m (7 + shift sub) "planes") a st v ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means wI
        (Item.worth m (7 + shift sub) "keys") a st v :=
  ⟨hall _ (head_forms_open h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm hs (by cases sub <;> simp
      [VerifiableInference.Desc.First.formsOf])),
    hall _ (head_forms_open h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm hs (by cases sub <;> simp
        [VerifiableInference.Desc.First.formsOf]))⟩

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.frontAt_link
#print axioms ProofFile.Honest.FirstThread.head_hfront
#print axioms ProofFile.Honest.FirstThread.head_hfront_order
#print axioms ProofFile.Honest.FirstThread.head_worths
