-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/LedgerCallers.lean: `LedgerIs` (Law/Rule/TiesFall.lean) AT
THE TWENTY-FOUR BORDERS IN FRONT OF A CALLER's MEMBER (kind K5: twelve; kind K4: twelve), AT THE
FIRST CHAIN's THREAD AT THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean): where the
thread holds in front of the caller's member of a segment, the verifier's ledger's next free slot
is the plan's own number for that segment, off the public record: `K5Data.first?`
(Johnson/Desc/First/Att/Door/PubK5.lean) at an attention segment, `nextOfPlan`
(Johnson/Desc/First/K4NextOf.lean) at a layers' segment.

Why it holds. The table's promise has a public item "callerIn m", whose test says, among other
things, just that; the item is open at that border (`open_callerIn`, Law/Rule/LedgerOpen.lean: by
Lean's kernel on the written lists); and the thread gives every public item that is open
(`thr_pub`, Honest/Thread/FormLaw.lean). After a finding of another author of this project.

  1  `sorts_at`   the segments 2 g + 1 are attention segments and the segments 2 g layers', by
     Lean's kernel on the written list
  2  `head_open`   the item is open at the head's letters
  3  `head_callerIn_att`, `head_callerIn_lay`   what the item's test is there
  4  `seg_fork`, `att_next`, `lay_next`   from the test's yes to the ledger's number
  5  `ledgerIs_k5`, `ledgerIs_k4`   THE STATEMENTS

BY `decide +kernel` (Lean's kernel evaluates a closed, true sentence on the library's own written
list): `sorts_at` alone; its first clause is its own control: it says "no" of "layers'" at the odd
segments.

Limits. THE FULL SIZE ALONE. The library's head has a member at the name under four premises on the
public files (the seal's `head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of our
files calls it; no member of the head TOGETHER WITH the thread's sentence is shown. ν IS THE PLAN's
NUMBER: THAT IT IS THE BOOK's (the number of the member's first scalar in the segment, as the book
of coins counts) IS ANOTHER SENTENCE, ON PUBLIC NUMBERS: not here. Where the public record gives no
such number the statements' premise fails. Nothing shows that the thread holds at any run. This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesFall
import Johnson.Desc.ProofFile.Honest.Law.Rule.LedgerOpen
import Johnson.Desc.First.Att.Door.Law.K5MgIsAll
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (pubSets leavesName pubAll_callerIn_att pubAll_callerIn_lay)
open VerifiableInference.Desc.First.FillK4 (isLay callerInLayB)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Door (moreOver9 callerIn3B)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

/-! ## 1 The segments' sorts -/

theorem sorts_at : ∀ g, g < 12 → isLay P5J.At.links (2 * g + 1) = false ∧
    (P5J.At.links[2 * g + 1]? == some .attention) = true ∧ isLay P5J.At.links (2 * g) = true := by
  decide +kernel

/-! ## 2 The item at the head's letters -/

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

theorem head_open {l : Nat} (hl : l < 24) :
    VerifiableInference.Desc.First.Pub.callerIn l ∈ ((pubSets (lettersHead h H Q test carryX item n₁
        n₂ b₀ Vd Rd Kp w).mgP.more
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps)[14 * l + 4]?).getD [] := by
  have hm : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more = (moreOver9
      {}).strike leavesName := H2K5.Door.hm_all h
  rw [hm]
  exact open_callerIn l hl

theorem head_callerIn_att {g : Nat} (hg : g < 12) (a : ProofFile.InstPub × TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub (.callerIn (2 * g + 1)) a =
      (h.𝔇.pubD.d5.first? (2 * g + 1)).any fun n => callerIn3B n a.2 := by
  have e : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub = (P5J.mgAtAll h).pub :=
      rfl
  rw [e, H2K5.Door.hpubPlus_all h]
  have h2 : h.𝔇.pubD.d5.isAtt (2 * g + 1) = true := (sorts_at g hg).2.1
  exact pubAll_callerIn_att h.𝔇.pubD _ (2 * g + 1) (sorts_at g hg).1 h2 a

theorem head_callerIn_lay {g : Nat} (hg : g < 12) (a : ProofFile.InstPub × TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub (.callerIn (2 * g)) a =
      (h.𝔇.pubD.nextOf (2 * g)).any fun n => callerInLayB n a.2 := by
  have e : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub = (P5J.mgAtAll h).pub :=
      rfl
  rw [e, H2K5.Door.hpubPlus_all h]
  exact pubAll_callerIn_lay _ _ _ (sorts_at g hg).2.2 a

end

/-! ## 3 From the test's yes to the number -/

theorem seg_fork {s : TS} {a : VerifiableInference.Desc.K9.Part} (h : segAt? s = some a) :
    s.fork? = some a.F := by
  unfold segAt? at h
  cases hL : s.link? with
  | none =>
    rw [hL] at h
    exact nomatch h
  | some L =>
    cases hF : s.fork? with
    | none =>
      rw [hL, hF] at h
      exact nomatch h
    | some F =>
      cases ht : s.tl? with
      | none =>
        rw [hL, hF, ht] at h
        exact nomatch h
      | some tl =>
        rw [hL, hF, ht] at h
        have e := Option.some.inj h
        rw [← e]

theorem att_next {n : Nat} {s : TS} {a : VerifiableInference.Desc.K9.Part}
    (hc : callerIn3B n s = true) (ha : segAt? s = some a) : a.F.next = n := by
  have hf := seg_fork ha
  unfold callerIn3B at hc
  unfold VerifiableInference.Desc.First.S.fork? at hf
  split at hc
  · rename_i o ho
    rw [ho] at hf
    have e : o.F = a.F := Option.some.inj hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [← e]
    exact hc.2
  · cases hc

theorem lay_next {n : Nat} {s : TS} {a : VerifiableInference.Desc.K9.Part}
    (hc : callerInLayB n s = true) (ha : segAt? s = some a) : a.F.next = n := by
  have hf := seg_fork ha
  unfold callerInLayB at hc
  unfold VerifiableInference.Desc.First.S.fork? at hf
  split at hc
  · rename_i o ho
    rw [ho] at hf
    have e : o.F = a.F := Option.some.inj hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [← e]
    exact hc.2
  · cases hc

/-! ## 4 The statements -/

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

/-- **In front of the attention caller's member of group g the ledger's next free slot is the plan's
number.** -/
theorem ledgerIs_k5 {g : Nat} (hg : g < 12) {ν : Nat}
    (hν : h.𝔇.pubD.d5.first? (2 * g + 1) = some ν) :
    LedgerIs (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (14 * (2 * g + 1)
        + 4)) segAt?
      (fun a => a.F.next) ν := by
  intro k s μ En hT a ha
  have e := thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT
    (head_open h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (l := 2 * g + 1) (by omega))
  rw [head_callerIn_att h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg, hν] at e
  exact att_next e ha

/-- **The like in front of the feed-forward caller's member of group g.** -/
theorem ledgerIs_k4 {g : Nat} (hg : g < 12) {ν : Nat} (hν : h.𝔇.pubD.nextOf (2 * g) = some ν) :
    LedgerIs (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (14 * (2 * g) +
        4)) segAt?
      (fun a => a.F.next) ν := by
  intro k s μ En hT a ha
  have e := thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT
    (head_open h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (l := 2 * g) (by omega))
  rw [head_callerIn_lay h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg, hν] at e
  exact lay_next e ha

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.sorts_at
#print axioms ProofFile.Honest.FirstThread.head_open
#print axioms ProofFile.Honest.FirstThread.head_callerIn_att
#print axioms ProofFile.Honest.FirstThread.head_callerIn_lay
#print axioms ProofFile.Honest.FirstThread.seg_fork
#print axioms ProofFile.Honest.FirstThread.att_next
#print axioms ProofFile.Honest.FirstThread.lay_next
#print axioms ProofFile.Honest.FirstThread.ledgerIs_k5
#print axioms ProofFile.Honest.FirstThread.ledgerIs_k4
