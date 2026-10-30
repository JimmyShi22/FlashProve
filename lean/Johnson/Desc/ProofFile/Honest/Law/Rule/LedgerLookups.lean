-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/LedgerLookups.lean: `LedgerIs` (Law/Rule/TiesFall.lean) AT
THE FIFTY BORDERS IN FRONT OF A LOOKUP's MEMBER (kind K3: on the calls 25, on the digits 25), AT
THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean): where
the thread holds in front of the lookup's member, the verifier's ledger's next free slot is the
plan's own number for that lookup: the field "first" of the lookup's place, off the public record
(`placeAt`, Johnson/Desc/First/Look/LookKind.lean).

Why it holds. As Law/Rule/LedgerCallers.lean: the public item is "lookIn l pc" (`lookInC`,
Johnson/Desc/First/Look/K3FillCode.lean; `k3OnIn`, Johnson/Desc/First/Look/K3Borders.lean); where
it is open: Law/Rule/LedgerOpen.lean.

  1  `head_lookIn`   what the item's test is at the head's letters
  2  `lookIn_next`   from the test's yes to the ledger's number
  3  `ledgerIs_lookIn`   the statement, at any border at which the item is open
  4  `ledgerIs_calls`, `ledgerIs_calls_head`, `ledgerIs_digits`, `ledgerIs_digits_head`   at the
     fifty

TWO PREMISES ON THE PUBLIC PARAMETERS STAND IN EACH: which of the segment's two lookups the table's
piece is (`k3SortAt`), and that the public record has the lookup's place (`placeAt`): tests with
code; not shown here.

Limits. THE FULL SIZE ALONE. The library's head has a member at the name under four premises on the
public files (the seal's `head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of our
files calls it; no member of the head TOGETHER WITH the thread's sentence is shown. THE NUMBER IS
THE PLAN's: that it is the book's is another sentence, on public numbers. Nothing shows that the
thread holds at any run. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.LedgerCallers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (pubSets leavesName pubAll_lookIn)
open VerifiableInference.Desc.First.Look (K3Data k3SortAt lookInC placeAt)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Door (moreOver9)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

theorem lookIn_next {d : K3Data} {l : Nat} {dg : Bool} {p : VerifiableInference.Desc.First.Look.P}
    {s : TS} {a : VerifiableInference.Desc.K9.Part} (hp : placeAt d.X l dg = some p)
    (hc : lookInC d l dg s = true) (ha : segAt? s = some a) : a.F.next = p.first := by
  unfold lookInC at hc
  rw [hp] at hc
  simp only [Option.any_some, Bool.and_eq_true] at hc
  have h1 := hc.1
  unfold VerifiableInference.Desc.K3.k3OnIn at h1
  split at h1
  · rw [seg_fork ha] at h1
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h1
    exact h1.2.1.1
  · cases h1

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

theorem head_lookIn {l pc : Nat} {dg : Bool} (hs : k3SortAt h.𝔇.pubD.d3.X l pc = some dg)
    (a : ProofFile.InstPub × TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub (.lookIn l pc) a = lookInC
        h.𝔇.pubD.d3 l dg a.2 := by
  have e : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub = (P5J.mgAtAll h).pub :=
      rfl
  rw [e, H2K5.Door.hpubPlus_all h]
  exact pubAll_lookIn _ _ _ _ _ hs a

/-- **Where "lookIn l pc" is open, the ledger's next free slot is the lookup's first.** -/
theorem ledgerIs_lookIn {b l pc : Nat} {dg : Bool} {p : VerifiableInference.Desc.First.Look.P}
    (hq : VerifiableInference.Desc.First.Pub.lookIn l pc ∈
      (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[b]?.getD [])
    (hs : k3SortAt h.𝔇.pubD.d3.X l pc = some dg) (hp : placeAt h.𝔇.pubD.d3.X l dg = some p) :
    LedgerIs (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b) segAt? (fun a
        => a.F.next) p.first := by
  intro k s μ En hT a ha
  have hm : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more = (moreOver9
      {}).strike leavesName := H2K5.Door.hm_all h
  have hq' : VerifiableInference.Desc.First.Pub.lookIn l pc ∈ ((pubSets (lettersHead h H Q test
      carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps)[b]?).getD [] := by
    rw [hm]
    exact hq
  have e := thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT hq'
  rw [head_lookIn h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hs] at e
  exact lookIn_next hp e ha

theorem ledgerIs_calls {l : Nat} (hl : l < 24) {dg : Bool}
    {p : VerifiableInference.Desc.First.Look.P} (hs : k3SortAt h.𝔇.pubD.d3.X l 2 = some dg)
    (hp : placeAt h.𝔇.pubD.d3.X l dg = some p) :
    LedgerIs (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (14 * l + 3))
        segAt? (fun a => a.F.next) p.first :=
  ledgerIs_lookIn h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (open_lookIn_calls.1 l hl) hs hp

theorem ledgerIs_calls_head {dg : Bool} {p : VerifiableInference.Desc.First.Look.P}
    (hs : k3SortAt h.𝔇.pubD.d3.X 24 3 = some dg) (hp : placeAt h.𝔇.pubD.d3.X 24 dg = some p) :
    LedgerIs (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 340) segAt? (fun a
        => a.F.next) p.first :=
  ledgerIs_lookIn h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w open_lookIn_calls.2 hs hp

theorem ledgerIs_digits {l : Nat} (hl : l < 24) {dg : Bool}
    {p : VerifiableInference.Desc.First.Look.P} (hs : k3SortAt h.𝔇.pubD.d3.X l 7 = some dg)
    (hp : placeAt h.𝔇.pubD.d3.X l dg = some p) :
    LedgerIs (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (14 * l + 8))
        segAt? (fun a => a.F.next) p.first :=
  ledgerIs_lookIn h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (open_lookIn_digits.1 l hl) hs hp

theorem ledgerIs_digits_head {dg : Bool} {p : VerifiableInference.Desc.First.Look.P}
    (hs : k3SortAt h.𝔇.pubD.d3.X 24 8 = some dg) (hp : placeAt h.𝔇.pubD.d3.X 24 dg = some p) :
    LedgerIs (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 345) segAt? (fun a
        => a.F.next) p.first :=
  ledgerIs_lookIn h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w open_lookIn_digits.2 hs hp

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.lookIn_next
#print axioms ProofFile.Honest.FirstThread.head_lookIn
#print axioms ProofFile.Honest.FirstThread.ledgerIs_lookIn
#print axioms ProofFile.Honest.FirstThread.ledgerIs_calls
#print axioms ProofFile.Honest.FirstThread.ledgerIs_calls_head
#print axioms ProofFile.Honest.FirstThread.ledgerIs_digits
#print axioms ProofFile.Honest.FirstThread.ledgerIs_digits_head
