-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FormsShareAtHead.lean: THE KIND K1's 101 SHARES OF THE
THREADS' ExchangeS AT THE ITEMS "forms l piece run", AT THE 25 READS' MEMBERS, AT ProofFile's
lettersHead: EACH UNDER THE LIBRARY's HEAD AND TWO PREMISES: THE SHARE AT "tie l" AND
ArmBehindTieS. Two theorems; no definition.

THIS LETTER IS FOR THE HONEST RUN's OWN FORMS ALONE: NO STATEMENT ON ANY OTHER PARTY MAY TAKE IT.
NEVER ON SOUNDNESS's ROAD. (A fence. WHY IT BINDS HERE:
the top joins laws that take the thread's invariant, whose clause on the promise stands at L.mgP,
and one that stands at that meaning, WtFwdAtHead.lean; ArmBehindTieS's own payers stand there too.)

AN IMPLICATION: NO MEMBER: no law says that the thread stands in front of that member at any run.

  - exchangeAtS_forms_head   UNDER h (A HYPOTHESIS), l < 25, (j, n) ∈ earlyRuns (subAt l), hArm :
                  ArmBehindTieS …, hTie : ExchangeAtS … (.tie l): ExchangeAtS (lettersHead
                  …).thread Said (K1.noL l false) (.forms l j n). BY another pen's
                  exchangeAtS_forms (Honest/K1/Law/FormsShare.lean), WITH SIX OF ITS EIGHT PREMISES
                  PAID: hF: formsAreLibrarys_head · hsub: links_reads · ho: forms_out_iff
                  (FormsReadsPublic.lean) · hi: formsT_open (FormsOpenFull.lean) · hStep:
                  readsStepS_head (ReadsStepAtHead.lean) · hWt: wtFwdS_head (WtFwdAtHead.lean).
  - forms_owed_head   THESE ARE THE ITEMS "forms" THAT THE THREAD's ROW OWES THERE: at (j, n) ∈
                  earlyRuns (subAt l): Item.forms l j n ∈ ((lettersHead …).thread.row (K1.noL l
                  false)).owes: forms_owed at the letters.

WHO PAYS THE TWO THAT ARE LEFT. hTie: had as a trial, under a fence, by another
pen (TieShare.lean, TiePlanShare.lean): under the record R. ArmBehindTieS: another pen's twins
(Honest/K1/Twin/): not joined. NEITHER IS CALLED HERE.

WHAT IT READS OF A WITNESS OR A SCRIPT: no equation on the Script and no field of it; Q stands in
the thread's letters alone. The witness enters where ExchangeAtS hands the thread's own.

Limits. At an item that stands for no run (at a layers' segment "planes" and "join") both sentences
hold of every witness and the share says nothing (FormsShare.lean's own limit). THE FULL SIZE, THE
FORMAT's EARLIER HASH. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.ReadsStepAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.WtFwdAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.FormsOpenFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item earlyRuns)
open VerifiableInference.Desc.Sound (MsgT uBySort)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE SHARE AT forms l j n, AT lettersHead**: under the head, the share at "tie l" and
ArmBehindTieS. -/
theorem exchangeAtS_forms_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : ℕ} (hl : l < 25) {j : ℕ} {n : String} (hjn : (j, n) ∈ earlyRuns (IM.subAt l))
    (hArm : ArmBehindTieS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said
      ⟨h.𝔇.pubD, h.𝔇.ms, h.𝔇.St, uBySort h.𝔇.uL h.𝔇.uA h.𝔇.uH, h.𝔇.after, h.𝔇.wt, h.𝔇.rw⟩
      h.𝔇.arr (K1.noL l false) l j n)
    (hTie : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (K1.noL l false) (.tie l)) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (K1.noL l false) (.forms l j n) :=
  exchangeAtS_forms (formsAreLibrarys_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (links_reads hl) ((forms_out_iff (IM.subAt l) l j n).2 hjn) (formsT_open hl hjn)
    (readsStepS_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl hjn) hArm
    (fun _ => wtFwdS_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl) hTie

/-- These are items that the thread's row owes at that member. -/
theorem forms_owed_head {l : ℕ} (hl : l < 25) {j : ℕ} {n : String}
    (hjn : (j, n) ∈ earlyRuns (IM.subAt l)) :
    Item.forms l j n ∈
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row (K1.noL l false)).owes :=
  forms_owed hl hjn

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.exchangeAtS_forms_head
#print axioms ProofFile.Honest.K1.forms_owed_head
