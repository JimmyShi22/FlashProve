-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/HeadHrun.lean: IN FRONT OF THE HEAD's BATCHING THE RUN's OWN
READER ANSWERS AT EVERY ENTRY OF THE HEAD's ORDER BUT "K8.equations": FROM THE FIRST CHAIN's THREAD
AT THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean). The library has the sentence
under its own table's condition (`hrun_any_at`, Johnson/LPFE1R/HrunAnyAt.lean); here its proof is
walked again beneath that condition: of the condition it spends (i) a public test at an item that
is tied to an open item, which the thread gives (`thr_pubI`, Honest/Thread/FormLawI.lean), and (ii)
that the state is reached by the members' own steps (`thr_reach`, Honest/Thread/ReachFacts.lean).
Asked for by the authors of the lookups' parts (K3).

  1  `head_formsIn`   the public test "formsIn" at every entry of a segment's order but
     "K8.equations", in front of that segment's batching: the library's `hin_at`
     (Johnson/LPFE1R/HinAtConst.lean), with the thread in the condition's stead
  2  `head_speaks`   where the link's readers answer at a block and a name that is not
     "K8.equations", the run's own reader answers: block and name free: the form that the authors
     of K6's part asked for
  3  `head_hrun`   THE STATEMENT

No theorem of this file goes by `decide +kernel`; it calls the library's own `named_full`, which
does.

Limits. THE FULL SIZE ALONE. The library's head has a member at the name under four premises on the
public files (the seal's `head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of our
files calls it; no member of the head TOGETHER WITH the thread's sentence is shown. AT
"K8.equations" NOTHING IS SAID. This file proves nothing about soundness, completeness, hiding or
any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormLawI
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.First.Att.Door.Law.K5MgIsAll
import Johnson.LPFE1R.HrunAnyAt
import Johnson.IMR.EndFive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Place Link Claim)
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item Pub pubOfItems pubAll_formsIn)
open VerifiableInference.Desc.LinkJoin (batchAt sortItems named_full reader_of_formsIn readers_at24
  tablesLaid_347)
open VerifiableInference.Desc.First.MergeLaw (speaks_of_forms)
open VerifiableInference.Desc.Sound (MsgT mem_runsAt)
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA CellsM TS)

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

/-- **The public test at every entry of the order but "K8.equations".** -/
theorem head_formsIn {m : Nat} (hm : m < 25) {k : Coins Bk} {s : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.fullLinks P5J.At.ps m) k s μ En)
    {e : Nat × String} (he : e ∈ VerifiableInference.Desc.First.orderOf (subAt m))
    (h8 : (e.2 == "K8.equations") = false) :
    K9.formsIn (h.𝔇.Rd m) (h.𝔇.N.group m) e.1 e.2 s = true := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 named_full m (List.mem_range.2 hm)) e he
  rw [h8, Bool.false_or] at h1
  obtain ⟨i, hi, h2⟩ := List.any_eq_true.1 h1
  cases i with
  | forms m' kk r =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h2
    obtain ⟨rfl, h3⟩ := h2
    have er : e ∈ h.𝔇.runs m' kk r :=
      mem_runsAt P5J.fullLinks m' (subAt m') (LPFK9.fullLinks_sub m' hm) kk r e h3
    have hq : Pub.formsIn m' kk r ∈ pubOfItems (P5J.oAt (batchAt P5J.fullLinks P5J.At.ps m')) :=
      List.mem_flatMap.2 ⟨_, hi, List.mem_singleton.2 rfl⟩
    have e1 := thr_pubI (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT hq
    have e0 : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub = (P5J.mgAtAll h).pub
        := rfl
    rw [e0, H2K5.Door.hpubPlus_all h, pubAll_formsIn] at e1
    have e2 := List.all_eq_true.1 e1 e er
    have ea : h.𝔇.pubD.ah e.1 e.2 = false := h8
    rw [ea] at e2
    simpa using e2
  | _ => exact absurd h2 (by simp)

/-- **Where the link's readers answer at a block and a name that is not "K8.equations", the run's
own reader answers**: block and name are free: the form that the authors of K6's part asked for. -/
theorem head_speaks {k : Coins Bk} {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 347 k s μ En)
    (L : Link TS Claim) (j : Nat) {name : String} (h8 : (name == "K8.equations") = false)
    (hR : ((K9.readersOfLink (K9.holesAt (P5J.At.X Zp) 24 24 L) L).forms j name s).isSome = true) :
    (K9.readerOf (K9.statesOfLink L) j name s).isSome = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hr := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (b := 347) (by omega) hT
  have ht := tablesLaid_347 h.scope h.reads O hr
  rw [O.W] at ht
  exact speaks_of_forms (K9.holesAt (P5J.At.X Zp) 24 24 L) L (K9.phAt (P5J.At.X Zp) 24) j
    h8 (by unfold K9.holesAt; rfl) ht hR

/-- **The run's own reader answers.** -/
theorem head_hrun {k : Coins Bk} {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.fullLinks P5J.At.ps 24) k s μ En)
    {L : Link TS Claim} (hlk : h.𝔇.lk 24 = some L) :
    ∀ e ∈ sortItems .head, (e.2 == "K8.equations") = false →
      (K9.readerOf (K9.statesOfLink L) e.1 e.2 s).isSome = true := by
  intro e he h8
  have hs : subAt 24 = .head := by decide
  have hin := head_formsIn h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (m := 24) (by omega) hT (hs ▸
      he) h8
  obtain ⟨R, hR⟩ := reader_of_formsIn _ _ _ _ _ hin
  rw [readers_at24 h 24, K9.readersAt_some _ _ _ _ L hlk] at hR
  have hb : batchAt P5J.fullLinks P5J.At.ps 24 = 347 := by
    rw [LPFK9.batchAt_full 24 (by omega)]
    decide
  rw [hb] at hT
  exact head_speaks h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT L e.1 h8 (by rw [hR]; rfl)

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_formsIn
#print axioms ProofFile.Honest.FirstThread.head_speaks
#print axioms ProofFile.Honest.FirstThread.head_hrun
