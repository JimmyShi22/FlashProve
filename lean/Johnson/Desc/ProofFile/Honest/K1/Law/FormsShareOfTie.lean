-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FormsShareOfTie.lean: THE KIND K1's 101 SHARES OF THE THREADS'
ExchangeS AT THE ITEMS "forms l piece run", AT THE 25 READS' MEMBERS, AT ProofFile's lettersHead: EACH
UNDER THE LIBRARY's HEAD, hSaid AND ONE PREMISE: THE SHARE AT "tie l". One theorem; no definition.

THIS LETTER IS FOR THE HONEST RUN's OWN FORMS ALONE: NO STATEMENT ON ANY OTHER PARTY MAY TAKE IT.
NEVER ON SOUNDNESS's ROAD. (A fence. WHY IT BINDS HERE:
it joins two fenced laws: exchangeAtS_forms_head and another pen's armBehindTieS_head, which stands
over laws at the meaning "honest".)

AN IMPLICATION: NO MEMBER: no law says that the thread stands in front of that member at any run.
NO FILLING IS NAMED: the prover H and the Script Q are free letters. WHERE IT WOULD BE SPENT ON
NOTHING [argued; no Lean]: at H := the prover that onlineProverFromPublicFiles returns at
ProofFile's filling widerFillAt, AND at a family Said that gives PlayedTo: there the pair in front of the
arrow is argued to hold of nothing from number 13 on (no side stands at the first closing): so at
l ≥ 1 (K1.noL 1 false = 19). AT A FAMILY THAT GIVES SaidOk ALONE, WHICH IS ALL THAT hSaid ASKS, THAT
ARGUMENT DOES NOT RUN: it is not shown that the pair is empty there, nor that it is inhabited.

  - exchangeAtS_forms_of_tie   UNDER h (A HYPOTHESIS), at every family Said that gives ProofFile's SaidOk
                  (hSaid), l < 25, (j, n) ∈ earlyRuns (subAt l), hTie : ExchangeAtS … (.tie l):
                  ExchangeAtS (lettersHead …).thread Said (K1.noL l false) (.forms l j n). BY
                  exchangeAtS_forms_head (FormsShareAtHead.lean) WITH ITS PREMISE hArm PAID BY
                  ANOTHER PEN's armBehindTieS_head (ArmBehindTieAtHead.lean), whose premise hrun is
                  formsT_in_rowQ (ReadsStepAtHead.lean). That law's five idle letters are handed
                  empty values here: no clause of its end names them.

WHO PAYS THE ONE THAT IS LEFT. hTie: had as a trial, under a fence, by another
pen (TieShare.lean, TiePlanShare.lean): under the record R; it names the input's trace. NOT CALLED
HERE. With it paid the share goes by name, as text, first.

Limits. INSIDE ArmBehindTieS THE TIE AT THE THREAD's OWN WITNESS IS A PREMISE: exchangeAtS_forms
feeds it from hTie. At an item that stands for no run both sentences hold of every witness and the
share says nothing. THE FULL SIZE, THE FORMAT's EARLIER HASH. Nothing on soundness, on completeness
or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormsShareAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.ArmBehindTieAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item earlyRuns)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

/-- **THE SHARE AT forms l j n, AT lettersHead**: under the head, hSaid and the share at "tie l". -/
theorem exchangeAtS_forms_of_tie {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25) {j : ℕ} {n : String}
    (hjn : (j, n) ∈ earlyRuns (IM.subAt l))
    (hTie : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (K1.noL l false) (.tie l)) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (K1.noL l false) (.forms l j n) :=
  exchangeAtS_forms_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl hjn
    (armBehindTieS_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid ⟨0, {}, []⟩ 0 [] [] []
      hl (formsT_in_rowQ hl hjn)) hTie

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.exchangeAtS_forms_of_tie
