-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/SmallOfTheTrace.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
THE PREMISE hSmall OF `k6_cellsOn_own_of_sym` (Honest/K6/Law/CellsOnOfSym.lean) WHERE THE ONE
INPUT's TRACE, READ BY cells, IS THE LIBRARY's READER BY LABELS AT `theTrace` AT A SERVED INSTANCE;
AND AT THE LETTERS OF `fullIn` (Honest/AtPureFullIn.lean). NEVER "cellsOn is paid". No definition;
three theorems.

  `k6_headMats_small`      h, hG, "served": at that reader every entry of the honest side's reading
                           of the head's matrices is, as a balanced integer, below 129 in absolute
                           value: at every number, row and column
  `k6_small_of_theTrace`   h, hG, hγ: hSmall, to the sign
  `k6_small_at_fullIn`     h, hG, hVd: hSmall at W₀ := Cm.Idx, Tr := Cells, cells := id

By. `headMats_cellOf_in_scope` (Honest/K6/Law/HeadMatsOfTrace.lean): at every number, row and column
the honest side's reading of that reader is the image of list 24 of the trace; the library's
`meetsAll_theTrace` (Johnson/Goal/HonestTrace/FullPlanesInScope.lean), whose field small says that
every entry of the trace is below 129; its `valMinAbs_cast` (Johnson/HonestTrace/Packed.lean);
`k6_seg_at_head` (Honest/K6/Law/GuestsOfTheTrace.lean); `k6_beta_at_fullIn`
(Honest/K6/Law/GuestsAtFullIn.lean).

What it is not.
  * NEVER "cellsOn is paid": the two other premises of `k6_cellsOn_of_sym_and_stream` (hSym,
    hStream) stay.
  * hSmall IS NOT PAID AT THE FILLING THAT IS RUN: it goes for hγ, which is two of the four limbs of
    the premise hβ of `k6_guests_of_theTrace`: that stays a premise, owed at the filling that is
    run.
  * AT THE LETTERS OF fullIn hγ HOLDS BY CONSTRUCTION, AT LETTERS THAT NO PROGRAM RUNS.
  * It speaks only of states at which the thread stands.
  * It names the input's trace.
  * h: the full size and the format's second hash function alone.
  * Modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.GuestsAtFullIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open Inst.Model (ppref Instance)
open OnBytes.Model.Verify (borderOf)
open OnBytes.HonestTrace (theTrace cellOf ServesAt meetsAll_theTrace valMinAbs_cast
  headMats_cellOf_in_scope)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.X)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS fullIn)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (headMats headWhereOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}

/-- CONDITIONAL: h; hG; "served". ON THE TRACE's CELLS. At the library's reader by labels at
theTrace every entry of the honest side's reading of the head's matrices is, as a balanced integer,
below 129 in absolute value: at every number, row and column. -/
theorem k6_headMats_small (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {i : Cm.Idx} {xI : Instance ppref}
    (Sv : ServesAt (At.X Zp) i xI) (a rr c : ℕ) :
    |(ZMod.valMinAbs (headMats (headWhereOf Zp G)
      ⟨cellOf (At.X Zp) (theTrace (At.X Zp) i xI)⟩ a rr c) : Int)| < 129 := by
  have eW : G.W = (At.X Zp) := ground_of_blank hG
  have M := meetsAll_theTrace h.scope h.reads h.pubOne Sv
  have hs : |theTrace (At.X Zp) i xI 24 a rr c| < 129 := M.small 24 a rr c
  rw [headMats_cellOf_in_scope h.scope h.reads h.pubOne M (headWhereOf Zp G) (k6_seg_at_head h hG)
    (by show G.W.hS = _; rw [eW]) a rr c, valMinAbs_cast (lt_trans hs (by norm_num))]
  exact hs

section General

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- NEVER "cellsOn is paid". CONDITIONAL: h; hG; hγ. **THE PREMISE hSmall OF k6_cellsOn_own_of_sym,
TO THE SIGN**, where the one input's trace, read by cells, is the library's reader by labels at
theTrace at a served instance. hγ is two of the four limbs of hβ (k6_guests_of_theTrace's premise):
IT STAYS A PREMISE, OWED AT THE FILLING THAT IS RUN. -/
theorem k6_small_of_theTrace (cells : Tr → ProofFile.Honest.Cells) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hγ : Vd w → ∃ (i : Cm.Idx) (xI : Instance ppref), ServesAt (At.X Zp) i xI ∧
      cells w.trace = ⟨cellOf (At.X Zp) (theTrace (At.X Zp) i xI)⟩) :
    ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        Said 341 k s m E → ∀ a rr c,
      InFour (At.X Zp).hS (At.X Zp).HLy (borderOf (At.X Zp).y) a rr c → a ≠ (At.X Zp).hS.NHf + 3 →
      |(ZMod.valMinAbs (headMats (headWhereOf Zp G) (cells m.st.input.trace) a rr c) : Int)| <
        2 ^ 18 := by
  intro k s m E hT a rr c _ _
  have hv : m.st.input = w ∧ Vd m.st.input := hT.1.2.2.2.2.2.2
  obtain ⟨ew, hVd⟩ := hv
  rw [ew] at hVd
  obtain ⟨i, xI, Sv, hcell⟩ := hγ hVd
  rw [ew, hcell]
  exact lt_trans (k6_headMats_small h hG Sv a rr c) (by norm_num)

end General

section FullIn

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {Rc Ky X₀ X : Type}
  (H : Prover Cm.Idx Rc ProofFile.Inst Ky ProofFile.Honest.Cells X₀ X)
  (Q : Script Bk (Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells) (CellsM OnBytes.Flat.numsFull)
    P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells → Prop)
  (Rd : Nat → Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells → TS → Prop)
  (Kp : Place → TS → TS → Prop) (w : Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells)
  (Said : Nat → Coins Bk → Mid (Local Cm.Idx Rc ProofFile.Inst ProofFile.Honest.Cells) X → Prop)

/-- NEVER "cellsOn is paid". hγ HOLDS HERE BY CONSTRUCTION, AT ProofFile's fullIn, WHICH NO PROGRAM RUNS.
CONDITIONAL: h; hG; hVd. **hSmall AT THE LETTERS OF fullIn.** -/
theorem k6_small_at_fullIn {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hVd : ∀ v, Vd v → fullIn.trace Zp v.w₀ v.x = some v.trace) :
    ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        Said 341 k s m E → ∀ a rr c,
      InFour (At.X Zp).hS (At.X Zp).HLy (borderOf (At.X Zp).y) a rr c → a ≠ (At.X Zp).hS.NHf + 3 →
      |(ZMod.valMinAbs (headMats (headWhereOf Zp G) (id m.st.input.trace) a rr c) : Int)| <
        2 ^ 18 :=
  k6_small_of_theTrace h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said id hG fun hV => by
    obtain ⟨i, xI, -, Sv, hC, -⟩ := k6_beta_at_fullIn h hG w Vd hVd hV
    exact ⟨i, xI, Sv, hC⟩

end FullIn

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_headMats_small
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_small_of_theTrace
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_small_at_fullIn
