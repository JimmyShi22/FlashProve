-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/TieAtBase.lean: K1's SHARE AT THE ITEM "tie l", AT THE BASE PROVER: exchangeAtS_tie_served
(K1/Law/TieShareServed.lean) AT lettersHead AT A RETURN OF THE MAKER AT onlineProverPartsInUse, THE INDEX A LETTER.

  hTr_at_base            hTr of that law, at the filling's own trace
  mg_tie_at_head         hM: by unfolding: mgAll_tie, and MgData.A1 is cellsAt at the head's own data
  exchangeAtS_tie_base   the law at the term's letters

IT PAYS NOTHING ALONE: hTr, hM, hMA, O, Mk, N are paid inside; the binder hI (on I), hV (on Vd) and the three families hSt, hF1, hF2 stand
as premises. The terms of exchangeAtS_tie_served ride: hTr and hMA are of completeness's kind,
NOT IN FRONT OF A LAW OVER COINS.
NO PROPERTY IS CLAIMED.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieShareServed
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.OpenHonest
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput
import Johnson.Goal.HonestTrace.FullPlanesInScope
import Johnson.Goal.HonestTrace.PlanMarksInScope
import Johnson.Goal.HonestTrace.FromCellsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt)
open OnBytes.HonestTrace (Sz PartsFit PlanMarks ServesAt MeetsAll theTrace)
open ProofFile.Honest.FirstThread (Letters lettersHead WtF Script)
open P5J (AtMgA TS)

variable {W₀ : Type}

/-- K1's reader of a place's input at the base prover: what the filling's field readers lays. -/
def witBT (I : WiderIn W₀) (Zq : ProofFile.Pub) : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → PlaceIn ProofFile.Inst :=
  fun v => ⟨v.x, ⟨v.trace, I.weights Zq v.w₀, v.rc⟩⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- hTr at the base prover. From the filling's text: atPure_trace, then hI. hI: A BINDER, on the terms of
TieDebtsAtServed.lean's head: i and x are fixed only up to what cellOf reads; at matrixInput it is paid by
fullIn_trace_some. NOT IN FRONT OF A LAW OVER COINS. -/
theorem hTr_at_base
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (hI : ∀ u ξ C, I.trace A.Z u ξ = some C → ∃ i x,
      C.cell = OnBytes.HonestTrace.cellOf (P5J.At.X A.Z) (theTrace (P5J.At.X A.Z) i x) ∧
        ServesAt (P5J.At.X A.Z) i x) {Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop}
    {w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells} (hV : Vd w → ReadyInput A.F A.H w) :
    ∀ v, (v = w ∧ Vd v) → ∃ i ξ,
      (witBT I A.Z v).R.cells.cell = OnBytes.HonestTrace.cellOf (P5J.At.X A.Z) (theTrace (P5J.At.X A.Z) i ξ) ∧
        ServesAt (P5J.At.X A.Z) i ξ := by
  rintro v ⟨rfl, hd⟩
  have ht := (hV hd).2.2
  rw [atPure_trace hA] at ht
  exact hI _ _ _ ht

/-- hM at lettersHead: the tie's table is the library's one accessor at the head's own data. -/
theorem mg_tie_at_head (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop) (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w v : Local W₀ IndexCommitterCoins ProofFile.Inst Cells) :
    ((lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).Mg v).tie =
      First.K8.tieK8Rec (cellsAt (P5J.At.cs A.Z) (P5J.At.arr A.Z) (P5J.At.ms A.Z Z.lay) (P5J.At.N A.Z cF)) :=
  rfl

/-- **K1's share at the item tie l, at the base prover.** hI: on the letter I. hV: on Vd. Idle at
Vd := fun _ => False: valid holds of nothing. Three families are handed on: hSt, the state; hF1, the
matrices; hF2, the reads. The binders' terms ride: hTr and hMA are of completeness's kind,
NOT IN FRONT OF A LAW OVER COINS. -/
theorem exchangeAtS_tie_base
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop) (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hI : ∀ u ξ C, I.trace A.Z u ξ = some C → ∃ i x,
      C.cell = OnBytes.HonestTrace.cellOf (P5J.At.X A.Z) (theTrace (P5J.At.X A.Z) i x) ∧
        ServesAt (P5J.At.X A.Z) i x) (hV : Vd w → ReadyInput A.F A.H w) {b l nR : ℕ} (hl : l < 25)
    (hSt : TieStateP (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said Sz.ref b l nR)
    (hF1 : TieMatS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said (P5J.At.cs A.Z)
      (P5J.At.arr A.Z) (P5J.At.ms A.Z Z.lay) Sz.ref (witBT I A.Z) b l)
    (hF2 : TieReadsS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said (P5J.At.cs A.Z)
      (P5J.At.arr A.Z) (P5J.At.ms A.Z Z.lay) (witBT I A.Z) (K3.matsOwn (P5J.At.X A.Z) l) b l nR) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b (.tie l) := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have hW : Bs.G₀.W = P5J.At.X A.Z := O.W
  have Mk : PlanMarks (P5J.At.X A.Z) :=
    OnBytes.HonestTrace.planMarks_in_scope h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne
  have N : PartsFit (P5J.At.X A.Z) :=
    OnBytes.HonestTrace.partsFit_in_scope h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne
  have hMA : ∀ i x, ServesAt (P5J.At.X A.Z) i x →
      MeetsAll (P5J.At.X A.Z) i x (theTrace (P5J.At.X A.Z) i x) := fun _ _ T =>
    OnBytes.HonestTrace.meetsAll_theTrace h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne T
  exact exchangeAtS_tie_served (wit := witBT I A.Z) O Mk N hMA
    (hTr_at_base hA hI hV) hl (mg_tie_at_head h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hSt hF1
    (hW ▸ hF2)

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.hTr_at_base
#print axioms ProofFile.Honest.K1.mg_tie_at_head
#print axioms ProofFile.Honest.K1.exchangeAtS_tie_base
