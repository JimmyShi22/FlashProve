-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/InsideAtStand.lean: THE PREMISE hin OF Honest/K9/FrontBridge.lean's BRIDGE, PAID AT ALL
25 SEGMENTS: "inside the members' ranges" at the part of a stand's state in front of the batching, at the frame's own
thread at the library's head. One theorem; no prover is in this file; no goal is stated.
  **`insideAt_at_stand`**   l < 25: at every stand of the batching, at every a with `segAt? s = some a`: `InsideAt
      h.𝔇.cs h.𝔇.ms (h.𝔇.N.group l) a`. By: the smallness test's `wrap_and_mark_at_stand`
      (Honest/K8/FourFactsOfWorthTwo.lean: a stand's state is reached by the wrapped blocks and bears no mark) · a part
      is there (`gathered_split`, `draw_iff`; the library's `segAt_of_atS`) · `insideAt_at_wrap` at i = 0
      (Honest/K9/InsideAtWrap.lean)
WHAT IS NOT CLAIMED. That a stand is there: NO MEMBER: where there is none it says nothing. Called by
Honest/K9/FrontLaid.lean alone. Nothing on any property.
GROUND: beneath this file, beside the sealed library, lie 575 files, this one among them: reading copies, all but ours.

-/
import Johnson.Desc.ProofFile.Honest.K9.InsideAtWrap
import Johnson.Desc.ProofFile.Honest.K9.TotalWorthTwo
import Johnson.Desc.ProofFile.Honest.K9.LedgerOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt pi8 SegAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K8 (FrontAtStandN ValuesAtStand k8Share FoldOnce)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **"INSIDE THE MEMBERS' RANGES" AT A STAND, IN FRONT OF THE BATCHING**: at the frame's own thread at the head, at
all 25 segments. -/
theorem insideAt_at_stand {l : ℕ} (hl : l < 25) {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} :
    ∀ κ s m En ds y cols s' x' z G, BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) κ s m En ds y cols s' x' z G →
      ∀ a, Desc.K9.segAt? s = some a → Sound.InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group l) a := by
  intro κ s m En ds y cols s' x' z G St a ha
  obtain ⟨⟨zp, hw⟩, hu⟩ := ProofFile.Honest.K8.wrap_and_mark_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl St
  obtain ⟨t₁, ht, -, -⟩ := gathered_split p _ s x' z St.bat.gathered
  obtain ⟨a', ha', -⟩ := (draw_iff p s x').1 ⟨t₁, ht⟩
  obtain rfl : a' = a := Option.some.inj ((Desc.K9.segAt_of_atS s a' ha').symm.trans ha)
  exact insideAt_at_wrap h hl (i := 0) (by omega) hw hu ha'

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.insideAt_at_stand
