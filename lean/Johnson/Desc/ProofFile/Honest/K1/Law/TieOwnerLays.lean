-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieOwnerLays.lean: OwnerHolds (TieMatOwners.lean) FROM THE FORM LaysFilling (Honest/K5/Law/LaysFilling.lean) AT THE
OWNER's SEGMENT: one law for K1's opening and for every switch. That the Script lays the filling is LaysFilling's to say.

  ownerHolds_of_lays   the statement, at the plan's number of (l₀, a.message)


NO PROPERTY IS CLAIMED.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieMatOwners
import Johnson.Desc.ProofFile.Honest.K1.Law.FirstIsPacked
import Johnson.Desc.ProofFile.Honest.K1.Law.CellIsVal
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysFilling
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.HonestTrace (Sz packedCells)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

/-- **OwnerHolds, from the form at the owner's segment.** hV: what is valid meets the form's letter.
hrd: the form's reader is K1's. -/
theorem ownerHolds_of_lays {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x} {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {test : Nat → TS → Option String} {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
    {item n₁ n₂ b₀ : Nat} {Vd Vf : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop} {Kp : Place → TS → TS → Prop}
    {w : Local W₀ Rc ProofFile.Inst Tr} {N : ℕ} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat : MsgAddr → Option (ℕ × ℕ)} {heard : MsgAddr → ℕ} {l₀ ν₀ : ℕ}
    (Lf : K5.LaysFilling h Q Vf N rd seat heard l₀)
    {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} (hrd : ∀ v, (wit v).R = rd v)
    (hV : ∀ v, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).valid v → Vf v)
    {nm : String} {a : OnBytes.Params.ReqArray}
    (hA : VerifiableInference.Desc.arrayOf h.𝔇.sent.layout l₀ nm = some a)
    (hnm : nm = a.name) (hmu : labelNo a.name = some ν₀)
    (hz : (cellsVals Sz.ref).size l₀ a.name = some (Sz.ref.packedShape l₀ ν₀)) :
    OwnerHolds (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) wit Sz.ref
      (P5J.At.num Zp l₀ a.message) N l₀ ν₀ a := by
  subst hnm
  intro k v hd hv hN i c rp hrp hc hi
  obtain ⟨hd', e⟩ := K5.msg_of_lays Lf hA hrp hz hi hc k (hV v hv) hN
  show Q.msg _ k v (hd.take (Q.fixedMsg _)) false rp.1 rp.2 = _
  rw [e, cells_val Sz.ref (rd v) hd' l₀ hmu i c, hrd]
  exact (dataE_asE (.inl _)).symm

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.ownerHolds_of_lays
