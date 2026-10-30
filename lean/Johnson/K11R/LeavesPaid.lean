-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/K11R/LeavesPaid.lean: THE ONE PREMISE THAT ANOTHER FILE LEFT IN FRONT
OF THE FIELD "leaves" OF THE FROZEN K11Cond (hSz: at every state that is reached at border 340 the
open ledger has its sizes; Johnson/K11R/LeavesAt346.lean) IS PAID BY ONE CALL of
`sized_340` (Johnson/Desc/AtSeats/RowsBareWalk.lean). No new proof: joinings.

Statements and proofs.
Main names:
  sized_at_340: hSz TO THE LETTER, at first tree 0: in the goals' scope, at the maker's opening: at
    every a that is reached at 340 along c.blocksInOrder from the first state, whatever ledger is open at
    a.2 has its sizes.
  leaves_reach_paid · leaves_at346_paid: LeavesAt346.lean's two tops without hSz.
  leaves_at_head: at the tower's head h : AtMg at the second hash function, at h.rch ("reached"
    and a typed public part): ∀ a, h.rch 346 a → a.1.2.failed = none → leavesLenB a.1.2 = true.
    STRONGER than the field and of another shape (one binder; no condition of the table in front).
  **leaves_field**: the field's own sentence at h : AtMgA, Rch := h.toAtMg.rch and the first
    chain's frame: z and a apart, the table's condition onQ in front, "¬ … ≠ none". That this IS
    the frozen field's type is Lean's word in Johnson/K11R/LeavesField.lean, not this file's.
Limits. Laws from accepts: idle where nothing is reached. sized_340 says MORE than hSz asks (a
ledger IS open at 340, with its sizes); hSz asks of whatever ledger is open. At OnBytes.secondHashFunction, in
the goals' scope, at first tree 0. No example. No soundness follows. It holds no coding theory.

-/
import Johnson.K11R.LeavesAt346
import Johnson.Desc.AtSeats.RowsBareWalk
import Johnson.P5J.FourAtMg
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes
open OnBytes.PscRun (Sized)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **hSz, TO THE LETTER.** -/
theorem sized_at_340 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ a, Reach 0 c.blocksInOrder (ProofFile.startS Z) 340 a → ∀ G, a.2.fork? = some G → Sized G := by
  intro a h G hG
  obtain ⟨G', hG', sG⟩ := VerifiableInference.Desc.K1.sized_340 hS hR O a h
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans hG)
  exact sG

/-- The top along "reached", without hSz. -/
theorem leaves_reach_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {a : ProofFile.InstPub × S} (R : Reach 0 c.blocksInOrder (ProofFile.startS Z) 346 a) : leavesLenB a.2 = true :=
  leaves_reach hS hR O hOk (sized_at_340 hS hR O) R

/-- LeavesAt346.lean's second top, without hSz. -/
theorem leaves_at346_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {Fr : Sound.Frame} (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (hsub : ∀ a, Rch 346 a → RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B
      (fun s => s) (ProofFile.startS Z) c) 346 a) :
    ∀ a, Rch 346 a → a.1.2.failed = none → leavesLenB a.1.2 = true :=
  leaves_at346 hS hR O hOk Rch hsub (sized_at_340 hS hR O)

end

end VerifiableInference.Desc.First.MergeLaw

namespace P5J

open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw (leavesLenB leaves_at346_paid)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- At the tower's head, at h.rch: stronger than the field, and of another shape. -/
theorem leaves_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∀ a : (ProofFile.InstPub × S) ×
        (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str,
      h.rch 346 a → a.1.2.failed = none → leavesLenB a.1.2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact leaves_at346_paid h.scope h.reads O h.laid.planOk
    (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h.rch
    (fun _ ha => ha.1)

/-- **THE FIELD's OWN SENTENCE, AT THE CLOSED CONSTANT's HEAD.** -/
theorem leaves_field (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ (z : ProofFile.InstPub)
      (a : S × (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str),
      onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      h.toAtMg.rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → leavesLenB a.1 = true :=
  fun z a _ hr hf => leaves_at_head h.toAtMg ((z, a.1), a.2) hr (not_not.1 hf)

end P5J

#print axioms VerifiableInference.Desc.First.MergeLaw.sized_at_340
#print axioms VerifiableInference.Desc.First.MergeLaw.leaves_reach_paid
#print axioms VerifiableInference.Desc.First.MergeLaw.leaves_at346_paid
#print axioms P5J.leaves_at_head
#print axioms P5J.leaves_field
