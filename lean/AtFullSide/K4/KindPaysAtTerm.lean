-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K4/KindPaysAtTerm.lean: CONDITIONAL.

What is here. THE KIND K4 PAYS AT THE RETURN OF THE ONLINE PROVER's MAKER: `k4_kindPays_at_maker`
(Honest/K4/Law/KindPaysAtMaker.lean) at the filling `onlineFilling` (E2E/TheHonestProver.lean), with
the lot's three readers fixed at the term's own: the cells by `id`, the index by `matrixInput`, the
lookup by `k4LookAt`. What the filling's lots are at K4 comes of `k4_lot_at_widerFill_through`
(Honest/K4/Law/LotThrough.lean): the filling is `onlineProverPartsInUse` read through, and K4's lot is
natural in its reader: that is the one equation K4 owes on the crossing; no law on sides read through
is called.

  `k4_sender_found_at_base`   the search of the base prover at K4's place finds K4's sender
  `kindPays_k4_at_return`, `kindPays_k4_at_term`   **the kind K4 pays**, at A.F and at the head's `F0T`
  `k4_sender_at_term`   **not empty**: at each of the twelve groups what a search of the
      first chain finds first at K4's place is K4's sender, at the member that `LaidK4` names
  `k4_members_at_term`   every member of the kind K4 stands at one of the twelve places
  `kindPays_k4_later_at_term`   the two later chains, for want of members

Limits. CONDITIONAL: on the head h and on the maker's return. h: `P5J.head_exists_at_name` has it from
`InScope Z`, `readFiles Z`, `protocolDataWellFormed (asDescriptionFiles Z)` and `At.CondsOwed Z`, the last by `owed_of_live` from
the third. The return: T1's `MakerReturns`, a named proposition; `atPure_returns_term` has it under h
and `protocolDataWellFormed`. Honest/K4/Part.lean is laws.14's own, with no stop at a zero challenge. It says that the book lends K4's row
at the list of one member: nothing on what is played, sent or accepted. The full size alone, the
format's second hash function alone.
No property is claimed.
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.K4.Law.KindPaysAtMaker
import Johnson.Desc.ProofFile.Honest.K4.Law.LotThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K4
open ProofFile ProofFile.Honest ProofFile.Honest.K4
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling matrixInput tableCoins)
open OnBytes.Maker (WholeD)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Chain Block KindName)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open AtPublicFiles.AtFiles (FullSizeMatrix)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- K4's lot among the lots of the online filling, at the term's readers, and no other lot with a
half of the kind K4. -/
theorem k4_lot_at_online (Z : VerifierAndGoals.PublicFiles) (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    (∃ M ∈ (onlineFilling Z).lots, M.halves Zq G =
      (k4HLot id (matrixInput.weights Zq ∘ id) (fun _ _ => k4LookAt)).halves Zq G) ∧
    ∀ M' ∈ (onlineFilling Z).lots, (∀ y ∈ M'.halves Zq G, y.place.kind ≠ .K4) ∨
      M'.halves Zq G = (k4HLot id (matrixInput.weights Zq ∘ id) (fun _ _ => k4LookAt)).halves Zq G :=
  k4_lot_at_widerFill_through matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest Zq G
    (id : FullSizeMatrix → FullSizeMatrix) (tableCoins Z) matrixInput.dummy

/-- CONDITIONAL on h and hA. **The base prover's search at K4's place finds K4's sender**, at the
wider filling at the index of matrices: H₀'s lists, from which the crossing to the term is made. -/
theorem k4_sender_found_at_base (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    {g : ℕ} (hg : g < 12) :
    ∃ x blk, LaidK4 Zp cF (28 * g + 4) (2 * g) g x blk ∧ blk ∈ cF.blocksInOrder ∧
      A.H.first.find? (fun q => q.place == IM.k4Place g) =
        some (k4Half id (matrixInput.weights A.Z) k4Tokens k4LookAt
          (k4PubAt cF (28 * g + 4) x)) := by
  obtain ⟨⟨M, hM, hE⟩, ho⟩ := k4_lot_at_widerFillAtCPUOWM matrixInput OnBytes.secondHashFunction
    OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G
  exact k4_sender_found_at_maker h hA id (matrixInput.weights A.Z) (fun _ _ => k4LookAt) hM hE ho hg

/-- CONDITIONAL on h and hA. **The kind K4 pays at the return of the online prover's maker.** It says
that the book lends K4's row, so that `chainSteps` returns at the list of one member: nothing on what
is played, sent or accepted. The full size alone, the format's second hash function alone. -/
theorem kindPays_k4_at_return (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K4 :=
  k4_kindPays_at_maker h hA id (matrixInput.weights A.Z ∘ id) (fun _ _ => k4LookAt)
    (k4_lot_at_online Z A.Z A.G).2

/-- CONDITIONAL on h and hA. **The kind K4 pays at the term**, at the list of the head's description:
the form in which `ReadyDebts` is asked at `F0T`. That the book lends the row: nothing on what is
played, sent or accepted. The full size alone, the format's second hash function alone. -/
theorem kindPays_k4_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder A.H.first KindName.K4 := by
  have e := kindPays_k4_at_return h hA
  rw [atPure_desc h hA] at e
  exact e

/-- CONDITIONAL on h and hA. **Not empty**: K4's sender, by the member that `LaidK4` names. -/
theorem k4_sender_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) {g : ℕ} (hg : g < 12) :
    ∃ x blk, LaidK4 Zp cF (28 * g + 4) (2 * g) g x blk ∧ blk ∈ cF.blocksInOrder ∧
      A.H.first.find? (fun q => q.place == IM.k4Place g) =
        some (k4Half id (matrixInput.weights A.Z ∘ id) k4Tokens k4LookAt
          (k4PubAt cF (28 * g + 4) x)) := by
  obtain ⟨M, hM, hE⟩ := (k4_lot_at_online Z A.Z A.G).1
  exact k4_sender_found_at_maker h hA id (matrixInput.weights A.Z ∘ id) (fun _ _ => k4LookAt) hM hE
    (k4_lot_at_online Z A.Z A.G).2 hg

/-- CONDITIONAL on h and hA. **Every member of the kind K4 stands at one of the twelve places.** -/
theorem k4_members_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) :
    ∀ b ∈ A.F.first.blocksInOrder, b.place.kind = .K4 → ∃ g, g < 12 ∧ b.place = IM.k4Place g :=
  k4_members_of_kind h hA

/-- CONDITIONAL on h and hA. **The kind K4 pays in the two later chains, for want of members.**
Nothing on what is played, sent or accepted. The full size alone, the format's second hash function alone. -/
theorem kindPays_k4_later_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) :
    KindPays A.B 1 A.F.shared.blocksInOrder A.H.shared KindName.K4 ∧
      KindPays A.B 2 A.F.second.blocksInOrder A.H.second KindName.K4 :=
  k4_kindPays_later h hA

end AtFullSide.K4

#print axioms AtFullSide.K4.k4_sender_found_at_base
#print axioms AtFullSide.K4.kindPays_k4_at_return
#print axioms AtFullSide.K4.kindPays_k4_at_term
#print axioms AtFullSide.K4.k4_sender_at_term
#print axioms AtFullSide.K4.k4_members_at_term
#print axioms AtFullSide.K4.kindPays_k4_later_at_term
