-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/RowsBareAtHead.lean: THE PREMISE K3Bare OF Johnson/Desc/AtSeats/RowsBareWalk.lean (an accept of
the lookup on the calls at link 24, from a ledger with its sizes, leaves rows that name no entry), PAID BY CALLS,
under the tests on the plan of the chain's sub-protocols (hOk): theStated_calls_yes
(Johnson/Meaning/HeardCalls.lean: where the seated sub-protocol's test on the plan says yes, its accept holds an
accept of the kind's own sub-protocol at the calls' seat, with the same state behind) ·
decide_named (Johnson/Top/H/Keep/K3Named.lean: from a ledger with its sizes what is laid has PadNames) · its
PadNames.noEntry · seatCalls_reads (K3SeatLaw.lean: what is laid is what is read as heard).
The road is that of pad_behind_look (PadAtRch.lean), at link 24. So RowsBareH holds at the
reached states in front of all 25 reads' places. Statements with their proofs: calls.

Main names:
  k3Bare_of           **K3Bare, in scope, from hOk.**
  rowsBareH_reached   **RowsBareH along the reached states in front of the reads' places.**
What is not claimed. hOk. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.AtSeats.RowsBareWalk
import Johnson.Meaning.HeardCalls
import Johnson.Top.H.Keep.K3Named

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Johnson.Desc.First.Walk.Tied (RchAt)
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S Numbers Meaning flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull onQ Frame)
open IM (Open k1Ix)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **K3Bare, in scope.** -/
theorem k3Bare_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true) : K3Bare Bs.G₀.W Z := by
  intro b' s s' rs gs h3 hd hsz
  obtain ⟨F₀, hf, hSz⟩ := hsz
  obtain ⟨Lk, b, b'', e1, e2, h3', hla⟩ := IM.k3_of hS hR O 24 (by omega) false
  obtain rfl : b' = b'' := Option.some.inj (h3.symm.trans h3')
  have iB := IM.hear_at_flat e1 e2
  have hp : b'.planOk = true := by
    rw [← IM.alone_planOk hla]
    exact (hOk b (List.mem_of_getElem? iB)).1
  have hh : K3.isHead Bs.G₀.W 24 = true := by
    show (24 == (if Bs.G₀.W.p4 then 2 else 1) * Bs.G₀.W.NGr) = true
    rw [show (if Bs.G₀.W.p4 then 2 else 1) * Bs.G₀.W.NGr = 24 from headLink_open hS hR O]
    rfl
  have hpc : K3.pieceAt Bs.G₀.W 24 false = 3 := by
    unfold K3.pieceAt
    rw [hh]
    rfl
  have h4 : K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes Z.first.shape
      ⟨1, some 24, K3.pieceAt Bs.G₀.W 24 false, .K3⟩ = some b' := by
    rw [hpc]
    exact h3
  obtain ⟨p, laid, sent, rs', gs', _, hb⟩ := _root_.Meaning.Planes.theStated_calls_yes K3Lot.ofForm
    (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes Z.first.shape 24 h4 hp hd
  obtain ⟨F₁, x, hF₁, hn, rfl, hN⟩ :=
    VerifiableInference.OnPublicFiles.decide_named _ _ _ _ _ _ _ _ _ _ hb
  have eF : F₁ = F₀ := Option.some.inj (hF₁.symm.trans hf)
  have N := hN (eF ▸ hSz)
  have hh2 : ((K3.seatCalls K3Lot.ofForm).put s x.1 x.2).lookHeard? = some x.1 :=
    K3.seatCalls_reads K3Lot.ofForm s x.1 x.2 (by rw [hF₁]; rfl) hn
  intro g' hg' f hfm
  obtain rfl : x.1 = g' := Option.some.inj (hh2.symm.trans hg')
  exact N.noEntry f hfm

/-- **RowsBareH along the reached states in front of the reads' places.** -/
theorem rowsBareH_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true) {W : Type} {Fr : Frame} (N : Numbers)
    (Mg : Meaning ProofFile.InstPub W) :
    ∀ l, l < 25 → ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        (14 * l + k1Ix l false + 2) a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → RowsBareH a.1.2 :=
  rowsBareH_at_reads hS hR O (k3Bare_of hS hR O hOk) N Mg

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k3Bare_of
#print axioms VerifiableInference.Desc.K1.rowsBareH_reached
