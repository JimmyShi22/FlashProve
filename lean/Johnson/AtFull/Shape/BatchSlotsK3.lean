-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchSlotsK3.lean: THE SLOTS OF THE LOOKUPS' RUNS OF CLAIMS IN THE PROOF FILE's
OWN FIRST CHAIN: "objects" AND "guests" AT ALL FIFTY LOOKUPS, "planes" AT THE HEAD's LINK (SlotAt,
BatchTable.lean), under the head at which the library's laws on that chain speak (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean). A joining of laws; nothing is evaluated. The three RunLaws, "keeps the
reply", "leaves the statement" are another house's
(Johnson/Desc/ProofFile/Honest/K3/Shape/ClaimRuns.lean, ClaimPlanes.lean, ClaimPlanesHead.lean,
ClaimKeeps.lean).

  `piece_tells`: a lookup's piece in its link tells whether it is the one on the digits, and whether
    the link is the head's: by the four numbers 2, 7, 3, 8 alone.
  `stated_piece`: where the lot's sub-protocol at an address is there, the address's piece is one of
    its link's two.
  **`k3_two_at`** (l < 25, both lookups): Lk by cF.links[l]?: SlotAt at (IM.k3Ix l digits,
    "objects"): objectsRun (seatOf K3Lot.ofForm digits) · objectsG digits · the Bool that always
    accepts; and at (IM.k3Ix l digits, "guests"): guestsRun [] · guestsG · the same Bool.
  **`k3_planes_head`**: Bs by baseOf's value · Lk by cF.links[24]? · iU3 by the plan · p by
    placeAt Bs.G₀.W 24 false: SlotAt at (2, "planes"): planesRun (seatCalls K3Lot.ofForm) p.lm
    (callerReaders (planesAt iU3)) · planesShG p.lm (headReadersG iU3) · the same Bool.

Limits. "planes" AT THE TWELVE ATTENTION LINKS HAS NO SLOT HERE (it is in BatchCellsAtt.lean:
k3_planes_att). Each of these laws' pre is True: the Bool says nothing. Whether planesShG returns at
the shape that the chain reaches is not shown (its house's own word). UNDER THE HEAD: that it has a
member is shown at two triples of files alone, in a side library. At the earlier hash. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.BatchTable
import Johnson.Desc.ProofFile.Honest.K3.Shape.ClaimKeeps
import Johnson.Desc.First.Look.K3OwnIs
import Johnson.Desc.First.Look.K03States
import Johnson.IMR.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (pieceAt isHead theStated theWhole theOwn seatCalls planesRun)
open VerifiableInference.OnPublicFiles (objectsRun guestsRun seatOf)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open ProofFile.Honest.K3.Shape (objectsLaw guestsLaw planesLawHead objectsG guestsG planesShG
  headReadersG objectsRun_reply guestsRun_reply planesRun_reply objectsRun_st guestsRun_st
  planesRun_st)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

theorem piece_tells (X : Verify.Public) (l : Nat) (digits d : Bool)
    (h : IM.k3Ix l digits + 1 = pieceAt X l d) :
    d = digits ∧ (isHead X l = true ↔ l = 24) := by
  unfold pieceAt at h
  by_cases h24 : l = 24
  · subst h24
    by_cases hH : isHead X 24 = true <;> cases digits <;> cases d <;>
      simp [IM.k3Ix, hH] at h ⊢
  · by_cases hH : isHead X l = true <;> cases digits <;> cases d <;>
      simp [IM.k3Ix, h24, hH] at h ⊢

theorem stated_piece {Cl : Type} {claim : Aff → Cl}
    {readers : Nat → Option (VerifiableInference.Desc.K3.Readers S)} {X : Verify.Public}
    {codes : Codes} {shape : Params.ReqShape} {a : Place} {B : Block S Cl}
    (h : theStated claim readers X codes shape a = some B) :
    ∃ i d, a.link = some i ∧ a.piece = pieceAt X i d := by
  obtain ⟨B₁, h1, -⟩ := VerifiableInference.Desc.K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, h2, -⟩ := VerifiableInference.Desc.K3.theWhole_is claim true X codes shape a B₁ h1
  obtain ⟨i, d, -, -, -, hi, hp, -⟩ :=
    VerifiableInference.Desc.K3.theOwn_is claim true X codes shape a b h2
  exact ⟨i, d, hi, hp⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k3_two_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (digits : Bool) :
    ∃ Lk : Link S ProofFile.Cl, cF.links[l]? = some Lk ∧
      SlotAt Lk.hear (IM.k3Ix l digits, "objects") (objectsRun (seatOf K3Lot.ofForm digits))
        (objectsG digits) (fun _ _ => true) ∧
      SlotAt Lk.hear (IM.k3Ix l digits, "guests")
        (guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest S Claim)))
        guestsG (fun _ _ => true) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, b', eL, eb, hst, hla⟩ := IM.k3_of h.scope h.reads O l hl digits
  have hs : Lk.hear[IM.k3Ix l digits]? = some (IM.seatedAs ProofFile.sameReply b' b.name
      (IM.k3Place l digits)) := eb.trans (congrArg some hla)
  obtain ⟨i, d, hi, hp⟩ := stated_piece hst
  obtain rfl : l = i := Option.some.inj hi
  obtain ⟨rfl, -⟩ := piece_tells Bs.G₀.W l digits d hp
  obtain ⟨tail, ht⟩ := VerifiableInference.OnPublicFiles.theStated_twoAt K3Lot.ofForm _ _ _ _ _ b' hst l d
    hi hp
  refine ⟨Lk, eL, ⟨
    { lot := b', name := b.name, place := IM.k3Place l d, seated := hs
      bare := objectsRun (seatOf K3Lot.ofForm d)
      states := by rw [ht]; rfl
      law := objectsLaw d
      keeps := fun n s s' cs hr => objectsRun_reply d n s (cs, s') hr
      still := fun n s s' cs hr => objectsRun_st d n s (cs, s') hr }, rfl, rfl,
    k11B _ rfl, rfl⟩, ⟨
    { lot := b', name := b.name, place := IM.k3Place l d, seated := hs
      bare := guestsRun []
      states := by rw [ht]; rfl
      law := guestsLaw
      keeps := fun n s s' cs hr => guestsRun_reply n s (cs, s') hr
      still := fun n s s' cs hr => guestsRun_st n s (cs, s') hr }, rfl, rfl,
    k11B _ rfl, rfl⟩⟩

theorem k3_planes_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl) (iU3 : Nat)
        (p : VerifiableInference.Desc.First.Look.P),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ cF.links[24]? = some Lk ∧
      Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W 24 false = some p ∧
      SlotAt Lk.hear (2, "planes")
        (planesRun (seatCalls K3Lot.ofForm) p.lm (callerReaders (planesAt iU3)))
        (planesShG p.lm (headReadersG iU3)) (fun _ _ => true) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Bs₆, Lk₆, iU3, hB₆, -, hU, -⟩ := k6_slots h
  obtain rfl : Bs = Bs₆ := Except.ok.inj (O.made.symm.trans hB₆)
  obtain ⟨Lk, b, b', eL, eb, hst, hla⟩ := IM.k3_of h.scope h.reads O 24 (by omega) false
  have hs : Lk.hear[2]? = some (IM.seatedAs ProofFile.sameReply b' b.name (IM.k3Place 24 false)) :=
    eb.trans (congrArg some hla)
  obtain ⟨i, d, hi, hp⟩ := stated_piece hst
  obtain rfl : 24 = i := Option.some.inj hi
  obtain ⟨rfl, hH⟩ := piece_tells Bs.G₀.W 24 false d hp
  have hr : K3Lot.readersAt Bs.G₀.W 24 = some (callerReaders (planesAt iU3)) := by
    unfold K3Lot.readersAt
    rw [if_pos (hH.2 rfl), hU]
    rfl
  obtain ⟨p, b₀, h1, h2, h3⟩ := VerifiableInference.Desc.K3.theStated_planes K3Lot.ofForm _ _ _ _ _
    b' hst 24 _ hi hp hr
  obtain ⟨tail, ht⟩ := VerifiableInference.OnPublicFiles.theWhole_twoAt K3Lot.ofForm _ _ _ _ b₀ h2 24
    false hi hp
  have hn := (VerifiableInference.Desc.K3.theWhole_names K3Lot.ofForm _ _ _ _ b₀ h2).1
  have htl : tail = [] := by
    rw [ht] at hn
    simpa using hn
  refine ⟨Bs, Lk, iU3, p, O.made, eL, hU, h1,
    { lot := b', name := b.name, place := IM.k3Place 24 false, seated := hs
      bare := planesRun (seatCalls K3Lot.ofForm) p.lm (callerReaders (planesAt iU3))
      states := by rw [h3, ht, htl]; rfl
      law := planesLawHead p.lm iU3
      keeps := fun n s s' cs hr => planesRun_reply p.lm _ n s (cs, s') hr
      still := fun n s s' cs hr => planesRun_st p.lm _ n s (cs, s') hr }, rfl, rfl,
    k11B _ rfl, rfl⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.piece_tells
#print axioms Johnson.AtFull.Shape.stated_piece
#print axioms Johnson.AtFull.Shape.k3_two_at
#print axioms Johnson.AtFull.Shape.k3_planes_head
