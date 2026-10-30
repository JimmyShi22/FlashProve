-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/DigThere.lean: THE FIELD «digThere» OF THE MERGE's CONDITION (Johnson/K11R/LawAtMg.lean): ∃ xd tl, First.Look.digAt (P5J.At.X Zp) 24 = some (xd, tl): FROM SCOPE, AN OPENING's LETTERS AND F.planOk = true ALONE: NO TEST, NO SHEET. (P5J.At.X Zp is Zp.p.X by its definition.)
HOW. First.Look.digAt X i (Johnson/Desc/First/Look/K3CallerTests.lean) is three look-ups in the public parameters: lookAt X i true · tlAt X i · (P.ofPlace … true x).shape. IM.k3_of (Johnson/IMR/K3Seat.lean) at (24, digits := true) says that number 345 of the first chain's flat list is, alone, what the lookups' own maker K3.theStated returns at the digits' address. WHERE THAT MAKER RETURNS, ITS TEXT HAS LOOKED UP placeAt X i digits (:= (lookAt X i digits).map (P.ofPlace …)) AND laidAt X i digits (at digits: (tlAt X i).bind laidDigits): THE FIRST TWO. THE THIRD: F.planOk = true gives the seated sub-protocol's own test on the plan, so the maker's; K3.Law.blockVia's planOk is K3.planOk p laid guests && fitsVia p, and K3.planOk (Johnson/Desc/First/Look/K3Lookup.lean:146-150) is false where p.shape is none.
  OwnParts X a          what the maker has looked up: the link i, «digits», p, laid, and p.shape.isSome.
  via_shape             the third look-up, from blockVia's test on the plan.
  theOwn_parts · theWhole_parts · theStated_parts   through the maker's three layers (K3Own.lean · K3Whole.lean · K3Stated.lean).
  digThere_in_scope     THE FIELD. «digits» is true because the address's piece is 8, which K3.pieceAt gives at digits alone.
LIMITS. At OnBytes.secondHashFunction alone. At link 24 alone (the proof goes at every l < 25 with the piece's number read off IM.k3Ix: not typed). No soundness. Nothing on hiding.
-/
import Johnson.IMR.K3Seat
import Johnson.IMR.FlatScope
import Johnson.Desc.First.Look.K3CallerTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K11Live

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim blocksOk)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt laidAt lookAt tlAt digAt)
open ProofFile (Cl)

/-- What the lookups' maker has looked up where it returns a sub-protocol that passes its test on the
plan. -/
def OwnParts (X : Verify.Public) (a : Place) : Prop :=
  ∃ i digits p laid, a.link = some i ∧ a.piece = VerifiableInference.Desc.K3.pieceAt X i digits ∧
    placeAt X i digits = some p ∧ laidAt X i digits = some laid ∧ p.shape.isSome = true

/-- Where the lookups' sub-protocol passes its test on the plan its parameters fix a shape. -/
theorem via_shape {C : Type} (seat : VerifiableInference.Desc.K3.Seat S C) (piece : ℕ)
    (laid : Array ℕ) (sent : List (ℕ × ℕ)) (p : VerifiableInference.Desc.First.Look.P)
    (h : (VerifiableInference.Desc.K3.Law.blockVia seat piece laid sent p []).planOk = true) :
    p.shape.isSome = true := by
  have h1 : (VerifiableInference.Desc.K3.planOk p laid
      ([] : List (VerifiableInference.Desc.First.Look.Guest S C)) &&
      VerifiableInference.Desc.K3.Law.fitsVia p) = true := h
  rw [Bool.and_eq_true] at h1
  have h2 := h1.1
  unfold VerifiableInference.Desc.K3.planOk at h2
  rw [Bool.and_eq_true] at h2
  have h4 := h2.2
  cases hs : p.shape with
  | none =>
    rw [hs] at h4
    have h3 : false = true := h4
    cases h3
  | some _ => rfl

theorem theOwn_parts (claim : Aff → Claim) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) {b : Block S Claim}
    (h : VerifiableInference.Desc.K3.theOwn claim runs X codes shape a = some b)
    (hp : b.planOk = true) : OwnParts X a := by
  unfold VerifiableInference.Desc.K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · rename_i hpc
      obtain ⟨p, hp1, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, hl1, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have hp' : ((VerifiableInference.Desc.K3.Law.blockVia
          (if digits = true then VerifiableInference.Desc.K3.seatDigits claim
            else VerifiableInference.Desc.K3.seatCalls claim) a.piece laid sent p []).planOk &&
          key) = true := by
        cases runs
        · exact hp
        · exact hp
      rw [Bool.and_eq_true] at hp'
      exact ⟨i, digits, p, laid, hi, by simpa using hpc, hp1, hl1, via_shape _ _ _ _ _ hp'.1⟩

theorem theWhole_parts (claim : Aff → Claim) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) {b : Block S Claim}
    (h : VerifiableInference.Desc.K3.theWhole claim runs X codes shape a = some b)
    (hp : b.planOk = true) : OwnParts X a := by
  unfold VerifiableInference.Desc.K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  refine theOwn_parts claim runs X codes shape a h0 ?_
  revert hp
  cases hf : (a.link.bind fun i => VerifiableInference.Desc.K3.quietAt X i
      (a.piece == VerifiableInference.Desc.K3.pieceAt X i true)) with
  | none => exact fun hp => hp
  | some f =>
    intro hp
    have hp' : (b₀.planOk && (VerifiableInference.Desc.roundlessBlock (b₀.name ++ _) _ _ _ f :
      Block S Claim).planOk) = true := hp
    rw [Bool.and_eq_true] at hp'
    exact hp'.1

theorem theStated_parts (claim : Aff → Claim)
    (readers : ℕ → Option (VerifiableInference.Desc.K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Claim}
    (h : VerifiableInference.Desc.K3.theStated claim readers X codes shape a = some b)
    (hp : b.planOk = true) : OwnParts X a := by
  unfold VerifiableInference.Desc.K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  refine theWhole_parts claim true X codes shape a h0 ?_
  split at h
  · cases h
    exact hp
  · split at h
    · cases h
      exact hp
    · split at h
      · cases h
        exact hp
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact hp

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE DIGITS' LOOKUP's PLACE AND THE SMALLNESS TEST's PUBLIC VALUE AT THE OUTPUT HEAD's LINK ARE
THERE.** -/
theorem digThere_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∃ xd tl, digAt Z.p.X 24 = some (xd, tl) := by
  have hd := O.desc
  subst hd
  obtain ⟨Lk, b, b', e1, e2, e3, hla⟩ := IM.k3_of hS hR O 24 (by decide) true
  have e345 : c.blocksInOrder[345]? = some b := by
    have h := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope hS hR O (Nat.le_refl 24) (IM.k3Ix 24 true)] at h
  have hb : blocksOk c.blocksInOrder = true := by
    cases hb : blocksOk (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
        (ProofFile.startS Z) c).first.blocksInOrder with
    | true => exact hb
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at hOk
  have hbp : b.planOk = true := by
    have h1 := List.all_eq_true.1 hb b (List.mem_of_getElem? e345)
    simp only [Bool.and_eq_true] at h1
    exact h1.1
  rw [IM.alone_planOk hla] at hbp
  rw [O.W] at e3
  obtain ⟨i, digits, p, laid, hi, hpc, hp1, hl1, hsh⟩ := theStated_parts _ _ _ _ _ _ e3 hbp
  obtain rfl : 24 = i := Option.some.inj hi
  have hdg : digits = true := by
    have hpc' : (8 : ℕ) = VerifiableInference.Desc.K3.pieceAt Z.p.X 24 digits := hpc
    unfold VerifiableInference.Desc.K3.pieceAt at hpc'
    cases digits with
    | true => rfl
    | false => split at hpc' <;> simp at hpc'
  subst hdg
  unfold placeAt at hp1
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hp1
  have hl2 : (tlAt Z.p.X 24).bind VerifiableInference.Desc.First.Look.laidDigits = some laid := hl1
  obtain ⟨tl, htl, _⟩ := Option.bind_eq_some_iff.1 hl2
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.1 hsh
  refine ⟨x, { tl with f9 := h }, ?_⟩
  unfold digAt
  rw [hx, htl]
  show ((VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf Z.p.X.P.frame) true
    x).shape.map fun h => (x, { tl with f9 := h })) = _
  rw [hh]
  rfl

end

end K11Live

#print axioms K11Live.theStated_parts
#print axioms K11Live.digThere_in_scope
