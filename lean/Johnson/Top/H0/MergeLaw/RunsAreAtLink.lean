-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RunsAreAtLink.lean: which runs of claims the output head's segment states:
the named premise `RunsAre` (RunsAre.lean), all nine fields, at the link that the IOP as written in
Lean holds, in the goals' scope. Theorems with their proofs.

How. In the first chain as it is made each sub-protocol of a lot stands alone behind a guard on the
reply that was heard (`IM.LaidAlone`, Johnson/IMR/SeatForm.lean), and its runs are the lot's
sub-protocol's runs, name by name, each behind that guard (`IM.claims_alone`). The two halves of
`RunIs` are what such a guarded run meets. So a field comes down to finding the run under its name
in the lot's own sub-protocol's list of runs.

Main names.
  `runIs_of_laid`: THE GENERAL STEP: from "laid alone", the place in the segment, and the run found
    under the name in the lot's sub-protocol.
  `theOwn_claims`, `theWhole_claims`: the lookup's sub-protocol at an address states "objects" and
    "guests", and which runs these are; the quiet step behind it states nothing.
  `piece_calls`, `piece_digits`: at the pieces 3 and 8 of a segment stand the lookup on the calls
    and the one on the digits, and the segment is the output head's.
  `runsAre_at_link24`: ALL NINE. The two numbers iU3 and lm are handed out each with the equation
    that makes it.

By: `IM.k6_of`, `IM.k3_of` (Johnson/IMR/K6Seat.lean, K3Seat.lean: which sub-protocols stand at the
numbers 3, 2 and 7 of link 24); `seated_runs`, `same_of_reply` (Johnson/Desc/Reads/GuardOff.lean);
`theWhole_is`, `theStated_planes` (Johnson/Desc/First/Look/K3OwnIs.lean).

Limits. The public record is the opening's own (Bs.G₀.W). It says which runs are stated, nothing of
what they answer. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.RunsAre
import Johnson.Desc.Reads.GuardOff
import Johnson.IMR.K6Seat
import Johnson.IMR.K3Seat
import Johnson.Desc.First.Look.K3OwnIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc (Block Chain Link FileDescription Claim Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (statesOfLink)
open VerifiableInference.Desc.Kinds.Head (kind asClaim seatAt parOf planesAt callerReaders
  callerKeys seatedClaims blockClaims)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.OnPublicFiles (objectsRun guestsRun)
open VerifiableInference.Reads.Pass (same_of_reply seated_runs)

/-- **The general step**: a run of a sub-protocol that is laid alone behind the guard. -/
theorem runIs_of_laid {bb B : Block S Claim} {nm : String} {a : Place} {l : Link S Claim} {k : ℕ}
    {name : String} {own : ℕ → S → Except String (List Claim × S)}
    (hL : IM.LaidAlone ProofFile.sameReply bb B nm a) (hh : l.hear[k]? = some bb)
    (hf : (B.claims.find? fun c => c.1 == name) = some (name, own)) : RunIs l k name own := by
  refine ⟨IM.guardRun ProofFile.sameReply own, ?_, fun n t y h => ?_, fun n t y h hr => ?_⟩
  · have hs : statesOfLink l k = B.claims.map fun c => (c.1, IM.guardRun ProofFile.sameReply c.2) := by
      unfold statesOfLink
      rw [hh]
      exact IM.claims_alone hL
    rw [hs, List.find?_map]
    have e : ((fun r : String × (ℕ → S → Except String (List Claim × S)) => r.1 == name) ∘
        fun c : String × (ℕ → S → Except String (List Claim × S)) =>
          (c.1, IM.guardRun ProofFile.sameReply c.2)) = fun c => c.1 == name := rfl
    rw [e, hf]
    rfl
  · unfold IM.guardRun at h
    cases hr : own n t with
    | error e =>
      rw [hr] at h
      cases h
    | ok z =>
      rw [hr] at h
      have h' : (VerifiableInference.Desc.seatSame ProofFile.sameReply t z.2).map (fun _ => z) =
          .ok y := h
      unfold VerifiableInference.Desc.seatSame at h'
      split at h'
      · exact h'
      · cases h'
  · unfold IM.guardRun
    rw [h]
    show (VerifiableInference.Desc.seatSame ProofFile.sameReply t y.2).map (fun _ => y) = .ok y
    unfold VerifiableInference.Desc.seatSame
    rw [if_pos (same_of_reply hr)]
    rfl

/-- The lookup's own sub-protocol at an address, with its runs on: which runs it states. -/
theorem theOwn_claims (claim : OnBytes.Model.Aff → Claim) (X : OnBytes.Model.Verify.Public)
    (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape) (a : Place) (b : Block S Claim)
    (h : K3.theOwn claim true X codes shape a = some b) :
    ∃ i dg, a.link = some i ∧ a.piece = K3.pieceAt X i dg ∧
      b.claims = [("objects", objectsRun (K3.seatOfLookupOnDigitsOrCalls claim dg)),
        ("guests", guestsRun ([] : List (Look.Guest S Claim)))] := by
  unfold K3.theOwn at h
  split at h
  · cases h
  · obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨dg, -, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · rename_i hp
      obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, -, h⟩ := Option.map_eq_some_iff.1 h
      subst h
      exact ⟨i, dg, hi, by simpa using hp, rfl⟩

/-- So does the whole sub-protocol: the quiet step behind it states nothing. -/
theorem theWhole_claims (claim : OnBytes.Model.Aff → Claim) (X : OnBytes.Model.Verify.Public)
    (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape) (a : Place) (B : Block S Claim)
    (h : K3.theWhole claim true X codes shape a = some B) :
    ∃ i dg, a.link = some i ∧ a.piece = K3.pieceAt X i dg ∧
      B.claims = [("objects", objectsRun (K3.seatOfLookupOnDigitsOrCalls claim dg)),
        ("guests", guestsRun ([] : List (Look.Guest S Claim)))] := by
  obtain ⟨b, hb, hB⟩ := K3.theWhole_is claim true X codes shape a B h
  obtain ⟨i, dg, hi, hp, hc⟩ := theOwn_claims claim X codes shape a b hb
  refine ⟨i, dg, hi, hp, ?_⟩
  rcases hB with ⟨-, rfl⟩ | ⟨f, -, rfl⟩
  · exact hc
  · show b.claims ++ [] = _
    rw [List.append_nil, hc]

/-- Piece 3 of a segment: the lookup on the calls, at the output head's segment. -/
theorem piece_calls {X : OnBytes.Model.Verify.Public} {i : ℕ} {dg : Bool}
    (h : 3 = K3.pieceAt X i dg) : dg = false ∧ K3.isHead X i = true := by
  unfold K3.pieceAt at h
  cases hH : K3.isHead X i <;> cases dg <;> simp [hH] at h ⊢

/-- Piece 8 of a segment: the lookup on the digits, at the output head's segment. -/
theorem piece_digits {X : OnBytes.Model.Verify.Public} {i : ℕ} {dg : Bool}
    (h : 8 = K3.pieceAt X i dg) : dg = true ∧ K3.isHead X i = true := by
  unfold K3.pieceAt at h
  cases hH : K3.isHead X i <;> cases dg <;> simp [hH] at h ⊢

/-- **WHICH RUNS THE OUTPUT HEAD's SEGMENT STATES: ALL NINE, at the link that the IOP as written in
Lean holds.** -/
theorem runsAre_at_link24 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Claim) (iU3 lm : ℕ), c.links[24]? = some Lk ∧
      Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      (∃ p, Look.placeAt Bs.G₀.W 24 false = some p ∧ p.lm = lm) ∧
      RunsAre Lk Bs.G₀.W iU3 lm := by
  obtain ⟨Lk, b6, B6, ms, e1, h6, -, hsc, hL6, -⟩ := IM.k6_of hS hR O
  obtain ⟨iU3, hi⟩ : ∃ i, Bs.G₀.W.H.tl.ix.U.getD 2 none = some i := by
    cases e : Bs.G₀.W.H.tl.ix.U.getD 2 none with
    | some i => exact ⟨i, rfl⟩
    | none =>
      unfold seatedClaims blockClaims at hsc
      rw [e] at hsc
      cases hsc
  obtain ⟨Lk2, b2, B2, e2, h2, hB2, hL2⟩ := IM.k3_of hS hR O 24 (by decide) false
  obtain rfl : Lk2 = Lk := Option.some.inj (e2.symm.trans e1)
  obtain ⟨Lk7, b7, B7, e7, h7, hB7, hL7⟩ := IM.k3_of hS hR O 24 (by decide) true
  obtain rfl : Lk7 = Lk2 := Option.some.inj (e7.symm.trans e1)
  -- the lookup on the calls
  have hB2' : K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes
      Z.first.shape (IM.k3Place 24 false) = some B2 := hB2
  obtain ⟨W2, hW2, -⟩ := K3.theStated_is _ _ _ _ _ _ _ hB2'
  obtain ⟨i2, dg2, hi2, hp2, hc2⟩ := theWhole_claims _ _ _ _ _ _ hW2
  obtain rfl : 24 = i2 := Option.some.inj hi2
  obtain ⟨rfl, hH⟩ := piece_calls (show 3 = K3.pieceAt Bs.G₀.W 24 dg2 from hp2)
  have hrd : K3Lot.readersAt Bs.G₀.W 24 = some (callerReaders (planesAt iU3)) := by
    unfold K3Lot.readersAt
    simp only [hH, if_true]
    rw [hi]
    rfl
  obtain ⟨p, W2', hp, hW2', hcl2⟩ := K3.theStated_planes _ _ _ _ _ _ _ hB2' 24 _ rfl hp2 hrd
  obtain rfl : W2' = W2 := Option.some.inj (hW2'.symm.trans hW2)
  rw [hc2] at hcl2
  -- the lookup on the digits
  have hB7' : K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes
      Z.first.shape (IM.k3Place 24 true) = some B7 := hB7
  have hcl7 : B7.claims = [("objects", objectsRun (K3.seatDigits K3Lot.ofForm)),
      ("guests", guestsRun ([] : List (Look.Guest S Claim)))] := by
    unfold K3.theStated at hB7'
    obtain ⟨W7, hW7, h⟩ := Option.bind_eq_some_iff.1 hB7'
    obtain ⟨i7, dg7, hi7, hp7, hc7⟩ := theWhole_claims _ _ _ _ _ _ hW7
    obtain rfl : 24 = i7 := Option.some.inj hi7
    obtain ⟨rfl, -⟩ := piece_digits (show 8 = K3.pieceAt Bs.G₀.W 24 dg7 from hp7)
    have hne : ((IM.k3Place 24 true).piece != K3.pieceAt Bs.G₀.W 24 false) = true := by
      unfold K3.pieceAt
      rw [hH]
      rfl
    have h' : (if ((IM.k3Place 24 true).piece != K3.pieceAt Bs.G₀.W 24 false) = true then some W7
        else
          match K3Lot.readersAt Bs.G₀.W 24 with
          | none => some W7
          | some r => (Look.placeAt Bs.G₀.W 24 false).map fun p =>
              K3.withCaller (K3.seatCalls K3Lot.ofForm) p r W7) = some B7 := h
    rw [if_pos hne] at h'
    rw [← Option.some.inj h']
    exact hc7
  have hcl6 := seated_runs hsc hi
  refine ⟨Lk7, iU3, p.lm, e1, hi, ⟨p, hp, rfl⟩, ?_⟩
  exact
    { objects2 := runIs_of_laid hL2 h2 (by rw [hcl2]; rfl)
      guests2 := runIs_of_laid hL2 h2 (by rw [hcl2]; rfl)
      planes2 := runIs_of_laid hL2 h2 (by rw [hcl2]; rfl)
      join3 := runIs_of_laid hL6 h6 (by rw [hcl6]; rfl)
      norm3 := ⟨_, rfl, runIs_of_laid hL6 h6 (by rw [hcl6]; rfl)⟩
      policy3 := ⟨_, rfl, runIs_of_laid hL6 h6 (by rw [hcl6]; rfl)⟩
      logits3 := ⟨_, rfl, runIs_of_laid hL6 h6 (by rw [hcl6]; rfl)⟩
      objects7 := runIs_of_laid hL7 h7 (by rw [hcl7]; rfl)
      guests7 := runIs_of_laid hL7 h7 (by rw [hcl7]; rfl) }

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.runIs_of_laid
#print axioms VerifiableInference.Desc.First.MergeLaw.theOwn_claims
#print axioms VerifiableInference.Desc.First.MergeLaw.theWhole_claims
#print axioms VerifiableInference.Desc.First.MergeLaw.runsAre_at_link24
