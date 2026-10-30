-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/PlainAtSeat.lean: THE SMALLNESS TEST: AT EACH OF THE 25 SEGMENTS OF THE PROOF FILE's
DESCRIPTION THE RUNS OF CLAIMS ARE PLAIN (`PlainLink`, Johnson/Desc/K8/Honest/CountFrom.lean), AND
THE SEATED BATCHING BLOCK IS THE LIBRARY's, LAID ALONE. Lemmas; none of the library's goals. An
assembly: no new argument.

  `plain_seat_layers`, `plain_seat_att`, `plain_seat_head`   at a segment of each kind
  **`plain_at_seat`**   in the goals' scope, at the term that an opening says the description is, l
      < 25: there are the segment Lk and the batching's numbers p; the member at 14 l + 9, or 347 at
      the head's, is Lk's batching block at Lk's own function of claims; Lk is plain; and that block
      is K9.batch K9.atS p at that function, laid alone (IM.LaidAlone, Johnson/IMR/SeatForm.lean) at
      a place whose kind is not K7: what the laws on a seated block's yes ask
The proofs take each kind's ties from the scope as Johnson/P1K8R/FallAtSeat.lean, FallAtSeatAtt.lean
and FallAtSeatHead.lean do.
Limits. Nothing on any state.

-/
import Johnson.P1K8R.FallAtSeatHead
import Johnson.Desc.K8.Honest.CountFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)

/-- What is said of a seat. -/
def PlainSeat (c : Chain S Claim) (Z : ProofFile.Pub) (l K : ℕ) : Prop :=
  ∃ (Lk : Link S Claim) (p : K9.Where), c.links[l]? = some Lk ∧ IM.k9At Z l = some p ∧
    c.blocksInOrder[K]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧ PlainLink Lk ∧
    ∃ (same : S → S → Bool) (name : String) (a : Place), a.kind ≠ KindName.K7 ∧
      IM.LaidAlone same (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order))
        (K9.batch K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)) name a

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem plain_seat_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) : PlainSeat c Z l (14 * l + 9) := by
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, hflat, -, -, -, hord, hordA, hlen, -⟩ :=
    (IM.k9_of hS hR O).2 l hl
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hsub] at hs25 hord hordA hlen
  have h7 : Lk.hear.length = 7 := by
    rw [hlen]
    cases (l == 0) <;> rfl
  obtain ⟨Lk', p4, X, e1', -, hX, ties⟩ := LPFK9.layers_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  have h24 : l ≠ 24 := by
    intro e
    rw [e] at hsub
    exact absurd hsub (by decide)
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  rw [h7] at hflat
  exact ⟨Lk, p, e1, e2, hflat, plain_layers Lk p4 _ ties tC tD hord, _, _, _,
    (by decide : KindName.K9 ≠ KindName.K7),
    hb (claimsInBy Lk.each Lk.hear Lk.order)⟩

theorem plain_seat_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .attention) : PlainSeat c Z l (14 * l + 9) := by
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, hflat, -, -, -, hord, hordA, hlen, -⟩ :=
    (IM.k9_of hS hR O).2 l hl
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hsub] at hs25 hord hordA hlen
  have h7 : Lk.hear.length = 7 := by
    rw [hlen]
    cases (l == 0) <;> rfl
  obtain ⟨Lk', Xl, Ap, X, e1', hXl, -, hA, hX, ties⟩ :=
    LPFK9.att_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, g, hg, rfl⟩ := Att.P.att_only O.pub O.blank hs25
  obtain ⟨Xl', hXl', -, hgX, -⟩ := Att.P.built_att O.pub O.blank h4 hg
  obtain rfl : Xl' = Xl := Option.some.inj (hXl'.symm.trans hXl)
  rw [hgX] at hA
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tJ : ∀ run, LinkJoin.At Lk (2, "join") run →
      LinkJoin.Under run
        (K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    rw [LinkJoin.at_join_is O h4 hg hA e1 hrun]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (1, "planes") run →
      ∃ lm, LinkJoin.Under run
        (K9.planesCalls lm
          (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "planes") run := by
      simpa [IM.k3Ix, h24] using hrun
    obtain ⟨q, -, rfl⟩ :=
      OnPublicFiles.at_planes_is hS hR O hl e1 (H2K5.Door.readersAt_att h4 hA) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  rw [h7] at hflat
  exact ⟨Lk, p, e1, e2, hflat, plain_att Lk (Att.P.parCOf Ap) _ ties tC tD tJ tP hord, _, _, _,
    (by decide : KindName.K9 ≠ KindName.K7), hb (claimsInBy Lk.each Lk.hear Lk.order)⟩

theorem plain_seat_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    PlainSeat c Z 24 (14 * 24 + 11) := by
  have hl : 24 < 25 := by omega
  have hsub : IM.subAt 24 = .head := rfl
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, hflat, -, -, -, hord, hordA, hlen, -⟩ :=
    (IM.k9_of hS hR O).2 24 hl
  have hs25 := IM.subs_scope hS hR O 24 hl
  rw [hsub] at hs25 hord hordA hlen
  have h9 : Lk.hear.length = 9 := by
    rw [hlen]
    rfl
  have hU3 := head_u3 O.public
  obtain ⟨Lk', X, e1', hX, ties⟩ := LPFK9.head_ties_at O.made O.places O.chain 24 hs25 0 hU3
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, hN⟩ := head_24 hS O.public
  have hH : K3.isHead Bs.G₀.W 24 = true := by
    unfold K3.isHead
    rw [h4, hN]
    rfl
  have tC : ∀ run, LinkJoin.At Lk (2, "objects") run → LinkJoin.Under run K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (7, "objects") run → LinkJoin.Under run K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 true, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (2, "planes") run →
      ∃ lm, LinkJoin.Under run (K9.planesCalls lm (callerReaders (planesAt 0))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "planes") run := hrun
    obtain ⟨q, -, rfl⟩ := OnPublicFiles.at_planes_is hS hR O hl e1 (OnPublicFiles.readersAt_head hH hU3) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  rw [h9] at hflat
  exact ⟨Lk, p, e1, e2, hflat, plain_head Lk _ 0 _ 4 _ _ ties tC tD tP hord, _, _, _,
    (by decide : KindName.K9 ≠ KindName.K7),
    hb (claimsInBy Lk.each Lk.hear Lk.order)⟩

/-- **At all 25 segments.** -/
theorem plain_at_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) :
    PlainSeat c Z l (14 * l + (if l = 24 then 11 else 9)) := by
  by_cases h24 : l = 24
  · subst h24
    exact plain_seat_head hS hR O
  · rw [if_neg h24]
    by_cases he : l % 2 = 0
    · exact plain_seat_layers hS hR O l hl (by unfold IM.subAt; rw [if_neg h24, if_pos he])
    · exact plain_seat_att hS hR O l hl (by unfold IM.subAt; rw [if_neg h24, if_neg he])

end

end P1K8

#print axioms P1K8.plain_seat_layers
#print axioms P1K8.plain_seat_att
#print axioms P1K8.plain_seat_head
#print axioms P1K8.plain_at_seat
