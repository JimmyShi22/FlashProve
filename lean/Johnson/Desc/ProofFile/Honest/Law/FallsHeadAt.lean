-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/FallsHeadAt.lean: where the records of `fallsHead`
(Honest/Law/FallsHead.lean) stand. Three things are proved of the first chain's list of falls at the
full size. Every record stands at a fall's seat (`fallSeat`, Honest/Law/CoverSeats.lean): this is
the field `hfs` of `FirstAsks` (Honest/Law/CoverAsks.lean). At each of the fifty numbers of the
chain at which a batching or the sub-protocol after it stands, the named record stands at the place
of the sub-protocol at that number. And at these numbers the list has a record at the sub-protocol's
place whose silence is the silence of the test: the form in which lemmas on the verifier's tests on
values take the list.

  1  `falls_seats_yes`, `falls_seats_control`   the records' written places are falls' seats: a
     closed statement by `decide +kernel`, and a control that rejects
  2  `fallsHead_seats`   `hfs`
  3  `front_at`, `front_at_head`   at a batching: a record whose silence is `k8Front`'s
  4  `quiet_at`, `quiet_at_head`, `share_at`, `share_at_head`   at the sub-protocol after it: a
     record whose silence is `freeSlotShare`'s, and one whose silence is `k8Share`'s

Limits.
  * `hps` (the chain's places are the written list) and `hq` (the chain, the segment and the piece
    of what `IM.k9At` returns) are hypotheses. The library proves `hps` of the proof file's first
    chain under hypotheses of its own. Of `hq` it proves the chain and the segment, and the piece
    in another form (`IM.k9_of`, Johnson/IMR/LinkSeat.lean).
  * The statements of sections 3 and 4 say that there is such a record. Their proofs give the named
    one, and the test is the record's own test.
  * A record's silence gives its test's silence. Nothing is said on how likely a record is to
    speak.
  * The closed statement is decided at one form of the written list. The full size alone.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.FallsHead
import Johnson.Desc.ProofFile.Honest.Law.FallPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName Block)
open VerifiableInference.Desc.First (S)

variable {Zp : ProofFile.Pub} {G₀ : ProofFile.Ground} {cols tau : Nat → Nat} {share notGood : Nat → Odds}
  {r0 : Nat → Nat}

/-! ## 1 The written places are falls' seats -/

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem falls_seats_yes : ((List.range 25).all fun l =>
      fallSeat P5J.At.links ⟨1, some l, 8 + 2 * oAt l, KindName.K9⟩ &&
        fallSeat P5J.At.links ⟨1, some l, 8 + 2 * oAt l + 1, KindName.frame⟩) = true ∧
    ((List.range 12).all fun g =>
      fallSeat P5J.At.links ⟨1, some (2 * g), 3, KindName.K4⟩) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- A control: one piece earlier the first test rejects. -/
theorem falls_seats_control : ((List.range 25).all fun l =>
      fallSeat P5J.At.links ⟨1, some l, 7 + 2 * oAt l, KindName.K9⟩ &&
        fallSeat P5J.At.links ⟨1, some l, 7 + 2 * oAt l + 1, KindName.frame⟩) = false := by
  decide +kernel

/-! ## 2 Every record stands at a fall's seat -/

/-- Every record of the list stands at a fall's seat. `hq`: what `IM.k9At` returns at segment `l`
stands in chain 1, in segment `l`, at the batching's piece. -/
theorem fallsHead_seats
    (hq : ∀ l, l < 25 → ∀ p, IM.k9At Zp l = some p →
      p.chain = 1 ∧ p.link = l ∧ p.piece = 8 + 2 * oAt l) :
    ∀ f ∈ fallsHead Zp G₀ cols tau share notGood r0, fallSeat P5J.At.links f.place = true := by
  intro f hf
  unfold fallsHead at hf
  rcases List.mem_append.1 hf with h | h
  · obtain ⟨l, hl, hF⟩ := List.mem_flatMap.1 h
    have hl' : l < 25 := List.mem_range.1 hl
    have t := List.all_eq_true.1 falls_seats_yes.1 l hl
    rw [Bool.and_eq_true] at t
    unfold linkFalls at hF
    rcases List.mem_append.1 hF with hF | hF
    · rcases List.mem_append.1 hF with hF | hF
      · obtain rfl := List.mem_singleton.1 hF
        exact t.1
      · cases hp : IM.k9At Zp l with
        | none =>
          rw [hp] at hF
          cases hF
        | some p =>
          cases hu : VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 with
          | none =>
            rw [hp, hu] at hF
            cases hF
          | some u =>
            rw [hp, hu] at hF
            obtain rfl := List.mem_singleton.1 hF
            obtain ⟨q1, q2, q3⟩ := hq l hl' p hp
            show fallSeat P5J.At.links ⟨p.chain, some p.link, p.piece + 1, KindName.frame⟩ = true
            rw [q1, q2, q3]
            exact t.2
    · cases hX : G₀.built[l]? with
      | none =>
        rw [hX] at hF
        cases hF
      | some Xl =>
        rw [hX] at hF
        obtain rfl := List.mem_singleton.1 hF
        show fallSeat P5J.At.links ⟨1, some l, 9 + 2 * oAt l, KindName.frame⟩ = true
        rw [show 9 + 2 * oAt l = 8 + 2 * oAt l + 1 by omega]
        exact t.2
  · obtain ⟨g, hg, hF⟩ := List.mem_filterMap.1 h
    cases hh : G₀.W.G[g]? with
    | none =>
      rw [hh] at hF
      cases hF
    | some hp =>
      rw [hh] at hF
      obtain rfl := Option.some.inj hF
      exact List.all_eq_true.1 falls_seats_yes.2 g hg

/-! ## 3 At a batching -/

variable {Cl : Type} {all : List (Block S Cl)}

/-- At the batching of segment `l`, for `l` below 24. -/
theorem front_at (hps : all.map (·.place) = P5J.At.ps) {l : Nat} (hl : l < 24) :
    ∀ blk, all[14 * l + 9]? = some blk →
      ∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K8.k8Front s ds = none := by
  intro blk hb
  refine ⟨_, fallsHead_front (l := l) (by omega), ?_, fun _ _ e => e⟩
  rw [place_batch hps hl hb]
  show (⟨1, some l, 8 + 2 * oAt l, KindName.K9⟩ : Place) = _
  rw [show oAt l = 0 from if_neg (by omega)]

/-- At the batching of segment 24. -/
theorem front_at_head (hps : all.map (·.place) = P5J.At.ps) :
    ∀ blk, all[347]? = some blk →
      ∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K8.k8Front s ds = none := by
  intro blk hb
  refine ⟨_, fallsHead_front (l := 24) (by omega), ?_, fun _ _ e => e⟩
  rw [place_batch_head hps hb]
  rfl

/-! ## 4 At the sub-protocol after a batching -/

/-- The fall of the free slots, at segment `l` below 24. -/
theorem quiet_at (hps : all.map (·.place) = P5J.At.ps) {l : Nat} (hl : l < 24)
    {p : VerifiableInference.Desc.K9.Where}
    {u : VerifiableInference.Desc.K9.SegSort × Nat × VerifiableInference.Desc.K9.TWhere}
    (hp : IM.k9At Zp l = some p) (hq : p.chain = 1 ∧ p.link = l ∧ p.piece = 8)
    (hu : VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 = some u) :
    ∀ blk, all[14 * l + 10]? = some blk →
      ∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K9.freeSlotShare u.2.2.filled s = none := by
  intro blk hb
  refine ⟨_, fallsHead_quiet (l := l) (by omega) hp hu, ?_, fun _ _ e => e⟩
  rw [place_behind hps hl hb]
  show (⟨p.chain, some p.link, p.piece + 1, KindName.frame⟩ : Place) = _
  rw [hq.1, hq.2.1, hq.2.2]

/-- The fall of the free slots, at segment 24. -/
theorem quiet_at_head (hps : all.map (·.place) = P5J.At.ps)
    {p : VerifiableInference.Desc.K9.Where}
    {u : VerifiableInference.Desc.K9.SegSort × Nat × VerifiableInference.Desc.K9.TWhere}
    (hp : IM.k9At Zp 24 = some p) (hq : p.chain = 1 ∧ p.link = 24 ∧ p.piece = 10)
    (hu : VerifiableInference.Desc.K9.testsWhere Zp.p.X 24 0 = some u) :
    ∀ blk, all[348]? = some blk →
      ∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K9.freeSlotShare u.2.2.filled s = none := by
  intro blk hb
  refine ⟨_, fallsHead_quiet (l := 24) (by omega) hp hu, ?_, fun _ _ e => e⟩
  rw [place_behind_head hps hb]
  show (⟨p.chain, some p.link, p.piece + 1, KindName.frame⟩ : Place) = _
  rw [hq.1, hq.2.1, hq.2.2]

/-- The smallness test's share, at segment `l` below 24. -/
theorem share_at (hps : all.map (·.place) = P5J.At.ps) {l : Nat} (hl : l < 24)
    {Xl : OnBytes.Model.Stages.LinkH} (hX : G₀.built[l]? = some Xl) :
    ∀ blk, all[14 * l + 10]? = some blk →
      ∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K8.k8Share (ProofFile.k8ParW Zp G₀ Xl l).nU s = none := by
  intro blk hb
  refine ⟨_, fallsHead_share (l := l) (by omega) hX, ?_, fun _ _ e => e⟩
  rw [place_behind hps hl hb]
  show (⟨1, some l, 9 + 2 * oAt l, KindName.frame⟩ : Place) = _
  rw [show oAt l = 0 from if_neg (by omega)]

/-- The smallness test's share, at segment 24. -/
theorem share_at_head (hps : all.map (·.place) = P5J.At.ps) {Xl : OnBytes.Model.Stages.LinkH}
    (hX : G₀.built[24]? = some Xl) :
    ∀ blk, all[348]? = some blk →
      ∃ F ∈ fallsHead Zp G₀ cols tau share notGood r0, F.place = blk.place ∧
        ∀ s ds, F.test s ds = none → K8.k8Share (ProofFile.k8ParW Zp G₀ Xl 24).nU s = none := by
  intro blk hb
  refine ⟨_, fallsHead_share (l := 24) (by omega) hX, ?_, fun _ _ e => e⟩
  rw [place_behind_head hps hb]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.falls_seats_yes
#print axioms ProofFile.Honest.falls_seats_control
#print axioms ProofFile.Honest.fallsHead_seats
#print axioms ProofFile.Honest.front_at
#print axioms ProofFile.Honest.front_at_head
#print axioms ProofFile.Honest.quiet_at
#print axioms ProofFile.Honest.quiet_at_head
#print axioms ProofFile.Honest.share_at
#print axioms ProofFile.Honest.share_at_head
