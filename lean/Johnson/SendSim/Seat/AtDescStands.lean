-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtDescStands.lean: for all public files at which the maker of the proof file's
description returns, the first chain has a sub-protocol at the place of every job of the two lots of
the kind K1, and the side there is Seated.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. The one premise is IM.Open; no further premise on the public files is left.
  stands_at_job   For every job J of lotJobs and wJobs, the first chain's list F.first.blocksInOrder has a
                  member at J's place.
  seat_at_job     The same in the form of the rule's premise seat₁ on a row's place.
  seatedAt_job    Every side that Side.seated returns there for our row at J is Seated at J: its row
                  is our sender alone with its simulator; it fits; its rounds and oracle messages
                  agree with the sender's in what a run reads; the challenges that its rounds can
                  sample are just the sender's seeds, and no seed's factor is 0.
  wJobs_some      The list wJobs is exactly one job: the one at the request's own table, at the
                  message that linMessageW gives.

How it fits. The first three serve AtDescLots.lean beside this file; AtDescOwn.lean and
FitsAtLots.lean use member_at_own. Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

The other names.
  places_any_flag   a place inside a segment is in the driver's table of places (flatPlacesOf,
                    Johnson/Desc/First/Driver/Chain.lean) whichever value the table's flag has. The
                    flag says whether the segments leave more than one pending claim on the weight
                    table; only then is there a sub-protocol that joins them (K13).
  own_kind_link     each sub-protocol of K1's own lot is of the kind K1 and inside a segment.
  member_at_own     F's first chain has a member at the place of each sub-protocol of that lot.
  own_of_job        each job of lotJobs has a sub-protocol of that lot with its place, rounds and
                    oracle messages.
  w_of_job          each job of wJobs is the job at the request's own table.
  wBlock_of_msg     where linMessageW gives a message, the lot K13.lot4 has its sub-protocol.

How member_at_own is proved. The maker rejects if a sub-protocol that is no frame block is at no
place of the list of places that it computes from Z (IM.stands_in_shape, from the field sound of
IM.Open). That list is the driver's table at some flag (IM.shape_places). The first chain's places
are the same table at the flag true (ProofFile.Honest.AtPlace.stands_iff). The flag changes only places
outside the segments (places_any_flag). At the request's own table the sealed library has the member
already (ProofFile.Honest.AtPlace.stands_m4).

Limits. Pointwise statements: no distribution is named. The first chain alone. That the maker
returns at given public files is not shown here. For these and all other limits see AtDescLots.lean.
-/
import Johnson.SendSim.Seat.AtDescSome
import Johnson.Desc.ProofFile.Honest.Member.Stands
import Johnson.IMR.LinkSeat

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

variable {V W X Xi Pb : Type}

/-- A place inside a segment is in the driver's table of places whichever value the flag has. -/
theorem places_any_flag {links : List First.ModelPart} {s s' : Bool} {a : Place}
    (h : a ∈ First.flatPlacesOf links s) (hl : a.link ≠ none) :
    a ∈ First.flatPlacesOf links s' := by
  unfold First.flatPlacesOf at h ⊢
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · exact absurd (IM.address_kind h).2 hl
  · obtain rfl := List.mem_singleton.1 h
    exact absurd rfl hl

/-- Each sub-protocol of the kind's own lot is of the kind K1 and is inside a segment. -/
theorem own_kind_link {Z : ProofFile.Pub} {G : ProofFile.Ground} {b₀ : Block First.S Unit}
    (h : b₀ ∈ (ProofFile.k1Pure Z).own G) : b₀.place.kind = KindName.K1 ∧ b₀.place.link ≠ none := by
  rcases IM.k1_mem h with rfl | ⟨l, Y, pr, pd, reads, digits, -, -, rfl | rfl⟩
  · exact ⟨rfl, fun e => nomatch e⟩
  · exact ⟨rfl, fun e => nomatch e⟩
  · exact ⟨rfl, fun e => nomatch e⟩

/-- Each job of the kind's own lot has a sub-protocol of that lot with its place, rounds and oracle
messages. -/
theorem own_of_job (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) {J : SendJob (PlaceIn Xi) X} (hJ : J ∈ lotJobs no D Z G) :
    ∃ b₀ ∈ (ProofFile.k1Pure Z).own G,
      b₀.place = J.P.place ∧ b₀.rounds = K1.rounds J.P ∧ b₀.oracles = K1.oracles J.P := by
  unfold lotJobs at hJ
  rcases List.mem_cons.1 hJ with rfl | hJ
  · exact ⟨_, own_first Z G, rfl, rfl, rfl⟩
  · obtain ⟨y, hy, hJ⟩ := List.mem_flatMap.1 hJ
    obtain ⟨Y, l⟩ := y
    have hY : G.built[l]? = some Y := by
      rw [← Array.getElem?_toList]
      simpa using (List.mk_mem_zipIdx_iff_getElem?.1 hy)
    dsimp only at hJ
    split at hJ
    · cases hJ
    · rename_i pr pd reads digits hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
      rcases hJ with rfl | rfl
      · exact ⟨_, own_reads Z G hY hn, (reads_member (X := X) Z G l Y pr reads _ _).2.2,
          (reads_member (X := X) Z G l Y pr reads _ _).1,
          (reads_member (X := X) Z G l Y pr reads _ _).2.1⟩
      · exact ⟨_, own_digits Z G hY hn,
          (later_rounds (X := X) G.first (K1.gpOf Z) l pd 2 _ _ digits).2.2,
          (later_rounds (X := X) G.first (K1.gpOf Z) l pd 2 _ _ digits).1,
          (later_rounds (X := X) G.first (K1.gpOf Z) l pd 2 _ _ digits).2.1⟩

/-- Each job of the lot at the request's own table is that table's job, at the message that the
shape gives. -/
theorem w_of_job (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) {J : SendJob (PlaceIn Xi) X} (hJ : J ∈ wJobs no D Z G) :
    ∃ msg, linMessageW Z.first.lin = some msg ∧
      J = wJobAt Z.first (wGp Z) 4 msg (no ⟨1, none, 4, .K1⟩) (D Z G) := by
  unfold wJobs at hJ
  rw [Option.mem_toList] at hJ
  obtain ⟨msg, hm, rfl⟩ := Option.map_eq_some_iff.1 hJ
  exact ⟨msg, hm, rfl⟩

/-- Where the shape gives the message with the request's own table, the lot there has its
sub-protocol. -/
theorem wBlock_of_msg {Z : ProofFile.Pub} {msg : Array OracleNotice}
    (hm : linMessageW Z.first.lin = some msg) :
    K13.wBlock Z = some (K1.sendAtS (K1.parW Z.first (wGp Z) 4 msg)) := by
  unfold K13.wBlock K1.wAt
  rw [hm]
  rfl

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Where the description's maker returns, the first chain's list has a member at the place of
each sub-protocol of K1's own lot.** -/
theorem member_at_own (O : IM.Open o pol lay KL F Z Bs base c A B) {b₀ : Block First.S Unit}
    (hown : b₀ ∈ (ProofFile.k1Pure Z).own Bs.G₀) : ∃ m ∈ c.blocksInOrder, m.place = b₀.place := by
  obtain ⟨hk, hl⟩ := own_kind_link hown
  have hb : (b₀.retype : Block First.S ProofFile.Cl) ∈ (ProofFile.k1Pure Z).blocks Bs.G₀ :=
    List.mem_append_left _ (List.mem_map.2 ⟨b₀, hown, rfl⟩)
  obtain ⟨-, hshape, -, hall⟩ := IM.base_made O.made
  have hin : (b₀.retype : Block First.S ProofFile.Cl) ∈ Bs.all.flatMap fun x => x.2 := by
    rw [hall]
    exact List.mem_flatMap.2
      ⟨(ProofFile.k1Pure Z, (ProofFile.k1Pure Z).blocks Bs.G₀),
        List.mem_map.2 ⟨ProofFile.k1Pure Z, k1_in_seat Z, rfl⟩, hb⟩
  obtain ⟨e, he, ee⟩ := IM.stands_in_shape O.sound hin
    (by show b₀.place.kind ≠ _; rw [hk]; decide)
  obtain ⟨s, hs⟩ := IM.shape_places hshape
  have h1 : b₀.place ∈ First.flatPlacesOf (ProofFile.subsOf Z) s := by
    rw [← hs]
    exact List.mem_map.2 ⟨e, he, ee⟩
  exact (ProofFile.Honest.AtPlace.stands_iff O b₀.place).2 (places_any_flag h1 hl)

/-- Where the maker returns, the list wJobs is exactly one job, the one at the request's own table.
-/
theorem wJobs_some (O : IM.Open o pol lay KL F Z Bs base c A B) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (G : ProofFile.Ground) :
    ∃ msg, linMessageW Z.first.lin = some msg ∧ wJobs (X := X) no D Z G =
      [wJobAt Z.first (wGp Z) 4 msg (no ⟨1, none, 4, .K1⟩) (D Z G)] := by
  obtain ⟨-, -, -, -, -, w, -, -, hw, -⟩ := IM.back_of O
  unfold K13.wBlock K1.wAt at hw
  obtain ⟨msg, hm, -⟩ := Option.map_eq_some_iff.1 hw
  refine ⟨msg, hm, ?_⟩
  unfold wJobs
  rw [hm]
  rfl

/-- **Where the description's maker returns, the first chain's list has a member at the place of
every job of the two lots.** -/
theorem stands_at_job (O : IM.Open o pol lay KL F Z Bs base c A B) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Z Bs.G₀ ++ wJobs no D Z Bs.G₀) :
    ∃ m ∈ F.first.blocksInOrder, m.place = J.P.place := by
  have e := O.desc
  subst e
  rcases List.mem_append.1 hJ with hJ | hJ
  · obtain ⟨b₀, hown, hp, -, -⟩ := own_of_job no D Z Bs.G₀ hJ
    obtain ⟨m, hm, hmp⟩ := member_at_own O hown
    exact ⟨m, hm, hmp.trans hp⟩
  · obtain ⟨msg, -, rfl⟩ := w_of_job no D Z Bs.G₀ hJ
    exact ProofFile.Honest.AtPlace.stands_m4 O

/-- The same in the form of the rule's premise on a row's place. -/
theorem seat_at_job (O : IM.Open o pol lay KL F Z Bs base c A B) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Z Bs.G₀ ++ wJobs no D Z Bs.G₀) :
    F.first.blocksInOrder.any (fun b => b.place == J.P.place) = true := by
  obtain ⟨m, hm, hp⟩ := stands_at_job O no D hJ
  exact List.any_eq_true.2 ⟨m, hm, beq_iff_eq.2 hp⟩

/-- **Where the description's maker returns, every side that Side.seated returns at the place of a
job of the two lots, for our row at that job, is Seated.** -/
theorem seatedAt_job (O : IM.Open o pol lay KL F Z Bs base c A B) (wit : W → PlaceIn Xi)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Z Bs.G₀ ++ wJobs no D Z Bs.G₀) {fs : List (Fall F.S₁)}
    {σ : Side F.S₁ F.Cl V W X Pb}
    (hσ : Side.seated F.first.blocksInOrder (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).place
      (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).row fs = some σ) :
    Seated σ (jobOver J wit) := by
  rcases List.mem_append.1 hJ with hJ | hJ
  · obtain ⟨b₀, hown, hp, hr, ho⟩ := own_of_job no D Z Bs.G₀ hJ
    exact seatedAt_own O hown J wit hp hr ho hσ
  · obtain ⟨msg, hm, rfl⟩ := w_of_job no D Z Bs.G₀ hJ
    exact seatedAt_w O wit hm (wBlock_of_msg hm) _ _ hσ

end

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.member_at_own
#print axioms OnBytes.SendSim.Seat.wJobs_some
#print axioms OnBytes.SendSim.Seat.stands_at_job
#print axioms OnBytes.SendSim.Seat.seat_at_job
#print axioms OnBytes.SendSim.Seat.seatedAt_job
