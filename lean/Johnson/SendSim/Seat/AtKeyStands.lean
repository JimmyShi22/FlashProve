-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtKeyStands.lean: in the first chain of a key file's description no two
sub-protocols are at one place; a member is at each of its three places of the kind K1 (two where
the shape has no message for W); and every side that Side.seated returns there for the sender's row
is Seated.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". There the description is the proof
file's; here it is the key file's Key.descriptionFromSource, and a link is a lookup's. Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. The statements on the description Key.descriptionFromSource Xs N Q (Johnson/Desc/Key/Desc.lean)
hold at every source Xs and all numbers N and Q, with no premise beyond those named below.
  key_places        the places of the first chain's list of sub-protocols, written out.
  key_places_apart  no two members of that list are at one place.
  key_member        for every entry x of keyPars Xs (Johnson/SendSim/Seat/AtKeyPars.lean), the list
                    has a member at x's place, and every member at that place has the rounds
                    K1.rounds x.1 and the oracle messages K1.oracles x.1.
  key_seat          part one of key_member, written as the premise seat₁ that the rule
                    file_owed_rows asks of a row's place
                    (Johnson/Desc/ProofFile/Honest/Thread/Rows.lean): the list has a member at that
                    place.
  seatedAt_key      for every entry x of keyPars Xs and every job J with J.P = x.1, whatever J's
                    first number, data and tables sent along are: every side that Side.seated
                    returns at J's place for the row sendRow J.P.place J is Seated
                    (Johnson/SendSim/At/Sim.lean).
  seated_some_key   Side.seated does return a side there, so seatedAt_key is not vacuous.
  msg_rideOwn, wKey_rideOwn   for any one-time values and groups, and for W where msg is the shape's
                    message for W (linMessageW one.lin = some msg): the table that msgFold, or
                    wFold, names is announced in the sending as that fold's fresh mask (rideOwn,
                    Johnson/Desc/ProofFile/Honest/K1/PlaceJob.lean). The announcement does not show
                    the fold's k.

How it fits. These are the parts, free of any distribution, of a statement for the key file like
Spec.fieldsAtLots (AtDescLots.lean) for the proof file: that at these places the side of the honest
sender has the fields fits and exact, and fresh if the book is clear (BookClearAny). That statement
is fieldsAtKey_all (AtKey.lean). Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

The other names. flat_places, mem_flat_first, mem_flat_front, mem_flat_back: a chain's list of
sub-protocols, by its parts. sixAt, link_places, links_places: the six places of a lookup's link.
p12At_place, k12_place, rng_place: the ranges' test is at its place at all numbers N. mem_sixAt,
sixAt_nodup, links_nodup: the links' places differ. wPlaces, w_places: the place of W's sending,
where there is one. sendW_member: W's sending has the sender's rounds and oracle messages.
tailPlaces, tail_facts: the places behind the links. block_of_seated: the sub-protocol of a side
that Side.seated returns is a member of the list.

Limits. Pointwise statements: no distribution is named. Nothing is said on a job's data, on the
number of its first new message, on which table is sent along, or on whether the job fits its place.
Among the files that this folder imports there is no honest prover of a key file in the framework of
Johnson/Desc/ProofFile/Honest/ (parts at the description's places). Only the first chain is covered,
and of its six sendings of new tables only the three at places of the kind K1 (AtKeyPars.lean,
Limits).
-/
import Johnson.SendSim.Seat.AtKeyPars
import Johnson.SendSim.Seat.Row

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open VerifiableInference.Desc.Key (groupsTold rootsAt rootsBefore lastSendRound batchRound pieces
  sendIndexMasks sendOwnMessage sendW lookupsOf lookupLink layRows rangesTest enterRanges
  leaveRanges batchTableRows firstChain FirstState rangesParams)

variable {V W X Pb : Type}

/-! ## A chain's list of sub-protocols, by its parts -/

/-- The places of a chain's list of sub-protocols. -/
theorem flat_places {S Cl : Type} (c : VerifiableInference.Desc.Chain S Cl) :
    c.blocksInOrder.map (·.place) =
      c.first.place :: c.front.map (·.place) ++ c.links.flatMap (fun L => L.blocksInOrder.map (·.place)) ++
        c.back.map (·.place) ++ [c.last.place] := by
  unfold Chain.blocksInOrder
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, List.map_flatMap]
  rfl

/-- The chain's first sub-protocol is in the list, with the test that it has no claims and no runs
behind a batching added to its test on the plan. -/
theorem mem_flat_first {S Cl : Type} (c : VerifiableInference.Desc.Chain S Cl) :
    { c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } ∈ c.blocksInOrder := by
  unfold Chain.blocksInOrder
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_cons_self ..)))

/-- Each sub-protocol of the chain's front is in the list, with the same test added. -/
theorem mem_flat_front {S Cl : Type} (c : VerifiableInference.Desc.Chain S Cl) {b : Block S Cl}
    (h : b ∈ c.front) :
    { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } ∈ c.blocksInOrder := by
  unfold Chain.blocksInOrder
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_map.2 ⟨b, h, rfl⟩))))

/-- Each sub-protocol of the chain's back is in the list, with the same test added. -/
theorem mem_flat_back {S Cl : Type} (c : VerifiableInference.Desc.Chain S Cl) {b : Block S Cl}
    (h : b ∈ c.back) :
    { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } ∈ c.blocksInOrder := by
  unfold Chain.blocksInOrder
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨b, h, rfl⟩))

/-! ## The places of the key file's first chain -/

/-- The six places of lookup number i's link. -/
def sixAt (i : Nat) : List Place :=
  [⟨1, some i, 0, .frame⟩, ⟨1, some i, 1, .frame⟩, ⟨1, some i, 2, .K3⟩, ⟨1, some i, 3, .frame⟩,
    ⟨1, some i, 4, .frame⟩, ⟨1, some i, 5, .frame⟩]

/-- A lookup's link has these six places. -/
theorem link_places (one : OneTime) (set : Setting) (i : Nat) (x : Key.Lookup) :
    (Link.blocksInOrder (lookupLink one set i x)).map (·.place) = sixAt i := rfl

/-- The places of all lookups' links. -/
theorem links_places (one : OneTime) (set : Setting) : ∀ (l : List Key.Lookup) (k : Nat),
    ((l.zipIdx k).map fun x => lookupLink one set x.2 x.1).flatMap
        (fun L => L.blocksInOrder.map (·.place)) = (List.range' k l.length).flatMap sixAt
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.flatMap_cons, List.length_cons, List.range'_succ,
      List.flatMap_cons, links_places one set l (k + 1), link_places]

/-- The parameters that are made for a place keep that place. -/
theorem p12At_place (a : Place) (x : H2U.PlaceNums) : (H2U.proximityTestParametersAt a x).place = a := by
  unfold H2U.proximityTestParametersAt
  split
  · rfl
  · split <;> rfl

/-- The proximity test is at its parameters' place. -/
theorem k12_place {T Cl : Type} (Xp : K12.Parts T) (p : K12.P12) :
    (K12.proximityTestKind (Cl := Cl) Xp p).place = p.place := by
  unfold K12.proximityTestKind
  split <;> rfl

/-- The ranges' test is at its place, at all numbers N. -/
theorem rng_place (one : OneTime) (N : H2U.PlaceNums) :
    (rangesTest (Cl := Key.Claim) (enterRanges one) leaveRanges N).place = ⟨1, none, 5, .K12⟩ := by
  exact (k12_place (Cl := Key.Claim) K12.guardedProximityTestParts (rangesParams N)).trans
    (p12At_place Key.rangesPlace N)

/-- The place of W's sending, where the shape has such a message. -/
def wPlaces (one : OneTime) : List Place :=
  if (linMessageW one.lin).isSome then [⟨1, none, 14, .K1⟩] else []

/-- W's sending is at that place. -/
theorem w_places (one : OneTime) (sent : Nat) (g : List (List Nat)) :
    (sendW (β := Key.LookupRecord) (Cl := Key.Claim) one pieces sent g).toList.map (·.place) =
      wPlaces one := by
  unfold sendW wPlaces
  cases linMessageW one.lin <;> rfl

/-- The places behind the links. -/
def tailPlaces (one : OneTime) : List Place :=
  [⟨1, none, 4, .frame⟩, ⟨1, none, 5, .K12⟩, ⟨1, none, 13, .K13⟩] ++ wPlaces one ++
    [⟨1, none, 15, .frame⟩]

/-- **The places of the first chain's list of sub-protocols.** -/
theorem key_places (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces) :
    (Key.descriptionFromSource Xs N Q).first.blocksInOrder.map (·.place) =
      ⟨1, none, 1, .K1⟩ :: ⟨1, none, 2, .K1⟩ ::
        ((List.range' 0 (lookupsOf Xs.Y.k.oneTime).length).flatMap sixAt ++
          tailPlaces Xs.Y.k.oneTime) := by
  show (firstChain Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N).blocksInOrder.map (·.place) = _
  rw [flat_places]
  have e1 : (firstChain Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N).links.flatMap
      (fun L => L.blocksInOrder.map (·.place)) =
      (List.range' 0 (lookupsOf Xs.Y.k.oneTime).length).flatMap sixAt :=
    links_places Xs.Y.k.oneTime Xs.set (lookupsOf Xs.Y.k.oneTime) 0
  have e2 : (firstChain Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N).back.map (·.place) =
      [⟨1, none, 4, .frame⟩, ⟨1, none, 5, .K12⟩, ⟨1, none, 13, .K13⟩] ++
        wPlaces Xs.Y.k.oneTime := by
    show (([layRows Xs.Y.k.oneTime, rangesTest (enterRanges Xs.Y.k.oneTime) leaveRanges N,
      batchTableRows (·.keys) Xs.Y.k.oneTime pieces _] ++
        (sendW Xs.Y.k.oneTime pieces _ _).toList : List (Block FirstState Key.Claim))).map
          (·.place) = _
    rw [List.map_append, w_places]
    show [(⟨1, none, 4, .frame⟩ : Place), (rangesTest (Cl := Key.Claim) (enterRanges Xs.Y.k.oneTime)
      leaveRanges N).place, ⟨1, none, 13, .K13⟩] ++ _ = _
    rw [rng_place]
  rw [e1, e2]
  show (((⟨1, none, 1, .K1⟩ : Place) :: [⟨1, none, 2, .K1⟩]) ++ _ ++ _) ++
    [(⟨1, none, 15, .frame⟩ : Place)] = _
  unfold tailPlaces
  simp only [List.cons_append, List.nil_append, List.append_assoc]

/-! ## No two at one place -/

/-- Each of the six places names its link. -/
theorem mem_sixAt {i : Nat} {q : Place} (h : q ∈ sixAt i) : q.link = some i := by
  simp only [sixAt, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The six places differ. -/
theorem sixAt_nodup (i : Nat) : (sixAt i).Nodup := by
  simp [sixAt]

/-- The links' places differ, and each names a link from number k on. -/
theorem links_nodup : ∀ (n k : Nat), ((List.range' k n).flatMap sixAt).Nodup ∧
    ∀ q ∈ (List.range' k n).flatMap sixAt, ∃ i, k ≤ i ∧ q.link = some i
  | 0, _ => ⟨List.nodup_nil, fun _ h => by cases h⟩
  | n + 1, k => by
    obtain ⟨h1, h2⟩ := links_nodup n (k + 1)
    rw [List.range'_succ, List.flatMap_cons]
    refine ⟨List.nodup_append.2 ⟨sixAt_nodup k, h1, fun a ha b hb e => ?_⟩, fun q hq => ?_⟩
    · obtain ⟨i, hi, hb'⟩ := h2 b hb
      have ha' := mem_sixAt ha
      rw [e, hb'] at ha'
      have : i = k := Option.some.inj ha'
      omega
    · rcases List.mem_append.1 hq with h | h
      · exact ⟨k, Nat.le_refl _, mem_sixAt h⟩
      · obtain ⟨i, hi, hq'⟩ := h2 q h
        exact ⟨i, by omega, hq'⟩

/-- The places behind the links differ, name no link, and are not the first two places. -/
theorem tail_facts (one : OneTime) :
    (tailPlaces one).Nodup ∧ (∀ q ∈ tailPlaces one, q.link = none) ∧
      (⟨1, none, 1, .K1⟩ : Place) ∉ tailPlaces one ∧
      (⟨1, none, 2, .K1⟩ : Place) ∉ tailPlaces one := by
  unfold tailPlaces wPlaces
  cases (linMessageW one.lin).isSome <;> decide

/-- **No two members of the first chain's list of sub-protocols are at one place.** -/
theorem key_places_apart (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces) :
    ((Key.descriptionFromSource Xs N Q).first.blocksInOrder.map (·.place)).Nodup := by
  rw [key_places]
  obtain ⟨l1, l2⟩ := links_nodup (lookupsOf Xs.Y.k.oneTime).length 0
  obtain ⟨t1, t2, t3, t4⟩ := tail_facts Xs.Y.k.oneTime
  have notLink : ∀ q : Place, q.link = none →
      q ∉ (List.range' 0 (lookupsOf Xs.Y.k.oneTime).length).flatMap sixAt := by
    intro q hq h
    obtain ⟨i, -, hi⟩ := l2 q h
    rw [hq] at hi
    cases hi
  refine List.nodup_cons.2 ⟨fun h => ?_, List.nodup_cons.2 ⟨fun h => ?_,
    List.nodup_append.2 ⟨l1, t1, fun a ha b hb e => notLink b (t2 b hb) (e ▸ ha)⟩⟩⟩
  · rcases List.mem_cons.1 h with h | h
    · exact absurd h (by decide)
    · rcases List.mem_append.1 h with h | h
      · exact notLink _ rfl h
      · exact t3 h
  · rcases List.mem_append.1 h with h | h
    · exact notLink _ rfl h
    · exact t4 h

/-! ## The three members -/

/-- Where the shape has a message for W, W's sending is there, at the sender's place and with the
sender's rounds and oracle messages. -/
theorem sendW_member (one : OneTime) (sent : Nat) (g : List (List Nat))
    {msg : Array OracleNotice} (hm : linMessageW one.lin = some msg) :
    ∃ b : Block FirstState Key.Claim, sendW one pieces sent g = some b ∧
      b.place = (K1.parWKey one msg g).place ∧ b.rounds = K1.rounds (K1.parWKey one msg g) ∧
      b.oracles = K1.oracles (K1.parWKey one msg g) := by
  unfold sendW
  rw [hm]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- **At each of the three places the list has a member, and every member there has the sender's
rounds and oracle messages.** -/
theorem key_member (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces) :
    ∀ x ∈ keyPars Xs,
      (∃ m ∈ (Key.descriptionFromSource Xs N Q).first.blocksInOrder, m.place = x.1.place) ∧
      ∀ m ∈ (Key.descriptionFromSource Xs N Q).first.blocksInOrder, m.place = x.1.place →
        m.rounds = K1.rounds x.1 ∧ m.oracles = K1.oracles x.1 := by
  have one_of : ∀ (P : K1.Par) (m₀ : Block FirstState Key.Claim),
      m₀ ∈ (Key.descriptionFromSource Xs N Q).first.blocksInOrder → m₀.place = P.place → m₀.rounds = K1.rounds P →
      m₀.oracles = K1.oracles P →
      (∃ m ∈ (Key.descriptionFromSource Xs N Q).first.blocksInOrder, m.place = P.place) ∧
      ∀ m ∈ (Key.descriptionFromSource Xs N Q).first.blocksInOrder, m.place = P.place →
        m.rounds = K1.rounds P ∧ m.oracles = K1.oracles P := by
    intro P m₀ hm hp hr ho
    refine ⟨⟨m₀, hm, hp⟩, fun m hm' hp' => ?_⟩
    obtain rfl : m = m₀ :=
      List.inj_on_of_nodup_map (key_places_apart Xs N Q) hm' hm (hp'.trans hp.symm)
    exact ⟨hr, ho⟩
  intro x hx
  unfold keyPars at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl) | hx
  · exact one_of _ _ (mem_flat_first (Key.descriptionFromSource Xs N Q).first) rfl rfl rfl
  · exact one_of _ _ (mem_flat_front (Key.descriptionFromSource Xs N Q).first (List.mem_singleton.2 rfl)) rfl rfl rfl
  · cases hm : linMessageW Xs.Y.k.oneTime.lin with
    | none =>
      rw [hm] at hx
      cases hx
    | some msg =>
      rw [hm] at hx
      obtain rfl := List.mem_singleton.1 hx
      obtain ⟨b, hb, hbp, hbr, hbo⟩ := sendW_member Xs.Y.k.oneTime
        (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1))
        (groupsTold Xs.Y.told.1 (rootsBefore Xs.Y.D.1 (lastSendRound Xs.Y.D.1))
          (rootsAt Xs.Y.D.1 (lastSendRound Xs.Y.D.1))) hm
      have hmem : b ∈ (firstChain Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N).back := by
        show b ∈ [layRows Xs.Y.k.oneTime, rangesTest (enterRanges Xs.Y.k.oneTime) leaveRanges N,
          batchTableRows (·.keys) Xs.Y.k.oneTime pieces _] ++
            (sendW Xs.Y.k.oneTime pieces _ _).toList
        rw [hb]
        exact List.mem_append_right _ (List.mem_singleton.2 rfl)
      exact one_of _ _ (mem_flat_back (firstChain Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N)
        hmem) hbp hbr hbo

/-- Part one of key_member, written as the rule's premise on a row's place: the list has a member at
that place. -/
theorem key_seat (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces) :
    ∀ x ∈ keyPars Xs,
      (Key.descriptionFromSource Xs N Q).first.blocksInOrder.any (fun b => b.place == x.1.place) = true := by
  intro x hx
  obtain ⟨m, hm, hp⟩ := (key_member Xs N Q x hx).1
  exact List.any_eq_true.2 ⟨m, hm, beq_iff_eq.2 hp⟩

/-- The sub-protocol of a side that Side.seated returns is a member of the list. -/
theorem block_of_seated {S Cl : Type} {bs : List (Block S Cl)} {a : Place}
    {row : List (ProofFile.Honest.Part V W X × Sim Pb)} {fs : List (Fall S)} {σ : Side S Cl V W X Pb}
    (h : Side.seated bs a row fs = some σ) : σ.block ∈ bs := by
  unfold Side.seated at h
  cases hb : bs.find? fun b => b.place == a with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    cases h
    exact List.mem_of_find?_eq_some hb

/-- **Every side that Side.seated returns at one of the three places, for the sender's row at any
job whose public numbers are the place's, is Seated.** -/
theorem seatedAt_key (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces)
    {x : K1.Par × (Nat → Option Ride)} (hx : x ∈ keyPars Xs) {J : SendJob W X} (hJ : J.P = x.1)
    {fs : List (Fall (Key.descriptionFromSource Xs N Q).S₁)}
    {σ : Side (Key.descriptionFromSource Xs N Q).S₁ (Key.descriptionFromSource Xs N Q).Cl V W X Pb}
    (hσ : Side.seated (Key.descriptionFromSource Xs N Q).first.blocksInOrder (sendRow (V := V) (Pb := Pb) J.P.place J).place
      (sendRow J.P.place J).row fs = some σ) : Seated σ J := by
  have hp : σ.block.place = J.P.place := place_of_seated hσ
  obtain ⟨hr, ho⟩ := (key_member Xs N Q x hx).2 σ.block (block_of_seated hσ) (hJ ▸ hp)
  exact seated_at hσ (hJ ▸ hr) (hJ ▸ ho)

/-- **Side.seated returns a side at the place of each entry of keyPars Xs**, for the sender's row at
any job whose public numbers are the entry's. So seatedAt_key is not vacuous. -/
theorem seated_some_key (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces)
    {x : K1.Par × (Nat → Option Ride)} (hx : x ∈ keyPars Xs) {J : SendJob W X} (hJ : J.P = x.1)
    (fs : List (Fall (Key.descriptionFromSource Xs N Q).S₁)) :
    ∃ σ : Side (Key.descriptionFromSource Xs N Q).S₁ (Key.descriptionFromSource Xs N Q).Cl V W X Pb,
      Side.seated (Key.descriptionFromSource Xs N Q).first.blocksInOrder (sendRow (V := V) (Pb := Pb) J.P.place J).place
        (sendRow J.P.place J).row fs = some σ := by
  obtain ⟨m, hm, hp⟩ := (key_member Xs N Q x hx).1
  have hpl : m.place = (sendRow (V := V) (Pb := Pb) J.P.place J).place := by
    rw [hp, ← hJ]
    rfl
  have h2 : (Side.seated (V := V) (Pb := Pb) (Key.descriptionFromSource Xs N Q).first.blocksInOrder
      (sendRow (V := V) (Pb := Pb) J.P.place J).place
      (sendRow (V := V) (Pb := Pb) J.P.place J).row fs).isSome := by
    unfold Side.seated
    rw [Option.isSome_map]
    exact List.find?_isSome.2 ⟨m, hm, beq_iff_eq.2 hpl⟩
  exact Option.isSome_iff_exists.1 h2

/-! ## The tables that are sent along -/

/-- The table that msgFold names is announced as that fold's fresh mask. -/
theorem msg_rideOwn (one : OneTime) (g : List (List Nat)) :
    rideOwn (K1.parMsg one g) (msgFold one.ranges) = true := by
  unfold rideOwn msgFold
  rw [K1.sendingPar_sent]
  unfold Wf.messageOf
  cases one.ranges.stages.head? with
  | none => rfl
  | some t =>
    cases one.ranges.choice.masksRide with
    | false => rfl
    | true => simp

/-- The table that wFold names is announced as that fold's fresh mask. -/
theorem wKey_rideOwn (one : OneTime) (msg : Array OracleNotice) (g : List (List Nat))
    (h : linMessageW one.lin = some msg) :
    rideOwn (K1.parWKey one msg g) (wFold one.lin) = true := by
  unfold rideOwn
  rw [K1.sendingPar_sent]
  rcases w_says one.lin msg h with ⟨_, e⟩ | ⟨s, _, _, e, hn⟩
  · rw [e]
    rfl
  · rw [e]
    show (msg[if one.lin.ownSplitNeeded then 2 else 1]? == _) = true
    rw [hn]
    exact beq_self_eq_true _

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.flat_places
#print axioms OnBytes.SendSim.Seat.link_places
#print axioms OnBytes.SendSim.Seat.links_places
#print axioms OnBytes.SendSim.Seat.rng_place
#print axioms OnBytes.SendSim.Seat.key_places
#print axioms OnBytes.SendSim.Seat.links_nodup
#print axioms OnBytes.SendSim.Seat.tail_facts
#print axioms OnBytes.SendSim.Seat.key_places_apart
#print axioms OnBytes.SendSim.Seat.sendW_member
#print axioms OnBytes.SendSim.Seat.key_member
#print axioms OnBytes.SendSim.Seat.key_seat
#print axioms OnBytes.SendSim.Seat.block_of_seated
#print axioms OnBytes.SendSim.Seat.seatedAt_key
#print axioms OnBytes.SendSim.Seat.seated_some_key
#print axioms OnBytes.SendSim.Seat.msg_rideOwn
#print axioms OnBytes.SendSim.Seat.wKey_rideOwn
