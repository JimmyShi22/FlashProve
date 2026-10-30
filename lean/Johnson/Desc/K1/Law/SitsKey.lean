-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/SitsKey.lean: THE ROW K01_sits AT THE KIND K1's FIVE PLACES OF A KEY FILE's
DESCRIPTION (`Key.descriptionFromSource X N P`, Johnson/Desc/Key/Desc.lean): the first chain's ⟨1, none, 1 | 2 | 14,
.K1⟩ and the shared chain's ⟨2, none, 2 | 5, .K1⟩: the seat, the wrappers' yes, the numbers.

Statements and proofs. one := X.Y.k.oneTime: the first chain's public values as read back; z := the
sizes of the key as the planner made them; kq X P: the shared chain's parameters.
Main names:
  andThen_yes: a yes of two blocks laid as one gives the first one's yes at its own rounds, and the
    second one's behind it. sendingSeat_yes: THE WRAPPER of the first chain: a yes of
    `Key.sendingSeat n P` gives a yes of the kind's own block `K1.sendOwn P` at the same rounds.
  key_first_seats: THE SEATS: the chain's first block is `sendIndexMasks`, its front is
    `[sendOwnMessage]`, entry 3 of its back is `sendW`'s value: each is `sendingSeat` at
    `sendingPar one ‹piece› …`, joined with steps without a round; idx_yes · msg_yes · w_yes: so a
    yes of each gives a yes of `K1.sendOwn` at these parameters. idx_place · msg_place ·
    sendW_there: each bears the kind K1's place.
  **k01_sits_key_shared**: the shared chain's two places, seat and numbers: `PlaceOk 0 1 0` ·
    `PlaceOk 0 1 1`: under hz alone: the sized key in the source's chains is the written value
    `keyFull`.
  **k01_sits_key_first**: the numbers at the first chain's three: `PlaceOk 0 0 0` · `0 0 1` ·
    `0 0 5`: under hz (z = keyFull) and FOUR EQUATIONS between what is read back and what was
    sized (TiesKey one z).
  sourceOf_chains: the chains of the source that `Key.sourceOf` makes are the maker's structure's.
THE PREMISES, BY NAME: hz · TiesKey one z: one.codes = z.codes · one.indexMasks = z.once.input ·
one.ranges = z.ranges.x · one.lin = z.once.shape. All are paid in the goals' scope, at a source that
`Key.sourceOf` makes and whose description passes its tests on the plan, by another house's laws:
Johnson/Desc/K1/Law/SitsKeyScope.lean.
What is not claimed. The fourteen code switches of the key file's four proximity tests: rounds
inside one block each of another kind's. No soundness, no completeness and no hiding is claimed.
It holds no coding theory.

-/
import Johnson.Desc.K1.Law.SitsShared
import Johnson.Goal.Numbers.K01KeyAt
import Johnson.Desc.Key.Desc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Plan Johnson.G Desc.Plain
open VerifiableInference.Desc (Block Chain Claim)
open _root_.Desc.K14 (P14 St parK1 withU withOmega blocksOr)
open VerifiableInference.Desc.Key (Source LaterPlaces sharedPar beforeSharedPoint sharedTests
  sendingSeat sendingPar sendIndexMasks sendOwnMessage sendW pieces groupsTold rootsAt rootsBefore
  lastSendRound batchRound FirstState ChainState withLoc)

/-! ## The wrappers -/

/-- A yes of two blocks laid as one. -/
theorem andThen_yes {T C : Type} (n : String) (p q : Block T C) {s t : T} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (p.andThen n q).decide s rs gs = .ok t) :
    ∃ m, p.decide s (rs.take p.rounds.length) (gs.take p.openings) = .ok m ∧
      q.decide m (rs.drop p.rounds.length) (gs.drop p.openings) = .ok t := by
  have h' : (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind
      (fun m => q.decide m (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok t := h
  cases hk : p.decide s (rs.take p.rounds.length) (gs.take p.openings) with
  | error e =>
    rw [hk] at h'
    cases h'
  | ok m =>
    rw [hk] at h'
    exact ⟨m, rfl, h'⟩

/-- **THE FIRST CHAIN's WRAPPER's YES.** -/
theorem sendingSeat_yes {β C : Type} (n : String) (P : Par) {s t : ChainState β}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (sendingSeat (Cl := C) n P).decide s rs gs = .ok t) :
    ∃ y : Owing (DState (Array Nat)),
      (sendOwn (Cl := C) P).decide { owed := s.debt, held := withLoc s.d #[] } rs gs = .ok y ∧
      t = { s with d := withLoc y.held (), owed := y.owed, sent := y.held.loc } := by
  have h' : ((sendOwn (Cl := C) P).decide { owed := s.debt, held := withLoc s.d #[] } rs gs).map
      (fun y => { s with d := withLoc y.held (), owed := y.owed, sent := y.held.loc }) = .ok t := h
  cases hk : (sendOwn (Cl := C) P).decide { owed := s.debt, held := withLoc s.d #[] } rs gs with
  | error e =>
    rw [hk] at h'
    cases h'
  | ok y =>
    rw [hk] at h'
    exact ⟨y, rfl, (Except.ok.inj h').symm⟩

/-! ## The first chain's three seats -/

/-- K1's parameters at the three places. -/
abbrev parIdx (one : OneTime) (g : List (List Nat)) : Par :=
  sendingPar one pieces.idx "the index masks" #[one.indexMasks] g

abbrev parMsg (one : OneTime) (g : List (List Nat)) : Par :=
  sendingPar one pieces.msg "the lookups' own message and what rides with it"
    (Wf.messageOf one.ranges) g

abbrev parWKey (one : OneTime) (msg : Array OracleNotice) (g : List (List Nat)) : Par :=
  sendingPar one pieces.w "W and what rides with it" msg g

/-- Entry 3 behind three. -/
theorem three_then {α : Type} (a b c : α) (o : Option α) : ([a, b, c] ++ o.toList)[3]? = o := by
  cases o <;> rfl

/-- **THE SEATS, IN THE DESCRIPTION's OWN CHAIN.** -/
theorem key_first_seats (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) :
    (Key.descriptionFromSource X N P).first.first = sendIndexMasks X.Y.k.oneTime pieces
        (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0)) ∧
      (Key.descriptionFromSource X N P).first.front = [sendOwnMessage X.Y.k.oneTime pieces
                         (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 2) (rootsAt X.Y.D.1 2))] ∧
      (Key.descriptionFromSource X N P).first.back[3]? = sendW X.Y.k.oneTime pieces
        (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
        (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1))
          (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) := by
  exact ⟨rfl, rfl, three_then _ _ _ _⟩

theorem idx_place {β C : Type} (one : OneTime) (g : List (List Nat)) :
    (sendIndexMasks (β := β) (Cl := C) one pieces g).place = ⟨1, none, 1, .K1⟩ := rfl

theorem msg_place {β C : Type} (one : OneTime) (g : List (List Nat)) :
    (sendOwnMessage (β := β) (Cl := C) one pieces g).place = ⟨1, none, 2, .K1⟩ := rfl

/-- A yes at "idx.1.send" gives the kind's own block's yes. -/
theorem idx_yes {β C : Type} (one : OneTime) (g : List (List Nat)) {s t : ChainState β}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (sendIndexMasks (Cl := C) one pieces g).decide s rs gs = .ok t) :
    ∃ rs' gs' y, (sendOwn (Cl := C) (parIdx one g)).decide
      { owed := s.debt, held := withLoc s.d #[] } rs' gs' = .ok y := by
  obtain ⟨m, h1, -⟩ := andThen_yes _ _ _ h
  obtain ⟨y, hy, -⟩ := sendingSeat_yes _ _ h1
  exact ⟨_, _, y, hy⟩

/-- A yes at "msg.1.send" gives the kind's own block's yes. -/
theorem msg_yes {β C : Type} (one : OneTime) (g : List (List Nat)) {s t : ChainState β}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (sendOwnMessage (Cl := C) one pieces g).decide s rs gs = .ok t) :
    ∃ rs' gs' y, (sendOwn (Cl := C) (parMsg one g)).decide
      { owed := s.debt, held := withLoc s.d #[] } rs' gs' = .ok y := by
  obtain ⟨m, h1, -⟩ := andThen_yes _ _ _ h
  obtain ⟨y, hy, -⟩ := sendingSeat_yes _ _ h1
  exact ⟨_, _, y, hy⟩

/-- A yes at "w.1.send" gives the kind's own block's yes, at the shape's message with W. -/
theorem w_yes {β C : Type} (one : OneTime) (sent : Nat) (g : List (List Nat))
    {b : Block (ChainState β) C} (hb : sendW one pieces sent g = some b) {s t : ChainState β}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (h : b.decide s rs gs = .ok t) :
    ∃ msg, linMessageW one.lin = some msg ∧ b.place = ⟨1, none, 14, .K1⟩ ∧
      ∃ s' : ChainState β, ∃ rs' gs' y, (sendOwn (Cl := C) (parWKey one msg g)).decide
        { owed := s'.debt, held := withLoc s'.d #[] } rs' gs' = .ok y := by
  unfold sendW at hb
  cases hm : linMessageW one.lin with
  | none =>
    rw [hm] at hb
    cases hb
  | some msg =>
    rw [hm] at hb
    obtain rfl := Option.some.inj hb
    refine ⟨msg, rfl, rfl, ?_⟩
    obtain ⟨m1, h1, -⟩ := andThen_yes _ _ _ h
    obtain ⟨m2, h2, -⟩ := andThen_yes _ _ _ h1
    obtain ⟨m3, -, h3⟩ := andThen_yes _ _ _ h2
    obtain ⟨y, hy, -⟩ := sendingSeat_yes _ _ h3
    exact ⟨m3, _, _, y, hy⟩

/-- Where the shape has a message with W, "w.1.send" is there, at the kind's place. -/
theorem sendW_there {β C : Type} (one : OneTime) (sent : Nat) (g : List (List Nat))
    {msg : Array OracleNotice} (hm : linMessageW one.lin = some msg) :
    ∃ b : Block (ChainState β) C, sendW one pieces sent g = some b ∧
      b.place = ⟨1, none, 14, .K1⟩ := by
  unfold sendW
  rw [hm]
  exact ⟨_, rfl, rfl⟩

/-! ## The numbers -/

theorem sendingPar_sent (one : OneTime) (piece : Nat) (what : String) (msg : Array OracleNotice)
    (g : List (List Nat)) : (sendingPar one piece what msg g).sent = msg := by
  simp [sendingPar, Par.sent]

/-- What is read back is what the planner sized: four equations. -/
structure TiesKey (one : OneTime) (z : KeySized) : Prop where
  codes : one.codes = z.codes
  idx : one.indexMasks = z.once.input
  ranges : one.ranges = z.ranges.x
  lin : one.lin = z.once.shape

/-- **THE FIRST CHAIN's THREE: THE NUMBERS.** -/
theorem k01_sits_key_first {one : OneTime} {z : KeySized} (hz : z = Lk6.AtPlan.keyFull)
    (T : TiesKey one z) (g0 g1 g2 : List (List Nat)) :
    PlaceOk 0 0 0 (parIdx one g0) ∧ PlaceOk 0 0 1 (parMsg one g1) ∧
      ∃ msg, linMessageW one.lin = some msg ∧ PlaceOk 0 0 5 (parWKey one msg g2) := by
  subst hz
  have hk : keySent Lk6.AtPlan.keyFull 0 = some (sentOf 0 0) := key_sent (by decide)
  have hk' : keySent0 Lk6.AtPlan.keyFull = some (sentOf 0 0) := hk
  unfold keySent0 at hk'
  cases hw : linMessageW Lk6.AtPlan.keyFull.once.shape with
  | none =>
    rw [hw] at hk'
    cases hk'
  | some w =>
    have hL : keySent Lk6.AtPlan.keyFull 0 = some
        ([Lk6.AtPlan.keyFull.once.input] ::
          (Wf.messageOf Lk6.AtPlan.keyFull.ranges.x).toList ::
          (switchesOf 1 Lk6.AtPlan.keyFull.ranges.x.stages ++ [w.toList])) := by
      show keySent0 _ = _
      unfold keySent0
      rw [hw]
      rfl
    have hlen : (switchesOf 1 Lk6.AtPlan.keyFull.ranges.x.stages).length = 3 := by
      have e := Option.some.inj (hL.symm.trans hk)
      have e2 := congrArg List.length e
      have e3 : (sentOf 0 0).length = 6 := by decide +kernel
      rw [e3] at e2
      simp only [List.length_cons, List.length_append, List.length_nil] at e2
      omega
    refine ⟨placeOk_key (c := 0) (k := 0) (by decide) hL rfl _ T.codes ?_,
      placeOk_key (c := 0) (k := 1) (by decide) hL rfl _ T.codes ?_,
      w, by rw [T.lin]; exact hw,
      placeOk_key (c := 0) (k := 5) (by decide) hL (s := w.toList) ?_ _ T.codes ?_⟩
    · rw [sendingPar_sent, T.idx]
    · rw [sendingPar_sent, T.ranges]
    · show ((switchesOf 1 Lk6.AtPlan.keyFull.ranges.x.stages ++ [w.toList]))[3]? = _
      rw [List.getElem?_append_right (by omega), hlen]
      rfl
    · rw [sendingPar_sent]

/-! ## The shared chain's two -/

/-- The key file's shared chain's parameters. -/
abbrev kq (X : Source) (P : LaterPlaces) : P14 := sharedPar X.chains (beforeSharedPoint P)

/-- **THE SEAT, IN THE DESCRIPTION's OWN LIST.** -/
theorem k01_sits_key_shared_seat (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {u : Array OracleNotice} (hu : withU (kq X P).S = some u) :
    (Key.descriptionFromSource X N P).shared.back[1]? = some (sendU (kq X P) u).retype ∧
      (Key.descriptionFromSource X N P).shared.back[4]? = some (sendOm (kq X P)).retype := by
  obtain ⟨h1, h4⟩ := blocksOr_sends (kq X P) hu (sharedTests P)
  exact ⟨map_retype _ 1 _ h1, map_retype _ 4 _ h4⟩

/-- The chains of the source that `Key.sourceOf` makes are the maker's structure's. -/
theorem sourceOf_chains {m : Johnson.G.OfPlan.Made} {X : Source} (h : Key.sourceOf m = .ok X) :
    X.chains = m.p.chains := by
  unfold Key.sourceOf at h
  obtain ⟨D, _, h⟩ := OnBytes.Params.exc_bind h
  obtain ⟨T, _, h⟩ := OnBytes.Params.exc_bind h
  cases h
  rfl

/-- **SEAT AND NUMBERS AT THE SHARED CHAIN's TWO PLACES.** -/
theorem k01_sits_key_shared (X : Source) (hz : X.chains.made.sized.key = Lk6.AtPlan.keyFull)
    (N : H2U.PlaceNums) (P : LaterPlaces) :
    ∃ u, withU (kq X P).S = some u ∧
      (Key.descriptionFromSource X N P).shared.back[1]? = some (sendU (kq X P) u).retype ∧
      PlaceOk 0 1 0 (parK1 (kq X P) 2 "o_u and the first mask" u) ∧
      (Key.descriptionFromSource X N P).shared.back[4]? = some (sendOm (kq X P)).retype ∧
      PlaceOk 0 1 1 (parK1 (kq X P) 5 "o_omega and o_sp" (withOmega (kq X P).S)) := by
  have hk : keySent Lk6.AtPlan.keyFull 1 = some (sentOf 0 1) := key_sent (by decide)
  have hS : (kq X P).S = Lk6.AtPlan.keyFull.once.shape := by
    show X.chains.made.sized.key.once.shape = _
    rw [hz]
  have hC : (kq X P).codes = Lk6.AtPlan.keyFull.codes := by
    show X.chains.made.sized.key.codes = _
    rw [hz]
  have hk' : sharedSent Lk6.AtPlan.keyFull.once.shape = some (sentOf 0 1) := hk
  cases hu : withU Lk6.AtPlan.keyFull.once.shape with
  | none =>
    unfold sharedSent at hk'
    rw [hu] at hk'
    cases hk'
  | some u =>
    have hL : keySent Lk6.AtPlan.keyFull 1 = some (u.toList ::
        (withOmega Lk6.AtPlan.keyFull.once.shape).toList ::
        (switchesOf 1 Lk6.AtPlan.keyFull.once.shape.testU ++
          switchesOf 1 Lk6.AtPlan.keyFull.once.shape.testOmega)) := by
      show sharedSent _ = _
      unfold sharedSent
      rw [hu]
      rfl
    have hu' : withU (kq X P).S = some u := by rw [hS]; exact hu
    obtain ⟨s1, s4⟩ := k01_sits_key_shared_seat X N P hu'
    refine ⟨u, hu', s1,
      placeOk_key (c := 1) (k := 0) (by decide) hL rfl _ hC (by rw [parK1_sent]), s4,
      placeOk_key (c := 1) (k := 1) (by decide) hL rfl _ hC (by rw [parK1_sent, hS])⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.andThen_yes
#print axioms VerifiableInference.Desc.K1.sendingSeat_yes
#print axioms VerifiableInference.Desc.K1.three_then
#print axioms VerifiableInference.Desc.K1.key_first_seats
#print axioms VerifiableInference.Desc.K1.idx_place
#print axioms VerifiableInference.Desc.K1.msg_place
#print axioms VerifiableInference.Desc.K1.idx_yes
#print axioms VerifiableInference.Desc.K1.msg_yes
#print axioms VerifiableInference.Desc.K1.w_yes
#print axioms VerifiableInference.Desc.K1.sendW_there
#print axioms VerifiableInference.Desc.K1.sendingPar_sent
#print axioms VerifiableInference.Desc.K1.k01_sits_key_first
#print axioms VerifiableInference.Desc.K1.k01_sits_key_shared_seat
#print axioms VerifiableInference.Desc.K1.sourceOf_chains
#print axioms VerifiableInference.Desc.K1.k01_sits_key_shared
