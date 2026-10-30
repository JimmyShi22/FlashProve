-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY FILLING: at any thread, and at any prover whose first list finds the lookup's seated row at a
site's place. No filling and no maker is named.

Johnson/Desc/ProofFile/Honest/K3/Term/LookupPlaysAndIsAccepted.lean: the honest side of the kind
"lookup" (K3): two of the five statements that Honest/Thread/PaysS.lean asks at a member of a chain,
`PlaysS T Said b` and `AcceptedS T Said fall b`, at each of the lookups' borders of the proof file's
first chain, with the thread T, the second condition Said and the letter fall variables.

Terms. Honest/K3/GLOSSARY.md: thread, border, half (side), seat, site, member, step, promise in
front. "The pair" is `ThrS T Said b` (Honest/Thread/Said.lean): the thread's invariant together with
Said.

What is shown.

  1  At any thread over the first chain's state, from the pair.
  `LookupPromiseInFront`, `LookupHeadReturns`: (definitions) the two hypotheses on the thread: at
    every stand of the pair the lookup's promise in front holds and the state bears no mark; at the
    digits of the head's link alone, the step without a round behind the lookup returns. They are
    the fields front and headReturns of `K3AtSite` (Honest/K3/Law/Thread/AtThreadSite.lean), asked
    from the pair in place of the invariant alone: weaker hypotheses.
  `LookupSeatedAtThePair`: (structure) the seat: the seven hypotheses of `K3PlaysAt`
    (Honest/K3/Law/Thread/PlaysAnyState.lean) as one field, the site, the lot's sub-protocol, the
    member, two tests on public data, and the two hypotheses above.
  `lookupSeatedOfAtSite`: `K3AtSite` gives the seat, at every Said.
  `LookupJoinsFromThePair`: (definition) the text of the field joins of `K3SeatedS`
    (PlaysAnyState.lean), asked from the pair; at any type of state.
  `lookupJoinsAtThePair`: where the description returns, the seat gives the join.
  `lookupPlaysOfTheSeven`: `K3PlaysAt` gives `PlaysS`, at every Said; at any type of state.
  `lookupIsAcceptedOfTheJoin`: `K3PlaysAt` and the join give `AcceptedS`, at every fall; at any type
    of state.
  `lookupIsAcceptedAtThePair`: where the description returns, the seat gives `AcceptedS`.

  2  Under the head `P5J.AtMgA`, at the written number of a site's border.
  `ThreadIsTheMakers`: (structure) six equations on the thread: its face, chain's number, first
    tree, members, sides, and that no round is ahead of the chain.
  `LookupPublicTests`: (structure) three tests with code on public data, each a field.
  `lookupSevenAtEveryBorder`: the seven, from the six equations, the side found at the site's place
    and the first of the three tests.
  `lookupPlaysAtEveryBorder`: so `PlaysS`, at every Said.
  `lookupSeatedAtEveryBorder`, `lookupJoinsAtEveryBorder`, `lookupIsAcceptedAtEveryBorder`: the
    seat, the join and `AcceptedS` at every fall, from these, the three tests and the two hypotheses
    on the thread.
  `lookupHeadReturnsButAtOne`: `LookupHeadReturns` holds, emptily, on the calls and off link 24.

  3  At the first chain's letters `lettersAt` and `lettersHead` (Honest/Thread/FirstAt.lean,
  FirstHead.lean), at every value of their arguments.
  `lookupPromiseInFrontAtLettersAt`: the promise in front holds there, from the invariant alone.
  `threadIsTheMakersAtLettersHead`: the six equations hold there, by rfl.
  `lookupPlaysAtLettersHead`, `lookupJoinsAtLettersHead`, `lookupIsAcceptedAtLettersHead`: the three
    there.

Hypotheses that remain, in the theorems of 2 and 3.
  `h`: the head. `hsite`: s is a site of the public part.
  `hSide`: the prover's first list finds, at the site's place, the seated row `proverSideOfLookupInChainAtOneOwner` at summands
    J and a reader wit, both variables.
  `baseIsTheChainsCount`: the site's number of rounds in front is the chain's own count: the first
    clause of `siteFits` (Honest/K3/Law/SiteFits.lean). Its second clause, on the round named RNG,
    is not asked here.
  `shapeIsTheLayouts`, `usedIsThePlans`: for the join and the acceptance alone.
  `LookupHeadReturns`: for the join and the acceptance, at the digits of link 24 alone.
  In 2 also `ThreadIsTheMakers` and `LookupPromiseInFront`.

On the letter fall. No hypothesis ties it: the acceptance is shown at all challenges that pass the
frame's test `drawsFit`. The member's own decision (Johnson/Desc/First/Look/K3Lookup.lean, `block`) asks
four things of the state in front and that the hearing returns; that it returns on the rounds that
the row plays, at all such challenges, is part of what the join holds.

Limits. All statements are implications. "At every border" is said here of every listed site: that
the sites cover the fifty borders, that the three tests accept, and an instance of the hypotheses
stand in Honest/K3/Term/LookupPlaysAndIsAcceptedAtAllFifty.lean, at the base prover. The acceptance is said at any
summands: it says nothing on values. `PlaysS` and `AcceptedS` are forms of hypothesis of the
frame's. The theorems of 2 and 3 stand at the full size alone (the written list of places). Of the
six equations of `ThreadIsTheMakers` the proofs read three: the members, the sides, nothing ahead.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ThinRest
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.PlaysAnyState
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtThreadSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CallerAtLink
import Johnson.Desc.ProofFile.Honest.K3.Law.LotOfSite
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.AtFull.Shape.FaceAtSites

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription Place Strs)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf k3OnIn pieceAt)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First (pubSets flatPlacesOf blockPlaces)
open VerifiableInference.Desc.First.Look (placeAt sameShape)
open VerifiableInference.Desc.Sound (mgAll mgBase mgAll_more_closed linksFull MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf k3_open_calls k3_open_digits)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt lettersHead Script WtF)
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Law.AtThr

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 At any thread, from the pair -/

section
variable {Bk : ProverCoinCounts} {S Cl V W X Pb Wj : Type} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **The join, asked from the pair**: the text of the field joins of `K3SeatedS`, with `ThrS T Said
b` in place of `Thr T b`. At any type of state. A definition, meant as a hypothesis. -/
def LookupJoinsFromThePair (b : Nat) (a : At) (J : LookJobs Wj) (wit : W → Wj) (first : Nat)
    (fork : S → Option Fork) (Q : S → S → HeardV → Fork → Prop) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (s : S) (m : Mid W X) (E : Env)
    (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V) (X₁ := X) ⟨ptsOf, pointsAt⟩ J wit a).parts),
    ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
    ∃ F, fork s = some F ∧ JoinedAtS blk a J wit (T.φ.sees m.st.input) m ds c first s F T.chain
      T.ft (fun _ _ => none) (fun _ => none) (Q s)

variable {T Said}
variable {b : Nat} {a : At} {J : LookJobs Wj} {wit : W → Wj} {es : List Fmt.Entry} {first : Nat}
  {fork : S → Option Fork} {Q : S → S → HeardV → Fork → Prop}

/-- **It plays, from the pair**, at every Said and at any type of state. Conditional on
`K3PlaysAt`. -/
theorem lookupPlaysOfTheSeven (hSeven : K3PlaysAt T b a J wit es) : PlaysS T Said b :=
  playsS_of T Said (plays_k3S hSeven)

/-- **It is accepted, from the pair**, at every letter fall and at any type of state. Conditional on
`K3PlaysAt` and the join. A lemma; it does not show the acceptance: the join holds the member's own
accepting step. -/
theorem lookupIsAcceptedOfTheJoin (hSeven : K3PlaysAt T b a J wit es)
    (hJoin : LookupJoinsFromThePair T Said b a J wit first fork Q)
    (fall : Nat → S → List Fmt.Drawn → Option String) : AcceptedS T Said fall b := by
  intro blk hb k s m E ds y cols hA hd _ _ hM
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  have hl' := hl
  obtain ⟨_, _, c, _, rfl⟩ := chainSteps_one Bk _ _ _ blk T.hs _ (hSeven.half blk hb) l hl
  obtain ⟨F, _, y', t, g, G, hy', _, _, _, hstep, _⟩ := hJoin blk hb k s m E ds c hA hd
  obtain rfl : y' = y := Except.ok.inj (hy'.symm.trans hy)
  have hc0 : cols = [] := by
    have hc' := hc
    rw [hSeven.rounds blk hb, readsOf_plain] at hc'
    exact (Except.ok.inj hc').symm
  subst hc0
  exact ⟨t, ⟨⟨_, hl', hy⟩, hc⟩, hstep⟩

end

section
variable {Bk : ProverCoinCounts} {V W X Pb Wj : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **From the pair in front: the lookup's promise in front, and no mark.** A definition, meant as a
hypothesis on the thread and on Said. -/
def LookupPromiseInFront (b : Nat) (s : Site) : Prop :=
  ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), ThrS T Said b k st m E →
    k3OnIn s.p st = true ∧ st.failed = none

/-- **At the digits of the head's link alone: at a stand of the pair, the step without a round
behind the lookup returns** at the state that the lookup's own decision leaves. A definition, meant
as a hypothesis on the thread and on Said; it is other kinds' to show. -/
def LookupHeadReturns (b : Nat) (Z : Pub) (s : Site) : Prop :=
  s.digits = true → s.caller = .head → ∀ (k : Coins Bk) (st : FS) (m : Mid W X)
    (E : Env) (F : Fork) (rs : List Fmt.RoundView) (g : HeardV) (G : Fork) (s' : FS),
    ThrS T Said b k st m E →
    (seatOf K3Lot.ofForm s.digits).fork st = some F → rs.length = (s.p.entries.getD []).length →
    hearV (faceOf s.shape) F rs = some (g, G) →
    decideVia (seatOf K3Lot.ofForm s.digits) s.p st rs = .ok s' → ∃ t, HeadBehind Z.p.X s' t

/-- **The seat of a lookup at the description's own member, from the pair.** Here b is the member's
number; Z, Bs and ch are the description's public part, its base and its first chain; s is the
lookup; lot is the lookups' own sub-protocol at its place; J and wit are the summands and the seat's
reader of the input. -/
structure LookupSeatedAtThePair (b : Nat) (Z : Pub) (Bs : PureBase) (ch : Chain FS ProofFile.Cl)
    (s : Site) (lot : Block FS ProofFile.Cl) (J : LookJobs Wj) (wit : W → Wj) : Prop where
  /-- the side found, the member's place, rounds and oracle messages, two tests, the rounds in
  front -/
  theSeven : K3PlaysAt T b s.at_ J wit (s.p.entries.getD [])
  siteOfThePublicPart : s ∈ lookSites Z
  blockOfTheLot : lot ∈ (K3Lot.lot Z).blocks Bs.G₀
  blockAtTheSite : lot.place = s.at_.place
  memberOfTheChain : ∀ blk, T.bs[b]? = some blk → blk ∈ ch.blocksInOrder
  memberPassesThePlan : ∀ blk, T.bs[b]? = some blk → blk.planOk = true
  shapeIsTheLayouts : (s.digits || s.caller != .layers || sameShape s.shape Z.p.X.y.fo) = true
  usedIsThePlans : (!s.digits || s.caller == .head ||
    usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true
  promiseInFront : LookupPromiseInFront T Said b s
  headReturns : LookupHeadReturns T Said b Z s

variable {T}
variable {b : Nat} {Z : Pub} {Bs : PureBase} {ch : Chain FS ProofFile.Cl} {s : Site}
  {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : W → Wj}

/-- **`K3AtSite` gives the seat**, at every Said. -/
theorem lookupSeatedOfAtSite (hS : K3AtSite T b Z Bs ch s lot J wit) :
    LookupSeatedAtThePair T Said b Z Bs ch s lot J wit where
  theSeven := ⟨hS.half, fun blk hb => (hS.place blk hb).trans hS.lotPlace, hS.rounds, hS.oracles,
    hS.ok, hS.entries, hS.base⟩
  siteOfThePublicPart := hS.site
  blockOfTheLot := hS.inLot
  blockAtTheSite := hS.lotPlace
  memberOfTheChain := hS.mem
  memberPassesThePlan := hS.plan
  shapeIsTheLayouts := hS.shapeIs
  usedIsThePlans := hS.usedIs
  promiseInFront := fun k st m E hA => hS.front k st m E hA.1
  headReturns := fun h1 h2 k st m E F rs g G s' hA => hS.headReturns h1 h2 k st m E F rs g G s' hA.1

variable {Said}

/-- **The seat gives the join**: at every stand of the pair the row's play, the hearing from the
ledger that the state itself holds, and the member's own step go through together. Conditional on
the description's return. -/
theorem lookupJoinsAtThePair (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst)
    (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B)
    (hS : LookupSeatedAtThePair T Said b Z Bs ch s lot J wit) :
    LookupJoinsFromThePair T Said b s.at_ J wit s.p.first (seatOf K3Lot.ofForm s.digits).fork
      (OneQ K3Lot.ofForm Z.p.X s.link s.digits s.shape) := by
  intro blk hb k st m E ds c hA hd
  have hs' := hS.siteOfThePublicPart
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨f1, _, f3, f4, _, _, _, _⟩ := site_facts _ _ x s hsx
  have hp : placeAt Z.p.X s.link s.digits = some s.p := by rw [f3, f4]; exact f1
  obtain ⟨hin, hfl⟩ := hS.promiseInFront k st m E hA
  obtain ⟨hh, F, Fo⟩ := front_seatOf K3Lot.ofForm hin
  rw [placeAt_digits hp] at Fo
  exact ⟨F, Fo.fork, member_yes_front o pol lay KL Fd Z Bs base ch A B O s hS.siteOfThePublicPart
    lot blk hS.blockOfTheLot hS.blockAtTheSite (hS.memberOfTheChain blk hb)
    ((hS.theSeven.place blk hb).trans hS.blockAtTheSite.symm) (hS.memberPassesThePlan blk hb)
    hS.theSeven.ok hS.shapeIsTheLayouts hS.usedIsThePlans J wit _ m ds c st
    ((Thread.heard_length T hA.1.2.1).trans hS.theSeven.base.symm)
    (by rw [← hS.theSeven.rounds blk hb]; exact hd) hfl Fo
    (fun h1 h2 rs g G s' => hS.headReturns h1 h2 k st m E F rs g G s' hA Fo.fork) _ _ _ _⟩

/-- **It is accepted, at every letter fall.** Conditional on the description's return and the seat.
-/
theorem lookupIsAcceptedAtThePair (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst)
    (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B)
    (hS : LookupSeatedAtThePair T Said b Z Bs ch s lot J wit)
    (fall : Nat → FS → List Fmt.Drawn → Option String) : AcceptedS T Said fall b :=
  lookupIsAcceptedOfTheJoin hS.theSeven (lookupJoinsAtThePair o pol lay KL Fd base A B O hS) fall

end

/-! ## 2 Under the head, at the written number of a site's border -/

/-- **The thread is taken from the description's first chain and the prover's first list**: the
first clause of `Sits` (Honest/Thread/File.lean), at the chain cF, and no round ahead of the chain.
Under the head the description that `onlineProverFromPublicFiles` returns is `P5J.F0T OnBytes.secondHashFunction Zp Np cF`
(`atPure_at_laid`, Honest/AtHead.lean), whose first chain is cF. -/
structure ThreadIsTheMakers {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (cF : Chain TS ProofFile.Cl) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X) : Prop where
  faceIsOwn : T.φ = .own
  chainIsTheFirst : T.chain = 0
  firstTreeIsZero : T.ft = 0
  membersAreTheChains : T.bs = cF.blocksInOrder
  sidesAreTheProvers : T.hs = H.first
  nothingIsAhead : T.ahead = []

/-- **Three tests with code on public data**, at a public part, a first chain and a site. -/
structure LookupPublicTests (Zp : Pub) (cF : Chain TS ProofFile.Cl) (s : Site) : Prop where
  /-- the site's number of rounds in front is the chain's own count: the first clause of
  `siteFits` -/
  baseIsTheChainsCount : roundsInFront cF.blocksInOrder s.at_.place = some s.at_.base
  /-- at the calls of a layers' link the shape is the layout's -/
  shapeIsTheLayouts : (s.digits || s.caller != .layers || sameShape s.shape Zp.p.X.y.fo) = true
  /-- at the digits, but for the head's, the lookup ends at the plan's number of slots in use -/
  usedIsThePlans : (!s.digits || s.caller == .head ||
    usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X Wj : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X}

include h in
/-- **The seven hypotheses of `K3PlaysAt`, at the written number of the site's border.** Conditional
on the head, the six equations, the site, the side found and the first test. -/
theorem lookupSevenAtEveryBorder (hT : ThreadIsTheMakers T cF H) (s : Site)
    (hsite : s ∈ lookSites Zp) (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (hSide : H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_))
    (hBase : roundsInFront cF.blocksInOrder s.at_.place = some s.at_.base) :
    K3PlaysAt T (borderOf s.link s.digits) s.at_ J wit (s.p.entries.getD []) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨lot, hin, hlp⟩ := lot_of_site _ _ _ _ _ Zp Bs base cF _ _ O s hsite
  obtain ⟨-, hb, -⟩ := site_border h s hsite lot hin hlp
  have hP : blockPlaces cF.blocksInOrder = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
  have hat : ∀ blk, cF.blocksInOrder[borderOf s.link s.digits]? = some blk → blk.place = s.at_.place := by
    intro blk hk
    have e : (blockPlaces cF.blocksInOrder)[borderOf s.link s.digits]? = some blk.place := by
      unfold blockPlaces
      rw [List.getElem?_map, hk]
      rfl
    rw [hP, hb] at e
    exact (Option.some.inj e).symm
  obtain ⟨blk0, hblk0⟩ : ∃ blk, cF.blocksInOrder[borderOf s.link s.digits]? = some blk := by
    have e : (blockPlaces cF.blocksInOrder)[borderOf s.link s.digits]? = some s.at_.place := by rw [hP, hb]
    unfold blockPlaces at e
    rw [List.getElem?_map] at e
    obtain ⟨blk, hk, _⟩ := Option.map_eq_some_iff.1 e
    exact ⟨blk, hk⟩
  have hpay := fun blk (hk : cF.blocksInOrder[borderOf s.link s.digits]? = some blk) =>
    member_plan_site _ _ _ _ _ Zp Bs base cF _ _ O s hsite lot blk hin hlp
      (List.mem_of_getElem? hk) ((hat blk hk).trans hlp.symm)
      (IM.plan_flat O h.laid.planOk blk (List.mem_of_getElem? hk))
  have hcount : s.at_.base = roundsTo cF.blocksInOrder (borderOf s.link s.digits) := by
    rw [← borderNo_of_nodup cF.blocksInOrder (borderOf s.link s.digits) blk0 s.at_.place hblk0
      (hat blk0 hblk0) (by
        show (blockPlaces cF.blocksInOrder).Nodup
        rw [hP]
        exact ps_nodup)]
    exact (roundsTo_inFront cF.blocksInOrder _ _ hBase).symm
  have hbs : ∀ blk, T.bs[borderOf s.link s.digits]? = some blk →
      cF.blocksInOrder[borderOf s.link s.digits]? = some blk := by
    intro blk hk
    rw [← hT.membersAreTheChains]
    exact hk
  exact
    { half := fun blk hk => by
        rw [hT.sidesAreTheProvers, hat blk (hbs blk hk)]
        exact hSide
      place := fun blk hk => hat blk (hbs blk hk)
      rounds := fun blk hk => (hpay blk (hbs blk hk)).1
      oracles := fun blk hk => (hpay blk (hbs blk hk)).2.1
      ok := Johnson.AtFull.Shape.face_ok_site Zp s hsite
      entries := (hpay blk0 hblk0).2.2
      base := by
        show s.at_.base = T.ahead.length + roundsTo T.bs (borderOf s.link s.digits)
        rw [hT.nothingIsAhead, hT.membersAreTheChains, ← hcount]
        exact (Nat.zero_add _).symm }

include h in
/-- **`PlaysS` at every one of the lookups' borders, at every Said.** Conditional on the head, the
six equations, the site, the side found and the first test. -/
theorem lookupPlaysAtEveryBorder (hT : ThreadIsTheMakers T cF H) (s : Site)
    (hsite : s ∈ lookSites Zp) (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (hSide : H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_))
    (hBase : roundsInFront cF.blocksInOrder s.at_.place = some s.at_.base)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    PlaysS T Said (borderOf s.link s.digits) :=
  lookupPlaysOfTheSeven (lookupSevenAtEveryBorder h hT s hsite J wit hSide hBase)

variable {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}

include h in
/-- **The seat at every one of the lookups' borders**, with the description's return at the same
values. Conditional on the head, the six equations, the site, the side found, the three tests and
the two hypotheses on the thread. -/
theorem lookupSeatedAtEveryBorder (hT : ThreadIsTheMakers T cF H) (s : Site)
    (hsite : s ∈ lookSites Zp) (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (hSide : H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_))
    (hTests : LookupPublicTests Zp cF s)
    (hFront : LookupPromiseInFront T Said (borderOf s.link s.digits) s)
    (hHead : LookupHeadReturns T Said (borderOf s.link s.digits) Zp s) :
    ∃ o pol lay KL Fd Bs base A B lot, IM.Open o pol lay KL Fd Zp Bs base cF A B ∧
      LookupSeatedAtThePair T Said (borderOf s.link s.digits) Zp Bs cF s lot J wit := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨lot, hin, hlp⟩ := lot_of_site _ _ _ _ _ Zp Bs base cF _ _ O s hsite
  have hmem : ∀ blk, T.bs[borderOf s.link s.digits]? = some blk → blk ∈ cF.blocksInOrder := by
    intro blk hk
    rw [← hT.membersAreTheChains]
    exact List.mem_of_getElem? hk
  exact ⟨_, _, _, _, _, Bs, base, _, _, lot, O,
    { theSeven := lookupSevenAtEveryBorder h hT s hsite J wit hSide hTests.baseIsTheChainsCount
      siteOfThePublicPart := hsite
      blockOfTheLot := hin
      blockAtTheSite := hlp
      memberOfTheChain := hmem
      memberPassesThePlan := fun blk hk => IM.plan_flat O h.laid.planOk blk (hmem blk hk)
      shapeIsTheLayouts := hTests.shapeIsTheLayouts
      usedIsThePlans := hTests.usedIsThePlans
      promiseInFront := hFront
      headReturns := hHead }⟩

include h in
/-- **The join at every one of the lookups' borders.** Conditional on the same. -/
theorem lookupJoinsAtEveryBorder (hT : ThreadIsTheMakers T cF H) (s : Site)
    (hsite : s ∈ lookSites Zp) (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (hSide : H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_))
    (hTests : LookupPublicTests Zp cF s)
    (hFront : LookupPromiseInFront T Said (borderOf s.link s.digits) s)
    (hHead : LookupHeadReturns T Said (borderOf s.link s.digits) Zp s) :
    LookupJoinsFromThePair T Said (borderOf s.link s.digits) s.at_ J wit s.p.first
      (seatOf K3Lot.ofForm s.digits).fork (OneQ K3Lot.ofForm Zp.p.X s.link s.digits s.shape) := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, lot, O, hS⟩ :=
    lookupSeatedAtEveryBorder h hT s hsite J wit hSide hTests hFront hHead
  exact lookupJoinsAtThePair o pol lay KL Fd base A B O hS

include h in
/-- **`AcceptedS` at every one of the lookups' borders, at every letter fall.** Conditional on the
same. -/
theorem lookupIsAcceptedAtEveryBorder (hT : ThreadIsTheMakers T cF H) (s : Site)
    (hsite : s ∈ lookSites Zp) (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (hSide : H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_))
    (hTests : LookupPublicTests Zp cF s)
    (hFront : LookupPromiseInFront T Said (borderOf s.link s.digits) s)
    (hHead : LookupHeadReturns T Said (borderOf s.link s.digits) Zp s)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS T Said fall (borderOf s.link s.digits) := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, lot, O, hS⟩ :=
    lookupSeatedAtEveryBorder h hT s hsite J wit hSide hTests hFront hHead
  exact lookupIsAcceptedAtThePair o pol lay KL Fd base A B O hS fall

include h in
/-- **`LookupHeadReturns` holds, emptily, at every site on the calls or off link 24**: at forty-nine
of the fifty borders. Conditional on the head and the site. -/
theorem lookupHeadReturnsButAtOne (b : Nat) (s : Site) (hsite : s ∈ lookSites Zp)
    (hn : s.digits = false ∨ s.link ≠ 24) : LookupHeadReturns T Said b Zp s := by
  intro h1 h2
  rcases hn with hd | hl
  · rw [hd] at h1
    cases h1
  · exact absurd h2 (caller_ne_head h s hsite hl)

end

/-! ## 3 At the first chain's letters -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}

/-- **At the letters `lettersAt`, at every value of their arguments: from the invariant in front of
a lookup, the lookup's promise in front, and no mark.** Conditional on the head and the site. -/
theorem lookupPromiseInFrontAtLettersAt {W₀ Rc Tr Xo : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) (s : Site) (hsite : s ∈ lookSites Zp)
    (k : Coins Bk) (st : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Xo) (E : Env)
    (hA : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (borderOf s.link s.digits) k st m E) :
    k3OnIn s.p st = true ∧ st.failed = none := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨lot, hin, hlp⟩ := lot_of_site _ _ _ _ _ Zp Bs base cF _ _ O s hsite
  obtain ⟨hl, -, hpc⟩ := site_border h s hsite lot hin hlp
  have hs' := hsite
  unfold lookSites at hs'
  obtain ⟨y, _, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨f1, _, f3, f4, _, _, _, _⟩ := site_facts _ _ y s hsy
  have hp : placeAt Zp.p.X s.link s.digits = some s.p := by rw [f3, f4]; exact f1
  refine ⟨onIn_thr _ (VerifiableInference.OnPublicFiles.k3At_mgAll h.𝔇 mgBase) hp ?_ hA,
    failed_of_thr _ hA⟩
  show VerifiableInference.Desc.First.Pub.lookIn s.link (pieceAt Zp.p.X s.link s.digits) ∈
    ((pubSets (mgAll h.𝔇 mgBase).more linksFull (flatPlacesOf linksFull true))[
      borderOf s.link s.digits]?).getD []
  rw [mgAll_more_closed h.𝔇 mgBase rfl, hpc]
  cases hd : s.digits with
  | false => exact (k3_open_calls hl).1
  | true => exact (k3_open_digits hl).2.1

variable {W₀ Rc Ky Tr X₀ X Wj : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LH" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w

/-- **The six equations at the letters `lettersHead`**, at every value of their arguments. -/
theorem threadIsTheMakersAtLettersHead : ThreadIsTheMakers (LH).thread cF H :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The promise in front at the letters `lettersHead`**, at every Said. Conditional on the head
and the site. -/
theorem lookupPromiseInFrontAtLettersHead (s : Site) (hsite : s ∈ lookSites Zp)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    LookupPromiseInFront (LH).thread Said (borderOf s.link s.digits) s :=
  fun k st m E hA => lookupPromiseInFrontAtLettersAt h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s
    hsite k st m E hA.1

/-- **`PlaysS` at the letters `lettersHead`, at every one of the lookups' borders and every Said.**
Conditional on the head, the site, the side found and the first test. -/
theorem lookupPlaysAtLettersHead (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (hSide : H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_))
    (hBase : roundsInFront cF.blocksInOrder s.at_.place = some s.at_.base)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    PlaysS (LH).thread Said (borderOf s.link s.digits) :=
  lookupPlaysAtEveryBorder h
    (threadIsTheMakersAtLettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) s hsite J wit hSide
    hBase Said

/-- **The join at the letters `lettersHead`.** Conditional on the head, the site, the side found,
the three tests, and `LookupHeadReturns`. -/
theorem lookupJoinsAtLettersHead (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (hSide : H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_))
    (hTests : LookupPublicTests Zp cF s)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hHead : LookupHeadReturns (LH).thread Said (borderOf s.link s.digits) Zp s) :
    LookupJoinsFromThePair (LH).thread Said (borderOf s.link s.digits) s.at_ J wit s.p.first
      (seatOf K3Lot.ofForm s.digits).fork (OneQ K3Lot.ofForm Zp.p.X s.link s.digits s.shape) :=
  lookupJoinsAtEveryBorder h
    (threadIsTheMakersAtLettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) s hsite J wit hSide
    hTests (lookupPromiseInFrontAtLettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w s hsite
      Said) hHead

/-- **`AcceptedS` at the letters `lettersHead`, at every letter fall.** Conditional on the head, the
site, the side found, the three tests, and `LookupHeadReturns`, which `lookupHeadReturnsButAtOne`
shows at forty-nine of the fifty borders. -/
theorem lookupIsAcceptedAtLettersHead (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (hSide : H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_))
    (hTests : LookupPublicTests Zp cF s)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hHead : LookupHeadReturns (LH).thread Said (borderOf s.link s.digits) Zp s)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (LH).thread Said fall (borderOf s.link s.digits) :=
  lookupIsAcceptedAtEveryBorder h
    (threadIsTheMakersAtLettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) s hsite J wit hSide
    hTests (lookupPromiseInFrontAtLettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w s hsite
      Said) hHead fall

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.LookupJoinsFromThePair
#print axioms ProofFile.Honest.K3.Term.lookupPlaysOfTheSeven
#print axioms ProofFile.Honest.K3.Term.lookupIsAcceptedOfTheJoin
#print axioms ProofFile.Honest.K3.Term.LookupPromiseInFront
#print axioms ProofFile.Honest.K3.Term.LookupHeadReturns
#print axioms ProofFile.Honest.K3.Term.LookupSeatedAtThePair
#print axioms ProofFile.Honest.K3.Term.lookupSeatedOfAtSite
#print axioms ProofFile.Honest.K3.Term.lookupJoinsAtThePair
#print axioms ProofFile.Honest.K3.Term.lookupIsAcceptedAtThePair
#print axioms ProofFile.Honest.K3.Term.ThreadIsTheMakers
#print axioms ProofFile.Honest.K3.Term.LookupPublicTests
#print axioms ProofFile.Honest.K3.Term.lookupSevenAtEveryBorder
#print axioms ProofFile.Honest.K3.Term.lookupPlaysAtEveryBorder
#print axioms ProofFile.Honest.K3.Term.lookupSeatedAtEveryBorder
#print axioms ProofFile.Honest.K3.Term.lookupJoinsAtEveryBorder
#print axioms ProofFile.Honest.K3.Term.lookupIsAcceptedAtEveryBorder
#print axioms ProofFile.Honest.K3.Term.lookupHeadReturnsButAtOne
#print axioms ProofFile.Honest.K3.Term.lookupPromiseInFrontAtLettersAt
#print axioms ProofFile.Honest.K3.Term.threadIsTheMakersAtLettersHead
#print axioms ProofFile.Honest.K3.Term.lookupPromiseInFrontAtLettersHead
#print axioms ProofFile.Honest.K3.Term.lookupPlaysAtLettersHead
#print axioms ProofFile.Honest.K3.Term.lookupJoinsAtLettersHead
#print axioms ProofFile.Honest.K3.Term.lookupIsAcceptedAtLettersHead
