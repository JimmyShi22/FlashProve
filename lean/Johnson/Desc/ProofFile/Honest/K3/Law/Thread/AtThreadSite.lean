-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtThreadSite.lean: the honest side of the kind "lookup"
(K3). Conditional: the sentence `Accepted T fall b` (Honest/Thread/Pays.lean) at the description's
own member at a lookup's place, with the thread a variable, from a structure of hypotheses none of
which is that sentence itself. One structure; theorems.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins. In this file: T is a thread's structure of letters (`Thread`,
Honest/Thread/Thr.lean), and b is the member's number.

What is shown.
  `K3AtSite`: the hypotheses, by name.
  `seated_of_atSite`: conditional on the description's return: `K3AtSite` gives `K3Seated`
    (Honest/K3/Law/Thread/AtThread.lean).
  `plays_atSite`: so `Plays T b`.
  `accepted_atSite`: so `Accepted T fall b`, at every letter fall.
  `atSite_of_site`: at the first chain's thread the structure follows from `SiteAt` and
    `HeadReturns` (Honest/K3/Law/Thread/SiteThr.lean).
Why this file: `K3Seated` has a field, joins, that holds the member's own accepting step, and
`accepted_k3` (AtThread.lean) only takes it out. Here that field is shown, from an implication out
of the thread to the lookup's promise in front (`k3OnIn`, Johnson/Desc/First/Look/K3Borders.lean), a
Boolean test of the library's on the state in front.

Hypotheses that remain.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hS`: `K3AtSite`. Its fields follow.
  site, inLot, lotPlace: of the description: the site; the lookups' own sub-protocol at its place.
  mem, place, plan, rounds, oracles: of the thread's member: it is a member of the description's
    first chain, at that place; it passes its test on the plan; its rounds and oracle messages are
    those of the parameters' entries.
  half: the thread's list of halves holds the lookup's seated row there.
  entries, ok, shapeIs, usedIs: four tests with code on public data.
  base: the site's number of rounds in front is the thread's.
  front: from the thread in front: the lookup's promise in front holds at the verifier's state, and
    the state bears no mark.
  headReturns: at the digits of the head's link alone: at a state at which the thread stands, the
    step without a round behind the lookup returns. It is other kinds' hypothesis on the thread.
Which letters of the thread are read: bs, hs, front, φ, chain and ft, and whatever shows the fields
front and headReturns.
In `atSite_of_site`: `hS`: `SiteAt`; `hH`: `HeadReturns`.

Imported. Files under Honest/Thread/.

Users. Honest/K3/Law/Thread/PlaysAtHead.lean [not in this library] calls `plays_atSite` and
`accepted_atSite`; Honest/K3/Law/Thread/RidersAtHeadSite.lean calls `atSite_of_site`.
Honest/K3/Law/Thread/HalfAtSite.lean [not in this library], Honest/K3/Law/Thread/HeadReturnsOf.lean,
Honest/K3/Law/Thread/K3KeepsForms.lean [not in this library] and
Honest/K3/Law/Thread/PlaysAtSite.lean [not in this library] import this file.

`K3AtSite` has the field half: the list of halves holds, at the lookup's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. Who pays the field, each at the fast summands and under hypotheses on
the list: where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot`
(HalfAtSite.lean [not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean
[not in this library]); where it holds a lot with the halves of `theLotInst` at the public part:
`half_like_ok`, `half_field_like` (HalfOfLotLike.lean [not in this library]). A lot of rows that
pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean) lays another term there: no file shows
the field at such a lot, so the theorems of this file that bear it cannot be called there as they
stand. Honest/K3/Law/Keep/ carries plays and runs from the one row to the other (`lotsPlayed_whole`,
`chain_lots`, `run_same`); no file carries these sentences over.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
`Plays` and `Accepted` are two of the sentences that Honest/Thread/Pays.lean lists as owed at a
member of a chain; they are forms of hypotheses of the frame's. The acceptance is said at any
summands: it says nothing on values.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtThread
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf k3OnIn entriesFit)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First.Look (Sent placeAt sameShape)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (K3Letters)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

section
variable {Bk : ProverCoinCounts} {V W X Pb Wj : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)

/-- **The hypotheses at the description's own member at a lookup's place, the thread a variable.**
-/
structure K3AtSite (b : Nat) (Z : Pub) (Bs : PureBase) (ch : Chain FS ProofFile.Cl) (s : Site)
    (lot : Block FS ProofFile.Cl) (J : LookJobs Wj) (wit : W → Wj) : Prop where
  site : s ∈ lookSites Z
  inLot : lot ∈ (K3Lot.lot Z).blocks Bs.G₀
  lotPlace : lot.place = s.at_.place
  mem : ∀ blk, T.bs[b]? = some blk → blk ∈ ch.blocksInOrder
  place : ∀ blk, T.bs[b]? = some blk → blk.place = lot.place
  plan : ∀ blk, T.bs[b]? = some blk → blk.planOk = true
  rounds : ∀ blk, T.bs[b]? = some blk → blk.rounds = (s.p.entries.getD []).map declOf
  oracles : ∀ blk, T.bs[b]? = some blk → blk.oracles = (s.p.entries.getD []).map fun _ => []
  half : ∀ blk, T.bs[b]? = some blk → T.hs.find? (fun h => h.place == blk.place) =
    some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_)
  entries : entriesFit s.at_.face (s.p.entries.getD []) = true
  ok : s.at_.face.ok = true
  shapeIs : (s.digits || s.caller != .layers || sameShape s.shape Z.p.X.y.fo) = true
  usedIs : (!s.digits || s.caller == .head ||
    usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true
  base : s.at_.base = T.front + roundsTo T.bs b
  /-- from the thread in front: the lookup's promise in front, and no mark -/
  front : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
    k3OnIn s.p st = true ∧ st.failed = none
  /-- at the digits of the head's link alone -/
  headReturns : s.digits = true → s.caller = .head → ∀ (k : Coins Bk) (st : FS) (m : Mid W X)
    (E : Env) (F : Fork) (rs : List Fmt.RoundView) (g : HeardV) (G : Fork) (s' : FS), Thr T b k st m E →
    (seatOf K3Lot.ofForm s.digits).fork st = some F → rs.length = (s.p.entries.getD []).length →
    hearV (faceOf s.shape) F rs = some (g, G) →
    decideVia (seatOf K3Lot.ofForm s.digits) s.p st rs = .ok s' → ∃ t, HeadBehind Z.p.X s' t

variable {T}
variable {b : Nat} {Z : Pub} {Bs : PureBase} {ch : Chain FS ProofFile.Cl} {s : Site}
  {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : W → Wj}

/-- **`K3AtSite` gives `K3Seated`**: the field joins is shown: from the thread in front the row's
play, the hearing from the ledger that the state itself holds, and the member's own step go through
together. Conditional on the description's return. -/
theorem seated_of_atSite (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst)
    (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (hS : K3AtSite T b Z Bs ch s lot J wit) :
    K3Seated T b s.at_ J wit (s.p.entries.getD []) s.p.first (seatOf K3Lot.ofForm s.digits).fork
      (OneQ K3Lot.ofForm Z.p.X s.link s.digits s.shape) where
  half := hS.half
  place := fun blk hb => (hS.place blk hb).trans hS.lotPlace
  rounds := hS.rounds
  oracles := hS.oracles
  ok := hS.ok
  entries := hS.entries
  base := hS.base
  joins := by
    intro blk hb k st m E ds c hA hd
    have hs' := hS.site
    unfold lookSites at hs'
    obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
    obtain ⟨f1, _, f3, f4, _, _, _, _⟩ := site_facts _ _ x s hsx
    have hp : placeAt Z.p.X s.link s.digits = some s.p := by rw [f3, f4]; exact f1
    obtain ⟨hin, hfl⟩ := hS.front k st m E hA
    obtain ⟨hh, F, Fo⟩ := front_seatOf K3Lot.ofForm hin
    rw [placeAt_digits hp] at Fo
    exact ⟨F, Fo.fork, member_yes_front o pol lay KL Fd Z Bs base ch A B O s hS.site lot blk
      hS.inLot hS.lotPlace (hS.mem blk hb) (hS.place blk hb) (hS.plan blk hb)
      hS.ok hS.shapeIs hS.usedIs J wit _ m ds c st
      ((Thread.heard_length T hA.2.1).trans hS.base.symm)
      (by rw [← hS.rounds blk hb]; exact hd) hfl Fo
      (fun h1 h2 rs g G s' => hS.headReturns h1 h2 k st m E F rs g G s' hA Fo.fork) _ _ _ _⟩

/-- **It plays**, the thread a variable. Conditional on the description's return and `K3AtSite`. -/
theorem plays_atSite (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst)
    (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (hS : K3AtSite T b Z Bs ch s lot J wit) :
    Plays T b := plays_k3 (seated_of_atSite o pol lay KL Fd base A B O hS)

/-- **It is accepted, at every letter fall**, the thread a variable. Conditional on the
description's return and `K3AtSite`. No instance of these hypotheses is exhibited in this file. -/
theorem accepted_atSite (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst)
    (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (hS : K3AtSite T b Z Bs ch s lot J wit)
    (fall : Nat → FS → List Fmt.Drawn → Option String) : Accepted T fall b :=
  accepted_k3 (seated_of_atSite o pol lay KL Fd base A B O hS) fall

end

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}
  {L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT}
  {b : Nat} {Z : Pub} {Bs : PureBase} {ch : Chain FS ProofFile.Cl} {s : Site} {lot : Block FS ProofFile.Cl}
  {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent} {Lk : K3Letters Cells Tok}

/-- **At the first chain's thread the structure follows from `SiteAt` and `HeadReturns`**: the field
front is shown from the thread's own clause on the table's promise. -/
theorem atSite_of_site (hS : SiteAt L b Z Bs ch s lot J wit D Lk) (hH : HeadReturns L b Z s) :
    K3AtSite L.thread b Z Bs ch s lot J wit where
  site := hS.site
  inLot := hS.inLot
  lotPlace := hS.lotPlace
  mem := fun blk hb => by
    have hb' : L.bs[b]? = some blk := hb
    rw [← hS.flat]
    exact List.mem_of_getElem? hb'
  place := hS.place
  plan := hS.plan
  rounds := hS.rounds
  oracles := hS.oracles
  half := hS.half
  entries := hS.entries
  ok := hS.ok
  shapeIs := hS.shapeIs
  usedIs := hS.usedIs
  base := by
    rw [hS.base]
    exact (Nat.zero_add _).symm
  front := fun k st m E hA => by
    have hs' := hS.site
    unfold lookSites at hs'
    obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
    obtain ⟨f1, _, f3, f4, _, _, _, _⟩ := site_facts _ _ x s hsx
    have hp : placeAt Z.p.X s.link s.digits = some s.p := by rw [f3, f4]; exact f1
    exact ⟨onIn_thr L hS.k3At hp hS.lookIn hA, failed_of_thr L hA⟩
  headReturns := hH

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.seated_of_atSite
#print axioms ProofFile.Honest.K3.Law.AtThr.plays_atSite
#print axioms ProofFile.Honest.K3.Law.AtThr.accepted_atSite
#print axioms ProofFile.Honest.K3.Law.AtThr.atSite_of_site
