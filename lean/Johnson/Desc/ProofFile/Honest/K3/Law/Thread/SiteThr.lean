-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/SiteThr.lean: the honest side of the kind "lookup" (K3).
Conditional: at a lookup of a public part, two of the frame's sentences on a member of the first
chain (`Plays`, `Accepted`, Honest/Thread/Pays.lean) at the description's own member at a lookup's
place. General in the first chain's letters. One structure, one definition; theorems.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins. In this file: L is the structure of the first chain's letters (`Letters`,
Honest/Thread/First.lean), and b is a border's number.

What is shown.
  `onIn_thr`: from the thread at the border in front: the lookup's promise in front (`k3OnIn`,
    Johnson/Desc/First/Look/K3Borders.lean).
  `SiteAt`: the hypotheses, by name: what ties the letters to the description and to the site.
  `HeadReturns`: what is asked at the digits of the head's link.
  `seated_site`: `SiteAt` gives `SeatedAt` (Honest/K3/Law/Thread/Plays.lean).
  `joins_site`: `SiteAt` gives `JoinsAt` (Honest/K3/Law/Thread/Accepted.lean).
  `plays_site`: `Plays L.thread b`.
  `accepted_site`: `Accepted L.thread fall b`, at every letter fall.

Hypotheses that remain.
  `hS`: `SiteAt`. Every clause of it is on public data or on the letters: none speaks of a run. Its
    fields on the member speak of whatever member stands at number b; none says that one stands
    there, and where none does `Plays` and `Accepted` say nothing either.
  `O`: (in `joins_site`, `accepted_site`) the description returns (`IM.Open`,
    Johnson/IMR/SeatOpen.lean).
  `hH`: (there) `HeadReturns`: asked at the digits of the head's link alone; it speaks of the states
    at which the thread stands in front of the member.
  `hK`, `hp`, `hq`, `h`: (in `onIn_thr`) the library's `K3At` at the letters' meaning of the
    promise; the public structure has the place; "lookIn" is open at the border; the thread.

Imported. Files under Honest/Thread/.
The theorems also stand over
files under Honest/SumLaw/ and Honest/Member/.

Users. Honest/K3/Law/Thread/AtLetters.lean calls `plays_site` and `accepted_site`;
Honest/K3/Law/Thread/AtThreadBridges.lean [not in this library] and
Honest/K3/Law/Thread/LeftThr.lean call `seated_site` and `joins_site`;
Honest/K3/Law/Thread/AtThreadSite.lean calls `onIn_thr`.

`SiteAt` has the field half: the list of halves holds, at the lookup's place, the elder row
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
No value of the first chain's letters at a description is given in this file. Shown in part:
Honest/K3/Law/Thread/SiteAtLetters.lean: `siteAt_lettersAt`: `SiteAt` at the letters `lettersAt`,
under `P5J.AtMgA`, the site and `SiteRest`. What stays open: these three are hypotheses there, and
no value of `P5J.AtMgA` is exhibited in that file: so it is no instance of `SiteAt`. `Plays` and
`Accepted` are two of the sentences that Honest/Thread/Pays.lean lists as owed at a member of a
chain; they are forms of hypotheses of the frame's. The acceptance is said at any summands: it says
nothing on values.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.Accepted
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.FrontSite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription Oracle)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf k3OnIn pieceAt entriesFit)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First (pubSets)
open VerifiableInference.Desc.First.Look (P Sent placeAt sameShape k3LookIn_onIn k3LookInAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (K3At K3Letters)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- **From the thread at the border in front: the lookup's promise in front.** Conditional on the
thread, on the library's `K3At` at the letters' meaning of the promise, on the public structure
having the place, and on "lookIn" being open at the border (where the table's test accepts it is:
the library's `calls_asks_open`, `digits_lookIn_open`). -/
theorem onIn_thr {X : OnBytes.Model.Verify.Public} {D : Sent} {Lk : K3Letters Cells Tok}
    (hK : K3At X D Lk L.MgP) {i : Nat} {dg : Bool} {p : P} (hp : placeAt X i dg = some p) {b : Nat}
    (hq : VerifiableInference.Desc.First.Pub.lookIn i (pieceAt X i dg) ∈
      ((pubSets L.MgP.more L.links L.ps)[b]?).getD [])
    {k : Coins Bk} {s : FS} {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env}
      (h : Thr L.thread b k s m E) :
    k3OnIn p s = true := by
  have hpub := onAt_pub (onAt_of_thr L h) (failed_of_thr L h) _ (List.mem_append_left _ hq)
  have e := (k3At_honest hK L.ans L.test).lookIn i dg (L.pubOf m.st.input.x, s)
  have h2 : k3LookInAt X D i dg s = true := e.symm.trans hpub
  unfold k3LookInAt at h2
  rw [hp] at h2
  exact k3LookIn_onIn h2

end

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}
  (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- **The hypotheses, by name: whatever member stands at number b of the first chain's letters is
the description's member at a lookup's place.** No field says that a member stands at number b:
where none does, the fields on the member ask nothing. Here Z, Bs and ch are the description's
public part, its base and its first chain; s is the lookup; lot is the lookups' own sub-protocol at
its place; J and wit are the summands and the seat's reader of the input. -/
structure SiteAt (b : Nat) (Z : Pub) (Bs : PureBase) (ch : Chain FS ProofFile.Cl) (s : Site)
    (lot : Block FS ProofFile.Cl) (J : LookJobs Wj) (wit : Local W₀ Rc Xi Tr → Wj) (D : Sent)
    (Lk : K3Letters Cells Tok) : Prop where
  /-- the letters' flat list is the description's -/
  flat : L.bs = ch.blocksInOrder
  site : s ∈ lookSites Z
  inLot : lot ∈ (K3Lot.lot Z).blocks Bs.G₀
  lotPlace : lot.place = s.at_.place
  place : ∀ blk, L.bs[b]? = some blk → blk.place = lot.place
  /-- the member's test on the plan -/
  plan : ∀ blk, L.bs[b]? = some blk → blk.planOk = true
  /-- the member's rounds and oracle messages, at the parameters' own entries -/
  rounds : ∀ blk, L.bs[b]? = some blk → blk.rounds = (s.p.entries.getD []).map declOf
  oracles : ∀ blk, L.bs[b]? = some blk → blk.oracles = (s.p.entries.getD []).map fun _ => []
  entries : entriesFit s.at_.face (s.p.entries.getD []) = true
  /-- the half that the letters hold at the member's place is the lookup's seated row -/
  half : ∀ blk, L.bs[b]? = some blk → L.hs.find? (fun h => h.place == blk.place) =
    some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_)
  /-- the site's number of rounds in front is the flat list's own -/
  base : s.at_.base = roundsTo L.bs b
  /-- three tests with code on public data -/
  ok : s.at_.face.ok = true
  shapeIs : (s.digits || s.caller != .layers || sameShape s.shape Z.p.X.y.fo) = true
  usedIs : (!s.digits || s.caller == .head ||
    usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true
  /-- the letters' meaning of the promise says at the lookups' own items what the
  lookups' layer says -/
  k3At : K3At Z.p.X D Lk L.MgP
  /-- "lookIn" is open at the border -/
  lookIn : VerifiableInference.Desc.First.Pub.lookIn s.link (pieceAt Z.p.X s.link s.digits) ∈
    ((pubSets L.MgP.more L.links L.ps)[b]?).getD []

variable {L}
variable {b : Nat} {Z : Pub} {Bs : PureBase} {ch : Chain FS ProofFile.Cl} {s : Site}
  {lot : Block FS ProofFile.Cl}
  {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent} {Lk : K3Letters Cells Tok}

/-- `SiteAt` gives what "it plays" asks. -/
theorem seated_site (hS : SiteAt L b Z Bs ch s lot J wit D Lk) :
    SeatedAt L b s.at_ J wit (s.p.entries.getD []) :=
  ⟨hS.half, fun blk hb => (hS.place blk hb).trans hS.lotPlace, hS.rounds, hS.oracles, hS.ok,
    hS.entries,
    hS.base⟩

/-- **It plays, at the description's own member at a lookup's place.** Conditional on `SiteAt`.
No instance of these hypotheses is exhibited in this file. -/
theorem plays_site (hS : SiteAt L b Z Bs ch s lot J wit D Lk) : Plays L.thread b :=
  plays_look (seated_site hS)

/-- What is asked at the digits of the head's link: at a state at which the thread stands in front
of the member, and from that state's own ledger: the step without a round that stands behind that
lookup returns at the state that the lookup's own decision leaves. That step asks more of the state
than the lookup's decision does (what the head heard and the head's tables are set; the covered
positions; the claim on the weights): so at a state that nothing ties to the thread the sentence
would be false. It is other kinds' hypothesis on the thread. No instance of these hypotheses is
exhibited in this file. -/
def HeadReturns (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT) (b : Nat) (Z : Pub)
    (s : Site) :
    Prop :=
  s.digits = true → s.caller = .head → ∀ (k : Coins Bk) (st : FS) (m : Mid (Local W₀ Rc Xi Tr) Xo)
    (E : Env)
    (F : Fork) (rs : List Fmt.RoundView) (g : HeardV) (G : Fork) (s' : FS), Thr L.thread b k st m E →
    (seatOf K3Lot.ofForm s.digits).fork st = some F → rs.length = (s.p.entries.getD []).length →
    hearV (faceOf s.shape) F rs = some (g, G) →
    decideVia (seatOf K3Lot.ofForm s.digits) s.p st rs = .ok s' → ∃ t, HeadBehind Z.p.X s' t

/-- **From the thread in front the join holds at the member itself, at the parameters' own first
slot and from the ledger that the state itself holds.** Conditional on the description's return,
`SiteAt` and `HeadReturns`. No instance of these hypotheses is exhibited in this file. -/
theorem joins_site (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst)
    (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    (hH : HeadReturns L b Z s) :
    JoinsAt L b s.at_ J wit s.p.first (seatOf K3Lot.ofForm s.digits).fork
      (OneQ K3Lot.ofForm Z.p.X s.link s.digits s.shape) := by
  intro blk hb k st m E ds c hA hd
  have hs' := hS.site
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨f1, _, f3, f4, _, _, _, _⟩ := site_facts _ _ x s hsx
  have hp : placeAt Z.p.X s.link s.digits = some s.p := by rw [f3, f4]; exact f1
  have hin := onIn_thr L hS.k3At hp hS.lookIn hA
  obtain ⟨hh, F, Fo⟩ := front_seatOf K3Lot.ofForm hin
  rw [placeAt_digits hp] at Fo
  exact ⟨F, Fo.fork, member_yes_front o pol lay KL Fd Z Bs base ch A B O s hS.site lot blk hS.inLot
    hS.lotPlace (by rw [← hS.flat]; exact List.mem_of_getElem? hb) (hS.place blk hb)
      (hS.plan blk hb)
    hS.ok hS.shapeIs hS.usedIs J wit _ m ds c st ((heard_of_thr L hA).trans hS.base.symm)
    (by rw [← hS.rounds blk hb]; exact hd) (failed_of_thr L hA) Fo
    (fun h1 h2 rs g G s' => hH h1 h2 k st m E F rs g G s' hA Fo.fork) _ _ _ _⟩

/-- **It is accepted, at the description's own member at a lookup's place, at every letter fall.**
Conditional on the description's return, `SiteAt` and `HeadReturns`. No instance of these hypotheses
is exhibited in this file. -/
theorem accepted_site (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst)
    (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    (hH : HeadReturns L b Z s) (fall : Nat → FS → List Fmt.Drawn → Option String) :
    Accepted L.thread fall b :=
  accepted_look (seated_site hS) (joins_site o pol lay KL Fd base A B O hS hH) fall

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.onIn_thr
#print axioms ProofFile.Honest.K3.Law.AtThr.seated_site
#print axioms ProofFile.Honest.K3.Law.AtThr.plays_site
#print axioms ProofFile.Honest.K3.Law.AtThr.joins_site
#print axioms ProofFile.Honest.K3.Law.AtThr.accepted_site
