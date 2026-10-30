-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/SeatAtLinks.lean: FROM THE CODE SWITCH's OWN SUB-PROTOCOL TO THE ONE
THAT THE PROOF FILE's DESCRIPTION SEATS AT THE NUMBER 14 l + 2 OF THE FIRST CHAIN's FLAT LIST, 1 ≤ l
< 24: THE SEATED DECISION IS: NOTHING IN FRONT, THE KIND's OWN AT THE PLAN's NUMBERS IN A LINK's
DRESS, THEN THE WAY OUT `leaveOpened f` (f: the link's own row of `framesOf`): BOTH WAYS, AT ALL
STATES; AND AT EVERY STATE THAT IS REACHED THERE THE WAY OUT RETURNS BEHIND EVERY YES OF THE KIND's
OWN. In the goals' scope, at an opening, under the plan's own test and the written cut. One short
name; statements with their proofs: calls.

  `switchPlaceAt l` the first place of link l, as the description writes it: a short name
  `k2_openings` the kind's sub-protocol reads as many groups of columns as the place reads trees
  `link_dress` at such a link the lot's live sub-protocol is the kind's own in a LINK's dress, at
                    the plan's numbers, under its own name at the link's first place: the other two
                    dresses are shut out by the library's test on the places
  `link_seat_decides` THE FIRST TOP: there are b, nm, fs, f, Pp, n with: b is entry 14 l + 2 · f is
                    row l of `framesOf`, and its test on the plan says yes · n are the plan's
                    numbers · at two rounds and as many groups as n.read has entries: b.decide s rs
                    gs = ok t ↔ ∃ m, the kind's own decision at s returns m ∧ leaveOpened f s m = ok
                    t
  `link_after_reached` at a state reached at 14 l + 2, for every row f at l whose test on the plan
                    says yes: behind every yes of a decision of the kind in a link's dress
                    `leaveOpened f s u` returns
  `link_seat_reached` THE SECOND TOP: at the first top's own letters, its seven clauses beside (so
                    that the name nm is pinned by the two-way clause): AT A REACHED STATE THE SEATED
                    SUB-PROTOCOL's DECISION SAYS YES WHEREVER THE KIND's OWN DOES, at two rounds and
                    as many groups as the place reads trees

By, this folder's: `joined_iff` (Returns/SeatIff.lean) · `leave_returns`
(Returns/OpenedReturns.lean). The library's: `k2_link_sits`, `Joined`, `Joined.planOk`
(Johnson/IMR/FirstSeats.lean, Johnson/IMR/SameSpot.lean) · `hear_at_flat` (Johnson/IMR/FlatIx.lean),
`flatIx_scope` (Johnson/IMR/FlatScope.lean) · `flat_planOk` (Johnson/P1K2R/SitsDoor.lean),
`retype_planOk` (Johnson/IMR/SeatForm.lean) · `seated_is_pAt`, `dressOf`
(Johnson/Top/H0/K2Caller/PAtSeated.lean) · `spots_open` (Johnson/Loose/H2K12/SpotsAtAll.lean),
`links25_open` (Johnson/Loose/H2K12/HsAtAll.lean) · `K2Is.live`, `k2P`, `under`
(Johnson/IMR/K2Seat.lean), `Open.blank` (Johnson/IMR/SeatOpen.lean) · `laid_at`
(Johnson/IMR/FrontPin.lean), `noMark_switch` (Johnson/P1K2R/BookTight.lean) · `reach_raw`,
`Reach.fold` (Johnson/Top/H0/Walk/Reach.lean). NEAR RELATIVES, ONE WAY, NOT CALLED: `k02_sits_step`,
`SitsJoined` (Johnson/P1K2R/SitsStep.lean): the way down at the step, with both dresses left open at
a link.

Limits. THE 23 LINKS ALONE: nothing at the output head's switch or behind the last segment, where
the description lays something in front or behind. AT THE DECISION, NOT AT THE STEP (the step's two
tests on rounds and columns are the same for both: `Joined.rounds`; not joined here). That the
kind's own decision says yes is a premise inside the second top: other tops pay it at a
reached state under the head `P5J.AtMgA`, at two rounds and columns that pass the step's two tests:
NOT JOINED HERE. "Reached" is: over the list of the wrapped sub-protocols. That a state is reached
is not said. The plan's own test and the written cut are premises (the heads `P5J.AtMg` and
`P5J.AtMgA` pay them). At the format's second hash function alone. This file's imports are heavy.
Nothing on any property.




-/
import Johnson.Desc.K2.Honest.Returns.OpenedReturns
import Johnson.Loose.H2K12.HsAtAll
import Johnson.P1K2R.SitsDoor
import Johnson.P1K2R.BookTight
import Johnson.IMR.FrontPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind decideWith rounds)
open VerifiableInference.Desc.First.K2Caller (seated_is_pAt dressOf)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (laid_at)
open P1K2 (Prep Nums numsAt prepOf leaveOpened)
open IM (k2P under)
open _root_.Tw.K2 (sendByL8)
open ProofFile (Cl)

/-- The first place of link l, as the description writes it. -/
abbrev switchPlaceAt (l : Nat) : Place := { chain := 1, link := some l, piece := 1, kind := .K2 }

/-- The kind's sub-protocol reads as many groups of columns as the place reads trees. -/
theorem k2_openings {C : Type} (p : P2) : (codeSwitchKind p : Block S C).openings = p.read.length := by
  show (rounds p).foldl (fun n r => n + r.stored.length + r.opens.length) 0 = _
  simp [rounds]

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **At a link 1 ≤ l < 24 the lot's live sub-protocol wears a link's dress.** -/
theorem link_dress (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) {l : Nat} (h24 : l < 24) {x : Block S Unit}
    (hx : x ∈ P1K2.pureTable (fun _ _ => some none) Z Bs.G₀) (hxp : x.planOk = true)
    (hpc : x.place = (switchPlaceAt l)) :
    ∃ Pp n, prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp (some l) = some n ∧
      x = under x.name (switchPlaceAt l)
        (codeSwitchKind (k2P Z (switchPlaceAt l) x.name .link n)) := by
  obtain ⟨Pp, n, hP, hn, ep, arms⟩ :=
    seated_is_pAt O.blank (H2K12.spots_open hS hR O hcut) hx hxp
  rw [H2K12.links25_open hS hR O hpl, hpc] at ep
  have hne : ¬ ((l + 1 == 25) = true) := by
    rw [beq_iff_eq]
    omega
  have hd : dressOf 25 (some l) = .link := by
    show (if (l + 1 == 25) = true then _ else _) = _
    rw [if_neg hne]
  rw [hd] at ep
  rw [hpc] at hn arms
  rw [ep] at arms
  refine ⟨Pp, n, hP, hn, ?_⟩
  rcases arms with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, e⟩
  · cases e
  · cases e
  · exact e

/-- **The seated decision at 14 l + 2, both ways.** -/
theorem link_seat_decides (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) :
    ∃ (b : Block S Cl) (nm : String) (fs : List LinkFrame) (f : LinkFrame) (Pp : Prep)
      (n : Nums), c.blocksInOrder[14 * l + 2]? = some b ∧
      framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧ fs[l]? = some f ∧ f.plan = true ∧
      prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp (some l) = some n ∧
      ∀ (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), rs.length = 2 →
        gs.length = n.read.length →
        (b.decide s rs gs = .ok t ↔ ∃ m,
          decideWith sendByL8 (k2P Z (switchPlaceAt l) nm .link n) s rs gs = .ok m ∧
            leaveOpened f s m = .ok t) := by
  obtain ⟨Lk, b, x, e1, e2, hx, J, hi⟩ := IM.k2_link_sits hS hR O l h1 h24
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
  have hb := P1K2.flat_planOk O hpl b (List.mem_of_getElem? hf)
  obtain ⟨fs, f, hfs, hff, ep⟩ := J.planOk
  rw [hb] at ep
  obtain ⟨hq, hfp⟩ := Bool.and_eq_true_iff.1 ep.symm
  have hxp := (IM.retype_planOk x hq).1
  have hpc : x.place = (switchPlaceAt l) := by
    obtain ⟨_, _, -, -, arms⟩ := hi.live hxp
    rcases arms with ⟨-, e⟩ | ⟨_, _, -, -, e⟩ | ⟨_, -, e⟩ <;> rw [e] <;> rfl
  obtain ⟨Pp, n, hP, hn, ex⟩ := link_dress hS hR O hpl hcut h24 hx hxp hpc
  obtain ⟨fs', f', hfs', hff', e⟩ := J
  obtain rfl : fs = fs' := Except.ok.inj (hfs.symm.trans hfs')
  obtain rfl : f = f' := Option.some.inj (hff.symm.trans hff')
  refine ⟨b, x.name, fs, f, Pp, n, by simpa using hf, hfs, hff, hfp, hP, hn,
    fun s t rs gs hr hg => ?_⟩
  have hr' : rs.length = (x.retype : Block S Cl).rounds.length := by
    rw [hr, ex]
    rfl
  have hg' : gs.length = (x.retype : Block S Cl).openings := by
    rw [hg, ex]
    exact (k2_openings (C := Unit) (k2P Z (switchPlaceAt l) x.name .link n)).symm
  have hk7 : (switchPlaceAt l).kind ≠ KindName.K7 := by
    intro h7
    cases h7
  rw [joined_iff e hk7 hr' hg' s t]
  have ed : ∀ m, ((x.retype : Block S Cl).decide s rs gs = .ok m ↔
      decideWith sendByL8 (k2P Z (switchPlaceAt l) x.name .link n) s rs gs = .ok m) := by
    intro m
    rw [ex]
    exact Iff.rfl
  exact ⟨fun ⟨m, a, b'⟩ => ⟨m, (ed m).1 a, b'⟩, fun ⟨m, a, b'⟩ => ⟨m, (ed m).2 a, b'⟩⟩

/-- **At a reached state the way out returns behind every yes.** -/
theorem link_after_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {fs : List LinkFrame} {f : LinkFrame}
    (hfs : framesOf Z.p.built.links Z.first Z.p.X = .ok fs) (hff : fs[l]? = some f)
    (hfp : f.plan = true) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 2) (z, s)) {p : P2}
    (hp : p.stands = .link) {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} {u : S}
    (hy : decideWith sendByL8 p s rs gs = .ok u) : ∃ t, leaveOpened f s u = .ok t := by
  obtain ⟨-, R, C, f₀⟩ := (reach_raw hr).fold
  have hl := (laid_at hS hR O (by omega : l < 25) f₀).2
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hu := P1K2.noMark_switch hS hR O (Or.inl ⟨m, by omega, rfl⟩) hr
  exact leave_returns hfs hff (by omega) hfp hp hy hl hu

/-- **So at a reached state the seated decision says yes wherever the kind's own does**: at the
first top's own letters, with its seven clauses beside. -/
theorem link_seat_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) :
    ∃ (b : Block S Cl) (nm : String) (fs : List LinkFrame) (f : LinkFrame) (Pp : Prep)
      (n : Nums), c.blocksInOrder[14 * l + 2]? = some b ∧
      framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧ fs[l]? = some f ∧ f.plan = true ∧
      prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp (some l) = some n ∧
      (∀ (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), rs.length = 2 →
        gs.length = n.read.length →
        (b.decide s rs gs = .ok t ↔ ∃ m,
          decideWith sendByL8 (k2P Z (switchPlaceAt l) nm .link n) s rs gs = .ok m ∧
            leaveOpened f s m = .ok t)) ∧
      ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 2) (z, s) →
        ∀ (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (u : S), rs.length = 2 →
          gs.length = n.read.length →
          decideWith sendByL8 (k2P Z (switchPlaceAt l) nm .link n) s rs gs = .ok u →
          ∃ t, b.decide s rs gs = .ok t := by
  obtain ⟨b, nm, fs, f, Pp, n, hb, hfs, hff, hfp, hP, hn, hd⟩ :=
    link_seat_decides hS hR O hpl hcut h1 h24
  refine ⟨b, nm, fs, f, Pp, n, hb, hfs, hff, hfp, hP, hn, hd,
    fun z s hr rs gs u h2 hg hy => ?_⟩
  obtain ⟨t, ht⟩ := link_after_reached hS hR O h1 h24 hfs hff hfp hr rfl hy
  exact ⟨t, (hd s t rs gs h2 hg).2 ⟨u, hy, ht⟩⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.k2_openings
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_dress
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_seat_decides
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_after_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_seat_reached
