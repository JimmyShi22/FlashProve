-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Joined.lean: the honest side of the kind "lookup" (K3). The
main theorems, composed: the frame's `play` on the seated row's steps at a sub-protocol returns, the
sub-protocol's own step accepts on what was played, and what holds behind the hearing is at hand.
One general form (`joined_of`) and four cases of it, by what stands behind the lookup in the
sub-protocol: nothing (`joined_plain`); the step behind a layers' link's calls (`joined_look`); the
step behind the digits of a layers' or an attention link (`joined_digits`); the step behind the
head's digits (`joined_head`, conditional on `HeadBehind` besides). Theorems, with two definitions.

The acceptance is said at any summands: it says nothing on values. All worth lies in `Left`, inside
`BehindYes`: conditional on `Lawful`, and at mask entries that are the coins spent.

Terms. Honest/K3/GLOSSARY.md ("hearing", "lawful", "play", "step", "sub-protocol", "world, worth").
`BehindYes` is the conclusion of `LeftInner` (Honest/K3/Law/Top.lean), under a name; `JoinedAt` is
what the composition concludes.

What is shown.
  `steps_eq`, `played_length`: the frame's steps of the half at a sub-protocol are `seatSteps`; what
    was played has as many rounds as there are entries.
  `joined_of`: the general form: `JoinedAt`.
  `joined_plain`, `joined_look`, `joined_digits`, `joined_head`: the four cases named above.

Hypotheses that remain. None of them is shown here.
  All five forms ask: `hS`, `hL`: `Stands` and `LedgerIn` (Top.lean). `ha`: the face is that of a
    shape (so: one part of keys). Of the sub-protocol: `hpl`: it stands at the place; `hr`: its
    rounds are the entries'; `ho`: it states no oracle message at any round; `hrd`: the row has as
    many moves as the sub-protocol has rounds.
  `hbl`: it decides on rounds without their digests as on the rounds: asked in all but
    `joined_plain`, which shows it from `hb`.
  `joined_of` asks besides `hyes`: wherever the hearing returns on as many rounds, the decision
    accepts, with Q behind it.
  The four cases ask in its place: `hb`: the decision has the form that is named; `hp`, `hN`: the
    place's parameters make the shape; it has more than one call; of the verifier's state in front:
  `hF`, `h0`, `hO`: the ledger is open, nothing was heard yet, no row waits. Public, in three of
    them:
  `hpr`: the parameters state as many rounds as there are entries; `hfs` (in `joined_look`): the
    shape is the layout's; `hu` (in `joined_digits`): the lookup ends at the plan's number of slots.
    `hHB` (in `joined_head`): wherever the hearing returns and the seated decision accepts, the step
    behind the head's digits returns (`HeadBehind`, Honest/K3/Law/StatedMember.lean).
  `hy`: (in `played_length`) the play returns.

Imported. All of this rests on the theorems of Honest/SumLaw/ (through Honest/K3/Law/HBPaid.lean).

Users. This file is imported by Honest/K3/Law/JoinedMember.lean [not in this library],
Honest/K3/Law/MemberYes.lean and Honest/K3/Law/Thread/Plays.lean.

Limits. A sub-protocol here is a letter with hypotheses on its form: that the description's member
at a lookup's place is such a sub-protocol is other files' to show. Shown in part:
Honest/K3/Law/MemberSite.lean shows the public hypotheses at a site, from the member's own test on
the plan and from tests with code; what stands in front of the lookup remains a hypothesis there.
An instance of all hypotheses of `joined_plain`, at one synthetic place:
Honest/K3/Law/JoinedMember.lean [not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.HBPaid
import Johnson.Desc.ProofFile.Honest.K3.Law.StatedMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open OnBytes.Model (Fork Aff)
open OnBytes.Slice (GE)
open OnBytes.Model.Forest (Shape)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Place Oracle OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG seatCalls seatDigits
  quietHead quietLook
  quietDigits)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First.Look (P sameShape)
open ProofFile.Honest.K3.NoDigest (decideVia_noDigest)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Cl V₁ W₁ X₁ W : Type}

/-- The frame's steps of the half at a sub-protocol are `seatSteps`, where the sub-protocol stands
at the place, has the entries' rounds, and states no oracle message at any round. -/
theorem steps_eq (a : At) (J : LookJobs W) (wit : W₁ → W) (v : Option V₁)
    (es : List Fmt.Entry) (b : Block FS Cl) (hpl : b.place = a.place)
    (hr : b.rounds = es.map declOf) (ho : b.oracles = es.map fun _ => [])
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts) :
    (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a).steps b v c = seatSteps a J wit b.name v es c := by
  show rowSteps b.name b.place v _ 0 (b.rounds.zip b.oracles) c =
    rowSteps b.name a.place v _ 0 (es.map fun e => (declOf e, ([] : List Oracle))) c
  rw [hpl, hr, ho, List.zip_map']

/-- What was played has as many rounds as there are entries. -/
theorem played_length (a : At) (J : LookJobs W) (wit : W₁ → W) (name : String) (v : Option V₁)
    (es : List Fmt.Entry) (m : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (y : List Played × Mid W₁ X₁) (hS : Stands a es m ds)
    (hy : play (seatSteps a J wit name v es c) ds [] m = .ok y) :
    (roundsOf y.1).length = es.length := by
  obtain ⟨c', _, hplay⟩ := rowPlaysSeated V₁ W₁ X₁ W
    (courseAt a J 0 wit m ds (courseCoins a fun _ _ _ => 0)) wit m.st name v es m.loc c rfl
  obtain ⟨y', x, hy', hx, hyx, _, _⟩ := hplay (fit_of_stands hS J 0 wit _) hS.entries []
  have e : y' = y := Except.ok.inj (hy'.symm.trans hy)
  subst e
  subst hyx
  have hx' : (courseAt a J 0 wit m ds c').rounds = some (roundsOf y'.1) := hx
  have C := cut_of_rounds _ _ (fit_of_stands hS J 0 wit c') hx'
  have h1 : (roundsOf y'.1).length = ds.length := by
    have := congrArg List.length C.drawn
    rw [List.length_map] at this
    exact this
  rw [h1, drawsFit_length _ _ hS.draws, List.length_map]

/-- **What holds behind the hearing's return**: the conclusion of `LeftInner`
(Honest/K3/Law/Top.lean), under a name. Its last clause is conditional on `Lawful`. -/
def BehindYes (a : At) (J : LookJobs W) (first : Nat) (wit : W₁ → W) (m : Mid W₁ X₁)
    (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts) (g : HeardV)
    (G : Fork) : Prop :=
  ∃ c' : (s : Stage) → StageCoins a s,
    CoinsAre (V := Unit) (courseAt a J first wit m ds c')
      (unlift (X := X₁) (fun (_ : V₁) => ()) wit (lookRow ⟨ptsOf, pointsAt⟩ J a) c) ∧
    HeardIs (courseAt a J first wit m ds c') g ∧
    PointsAgree a.face g a.base (m.st.heard ++ ds) ∧
    Inv (courseAt a J first wit m ds c') (stages a.face).length G ∧
    ∀ (planes : List (E × E) → GE) (keys : Nat → Array E → GE),
      Lawful (courseAt a J first wit m ds c') planes keys →
      Left (courseAt a J first wit m ds c') planes keys g G

/-- **What the composition concludes.** Q: what is said of the state that the sub-protocol's step
leaves, with what was heard and the ledger behind it. The play returns; all that it leaves (the
columns opened stand as they stood in front); every round bears the place and no table; no column is
read; the sub-protocol's own step accepts on what was played, with no column; `hearV` has returned
on it; Q; `BehindYes`. -/
def JoinedAt (b : Block FS Cl) (a : At) (J : LookJobs W) (wit : W₁ → W) (v : Option V₁)
    (m : Mid W₁ X₁)
    (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts) (first : Nat)
    (s : FS) (F : Fork) (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (Q : FS → HeardV → Fork → Prop) : Prop :=
  ∃ y s' g G, play ((proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a).steps b v c) ds [] m = .ok y ∧
    y.2 = ⟨{ m.st with heard := m.st.heard ++ ds }, m.loc ++ ds, m.seen ++ roundsOf y.1, m.opened⟩ ∧
    (∀ q ∈ y.1, q.place = a.place ∧ q.told = true ∧ q.tables = []) ∧
    fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] ∧
    b.step ft s (roundsOf y.1) [] = .ok (s', 0) ∧
    hearV a.face F (roundsOf y.1) = some (g, G) ∧ Q s' g G ∧ BehindYes a J first wit m ds c g G

/-- **The composition, for whatever the sub-protocol does behind the hearing.** Conditional on
`Stands`; `LedgerIn`; the face being a shape's; the hypotheses on the sub-protocol's form (`hpl`,
`hr`, `ho`, `hrd`, `hbl`); and on `hyes`: wherever `hearV` has returned on as many rounds as there
are entries, the sub-protocol's decision accepts, with Q of the state that it leaves. It rests on
the theorems of Honest/SumLaw/. It holds for every such sub-protocol: the description's own member
at a lookup's place (the lot's sub-protocol with guards around it, under the place's name) is served
by this form, not by the four cases below, which speak of the lot's sub-protocol. -/
theorem joined_of (Q : FS → HeardV → Fork → Prop) (h : Shape) (first : Nat) (b : Block FS Cl)
    (hbl : DecidesBlind b) (a : At)
    (ha : a.face = faceOf h) (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (es : List Fmt.Entry)
    (hpl : b.place = a.place) (hr : b.rounds = es.map declOf) (ho : b.oracles = es.map fun _ => [])
    (m : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (hrd : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).rounds = b.rounds.length)
    (s : FS) (F : Fork) (hS : Stands a es m ds) (hL : LedgerIn a.face first F)
    (hyes : ∀ (rs : List Fmt.RoundView) (g : HeardV) (G : Fork) (gs : List (List (Nat × List UInt64))),
      rs.length = es.length → hearV (faceOf h) F rs = some (g, G) →
      ∃ s', b.decide s rs gs = .ok s' ∧ Q s' g G)
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    JoinedAt b a J wit v m ds c first s F chain ft stored tree Q := by
  obtain ⟨y, hy, hy2, hq, hc⟩ :=
    movedInner V₁ W₁ X₁ W a J wit b.name v es m ds c chain ft stored tree hS
  have hp1 : a.face.parts = [h.v] := by rw [ha]; rfl
  obtain ⟨g, G, hh⟩ := heardInnerP V₁ W₁ X₁ W a J wit b.name v es m ds c first F h.v y hS hp1 hL hy
  have hB : BehindYes a J first wit m ds c g G :=
    leftInnerP V₁ W₁ X₁ W a J wit b.name v es m ds c first F G h.v y g hS hp1 hL hy hh
  have hh' : hearV (faceOf h) F (roundsOf y.1) = some (g, G) := by rw [← ha]; exact hh
  have hy' : play ((proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a).steps b v c) ds [] m = .ok y := by
    rw [steps_eq a J wit v es b hpl hr ho c]
    exact hy
  have hc' : fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] := by rw [hr]; exact hc
  obtain ⟨s', hd, hQ⟩ := hyes (roundsOf y.1) g G
    (VerifiableInference.Desc.regroup
      ((VerifiableInference.Desc.groupsOf ft b.rounds ds).map (·.length)) [])
    (played_length a J wit b.name v es m ds c y hS hy) hh'
  refine ⟨y, s', g, G, hy', hy2, hq, hc', ?_, hh, hQ, hB⟩
  exact (step_yes (chain := chain) (stored := stored) (tree := tree) (cols := []) s s' hbl hrd
    (by rw [hr, ho, List.length_map, List.length_map]) hy' (by rw [hr]; exact hS.draws) hc').2 hd

/-- **The composition where nothing stands behind the lookup.** Conditional as `joined_of`, but that
`hbl` is shown from `hb`; its `hyes` is shown by `stated_yes_plain` from: the place's shape; more
than one call; the ledger open; nothing heard; no row waits. Of the state behind: it holds what was
heard, as the seat keeps it, and the ledger behind the hearing; its mark is as it was. It rests on
the theorems of Honest/SumLaw/. -/
theorem joined_plain (claim : Aff → Cl) (p : P) (h : Shape) (digits : Bool) (b : Block FS Cl)
    (hb : ∀ s rs gs, b.decide s rs gs = decideVia (seatOf claim digits) p s rs) (a : At)
    (ha : a.face = faceOf h) (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (es : List Fmt.Entry)
    (hpl : b.place = a.place) (hr : b.rounds = es.map declOf) (ho : b.oracles = es.map fun _ => [])
    (m : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (hrd : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).rounds = b.rounds.length)
    (s : FS) (F : Fork) (hS : Stands a es m ds) (hL : LedgerIn a.face p.first F)
    (hp : p.shape = some h) (hN : 1 < h.NC) (hF : (seatOf claim digits).fork s = some F)
    (h0 : ((seatOf claim digits).heard s).isNone = true)
    (hO : ((seatOf claim digits).owed s).noneWaits = true)
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    JoinedAt b a J wit v m ds c p.first s F chain ft stored tree fun s' g G =>
      ∃ g', toHeard h (toHeardG g) = some g' ∧ (seatOf claim digits).heard s' = some g' ∧
        (seatOf claim digits).fork s' = some G ∧ s'.failed = s.failed :=
  joined_of _ h p.first b (fun s rs gs => by rw [hb, hb, decideVia_noDigest]) a ha J wit v es hpl hr
    ho m ds c hrd s F hS hL
    (fun _ _ _ gs _ hh =>
      let ⟨g', s', hg, hd, a1, a2, a3⟩ :=
        stated_yes_plain claim p h digits b hb s gs hp hN hF h0 hO hL.next hh
      ⟨s', hd, g', hg, a1, a2, a3⟩)
    chain ft stored tree

/-- **The composition behind a layers' link's calls.** Conditional as `joined_of` (`hbl` among it);
its `hyes` is shown by `stated_yes_look` from the hypotheses of `joined_plain` and two public ones:
the place's shape is the layout's; the parameters state as many rounds as there are entries. It
rests on the theorems of Honest/SumLaw/. -/
theorem joined_look (claim : Aff → Cl) (p : P) (h fs : Shape) (b : Block FS Cl)
    (hb : ∀ s rs gs, b.decide s rs gs =
      (decideVia (seatOf claim false) p s (rs.take p.rounds.length)).bind (quietLook fs))
    (hbl : DecidesBlind b) (a : At)
    (ha : a.face = faceOf h) (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (es : List Fmt.Entry)
    (hpl : b.place = a.place) (hr : b.rounds = es.map declOf) (ho : b.oracles = es.map fun _ => [])
    (hpr : p.rounds.length = es.length) (m : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (hrd : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).rounds = b.rounds.length)
    (s : FS) (F : Fork) (hS : Stands a es m ds) (hL : LedgerIn a.face p.first F)
    (hp : p.shape = some h) (hN : 1 < h.NC) (hfs : sameShape h fs = true)
    (hF : (seatCalls claim).fork s = some F) (h0 : ((seatCalls claim).heard s).isNone = true)
    (hO : ((seatCalls claim).owed s).noneWaits = true)
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    JoinedAt b a J wit v m ds c p.first s F chain ft stored tree fun s' g G =>
      ∃ g', toHeard h (toHeardG g) = some g' ∧ (seatCalls claim).heard s' = some g' ∧
        (seatCalls claim).fork s' = some G ∧ s'.failed = s.failed :=
  joined_of _ h p.first b hbl a ha J wit v es hpl hr ho m ds c hrd s F hS hL
    (fun _ _ _ gs hl hh =>
      let ⟨g', s', hg, hd, a1, a2, a3⟩ :=
        stated_yes_look claim p h fs b hb s gs (hl.trans hpr.symm) hp
        hN hfs hF h0 hO hL.next hh
      ⟨s', hd, g', hg, a1, a2, a3⟩)
    chain ft stored tree

/-- **The composition behind the digits of a layers' or an attention link.** Conditional as
`joined_of` (`hbl` among it); its `hyes` is shown by `stated_yes_digits` from the hypotheses of
`joined_plain` and two public ones: the lookup's hidden values end at the plan's number of slots;
the parameters state as many rounds as there are entries. It rests on the theorems of
Honest/SumLaw/. s' is bound by "∃": some state of the verifier's between two steps, held by what
readers return of it; there is no equation on it. -/
theorem joined_digits (claim : Aff → Cl) (p : P) (h : Shape) (used claims : Nat) (b : Block FS Cl)
    (hb : ∀ s rs gs, b.decide s rs gs =
      (decideVia (seatOf claim true) p s (rs.take p.rounds.length)).bind (quietDigits used claims))
    (hbl : DecidesBlind b) (a : At)
    (ha : a.face = faceOf h) (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (es : List Fmt.Entry)
    (hpl : b.place = a.place) (hr : b.rounds = es.map declOf) (ho : b.oracles = es.map fun _ => [])
    (hpr : p.rounds.length = es.length) (m : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (hrd : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).rounds = b.rounds.length)
    (s : FS) (F : Fork) (hS : Stands a es m ds) (hL : LedgerIn a.face p.first F)
    (hp : p.shape = some h) (hN : 1 < h.NC) (hu : p.first + (faceOf h).slots = used)
    (hF : (seatDigits claim).fork s = some F) (h0 : ((seatDigits claim).heard s).isNone = true)
    (hO : ((seatDigits claim).owed s).noneWaits = true)
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    JoinedAt b a J wit v m ds c p.first s F chain ft stored tree fun t g G =>
      ∃ g' s', toHeard h (toHeardG g) = some g' ∧ t = s'.putFork { G with planClaimsF := claims } ∧
        (seatDigits claim).heard s' = some g' ∧ s'.failed = s.failed :=
  joined_of _ h p.first b hbl a ha J wit v es hpl hr ho m ds c hrd s F hS hL
    (fun _ _ _ gs hl hh =>
      let ⟨g', s', hg, _, hd, a1, a3⟩ := stated_yes_digits claim p h used claims b hb s gs
        (hl.trans hpr.symm) hp hN hu hL.sized hF h0 hO hL.next hh
      ⟨_, hd, g', s', hg, rfl, a1, a3⟩)
    chain ft stored tree

/-- **The composition behind the head's digits.** Conditional as `joined_of` (`hbl` among it), on
the hypotheses of `joined_plain`, on the parameters stating as many rounds as there are entries, and
on `HeadBehind`: the step without a round that stands behind that lookup returns at the state that
the lookup's own decision leaves, wherever `hearV` has returned on as many rounds as there are
entries: other kinds' hypotheses (Honest/K3/Law/StatedMember.lean lists them). No instance of these
hypotheses is exhibited in this file. It rests on the theorems of Honest/SumLaw/. s' is bound by
"∃": some state of the verifier's between two steps, held by what readers return of it; there is no
equation on it. -/
theorem joined_head (claim : Aff → Cl) (X : OnBytes.Model.Verify.Public) (p : P) (h : Shape)
    (b : Block FS Cl)
    (hb : ∀ s rs gs, b.decide s rs gs =
      (decideVia (seatOf claim true) p s (rs.take p.rounds.length)).bind (quietHead X))
    (hbl : DecidesBlind b) (a : At)
    (ha : a.face = faceOf h) (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (es : List Fmt.Entry)
    (hpl : b.place = a.place) (hr : b.rounds = es.map declOf) (ho : b.oracles = es.map fun _ => [])
    (hpr : p.rounds.length = es.length) (m : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (hrd : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).rounds = b.rounds.length)
    (s : FS) (F : Fork) (hS : Stands a es m ds) (hL : LedgerIn a.face p.first F)
    (hp : p.shape = some h) (hN : 1 < h.NC)
    (hF : (seatDigits claim).fork s = some F) (h0 : ((seatDigits claim).heard s).isNone = true)
    (hO : ((seatDigits claim).owed s).noneWaits = true)
    (hHB : ∀ rs g G s', rs.length = es.length → hearV (faceOf h) F rs = some (g, G) →
      decideVia (seatDigits claim) p s rs = .ok s' → ∃ t', HeadBehind X s' t')
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    JoinedAt b a J wit v m ds c p.first s F chain ft stored tree fun t g G =>
      ∃ g' s', toHeard h (toHeardG g) = some g' ∧ (seatDigits claim).heard s' = some g' ∧
        (seatDigits claim).fork s' = some G ∧ s'.failed = s.failed ∧ HeadBehind X s' t :=
  joined_of _ h p.first b hbl a ha J wit v es hpl hr ho m ds c hrd s F hS hL
    (fun rs g G gs hl hh =>
      let ⟨g', s', hg, hd, a1, a2, a3, hall⟩ := stated_yes_head claim X p h b hb s gs
        (hl.trans hpr.symm) hp hN hF h0 hO hL.next hh
      let ⟨t', ht⟩ := hHB rs g G s' hl hh hd
      ⟨t', hall t' ht, g', s', hg, a1, a2, a3, ht⟩)
    chain ft stored tree

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.steps_eq
#print axioms ProofFile.Honest.K3.Law.played_length
#print axioms ProofFile.Honest.K3.Law.joined_of
#print axioms ProofFile.Honest.K3.Law.joined_plain
#print axioms ProofFile.Honest.K3.Law.joined_look
#print axioms ProofFile.Honest.K3.Law.joined_digits
#print axioms ProofFile.Honest.K3.Law.joined_head
