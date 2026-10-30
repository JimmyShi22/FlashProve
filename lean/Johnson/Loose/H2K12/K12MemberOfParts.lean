-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.AtPlan
/-
H2K12/K12MemberOfParts.lean: FOR THE PROXIMITY
TEST's (the kind K12's) ROW AMONG THE ROWS THAT "the proof file's description returns, with its cut"
WANTS OF EACH LOT: THE ROUTINE THAT MAKES THE KIND's FOUR MEMBERS OFF THE PLAN, WITH WHAT IT READS
OF THE PLANNER's RECORD AS LETTERS. Definitions and four small laws; nothing is evaluated here.
WHY. H2U.placesOfMade (Johnson/Desc/K12/Plan/PlaceOfPlan.lean) takes m : Made, a record too large to
write out. Of m it reads five things alone: the setting and the proof file's sizes
(m.p.chains.made.sized.set | .proof), the planner's three lists of rounds (m.p.chains.made.proof),
the three plans as read back (m.p.chains.proof.first | shared | second .given.plan) and the three
lists of what is sent (m.proof). With these as letters the routine can be evaluated at written
values (H2K12/K12MemberWritten.lean).
  placesAt         placesOfMade's text at the five letters; firstsAt, cutAtP, cutLAt, laterAt: the
                   like for H2U.firstsOfPlan, testCutAt, cutTestL, laterOfProof, which it calls.
                   COPIES OF THESE TEXTS, sign for sign but for the letters
  placesOfMade_eq  H2U.placesOfMade m = placesAt ‹the five reads of m›: at every m, by unfolding: so
                   a copy that parts from its original makes this file red
  sameP12          the test with code: two members agree in all thirteen fields. sameP12_eq: then
                   they are equal
  fourAt           the test with code on a return R of the routine: it returns, it has a place for
                   Omega's test, and H2U.proximityTestParametersAt lays its four places at ⟨1, none, 2⟩, ⟨2, none, 9⟩,
                   ⟨2, none, 10⟩, ⟨3, none, 2⟩ as the four members qL qU qO qW. of_fourAt: what its
                   yes gives. fourNot: R returns, has that place, and each of the four PARTS from
                   its q: for negative tests
  members_of       where fourAt says yes of H2U.placesOfMade m: the four parameters that the
                   description's lots and later seats take (H2U.p12OfMade m, p12FoldedOfMade m 9,
                   p12OmegaOfMade m 10, p12OwnOfMade m 2; Johnson/Desc/K12/AtPlan.lean) are qL qU qO
                   qW
WHAT IT IS NOT: no value is named here. That 9, 10 and 2 are the numbers under which the description
calls the three later ones is not shown here. No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes OnBytes.Params Johnson.G.OfPlan H2U
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.K12 (P12)
open Johnson.G (ChainSends)

/-- `H2U.firstsOfPlan`'s text at its reads. -/
def firstsAt (z : ProofSized) (P0 P1 P2 : Fmt.Plan) (c : ChainSends × ChainSends × ChainSends) :
    Except String Firsts := do
  let S := z.batch.shape
  let t0 ← treesSent "proof file, first chain" c.1 P0 []
  let t1 ← treesSent "proof file, shared chain" c.2.1 P1
    (ownMasks c.2.1.codes S P1.rounds)
  let t2 ← treesSent "proof file, second chain" c.2.2 P2 []
  let riders := z.request.atStart.map (·.leafClass)
  let locs := (P0.rounds.filter fun e => e.name == "LOC").length
  let get {α : Type} (what : String) (x : Option α) : Except String α := match x with
    | some a => pure a
    | none => throw ("firstsOfPlan: the rule has no list for " ++ what)
  let l ← get "the last test" (frameOpens riders t0 locs)[locs]?
  let sh := sharedOpens S t1
  let u ← get "the folded row's test" (sh[1]?)
  let o :=
    if S.sharedSplitNeeded then
      (sh[2 + (switchOpens 0 .folded t1).length]?).map fun x => (x.1.dropLast, 0)
    else none
  let w ← get "the own test"
    (secondOpens S (fun t => t.tag == .link 0 0 && riders.contains t.cls) t0 t1 t2).head?
  pure { L := (l, 0), U := (u.1, 0), O := o, W := (w, t0.length + 1) }

/-- `H2U.testCutAt`'s text at the planner's lists. -/
def cutAtP (Pl : List Planned) (ch i : Nat) (st : List IoppStage) : Option TestCut := do
  let P ← Pl[ch]?
  let es := P.rounds.map (·.entry)
  let cut := (es.drop i).take (1 + towerLen st)
  if st.length < 2 || cut.map (·.name) != "BAT" :: towerNames st then none
  pure ⟨ch, i, cut, ((es.take i).map (·.roots)).foldl (· + ·) 0, st⟩

/-- `H2U.cutTestL`'s, with `H2U.batsOn`, which it calls, laid into it: the one copy that is not line
for line. -/
def cutLAt (Pl : List Planned) (last : List IoppStage) : Option TestCut := do
  cutAtP Pl 0 (← (← (Pl[0]?).map fun P => batPlaces (P.rounds.map (·.entry))).getLast?) last

/-- `H2U.laterOfProof`'s. -/
def laterAt (set : Setting) (z : ProofSized) (Pl : List Planned) (P0 P1 P2 : Fmt.Plan)
    (c : ChainSends × ChainSends × ChainSends) (groupsFirst : Nat) : LaterArgs :=
  let riders := z.request.atStart.map (·.leafClass)
  { file := "proof file", set := set, batch := z.batch
    P0 := P0, P1 := P1, P2 := P2
    c0 := c.1, c1 := c.2.1, c2 := c.2.2, es1 := entriesOf Pl 1, es2 := entriesOf Pl 2
    input := fun t => t.tag == .link 0 0 && riders.contains t.cls, groupsFirst := groupsFirst }

/-- **`H2U.placesOfMade`'s text at its five reads.** -/
def placesAt (set : Setting) (z : ProofSized) (Pl : List Planned) (P0 P1 P2 : Fmt.Plan)
    (c : ChainSends × ChainSends × ChainSends) : Except String Places4 := do
  let Fs ← firstsAt z P0 P1 P2 c
  let locs := (P0.rounds.filter fun e => e.name == "LOC").length
  let get {α : Type} (what : String) (x : Option α) : Except String α := match x with
    | some v => pure v
    | none => throw ("placesOfMade: no cut at " ++ what)
  let tL ← get "the last test" (cutLAt Pl z.request.last)
  let gL := locs + 1
  let X ← placesLater (laterAt set z Pl P0 P1 P2 c (gL + (tL.stages.length - 1)))
  pure
    { L := mkPlace set.samples 1 z.last.stages
        (← get "the rows of the last test" (rowsAtLast z)) (set.workOf .query .request)
        false tL Fs.L gL z.request.choice.masksRide
      U := X.U, O := X.O, W := X.W }

/-- **The two texts are one, at every m.** -/
theorem placesOfMade_eq (m : Made) :
    placesOfMade m = placesAt m.p.chains.made.sized.set m.p.chains.made.sized.proof
      m.p.chains.made.proof m.p.chains.proof.first.given.plan
      m.p.chains.proof.shared.given.plan m.p.chains.proof.second.given.plan m.proof := rfl

/-- Two members agree in all thirteen fields. -/
def sameP12 (p q : P12) : Bool :=
  decide (p.place = q.place) && decide (p.nums.rows = q.nums.rows) &&
    decide (p.nums.work = q.nums.work) && decide (p.nums.stages = q.nums.stages) &&
    decide (p.nums.ownMask = q.nums.ownMask) && decide (p.nums.first = q.nums.first) &&
    decide (p.nums.free = q.nums.free) && decide (p.nums.firstTree = q.nums.firstTree) &&
    decide (p.idx = q.idx) && decide (p.oracles = q.oracles) && decide (p.before = q.before) &&
    decide (p.answers = q.answers) && decide (p.early = q.early)

theorem sameP12_eq {p q : P12} (h : sameP12 p q = true) : p = q := by
  unfold sameP12 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  obtain ⟨a, ⟨n1, n2, n3, n4, n5, n6, n7⟩, c, d, e, f, g⟩ := p
  obtain ⟨a', ⟨m1, m2, m3, m4, m5, m6, m7⟩, c', d', e', f', g'⟩ := q
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rfl

/-- **A return of the routine gives the four members.** -/
def fourAt (R : Except String Places4) (qL qU qO qW : P12) : Bool :=
  match R with
  | .ok X =>
    sameP12 (proximityTestParametersAt ⟨1, none, 2, .K12⟩ X.L) qL && sameP12 (proximityTestParametersAt ⟨2, none, 9, .K12⟩ X.U) qU &&
      (match X.O with
        | some o => sameP12 (proximityTestParametersAt ⟨2, none, 10, .K12⟩ o) qO
        | none => false) &&
      sameP12 (proximityTestParametersAt ⟨3, none, 2, .K12⟩ X.W) qW
  | .error _ => false

/-- It returns, and each of the four parts from its q. -/
def fourNot (R : Except String Places4) (qL qU qO qW : P12) : Bool :=
  match R with
  | .ok X =>
    !sameP12 (proximityTestParametersAt ⟨1, none, 2, .K12⟩ X.L) qL && !sameP12 (proximityTestParametersAt ⟨2, none, 9, .K12⟩ X.U) qU &&
      (match X.O with
        | some o => !sameP12 (proximityTestParametersAt ⟨2, none, 10, .K12⟩ o) qO
        | none => false) &&
      !sameP12 (proximityTestParametersAt ⟨3, none, 2, .K12⟩ X.W) qW
  | .error _ => false

theorem of_fourAt {R : Except String Places4} {qL qU qO qW : P12}
    (h : fourAt R qL qU qO qW = true) :
    ∃ X o, R = .ok X ∧ X.O = some o ∧ proximityTestParametersAt ⟨1, none, 2, .K12⟩ X.L = qL ∧
      proximityTestParametersAt ⟨2, none, 9, .K12⟩ X.U = qU ∧ proximityTestParametersAt ⟨2, none, 10, .K12⟩ o = qO ∧
      proximityTestParametersAt ⟨3, none, 2, .K12⟩ X.W = qW := by
  cases R with
  | error e => exact absurd h (by simp [fourAt])
  | ok X =>
    have h' : (sameP12 (proximityTestParametersAt ⟨1, none, 2, .K12⟩ X.L) qL &&
        sameP12 (proximityTestParametersAt ⟨2, none, 9, .K12⟩ X.U) qU &&
        (match X.O with
          | some o => sameP12 (proximityTestParametersAt ⟨2, none, 10, .K12⟩ o) qO
          | none => false) &&
        sameP12 (proximityTestParametersAt ⟨3, none, 2, .K12⟩ X.W) qW) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
    cases hO : X.O with
    | none =>
      rw [hO] at h3
      exact absurd h3 (by simp)
    | some o =>
      rw [hO] at h3
      exact ⟨X, o, rfl, hO, sameP12_eq h1, sameP12_eq h2, sameP12_eq h3, sameP12_eq h4⟩

/-- **The four parameters that the description takes.** -/
theorem members_of (m : Made) {qL qU qO qW : P12}
    (h : fourAt (placesOfMade m) qL qU qO qW = true) :
    p12OfMade m = qL ∧ p12FoldedOfMade m 9 = qU ∧ p12OmegaOfMade m 10 = qO ∧
      p12OwnOfMade m 2 = qW := by
  obtain ⟨X, o, hX, hO, h1, h2, h3, h4⟩ := of_fourAt h
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold p12OfMade
    rw [hX]
    exact h1
  · unfold p12FoldedOfMade
    rw [hX]
    exact h2
  · unfold p12OmegaOfMade
    rw [hX]
    show ((X.O.map (proximityTestParametersAt ⟨2, none, 10, .K12⟩)).getD (noP12 ⟨2, none, 10, .K12⟩)) = qO
    rw [hO]
    exact h3
  · unfold p12OwnOfMade
    rw [hX]
    exact h4

end H2K12

#print axioms H2K12.placesOfMade_eq
#print axioms H2K12.sameP12_eq
#print axioms H2K12.of_fourAt
#print axioms H2K12.members_of
