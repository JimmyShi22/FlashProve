-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchCovers.lean: at the written numbers of both examples, the errors of the plan's two
rounds SEND seed and LOC cover the two errors of the code switch's block, round by round, at the
caller with kept members: every premise of `sendLoc_covers` is shown; and each of the block's two
errors, as a share, is at most 2 ^ work / 2 ^ target, at the plan's bits of work.

`sendLoc_covers` (OnBytes/Tie/Pv/Switch/SendLocPrices.lean) takes the conditions on the prices
(`SendLocPrices`), the conditions on the shape (`SendLocFits`, SendLocShape.lean), and what the
planner has tested of the two rounds (`RoundSpec.Good`, OnBytes/Params/PlanningLaws.lean).
Johnson/G/SwitchKeptLit.lean has the first. The bijections of the second are those of
Johnson/Pack/SeedDraw.lean. The third is a test on numbers, evaluated in Lean's kernel. With the
planner's own test that a round holds at the target, work counted (`roundHolds`,
OnBytes/Params/Planner.lean), OnBytes/Tie/Pv/Below.lean gives `Err.BelowG`. Near kin in the library:
Johnson/Top/H/SendAt.lean (the round SEND seed covers a sending's error, for the kind of a sending
alone; its `cube_eq` has in general what `sendsFull_ok` evaluates at the written lists: the largest
cube is `bMax`), OnBytes/Tie/Pv/Held.lean (`share_of_holds`, `held_of_covered`: the like bound in
the form of `Maps.Held`), OnBytes/Tie/Pv/TestPort.lean (a key's second chain). Definitions,
statements and proofs.
Main names:
  `goodB`, `good_of`, `holds_of`: what the planner has tested of a round, and that the round holds
    at the target, as one test; its yes gives `RoundSpec.Good` and `roundHolds`. The test reads the
    round's bound, work and draws alone, not its bytes, roots and answers: so one evaluation at 0
    serves all of these.
  `CoveredBy z ys`, `coveredBy_of`: round by round, the block's count of bad values over its number
    of values is at most the error that the plan holds for the planned round (`Cb.Pv.Covered`,
    OnBytes/Tie/Pv/PortKit.lean); from the form in which `sendLoc_covers` concludes.
  `bitsTwo`, `belowG_two`: bits of work for the block's two rounds; `Err.BelowG` of the block's
    errors at 1 / 2 ^ target, from `CoveredBy` and `roundHolds` at the two planned rounds.
  `sendsFull_ok`, `locFull_ok`, and the same with Small: the evaluations.
  `shape_full`, `shape_small`: `SendLocFits` of `switchOf` at `heldAtFull`, `heldAtSmall`, where as
    many positions are drawn as the planner's `baseCount` says.
  `two_lanes_full`, `two_lanes_small`: `CoveredBy` of that caller.
  `two_lanes_full_vec`, `two_lanes_small_vec`: the same, with `SendLocRide.OK`, at the caller
    `switchVec` (Johnson/Top/H/SwitchVec.lean), and so at `switchSel`.
  `level_full_vec`, `level_small_vec`: `Err.BelowG` there, at the bits of work that the plan holds
    for the two rounds.
Limits: those of Johnson/G/SwitchKeptLit.lean: written numbers, tied to the planner by an evaluation
outside these files; the samples `oOf` are made of the messages' own cubes and one pricing group;
the stage's group gs and the group g that prices LOC are free of each other, and list, sending and
groups are free of each other: the statements hold at every choice, not at a place's own alone; the
other letters' types are not shown to have a value. That a switch of the programs' protocol is a
value of these callers is not said. `CoveredBy` is on the prices with the proof of work not counted.
`Err.BelowG` is a statement on numbers: that work is worth its bits is not said here; it is a bound
on each round, not on a sum over rounds; and the planner's addition for the distance from uniform
of its draws is dropped (the limits of OnBytes/Tie/Pv/Below.lean). That the two counts bound a
prover's chance is `SendLocRide.hAt`, under `SendLocRide.OK`. No error is written out here. Nothing
on soundness.

-/
import Johnson.G.SwitchKeptLit
import Johnson.Top.H.SwitchVec
import Johnson.Pack.SeedDraw
import OnBytes.Tie.Pv.Below

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open scoped ENNReal

/-- What the planner has tested of a round, as a test. -/
def goodB (s : Setting) (c : Scope) (x : RoundSpec) : Bool :=
  decide ((x.bound s c).bad = false) && decide (x.work s c < s.target) &&
    decide (x.work s c ≠ 0 → x.work s c + 6 ≤ 8 * s.nonceBytes) &&
    roundHolds s (capped s) (x.round s c)

theorem good_of (s : Setting) (c : Scope) (x : RoundSpec) (h : goodB s c x = true) :
    x.Good s c := by
  unfold goodB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  cases x with
  | said _ _ _ _ _ _ _ => exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
  | silent _ _ _ => trivial
  | record _ _ _ => trivial

theorem holds_of (s : Setting) (c : Scope) (x : RoundSpec) (h : goodB s c x = true) :
    roundHolds s (capped s) (x.round s c) = true := by
  unfold goodB at h
  exact (Bool.and_eq_true_iff.1 h).2

/-- Round by round, the block's count over its number of values is at most the error that the plan
holds for the planned round (`Cb.Pv.Covered`, OnBytes/Tie/Pv/PortKit.lean). -/
def CoveredBy (z : Cb.Pv.SendLocRide.Size GE) (ys : List RoundSpec) : Prop :=
  List.Forall₂ (Cb.Pv.Covered setLit .request)
    ((Err.toList (Cb.Pv.SendLocRide.eps z)).zip (Shape.chalList (Cb.Pv.SendLocRide.R z).shape))
    ys

/-- From the form in which `sendLoc_covers` concludes. -/
theorem coveredBy_of {z : Cb.Pv.SendLocRide.Size GE} {ys : List RoundSpec}
    (h : List.Forall₂
      (fun (x : ℕ × ℕ) (ρ : PlanRound) => (x.1 : ℝ) / (x.2 : ℝ) ≤ ((ρ.error.val : ℚ) : ℝ))
      ((Err.toList (Cb.Pv.SendLocRide.eps z)).zip
        (Shape.chalList (Cb.Pv.SendLocRide.R z).shape))
      (ys.map fun y => y.round setLit .request)) : CoveredBy z ys :=
  (List.forall₂_map_right_iff (f := fun y : RoundSpec => y.round setLit .request)).1 h

/-- Bits of work for the block's two rounds. -/
def bitsTwo (z : Cb.Pv.SendLocRide.Size GE) (a b : ℕ) : GBits (Cb.Pv.SendLocRide.R z).shape :=
  (a, b, ())

/-- Two rounds that are covered by planned rounds which hold in the planner's reckoning: each of
the block's two errors, as a share, is at most 2 ^ work / 2 ^ target, at the plan's bits of work. -/
theorem belowG_two {z : Cb.Pv.SendLocRide.Size GE} {y₁ y₂ : RoundSpec}
    (h : CoveredBy z [y₁, y₂])
    (h₁ : roundHolds setLit (capped setLit) (y₁.round setLit .request) = true)
    (h₂ : roundHolds setLit (capped setLit) (y₂.round setLit .request) = true) :
    Err.BelowG
      (bitsTwo z (Cb.Pv.heldWork setLit .request y₁) (Cb.Pv.heldWork setLit .request y₂))
      (Cb.Pv.SendLocRide.eps z) (ENNReal.ofReal ((2 : ℝ) ^ setLit.target)⁻¹) :=
  Cb.Pv.belowG_of_covered setLit .request _ (by positivity) _ _ _ [y₁, y₂] h rfl fun y hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Cb.Pv.held_of_holds h₁
    · obtain rfl := List.mem_singleton.1 hy
      exact Cb.Pv.held_of_holds h₂

/-! ### The full example -/

set_option maxRecDepth 1000000 in
/-- At each written sending and either pricing group: the sending is not empty; the largest cube of
its samples is the joint seed's number of coordinates; the round SEND seed passes the test. -/
theorem sendsFull_ok : ∀ l ∈ swSendsFull, ∀ pg ∈ priceFull, l ≠ [] ∧
    largestCube (oOf codesFull2 pg l) = bMax codesFull2 l ∧
    goodB setLit .request (sendSeed setLit (oOf codesFull2 pg l) 0) = true := by decide +kernel

/-- At each group in front the round LOC passes the test. -/
theorem locFull_ok : ∀ g ∈ frontFull,
    goodB setLit .request (locRound setLit .request g 0 0 0) = true := by decide +kernel

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (t₀ : ℕ) (oM oZ : Fin lo.length → ℕ)
  (kp : {i // memMain lo i} → Prop) [DecidablePred kp]
  (h0 : ∀ a, kp a → (lo.get a.1).1.maskRows = 0) (kq : Fin lo.length → Prop) [DecidablePred kq]

local notation "HdE" => heldAtFull lo hlo gs hgs t₀ oM oZ kp h0 kq

variable {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsAtFull lo hlo gs hgs t₀ oM oZ).G.C.J)
  (Z : Evader GE ((rowsAtFull lo hlo gs hgs t₀ oM oZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub kq).Msg × Wp))
  {l : List (OracleShape × ℕ)} (hl : l ∈ swSendsFull) {pg g : GroupSize}
  (hp : pg ∈ priceFull) (hg : g ∈ frontFull) {Pw : Type} (Cw : LdCode GE Pw)

local notation "tE" => baseCount setLit Scope.request g

include hl hp hg in
/-- The conditions on the shape, at as many positions as the planner draws. -/
theorem shape_full (cutN : (sigOf codesFull2 l).Msg → ((HdE).foldD Sb sl Z A₀).Cf.N.Wit)
    (w₀ : ((HdE).foldD Sb sl Z A₀).tgt.W) :
    SendLocFits (switchOf HdE Sb sl Z A₀ codesFull2 l cutN tE w₀ Cw) setLit.samples
      (largestCube (oOf codesFull2 pg l)) (setLit.samples * (oOf codesFull2 pg l).length) tE
      g.main.logN := by
  obtain ⟨hne, hc, -⟩ := sendsFull_ok l hl pg hp
  rw [hc]
  show SendLocFits _ 1 (bMax codesFull2 l) (1 * (oOf codesFull2 pg l).length) _ _
  rw [Nat.one_mul, show (oOf codesFull2 pg l).length = l.length from List.length_map _]
  exact ⟨⟨eS codesFull2 l⟩, (member_place codesFull2 l hne).map Sum.inr, ⟨eA codesFull2 l⟩, rfl,
    ⟨finCongr (by
      show 2 ^ (stageOf gs 0).C.a = 2 ^ (stageOf g 0).C.a
      rw [(tablesFull_ok gs hgs).1, (tablesFull_ok g hg).1])⟩⟩

include hl hp hg in
/-- The plan's two errors cover the block's two errors, round by round. -/
theorem two_lanes_full (cutN : (sigOf codesFull2 l).Msg → ((HdE).foldD Sb sl Z A₀).Cf.N.Wit)
    (w₀ : ((HdE).foldD Sb sl Z A₀).tgt.W)
    (roots b r a : ℕ) :
    CoveredBy (switchOf HdE Sb sl Z A₀ codesFull2 l cutN tE w₀ Cw)
      [sendSeed setLit (oOf codesFull2 pg l) roots,
        locRound setLit .request g b r a] :=
  coveredBy_of <| sendLoc_covers
    (kept_both_full_at lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg cutN _ w₀ Cw).2 .request
        roots
    (shape_full lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg Cw cutN w₀) b r a
    (good_of _ _ _ (sendsFull_ok l hl pg hp).2.2) (good_of _ _ _ (locFull_ok g hg))

include hl hp hg in
/-- The same at the caller whose claim is stated by its vector, with that caller's condition. -/
theorem two_lanes_full_vec (cutN : (sigOf codesFull2 l).Msg → ((HdE).foldD Sb sl Z A₀).Cf.N.Wit)
    (w₀ : ((HdE).foldD Sb sl Z A₀).tgt.W)
    (roots b r a : ℕ) :
    Cb.Pv.SendLocRide.OK (switchVec HdE Sb sl Z A₀ codesFull2 l cutN tE w₀ Cw) ∧
      CoveredBy (switchVec HdE Sb sl Z A₀ codesFull2 l cutN tE w₀ Cw)
        [sendSeed setLit (oOf codesFull2 pg l) roots,
          locRound setLit .request g b r a] :=
  ⟨switchVec_ok_of _ _ _ _ _ _ _ _ _ _ _
      (kept_both_full_at lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg cutN _ w₀ Cw).1,
    coveredBy_of <| sendLoc_covers
      (switchVec_prices _ _ _ _ _ _ _ _ _ _ _
        (kept_both_full_at lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg cutN _ w₀ Cw).2)
            .request roots
      (switchVec_fits _ _ _ _ _ _ _ _ _ _ _
        (shape_full lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg Cw cutN w₀)) b r a
      (good_of _ _ _ (sendsFull_ok l hl pg hp).2.2) (good_of _ _ _ (locFull_ok g hg))⟩

include hl hp hg in
/-- At the caller whose claim is stated by its vector: each of the block's two errors, as a share,
is at most 2 ^ work / 2 ^ target, at the bits of work that the plan holds for the two rounds. -/
theorem level_full_vec (cutN : (sigOf codesFull2 l).Msg → ((HdE).foldD Sb sl Z A₀).Cf.N.Wit)
    (w₀ : ((HdE).foldD Sb sl Z A₀).tgt.W)
    (roots b r a : ℕ) :
    Err.BelowG
      (bitsTwo (switchVec HdE Sb sl Z A₀ codesFull2 l cutN tE w₀ Cw)
        (Cb.Pv.heldWork setLit .request (sendSeed setLit (oOf codesFull2 pg l) roots))
        (Cb.Pv.heldWork setLit .request (locRound setLit .request g b r a)))
      (Cb.Pv.SendLocRide.eps (switchVec HdE Sb sl Z A₀ codesFull2 l cutN tE w₀ Cw))
      (ENNReal.ofReal ((2 : ℝ) ^ setLit.target)⁻¹) :=
  belowG_two
    (two_lanes_full_vec lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg Cw cutN w₀ roots b r
      a).2
    (holds_of _ _ _ (sendsFull_ok l hl pg hp).2.2) (holds_of _ _ _ (locFull_ok g hg))

end

/-! ### The small example -/

set_option maxRecDepth 1000000 in
/-- At each written sending and either pricing group: the sending is not empty; the largest cube of
its samples is the joint seed's number of coordinates; the round SEND seed passes the test. -/
theorem sendsSmall_ok : ∀ l ∈ swSendsSmall, ∀ pg ∈ priceSmall, l ≠ [] ∧
    largestCube (oOf codesSmall2 pg l) = bMax codesSmall2 l ∧
    goodB setLit .request (sendSeed setLit (oOf codesSmall2 pg l) 0) = true := by decide +kernel

/-- At each group in front the round LOC passes the test. -/
theorem locSmall_ok : ∀ g ∈ frontSmall,
    goodB setLit .request (locRound setLit .request g 0 0 0) = true := by decide +kernel

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) (gs : GroupSize)
  (hgs : gs ∈ frontSmall) (t₀ : ℕ) (oM oZ : Fin lo.length → ℕ)
  (kp : {i // memMain lo i} → Prop) [DecidablePred kp]
  (h0 : ∀ a, kp a → (lo.get a.1).1.maskRows = 0) (kq : Fin lo.length → Prop) [DecidablePred kq]

local notation "HdF" => heldAtSmall lo hlo gs hgs t₀ oM oZ kp h0 kq

variable {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsAtSmall lo hlo gs hgs t₀ oM oZ).G.C.J)
  (Z : Evader GE ((rowsAtSmall lo hlo gs hgs t₀ oM oZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesSmall2 lo).sub kq).Msg × Wp))
  {l : List (OracleShape × ℕ)} (hl : l ∈ swSendsSmall) {pg g : GroupSize}
  (hp : pg ∈ priceSmall) (hg : g ∈ frontSmall) {Pw : Type} (Cw : LdCode GE Pw)

local notation "tF" => baseCount setLit Scope.request g

include hl hp hg in
/-- The conditions on the shape, at as many positions as the planner draws. -/
theorem shape_small (cutN : (sigOf codesSmall2 l).Msg → ((HdF).foldD Sb sl Z A₀).Cf.N.Wit)
    (w₀ : ((HdF).foldD Sb sl Z A₀).tgt.W) :
    SendLocFits (switchOf HdF Sb sl Z A₀ codesSmall2 l cutN tF w₀ Cw) setLit.samples
      (largestCube (oOf codesSmall2 pg l)) (setLit.samples * (oOf codesSmall2 pg l).length) tF
      g.main.logN := by
  obtain ⟨hne, hc, -⟩ := sendsSmall_ok l hl pg hp
  rw [hc]
  show SendLocFits _ 1 (bMax codesSmall2 l) (1 * (oOf codesSmall2 pg l).length) _ _
  rw [Nat.one_mul, show (oOf codesSmall2 pg l).length = l.length from List.length_map _]
  exact ⟨⟨eS codesSmall2 l⟩, (member_place codesSmall2 l hne).map Sum.inr, ⟨eA codesSmall2 l⟩, rfl,
    ⟨finCongr (by
      show 2 ^ (stageOf gs 0).C.a = 2 ^ (stageOf g 0).C.a
      rw [(tablesSmall_ok gs hgs).1, (tablesSmall_ok g hg).1])⟩⟩

include hl hp hg in
/-- The plan's two errors cover the block's two errors, round by round. -/
theorem two_lanes_small (cutN : (sigOf codesSmall2 l).Msg → ((HdF).foldD Sb sl Z A₀).Cf.N.Wit)
    (w₀ : ((HdF).foldD Sb sl Z A₀).tgt.W)
    (roots b r a : ℕ) :
    CoveredBy (switchOf HdF Sb sl Z A₀ codesSmall2 l cutN tF w₀ Cw)
      [sendSeed setLit (oOf codesSmall2 pg l) roots,
        locRound setLit .request g b r a] :=
  coveredBy_of <| sendLoc_covers
    (kept_both_small_at lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg cutN _ w₀ Cw).2 .request
        roots
    (shape_small lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg Cw cutN w₀) b r a
    (good_of _ _ _ (sendsSmall_ok l hl pg hp).2.2) (good_of _ _ _ (locSmall_ok g hg))

include hl hp hg in
/-- The same at the caller whose claim is stated by its vector, with that caller's condition. -/
theorem two_lanes_small_vec (cutN : (sigOf codesSmall2 l).Msg → ((HdF).foldD Sb sl Z A₀).Cf.N.Wit)
    (w₀ : ((HdF).foldD Sb sl Z A₀).tgt.W)
    (roots b r a : ℕ) :
    Cb.Pv.SendLocRide.OK (switchVec HdF Sb sl Z A₀ codesSmall2 l cutN tF w₀ Cw) ∧
      CoveredBy (switchVec HdF Sb sl Z A₀ codesSmall2 l cutN tF w₀ Cw)
        [sendSeed setLit (oOf codesSmall2 pg l) roots,
          locRound setLit .request g b r a] :=
  ⟨switchVec_ok_of _ _ _ _ _ _ _ _ _ _ _
      (kept_both_small_at lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg cutN _ w₀ Cw).1,
    coveredBy_of <| sendLoc_covers
      (switchVec_prices _ _ _ _ _ _ _ _ _ _ _
        (kept_both_small_at lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg cutN _ w₀ Cw).2)
            .request roots
      (switchVec_fits _ _ _ _ _ _ _ _ _ _ _
        (shape_small lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg Cw cutN w₀)) b r a
      (good_of _ _ _ (sendsSmall_ok l hl pg hp).2.2) (good_of _ _ _ (locSmall_ok g hg))⟩

include hl hp hg in
/-- At the caller whose claim is stated by its vector: each of the block's two errors, as a share,
is at most 2 ^ work / 2 ^ target, at the bits of work that the plan holds for the two rounds. -/
theorem level_small_vec (cutN : (sigOf codesSmall2 l).Msg → ((HdF).foldD Sb sl Z A₀).Cf.N.Wit)
    (w₀ : ((HdF).foldD Sb sl Z A₀).tgt.W)
    (roots b r a : ℕ) :
    Err.BelowG
      (bitsTwo (switchVec HdF Sb sl Z A₀ codesSmall2 l cutN tF w₀ Cw)
        (Cb.Pv.heldWork setLit .request (sendSeed setLit (oOf codesSmall2 pg l) roots))
        (Cb.Pv.heldWork setLit .request (locRound setLit .request g b r a)))
      (Cb.Pv.SendLocRide.eps (switchVec HdF Sb sl Z A₀ codesSmall2 l cutN tF w₀ Cw))
      (ENNReal.ofReal ((2 : ℝ) ^ setLit.target)⁻¹) :=
  belowG_two
    (two_lanes_small_vec lo hlo gs hgs t₀ oM oZ kp h0 kq Sb sl Z A₀ hl hp hg Cw cutN w₀ roots b r
      a).2
    (holds_of _ _ _ (sendsSmall_ok l hl pg hp).2.2) (holds_of _ _ _ (locSmall_ok g hg))

end

end Johnson.G

#print axioms Johnson.G.sendsFull_ok
#print axioms Johnson.G.locFull_ok
#print axioms Johnson.G.sendsSmall_ok
#print axioms Johnson.G.locSmall_ok
#print axioms Johnson.G.two_lanes_full
#print axioms Johnson.G.two_lanes_small
#print axioms Johnson.G.two_lanes_full_vec
#print axioms Johnson.G.two_lanes_small_vec
#print axioms Johnson.G.level_full_vec
#print axioms Johnson.G.level_small_vec
