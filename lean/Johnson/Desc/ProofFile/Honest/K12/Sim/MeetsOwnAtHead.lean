-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/MeetsOwnAtHead.lean: under the library's head (`P5J.AtMg`,
Johnson/P5J/AtMg.lean), at the first member of the proximity test on G_omega, whose first fold sends
its own fresh table: the six hypotheses of the sentence `ExactMember`
(Johnson/Desc/ProofFile/Honest/Small/Field.lean) hold together, in the sentence's order, at written
letters; there what the part shows is something at all random values; and the equation in which the
sentence ends holds. The job is any `TestJob` (Test.lean) at the seated place whose first fold sends
its own table; `jobAtOmega` (JobShared.lean) at that place is one, at every plan and every number of
"LIN point" (`jobAtOmega_is`). It imports Mathlib.

The letters. On and bud: `testOn φ J Js` and `testBud Js` (Sim/Row.lean). The stand m, the carried
values ca, the face, the side, the chain's number and the first tree's number: any. The front:
`bareFront chain m` (Sim/MeetsAtHead.lean). The challenges: `dsOwn`. The positions asks: any list
that passes `budFirst` (Sim/Row.lean) at the first stage; and two written lists that pass it.

  `MeetsAt`      a record, general in the frame's letters: the six hypotheses of `ExactMember` in
                 its order (`on`, `seen`, `draws`, `bud`, `holds`, `stop`), "something" (`some`),
                 and the equation (`eq`). A definition of this file, made so that one block need not
                 stand thrice in a statement
  `meetsAt_of_exact`   the record from `ExactMember`, its six hypotheses and "something"
  `dsOwn`        six challenges, each the one field element (1, 0, 0); no position
  `asksTo n`     positions 0 to n - 1 of the one tree that the round "FOLD epsilon" sends
  `draws_OFull`, `quiet_OFull`   at the first rounds of the written place `piOFull`
                 (Johnson/Desc/K12/Law/PlacesFull.lean): they can draw `dsOwn`; they open nothing:
                 by Lean's kernel
  `bud_152`, `bud_51`, `bud_153`   `budFirst` at that place's first stage: true at 152 different
                 positions and at 51, false at 153: by Lean's kernel. `bud_153` says nothing on the
                 equation at 153 positions
  `stage_head_O`   under the head the first stage of the seated place has k = 4, h = 0, Z.r = 152,
                 Z.a = 13 and t = 51
  `testBud_own`  at the first member `testBud` is `budFirst`
  `jobAtOmega_is`, `firstPubOwn_at`, `exact_at_O`, `seat_at_O`, `seated_at_O`   at every such job:
                 the public premise; the sentence; the side off the description's shared list is
                 there, passes `Side.fits`, and has the two written members
  `some_head_O`  what the part shows there is something, at all random values and positions
  `meets_head_O`   `MeetsAt` at every list of positions that passes `budFirst`
  `meets_head_O_152`, `meets_head_O_51`   `MeetsAt` at the two written lists, with no premise on
                 positions

Of the six, three ask nothing at this member, at any letters: On, "the front holds what is read",
and "no second stop". Three say something: the front shows what the stand has seen, which holds
because the front is made of the stand; the challenges have the declared form; and bud: every asked
position lies below 2 ^ Z.a, and at most Z.r different ones are asked.

By what. `firstPubOwn_head`, `exact_bud`, `budBoth_of_testBud`, `nums_head_O`, `thin_head_O`,
`planOk_head_O`, `count_head_O`, `find_gomega` (Sim/FirstPubOwnAtHead.lean); `exact_first_job`
(Sim/ExactFirstOwn.lean); `fits_of` (Sim/FirstSeatAtHead.lean); `members_of_seat`
(Sim/ExactSide.lean); `zip_laid` (PlaysK12.lean); `tablesFitB_eq` (Sim/FirstPubAtHead.lean);
`testOn_first`, `seen_bareFront`, `holds_of_quiet`, `stop_first` (Sim/MeetsAtHead.lean);
`decls_thin` (Sim/FirstPubAtHead.lean); `shows_first` (Sim/ShowsFirst.lean); `formPub_of_B`
(FormPubAt.lean).

Limits.
- "At every job at the place" says nothing on whether any job there is the prover's. Nor does it
  settle the state on entry: every job's `rec₀` is handed no opened column (the limits of
  Test.lean), and in front of this test the chain's test on G_u reads columns: so "every job" may
  hold no job whose state on entry is the verifier's at an honest run.
- The stand is any: no stand is shown to be one that a play reaches.
- The front lists no column and no root; the challenges are written by hand: the one element
  (1, 0, 0), six times; the two lists of positions are written by hand: 0, 1, 2 and so on. None is
  taken from a run. Such a front could not serve the test's second member.
- 51 is the first stage's t. That the positions which a run reads of this tree are at most Z.r
  different ones is not shown: which rounds of the file read the tree is not treated here.
- The job's three functions (the state on entry, the first stage's rows, the trees) are any: nothing
  says that the state is the verifier's, or that the rows were sent.
- It is shown at no job that is played.
- It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of halves with a guard in front.
- The parts and their random values are defined in Test.lean, Parts.lean and Coins.lean of
  Johnson/Desc/ProofFile/Honest/K12/. What the parts send is that folder's own `testAll`; how far it
  is tied to the library's `bodyAll` (Johnson/Prover/Link/BodyAll.lean) is said in the limits of
  Test.lean.
- The part's own values are sampled anew in the equation. `restPart` (Parts.lean) states a carried
  run for the whole fresh table (`freshRun`); nothing here says that a book deals the first part's
  own values to it, and nothing here joins the two.
- The five numbers are shown; what the member shows is counted by no statement here.
- The first member alone. The full size alone. No example of the head is shown here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubOwnAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.MeetsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K12 (P12 T12)
open H2K.Member (piOFull)
open H2K.JointK (laidOf)
open Desc.K14 (St)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {S Cl V W X Pb : Type}

local instance (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) :=
  ⟨(default, default)⟩

local instance (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-! ## 1 The record -/

/-- **The six hypotheses of `ExactMember`, in its order; "something"; the equation.** The first six
fields are the six hypotheses of that sentence's text, one by one, at the same letters. The last two
are no hypotheses: `some` is not in the sentence; `eq` is the equation in which it ends. -/
structure MeetsAt (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → ProofFile.Honest.Mid W X → Before → Prop)
    (bud : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop) (u : Member V W X Pb)
    (ca : CsAll u.part.carries) (m : ProofFile.Honest.Mid W X) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List ℕ))) : Prop where
  /-- the first hypothesis: On -/
  on : On u ca m front
  /-- the second: the front shows what the stand has seen -/
  seen : m.seen = front.seen
  /-- the third: the challenges are such as the member's declared rounds can draw -/
  draws : drawsFit (u.rounds.map (·.1)) ds = true
  /-- the fourth: bud -/
  bud : bud u.number ds asks
  /-- the fifth: the front holds a column for every read that these rounds make -/
  holds : front.holds chain firstTree (u.rounds.map (·.1)) ds = true
  /-- the sixth: the part does not stop by its second stop -/
  stop : u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid
  /-- no hypothesis: what the part shows is something, at all random values -/
  some : ∀ c, (σ.shows φ u c m ds asks).isSome = true
  /-- no hypothesis: the sentence's conclusion -/
  eq : (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
      (fun c => σ.shows φ u (c.1, c.2, ca) m ds asks) =
    (Prob.unif (Cs u.sim.takes)).map fun c => u.tells φ c m.st.input front ds asks

/-- **The record from the sentence**: whoever holds `ExactMember` and its six hypotheses, in its
order, and "something", holds the record. So the first six fields are that sentence's hypotheses:
Lean feeds them to it one by one. -/
theorem meetsAt_of_exact {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {chain firstTree : ℕ}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → ProofFile.Honest.Mid W X → Before → Prop}
    {bud : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop} {u : Member V W X Pb}
    (H : ExactMember φ σ chain firstTree On bud u) (ca : CsAll u.part.carries)
    (m : ProofFile.Honest.Mid W X) (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (h1 : On u ca m front) (h2 : m.seen = front.seen)
    (h3 : drawsFit (u.rounds.map (·.1)) ds = true) (h4 : bud u.number ds asks)
    (h5 : front.holds chain firstTree (u.rounds.map (·.1)) ds = true)
    (h6 : u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid)
    (hs : ∀ c, (σ.shows φ u c m ds asks).isSome = true) :
    MeetsAt φ σ chain firstTree On bud u ca m front ds asks :=
  ⟨h1, h2, h3, h4, h5, h6, hs, H ca m front ds asks h1 h2 h3 h4 h5 h6⟩

/-! ## 2 The written letters, at the written place -/

/-- Six challenges, each of one field element. -/
def dsOwn : List Fmt.Drawn := List.replicate 6 ⟨[(1, 0, 0)], [], [], none⟩

/-- Positions 0 to n - 1 of the one tree that round number 1 sends. -/
def asksTo (n : ℕ) : List (List (List ℕ)) := [[], [List.range n]]

theorem draws_OFull :
    drawsFit (((laidOf piOFull).take (firstLen piOFull.nums.stages)).map (·.1)) dsOwn = true := by
  decide +kernel

theorem quiet_OFull :
    quietB (((laidOf piOFull).take (firstLen piOFull.nums.stages)).map (·.1)) = true := by
  decide +kernel

theorem bud_152 : budFirst (piOFull.nums.stages.headD default) (asksTo 152) = true := by
  decide +kernel

theorem bud_51 : budFirst (piOFull.nums.stages.headD default) (asksTo 51) = true := by
  decide +kernel

/-- At 153 written positions the bound says no: by Lean's kernel, at the written place's first
stage. It says nothing on the equation at 153 positions. Within the bound the equation holds, at 152
too (`meets_head_O_152`). -/
theorem bud_153 : budFirst (piOFull.nums.stages.headD default) (asksTo 153) = false := by
  decide +kernel

/-- At the first member `testBud` is `budFirst`. -/
theorem testBud_own (Js : SimJob Pb) (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (hb : budFirst Js.s₀ asks = true) : testBud Js 0 ds asks :=
  ⟨fun _ _ => hb, fun h => absurd h Nat.zero_ne_one⟩

/-! ## 3 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- **Under the head: five numbers of the first stage of the seated place of the test on G_omega.**
-/
theorem stage_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    (pO.nums.stages.headD default).k = 4 ∧ (pO.nums.stages.headD default).h = 0 ∧
      (pO.nums.stages.headD default).Z.r = 152 ∧ (pO.nums.stages.headD default).Z.a = 13 ∧
      (pO.nums.stages.headD default).t = 51 := by
  rw [nums_head_O h hO]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

section Job
variable (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) (Js : SimJob Pb)
  (J : TestJob W X) (hp : J.p = pO) (hfr : J.fresh.isNone = true)

/-- `jobAtOmega` at that place is such a job, at every plan, number of "LIN point", state function,
pair of readers and vector passed in. -/
theorem jobAtOmega_is (A : ProofFile.Honest.K14.SendPub) (p : P12) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtOmega A p door weights rand omega?).toRun.toTest.p = p ∧
      (jobAtOmega A p door weights rand omega?).toRun.toTest.fresh.isNone = true := ⟨rfl, rfl⟩

include h hO hp hfr in
/-- **The public premise at every job at the seated place whose first fold sends its own table.** -/
theorem firstPubOwn_at (hJ : Js.p = pO) (ho : Js.own = true) : FirstPubOwn J Js := by
  have T := firstPubOwn_head (W := W) (X := X) h hO (fun _ _ => noState) (fun _ => ⟨fun _ _ => 0⟩)
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩) none Js hJ ho
  subst hp
  refine ⟨hJ, ho, T.form, T.enough, ?_, T.points⟩
  rw [tablesFitB_eq, hfr]
  exact T.tables

include h hO hp in
theorem draws_head_O : drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) dsOwn = true := by
  subst hp
  show drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1)) dsOwn = true
  rw [List.map_take, decls_thin, thin_head_O h hO, ← decls_thin, ← List.map_take,
    nums_head_O h hO]
  exact draws_OFull

include h hO hp in
theorem quiet_head_O : quietB ((firstMember (V := V) J Js).rounds.map (·.1)) = true := by
  subst hp
  show quietB (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1)) = true
  rw [List.map_take, decls_thin, thin_head_O h hO, ← decls_thin, ← List.map_take,
    nums_head_O h hO]
  exact quiet_OFull

include h hO in
/-- The simulators' job's first stage is the written place's. -/
theorem s₀_head_O (hJ : Js.p = pO) : Js.s₀ = piOFull.nums.stages.headD default := by
  show Js.p.nums.stages.headD default = _
  rw [hJ, nums_head_O h hO]

include h hO hp hfr in
/-- What the part shows at the written challenges is something, at all random values. -/
theorem some_head_O (hJ : Js.p = pO) (ho : Js.own = true) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (m : ProofFile.Honest.Mid W X) (asks : List (List (List ℕ)))
    (c : (firstMember J Js : Member V W X Pb).part.Coins) :
    (σ.shows φ (firstMember J Js) c m dsOwn asks).isSome = true := by
  have T := firstPubOwn_at h hO Js J hp hfr hJ ho
  subst hp
  have hst : J.p.nums.stages = piOFull.nums.stages := congrArg (·.stages) (nums_head_O h hO)
  obtain ⟨s, t, rest, hlit⟩ : ∃ s t rest, piOFull.nums.stages = s :: t :: rest := ⟨_, _, _, rfl⟩
  have hlen : dsOwn.length = firstLen J.p.nums.stages := by
    rw [hst]
    rfl
  rw [shows_first φ σ J Js s t rest m (byNo dsOwn) dsOwn
    ⟨hst.trans hlit, T.enough, (formPub_of_B _ s t rest (hst.trans hlit) T.form).sorts, T.tables,
      hlen, fun n hn => (List.getD_eq_getElem _ _ hn).symm⟩ c asks]
  rfl

include h hO hp hfr in
/-- The sentence at the first member, at the side's own On and bud. -/
theorem exact_at_O (hJ : Js.p = pO) (ho : Js.own = true) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (chain firstTree : ℕ) :
    ExactMember φ σ chain firstTree (testOn φ J Js) (testBud Js) (firstMember J Js) :=
  exact_bud (fun ds asks hb => budBoth_of_testBud Js ds asks hb)
    (exact_first_job φ σ J Js chain firstTree _ hfr (firstPubOwn_at h hO Js J hp hfr hJ ho))

include h hO hp in
/-- **The side is there**, at every list of falls. -/
theorem seat_at_O (fs : List (Fall St)) : ∃ σ : Side St ProofFile.Cl V W X Pb,
    testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ := by
  subst hp
  obtain ⟨b, hf, _, _, _⟩ := find_gomega h hO
  unfold testSide Side.seated
  exact ⟨_, by rw [hf]; rfl⟩

include h hO hp in
/-- **Whatever side `testSide` returns there** passes the frame's test on sides, and its members are
the two that are written out. -/
theorem seated_at_O (hJ : Js.p = pO) (fs : List (Fall St)) (σ : Side St ProofFile.Cl V W X Pb)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ) :
    σ.fits = true ∧ σ.members = [firstMember J Js, restMember J Js] := by
  subst hp
  have hk := planOk_head_O h hO
  have hst : J.p.nums.stages = piOFull.nums.stages := congrArg (·.stages) (nums_head_O h hO)
  obtain ⟨s, t, rest, hlit⟩ : ∃ s t rest, piOFull.nums.stages = s :: t :: rest := ⟨_, _, _, rfl⟩
  obtain ⟨b, hf, hpl, hr, hor⟩ := find_gomega h hO
  have hσ' := hσ
  unfold testSide Side.seated at hσ'
  rw [hf] at hσ'
  obtain rfl := Option.some.inj hσ'
  refine ⟨?_, ?_⟩
  · exact fits_of J Js hJ b _ hpl hk hr hor s t rest (hst.trans hlit) (count_head_O h hO)
  · refine members_of_seat _ J Js fs _ hσ ?_ s t rest (hst.trans hlit) (count_head_O h hO)
    show b.rounds.zip b.oracles = _
    rw [hr, hor]
    exact zip_laid J.p hk

include h hO hp hfr in
/-- **At every list of positions that passes `budFirst`.** -/
theorem meets_head_O (hJ : Js.p = pO) (ho : Js.own = true) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (chain firstTree : ℕ)
    (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X)
    (asks : List (List (List ℕ))) (hb : budFirst Js.s₀ asks = true) :
    MeetsAt φ σ chain firstTree (testOn φ J Js) (testBud Js) (firstMember J Js) ca m
      (bareFront chain m) dsOwn asks :=
  meetsAt_of_exact (exact_at_O h hO Js J hp hfr hJ ho φ σ chain firstTree) ca m
    (bareFront chain m) dsOwn asks (testOn_first φ J Js ca m (bareFront chain m))
    (seen_bareFront chain m) (draws_head_O (V := V) h hO Js J hp) (testBud_own Js dsOwn asks hb)
    (holds_of_quiet (bareFront chain m) chain firstTree _ dsOwn
      (quiet_head_O (V := V) h hO Js J hp))
    (stop_first (V := V) J Js (φ.sees m.st.input) m.loc dsOwn)
    (some_head_O h hO Js J hp hfr hJ ho φ σ m asks)

include h hO hp hfr in
/-- **At 152 different positions**: as many as the mask code's tail has entries. -/
theorem meets_head_O_152 (hJ : Js.p = pO) (ho : Js.own = true) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (chain firstTree : ℕ)
    (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X) :
    MeetsAt φ σ chain firstTree (testOn φ J Js) (testBud Js) (firstMember J Js) ca m
      (bareFront chain m) dsOwn (asksTo 152) :=
  meets_head_O h hO Js J hp hfr hJ ho φ σ chain firstTree ca m _
    (by rw [s₀_head_O h hO Js hJ]; exact bud_152)

include h hO hp hfr in
/-- **At 51 different positions**: the first stage's t. -/
theorem meets_head_O_51 (hJ : Js.p = pO) (ho : Js.own = true) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (chain firstTree : ℕ)
    (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X) :
    MeetsAt φ σ chain firstTree (testOn φ J Js) (testBud Js) (firstMember J Js) ca m
      (bareFront chain m) dsOwn (asksTo 51) :=
  meets_head_O h hO Js J hp hfr hJ ho φ σ chain firstTree ca m _
    (by rw [s₀_head_O h hO Js hJ]; exact bud_51)

end Job

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.MeetsAt
#print axioms ProofFile.Honest.K12.Light.meetsAt_of_exact
#print axioms ProofFile.Honest.K12.Light.dsOwn
#print axioms ProofFile.Honest.K12.Light.asksTo
#print axioms ProofFile.Honest.K12.Light.draws_OFull
#print axioms ProofFile.Honest.K12.Light.quiet_OFull
#print axioms ProofFile.Honest.K12.Light.bud_152
#print axioms ProofFile.Honest.K12.Light.bud_51
#print axioms ProofFile.Honest.K12.Light.bud_153
#print axioms ProofFile.Honest.K12.Light.testBud_own
#print axioms ProofFile.Honest.K12.Light.stage_head_O
#print axioms ProofFile.Honest.K12.Light.jobAtOmega_is
#print axioms ProofFile.Honest.K12.Light.firstPubOwn_at
#print axioms ProofFile.Honest.K12.Light.draws_head_O
#print axioms ProofFile.Honest.K12.Light.quiet_head_O
#print axioms ProofFile.Honest.K12.Light.s₀_head_O
#print axioms ProofFile.Honest.K12.Light.some_head_O
#print axioms ProofFile.Honest.K12.Light.exact_at_O
#print axioms ProofFile.Honest.K12.Light.seat_at_O
#print axioms ProofFile.Honest.K12.Light.seated_at_O
#print axioms ProofFile.Honest.K12.Light.meets_head_O
#print axioms ProofFile.Honest.K12.Light.meets_head_O_152
#print axioms ProofFile.Honest.K12.Light.meets_head_O_51
