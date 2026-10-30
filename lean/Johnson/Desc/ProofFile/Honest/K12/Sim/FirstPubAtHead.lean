-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FirstPubAtHead.lean: the public premise `FirstPub`
(Sim/ExactFirst.lean) of the sentence `exact_first` holds at the job `jobAtU` (JobShared.lean) at
the proof file's own plan and the seated place of the test on G_u, under the library's head
(`P5J.AtMg`, Johnson/P5J/AtMg.lean); and so the sentence holds at that job's first member. It
imports Mathlib.

  `nums_head_U`   under the head all seven numbers of the seated place `(fourOf Np).U`
                 (AtProof/Places.lean) are those of the written place `piUFull`
                 (Johnson/Desc/K12/Law/PlacesFull.lean)
  `pairs_of_planOk`   where the test's block passes its test on the plan, the depth and width of
                 each declared oracle message are what `H2U.testOracles` gives for the place's
                 numbers
  `thinOf`, `thinOf_congr`, `thin_of_planOk`   the declared rounds, each with its oracle messages'
                 depths and widths; two places with the same numbers whose blocks pass have the same
  `formPubB_congr`, `length_congr`, `tabB_congr`   the three facts on numbers in `FirstPub` read of
                 a place no more than its numbers and `thinOf`
  `tabB`, `tablesFitB_eq`   `tablesFitB` (FitsAll.lean) as a function of the place and one flag
  `formPubB_U`, `enough_U`, `tabB_U`   the three facts at `piUFull`, evaluated by Lean's kernel
  `firstPub_head`   `FirstPub J Js` at J the job above, for every state function, pair of readers
                 and vector passed in, and every Js with that place that says "the fold sends no
                 table"
  `exact_first_head`   `ExactMember φ σ chain firstTree On bud (firstMember J Js)`, at every face,
                 side, On and bud

By what. `nums_head_U`: the library's `nums_U_of_full`
(Johnson/Desc/K12/Law/Sizes/ClosedAtScope.lean), `rounds_at_seat_U`, `free_at_seat_U`
(Johnson/Loose/H2K12/RoundsAtFull.lean) and `seat_in_scope`
(Johnson/Goal/Numbers/PlanWrittenDescScope.lean), called as `closedL_in_scope_U`
(Johnson/Loose/H2K12/ClosedAtSeats.lean) calls them. The block's test on the plan: `planOk_head_U`
(NearAtHead.lean) at the seated place, the library's `closed_UFull`
(Johnson/Desc/K12/Coin/LawAtFull.lean) at the written one. `exact_first_head`: one call of
`exact_first`. `formPubB_U` and `tabB_U` are evaluated under `set_option maxRecDepth 100000`, as
`formPubB_KR` (FormPubAt.lean) is.

The 0 in `⟨K1.qAt Zp Np, 0⟩` is the field `atPoint` of `SendPub`
(Johnson/Desc/ProofFile/Honest/K14/Sendings.lean): the number, among the shared chain's rounds, of
"LIN point", by which the sender's vector is computed. It is compared with nothing here, and nothing
here says that 0 is that number at this plan.

Limits.
- The sentence is shown at a job whose state on entry is any function: nothing says that it is the
  verifier's state.
- It is shown at no job that is played: that a job which somebody lays is this one is up to whoever
  lays it. The face, the side, On and bud are free letters; no side that holds this member is laid
  here.
- It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of halves with a guard in front.
- The parts and their random values are defined in Test.lean, Parts.lean and Coins.lean of
  Johnson/Desc/ProofFile/Honest/K12/. What the parts send is that folder's own `testAll`; how far it
  is tied to the library's `bodyAll` (Johnson/Prover/Link/BodyAll.lean) is said in the limits of
  Test.lean.
- It is the spender's half: the 2 k + 1 values that the first member spends are sampled anew in the
  sentence. The same values stand in the sender's tree and in what the second part carries; nothing
  here joins these.
- The first member alone, and only where the fresh table came earlier: not at the test on G_omega.
- No stand, front or challenges at which the sentence's own hypotheses hold are written here;
  Sim/MeetsAtHead.lean has them, under the head, at written letters (`meets_head_U`).
- The full size alone. No example of the head is shown here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirst
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead
import Johnson.Loose.H2K12.ClosedAtSeats
import Johnson.Desc.K12.Coin.LawAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Oracle)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 Parts proximityTestKind guardedProximityTestParts)
open H2K.Member (piUFull)
open H2K.JointK (descN laidOf laidS)
open Johnson.Prover.Link (asked switchCut)
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)

/-! ## 1 What the three facts read of a place -/

/-- An oracle message's depth and width. -/
def pairOf (o : Oracle) : ℕ × ℕ := (o.logLength, o.words)

/-- The declared rounds, each with the depths and widths of its oracle messages. -/
def thinOf (p : P12) : List (Fmt.DeclaredRound × List (ℕ × ℕ)) :=
  (laidOf p).map fun d => (d.1, d.2.map pairOf)

theorem zip_thin {α β γ : Type} (F : β → γ) : ∀ (l : List α) (m : List β),
    (l.zip m).map (fun d => (d.1, F d.2)) = l.zip (m.map F)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: m => by
    rw [List.zip_cons_cons, List.map_cons, List.map_cons, List.zip_cons_cons, zip_thin F l m]

theorem thinOf_eq (p : P12) :
    thinOf p = ((H2U.roundsOfNums p.nums).getD []).zip (p.oracles.map (·.map pairOf)) :=
  zip_thin _ _ _

theorem thinOf_congr {p q : P12} (hn : p.nums = q.nums)
    (ho : p.oracles.map (·.map pairOf) = q.oracles.map (·.map pairOf)) : thinOf p = thinOf q := by
  rw [thinOf_eq, thinOf_eq, hn, ho]

/-- What the block's test on the plan holds of the declared oracle messages. -/
theorem pairs_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) :
    H2U.testOracles p.nums = some (p.oracles.map (·.map pairOf)) := by
  unfold proximityTestKind at hp
  split at hp
  · rename_i first rest rs os h1 h2 h3
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [h3, ← hp.1.2]
    rfl
  · cases hp

theorem thin_of_planOk {T Cl : Type} (X : Parts T) {p q : P12} (hn : p.nums = q.nums)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (hq : (proximityTestKind X q : Block T Cl).planOk = true) :
    thinOf p = thinOf q := by
  refine thinOf_congr hn (Option.some.inj ?_)
  rw [← pairs_of_planOk X p hp, ← pairs_of_planOk X q hq, hn]

theorem decls_thin (p : P12) : (laidOf p).map (·.1) = (thinOf p).map (·.1) := by
  unfold thinOf
  rw [List.map_map]
  rfl

theorem pairs_thin (p : P12) :
    (laidOf p).map (fun d => d.2.map pairOf) = (thinOf p).map (·.2) := by
  unfold thinOf
  rw [List.map_map]
  rfl

theorem asked_thin (p : P12) :
    (laidOf p).map asked = ((thinOf p).map (·.1)).map fun d => d.items.filter (· != .root) := by
  rw [← decls_thin, List.map_map]
  rfl

theorem cut_thin (p : P12) (n : ℕ) :
    (((laidS p).drop n).take 2).map (·.1) = ((((thinOf p).map (·.1)).drop 1).drop n).take 2 := by
  unfold laidS
  rw [← decls_thin, List.map_take, List.map_drop, List.map_drop]

theorem length_thin (p : P12) : (laidOf p).length = (thinOf p).length := by
  unfold thinOf
  rw [List.length_map]

theorem length_congr {p q : P12} (hT : thinOf p = thinOf q) :
    (laidOf p).length = (laidOf q).length := by
  rw [length_thin, length_thin, hT]

theorem formPubB_congr {p q : P12} (hn : p.nums = q.nums) (hT : thinOf p = thinOf q) :
    formPubB p = formPubB q := by
  have e1 : (laidOf p).map asked = (laidOf q).map asked := by rw [asked_thin, asked_thin, hT]
  have e2 : ∀ n, (((laidS p).drop n).take 2).map (·.1) = (((laidS q).drop n).take 2).map (·.1) :=
    fun n => by rw [cut_thin, cut_thin, hT]
  unfold formPubB lettersOf
  simp only [e1, e2, hn]

/-- `tablesFitB` as a function of the place and of "the first fold sends its own table". -/
def tabB (p : P12) (own : Bool) : Bool :=
  (List.range (laidOf p).length).all fun i =>
    ((none :: depths own p.nums.stages).getD i none).toList.map
        (fun a => (a, (widthsOf own p.nums.stages).getD i 0)) ==
      ((((laidOf p)[i]?).map fun d => d.2).getD []).map fun o => (o.logLength, o.words)

theorem tablesFitB_eq {W X : Type} (J : TestJob W X) : tablesFitB J = tabB J.p J.fresh.isNone := rfl

theorem at_pairs (l : List (Fmt.DeclaredRound × List Oracle)) (i : ℕ) :
    (((l[i]?).map fun d => d.2).getD []).map (fun o => (o.logLength, o.words)) =
      ((l.map fun d => d.2.map pairOf)[i]?).getD [] := by
  rw [List.getElem?_map]
  cases l[i]? <;> rfl

theorem tabB_congr {p q : P12} (hn : p.nums = q.nums) (hT : thinOf p = thinOf q) (own : Bool) :
    tabB p own = tabB q own := by
  unfold tabB
  simp only [at_pairs, pairs_thin, length_congr hT, hT, hn]

/-! ## 2 At the written place -/

set_option maxRecDepth 100000 in
theorem formPubB_U : formPubB piUFull = true := by decide +kernel

theorem enough_U : firstLen piUFull.nums.stages ≤ (laidOf piUFull).length := by decide +kernel

set_option maxRecDepth 100000 in
theorem tabB_U : tabB piUFull false = true := by decide +kernel

/-! ## 3 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Under the head all seven numbers of the seated place of the test on G_u are the written
place's.** -/
theorem nums_head_U (h : P5J.AtMg o Z D r Zp Np cF) : (fourOf Np).U.nums = piUFull.nums := by
  obtain ⟨Z', N', c', hZ', hN', e, R⟩ :=
    H2K.JointK.k12_sits_row o Z.pol Z.lay Z.KL _ h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  subst eZ
  have eN : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  subst eN
  have hp : (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c').planOk = true := by
    rw [← e]
    exact h.laid.planOk
  have hpin : VerifiableInference.PlanWritten.seatPinnedProof Z.pol
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c') = true := by
    rw [← e]
    exact LPFD.asks_written h.laid.asks
  have A := H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ Z h.scope hpin).1
  refine (R.nums hp).2.1.trans ?_
  exact H2K.Sizes.nums_U_of_full A h.laid.places _
    (H2K.JointK.plan_at_seat_U o Z' ProofFile.pureRoad.links N' c' hp)
    (H2K.JointK.rounds_at_seat_U o Z.pol Z.lay Z.KL Z' h.laid.pub ProofFile.pureRoad.links N' c'
      h.laid.places hp A hW)
    (H2K.JointK.free_at_seat_U o Z.pol Z.lay Z.KL Z' h.laid.pub ProofFile.pureRoad.links N' c'
      h.laid.places hp hW)

theorem thin_head_U (h : P5J.AtMg o Z D r Zp Np cF) : thinOf (fourOf Np).U = thinOf piUFull :=
  thin_of_planOk guardedProximityTestParts (nums_head_U h) (planOk_head_U h)
    VerifiableInference.Desc.K12.Coin.At.closed_UFull.plan

variable {S Cl V W X Pb : Type}

/-- **The public premise of `exact_first` at `jobAtU`, under the head.** -/
theorem firstPub_head (h : P5J.AtMg o Z D r Zp Np cF) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (Js : SimJob Pb) (hJ : Js.p = (fourOf Np).U) (ho : Js.own = false) :
    FirstPub (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest Js := by
  have hn := nums_head_U h
  have hT := thin_head_U h
  refine ⟨hJ, ho, ?_, ?_, ?_⟩
  · show formPubB (fourOf Np).U = true
    rw [formPubB_congr hn hT]
    exact formPubB_U
  · show firstLen (fourOf Np).U.nums.stages ≤ (laidOf (fourOf Np).U).length
    rw [hn, length_congr hT]
    exact enough_U
  · rw [tablesFitB_eq]
    show tabB (fourOf Np).U false = true
    rw [tabB_congr hn hT]
    exact tabB_U

/-- **The sentence at the first member of that job, under the head**: at every face, side, On and
bud. -/
theorem exact_first_head (h : P5J.AtMg o Z D r Zp Np cF) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb)
    (hJ : Js.p = (fourOf Np).U) (ho : Js.own = false) (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → ProofFile.Honest.Mid W X → Before → Prop)
    (bud : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop) :
    ExactMember φ σ chain firstTree On bud
      (firstMember (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest Js) :=
  exact_first φ σ _ Js chain firstTree On bud rfl (firstPub_head h door weights rand u? Js hJ ho)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.pairOf
#print axioms ProofFile.Honest.K12.Light.thinOf
#print axioms ProofFile.Honest.K12.Light.zip_thin
#print axioms ProofFile.Honest.K12.Light.thinOf_eq
#print axioms ProofFile.Honest.K12.Light.thinOf_congr
#print axioms ProofFile.Honest.K12.Light.pairs_of_planOk
#print axioms ProofFile.Honest.K12.Light.thin_of_planOk
#print axioms ProofFile.Honest.K12.Light.decls_thin
#print axioms ProofFile.Honest.K12.Light.pairs_thin
#print axioms ProofFile.Honest.K12.Light.asked_thin
#print axioms ProofFile.Honest.K12.Light.cut_thin
#print axioms ProofFile.Honest.K12.Light.length_thin
#print axioms ProofFile.Honest.K12.Light.length_congr
#print axioms ProofFile.Honest.K12.Light.formPubB_congr
#print axioms ProofFile.Honest.K12.Light.tabB
#print axioms ProofFile.Honest.K12.Light.tablesFitB_eq
#print axioms ProofFile.Honest.K12.Light.at_pairs
#print axioms ProofFile.Honest.K12.Light.tabB_congr
#print axioms ProofFile.Honest.K12.Light.formPubB_U
#print axioms ProofFile.Honest.K12.Light.enough_U
#print axioms ProofFile.Honest.K12.Light.tabB_U
#print axioms ProofFile.Honest.K12.Light.nums_head_U
#print axioms ProofFile.Honest.K12.Light.thin_head_U
#print axioms ProofFile.Honest.K12.Light.firstPub_head
#print axioms ProofFile.Honest.K12.Light.exact_first_head
