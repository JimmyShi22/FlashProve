-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/Dear.lean: at the typed full-size sizes of the setting "record with work", 34 rounds
of a proof's shared chain have a price, work counted, above 2 ^ -129.

`dear s r`: the round r holds at the setting s, and its whole error (`wholeError`, the price with
the planner's addition for the round's draws) is above 2 ^ (work - target - 1); two exact
comparisons (`dear_sound`). `sharedFolded` and `sharedOmega` are typed lists of the stages of the
two proximity tests of a shared chain. `AtRecord x` says of the sizes x of a test on the table: the
table is `recordTable`; it is no one-time test; the row is split; the two tests have the typed
stages; one answer, 64 columns; masks are sent ahead and ride. For every such x, every list of codes
and every plan P that `sharedPlan recordSet codes x` returns: the rounds of P from place 7 on are
those of the typed list `sharedTail`, then SEAL, and the round at place 3 is the typed LOC
(`shared_rounds_at`); so 33 named places from 7 on, and place 3, have a dear round (`shared_dear`).

By `decide +kernel`, that is, evaluated by Lean's kernel at the written numbers, and turning with
them: `sharedTail_dear`, `sharedLoc_dear`.

Main definitions: `dear`, `sharedFolded`, `sharedOmega`, `sharedTail`, `sharedLoc`, `AtRecord`.
Main theorems: `dear_sound`, `sharedTail_dear`, `sharedLoc_dear`, `shared_rounds_at`, `shared_dear`.
What is not claimed: that the typed stages are those that `linSized` returns at `recordLines` (an
evaluation outside the kernel says so at a matrix of 3076096 rows). That `recordLines` are the lines
of any file. That some x meets `AtRecord` and has a plan. That a price bounds a prover's chance, or
is near one. Nothing on the rounds at the places 0 to 2 and 4 to 6.

-/
import Johnson.Prices.Pays
import OnBytes.Params.EntryStagesRecord
import OnBytes.Plan.PlanListsConfigure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices

/-- The round holds, and its whole error is above half of what it may be. -/
def dear (s : Setting) (r : PlanRound) : Bool :=
  roundHolds s (capped s) r &&
    !(wholeError s (capped s) r).le (Binary.twoTo ((r.entry.work : Int) - (s.target : Int) - 1))

/-- **What `dear` says, in rational numbers.** -/
theorem dear_sound {s : Setting} {r : PlanRound} (h : dear s r = true) :
    (2 : ℚ) ^ ((r.entry.work : ℤ) - (s.target : ℤ) - 1) < (wholeError s (capped s) r).val ∧
      (wholeError s (capped s) r).val ≤ (2 : ℚ) ^ ((r.entry.work : ℤ) - (s.target : ℤ)) := by
  unfold dear at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  have h1 := Binary.le_sound _ _ h.1
  have h2 := Binary.lt_of_not_le _ _ h.2
  rw [Binary.val_twoTo] at h1 h2
  exact ⟨h2, h1⟩

/-- The stages of the test on the folded row's group. -/
def sharedFolded : List StageSize :=
  [⟨⟨⟨24, 4194304, 101, true⟩, ⟨13, 64, 152, true⟩, 7, 0, 1, .johnson, 182⟩, 101, 0⟩,
    ⟨⟨⟨21, 131072, 54, true⟩, ⟨12, 256, 54, true⟩, 5, 2, 1, .johnson, 168⟩, 54, 491⟩,
    ⟨⟨⟨17, 8192, 54, true⟩, ⟨12, 256, 54, true⟩, 4, 2, 1, .johnson, 293⟩, 54, 350⟩,
    ⟨⟨⟨13, 512, 54, true⟩, ⟨12, 256, 54, true⟩, 4, 2, 1, .johnson, 510⟩, 54, 350⟩,
    ⟨⟨⟨14, 512, 51, true⟩, ⟨14, 1024, 51, true⟩, 0, 0, 1, .johnson, 489⟩, 51, 350⟩]

/-- The stages of the test on Omega's group. -/
def sharedOmega : List StageSize :=
  [⟨⟨⟨22, 262144, 3571, true⟩, ⟨13, 64, 152, true⟩, 4, 0, 1, .johnson, 159⟩, 51, 0⟩,
    ⟨⟨⟨18, 16384, 51, true⟩, ⟨14, 512, 51, true⟩, 4, 3, 1, .johnson, 277⟩, 51, 93⟩,
    ⟨⟨⟨14, 1024, 51, true⟩, ⟨13, 256, 51, true⟩, 4, 3, 1, .johnson, 489⟩, 51, 871⟩,
    ⟨⟨⟨15, 1024, 41, true⟩, ⟨15, 1024, 41, true⟩, 0, 0, 1, .johnson, 299⟩, 41, 359⟩]

/-- The rounds of a shared chain behind LIN zeta and before SEAL, at the typed stages. -/
def sharedTail : List RoundSpec :=
  .silent "SPLIT" (24 * 1) 0 ::
    (ioppList recordSet .shared sharedFolded (1 + 64 + 1 + 2 * recordSet.samples) 0 true ++
      ioppList recordSet .shared sharedOmega (1 + 2 * recordSet.samples) 1 true)

/-- The round LOC of a shared chain, at the typed table and 64 columns. -/
def sharedLoc : RoundSpec :=
  .said "LOC" .query (Bound.pow (tableAnalysis recordSet recordTable).later.agree 64)
    { poss := 64, logN := recordTable.code.logN, priced := .callersWord } 0 0 0

/-- Which of the 60 rounds of `sharedTail` are dear. -/
def sharedTailMarks : List Bool :=
  [false, false, false, true, true, true, true, true, true, true, false, true, false, true, true,
    false, false, false, false, true, false, true, true, false, false, false, true, false, true,
    true, false, false, false, true, true, true, false, false, true, true, true, true, false,
    false, false, true, true, true, true, false, false, false, true, true, true, true, false,
    true, true, false]

/-- The 60 rounds of `sharedTail`, one by one. By evaluation in Lean's kernel. -/
theorem sharedTail_dear :
    (sharedTail.map fun y => dear recordSet (y.round recordSet .shared)) = sharedTailMarks := by
  decide +kernel

/-- The typed LOC is dear. By evaluation in Lean's kernel. -/
theorem sharedLoc_dear : dear recordSet (sharedLoc.round recordSet .shared) = true := by
  decide +kernel

/-- The sizes of a test on the table at which the typed lists are the plan's. -/
structure AtRecord (x : LinSized) : Prop where
  table : x.table = recordTable
  oneTime : x.lines.oneTime = false
  split : x.shape.sharedSplitNeeded = true
  folded : x.folded.stages = sharedFolded
  omega : x.omega.stages = sharedOmega
  answers : x.shape.fold.index.answers = 1
  columns : x.shape.fold.columns = 64
  ahead : x.shape.masksAhead = true
  ride : x.shape.choice.masksRide = true

/-- **The rounds of every shared plan at such sizes**: from place 7 on the typed list, then SEAL; at
place 3 the typed LOC. -/
theorem shared_rounds_at {codes : Codes} {x : LinSized} {P : Planned} (hx : AtRecord x)
    (h : sharedPlan recordSet codes x = .ok P) :
    P.rounds.drop 7 = (sharedTail ++ [sealRound]).map (·.round recordSet .shared) ∧
      P.rounds[3]? = some (sharedLoc.round recordSet .shared) := by
  obtain ⟨L, hL, hc, hP⟩ := sharedPlan_is h
  simp only [hx.oneTime, Bool.false_eq_true, ↓reduceIte] at hc hP
  have hot : L.oneTime = false := (linSizeOf_lines hL).1.trans hx.oneTime
  have hr := hP.rounds
  unfold linSharedTests at hr
  rw [if_pos hx.split, hc, hx.folded, hx.omega, hx.answers, hx.columns, hx.ahead, hx.ride] at hr
  rw [hx.table] at hc
  constructor
  · rw [hr]
    simp [linSharedList, sharedTail]
  · rw [hr]
    simp [linSharedList, sharedLoc, hx.table, hot, hc, hx.columns]

/-- The places of the dear rounds. -/
def dearPlaces : List ℕ :=
  [3, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 26, 28, 29, 33, 35, 36, 40, 41, 42, 45, 46, 47, 48,
    52, 53, 54, 55, 59, 60, 61, 62, 64, 65]

/-- The places are 34, and from 7 on they are the places of the marks. -/
theorem dearPlaces_marks : dearPlaces.length = 34 ∧
    dearPlaces.tail =
      ((List.range 60).filter fun i => sharedTailMarks.getD i false).map (· + 7) := by
  decide

/-- **At each of the 34 places every shared plan at such sizes has a dear round.** -/
theorem shared_dear {codes : Codes} {x : LinSized} {P : Planned} (hx : AtRecord x)
    (h : sharedPlan recordSet codes x = .ok P) :
    ∀ i ∈ dearPlaces, ∃ r, P.rounds[i]? = some r ∧ dear recordSet r = true := by
  obtain ⟨h7, h3⟩ := shared_rounds_at hx h
  intro i hi
  have hi' : i = 3 ∨ i ∈ dearPlaces.tail := by
    simpa [dearPlaces] using hi
  rcases hi' with rfl | hi'
  · exact ⟨_, h3, sharedLoc_dear⟩
  · rw [dearPlaces_marks.2] at hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    obtain ⟨hj1, hj2⟩ := List.mem_filter.mp hj
    have hj60 : j < 60 := List.mem_range.mp hj1
    have hlen : sharedTail.length = 60 := by
      have := congrArg List.length sharedTail_dear
      simpa [sharedTailMarks] using this
    have hget : P.rounds[j + 7]? = (P.rounds.drop 7)[j]? := by
      rw [List.getElem?_drop, Nat.add_comm]
    have hj' : j < sharedTail.length := by omega
    refine ⟨(sharedTail[j]).round recordSet .shared, ?_, ?_⟩
    · rw [hget, h7, List.getElem?_map, List.getElem?_append_left hj', List.getElem?_eq_getElem hj']
      rfl
    · have e := congrArg (fun l => l.getD j false) sharedTail_dear
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj',
        Option.map_some, Option.getD_some] at e
      rw [e]
      simpa [List.getD_eq_getElem?_getD] using hj2

end OnBytes.Params.Prices
