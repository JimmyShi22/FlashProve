-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/PlanListsChains.lean: the rounds of the test on the table and of a link, and the
whole plans of an entry's chain, of a shared chain and of a second chain, as lists.

OnBytes/Params/PlanListsSum.lean and OnBytes/Params/PlanListsProx.lean give, for the planner's
routines, the lists of the rounds that they add. This file does the same for the routines on the
committed table and for the routines that plan a chain, and then says of a finished plan that holds
(`finishHeld`, OnBytes/Params/Planner.lean): its rounds are the rounds of the chain's list; of each
round with a verifier's message, the bound is not marked bad, the work is below the target and fits
the nonce (of a silent round and of a record's entry this is not said); and each round holds in the
planner's reckoning. It also keeps what the routines' own tests found on the numbers of columns, and
that the sizes which the plans read were there. A shared chain's list ends in SEAL; a second chain's
and an entry's have none, as the routines plan none. All for every setting and all sizes: nothing is
evaluated.

Main definitions: `PlanIs`, `sealRound`, `recordList`, `linSharedList`, `linSharedTests`,
`linkBlockList`, `sharedChainList`, `secondChainList`, `entryChainList`, `linColumns`,
`linkColumnsFirst`, `linkColumnsFurther`.
Main theorems: `runs_linShared`, `runs_link`, `runs_linPlanShared`, `runs_linPlanSecond`,
`runs_linkPlan`, `planIs_of`, `PlanIs.entries`, `sharedPlan_rounds`, `sharedPlan_is`,
`secondPlan_rounds`, `secondPlan_is`, `linkPlan_is`, `entrySized_rounds`, `linSized_lines`.
What is not claimed: that a plan is finished or holds: that is each theorem's hypothesis. The
converse: that a plan whose described rounds hold is finished or holds. Of the plan's verdict only
that each round holds is kept, not `wordsFit` and `oneDistance`. Of the routines' own tests only
those on the numbers of columns, on the sizes, and that a second chain's test has two stages are
kept; not that a number of positions is not 0 or within what its stage was sized for, that an
analysis or the table's distances are admitted, or what `planListed` asks. That the program's blocks
state these rounds in a dry run. Nothing on the kinds of written rounds: an entry of a plan has
none. Nothing on the C++ planner, of which OnBytes/Params/ is a rendering. For proofs only; the
program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.ConfigureLaws
import OnBytes.Params.DeriveLin
import OnBytes.Params.PlanListsProx

set_option autoImplicit false

namespace OnBytes.Params

/-- The round that ends a chain. -/
def sealRound : RoundSpec := .said "SEAL" .zero (Bound.ofWord 0) {} 0 0 0

/-- The entry for a table's own sample. -/
def recordList (s : Setting) (T : TableSize) : List RoundSpec :=
  [.record T.answers (clog2 T.code.ell)
    (sampleError s (tableAnalysis s T).once.list (clog2 T.code.ell) T.answers)]

/-- The number of columns of the table that the test on the table opens. -/
def linColumns (s : Setting) (c : Scope) (T : TableSize) (x : LinSize) : Nat :=
  scopePositions s c
    (if x.oneTime = true then (tableAnalysis s T).once
      else (tableAnalysis s T).later).agree (Bound.ofWord 0)

/-- The rounds of the test on the table on the shared chain, before its proximity tests. -/
def linSharedList (s : Setting) (c : Scope) (T : TableSize) (x : LinSize) : List RoundSpec :=
  let A := tableAnalysis s T
  let y := if x.oneTime then A.once else A.later
  let point := Bound.ofNat x.instances * fieldError s (T.v + x.kLo)
  let agree := y.agree
  .said "LIN point" .closeness (point + tableFoldError s T y)
      { drawE := T.v + x.kLo, rests := y.source, priced := .callersWord }
      0 0 0 ::
  sendSeed s [x.u] x.rootsU ::
  .silent "SEND answer" (24 * (s.samples * 1)) (s.samples * 1) ::
  .said "LOC" .query (Bound.pow agree (linColumns s c T x))
      { poss := linColumns s c T x, logN := T.code.logN, priced := .callersWord } 0 0 0 ::
  sendSeed s (x.omega :: x.besideOmega) x.rootsOmega ::
  .silent "SEND answer" (24 * (s.samples * (x.besideOmega.length + 1)))
      (s.samples * (x.besideOmega.length + 1)) ::
  [.said "LIN zeta" .field (fieldError s x.rowsLog) { drawE := x.rowsLog, priced := .roundItself }
      0 0 0]

/-- The agreement at which a link reads the first table, in the routine's own words. -/
def linkFirstAgree (s : Setting) (T : TableSize) : Bound :=
  (tableAnalysis s T).later.agree

/-- The number of columns of the first table that a link opens. -/
def linkColumnsFirst (s : Setting) (c : Scope) (T : TableSize) : Nat :=
  scopePositions s c (linkFirstAgree s T) (Bound.ofWord 0)

/-- The number of columns of the further table that a link opens. -/
def linkColumnsFurther (s : Setting) (c : Scope) (T : TableSize) : Nat :=
  scopePositions s c (tableAnalysis s T).once.agree (Bound.ofWord 0)

/-- The rounds of a link before its proximity test. -/
def linkBlockList (s : Setting) (c : Scope) (T : TableSize) (u : SampleSize) : List RoundSpec :=
  let A := tableAnalysis s T
  let first := A.later
  let e := fieldError s T.v + tableFoldError s T A.once
  let e0 := Bound.pow (linkFirstAgree s T) (linkColumnsFirst s c T)
  let ej := Bound.pow A.once.agree (linkColumnsFurther s c T)
  .said "LINK point" .closeness (e + tableFoldError s T first)
      { drawE := T.v, priced := .callersWord,
        rests := if A.once.source.rank < first.source.rank then first.source
          else A.once.source } 0 0 0 ::
  .said "SEND seed" .sample
      (Bound.ofWord 2 * sampleError s (largestList s u.groups) u.cubeBits s.samples)
      { drawE := s.samples * (u.cubeBits + 1), drawNZ := s.samples, priced := .callersWord }
      (32 * 1) 1 0 ::
  .silent "SEND answer" (24 * (2 * s.samples)) (2 * s.samples) ::
  .said "LINK" .query (if e0.hi.lt ej.hi then ej else e0)
      { poss := linkColumnsFirst s c T + linkColumnsFurther s c T, logN := T.code.logN,
        priced := .callersWord } 0 0 0 ::
  [.said "LINK phi" .field (fieldError s (clog2 T.code.ell))
      { drawE := clog2 T.code.ell, priced := .roundItself } 0 0 0]

/-- The rounds of an entry's chain: the entry for the record, if tables have one; the link; its
proximity test. The chain has no SEAL. -/
def entryChainList (s : Setting) (c : Scope) (x : LinkSized) : List RoundSpec :=
  recordList s x.table ++
    (linkBlockList s c x.table
        ⟨clog2 x.shape.rows + clog2 x.linked.group.main.ell, [x.linked.group]⟩ ++
      ioppList s c x.linked.stages
        (2 * x.shape.table.answers + linkColumnsFirst s c x.table +
          linkColumnsFurther s c x.table + 1 + 2 * s.samples)
        (if x.shape.masksAhead then 0 else 1) x.shape.choice.masksRide)

/-- The rounds of the test on the table on the shared chain, with its proximity tests, at the sizes
L that the plans read. -/
def linSharedTests (s : Setting) (c : Scope) (x : LinSized) (L : LinSize) : List RoundSpec :=
  linSharedList s c x.table L ++
    (if x.shape.sharedSplitNeeded = true then
      .silent "SPLIT" (24 * 1) 0 ::
        (ioppList s c x.folded.stages
            (x.shape.fold.index.answers + linColumns s c x.table L + 1 + 2 * s.samples)
            (if x.shape.masksAhead then 0 else 1) x.shape.choice.masksRide ++
          ioppList s c x.omega.stages (1 + 2 * s.samples) 1 x.shape.choice.masksRide)
    else
      ioppList s c x.folded.stages
        (x.shape.fold.index.answers + linColumns s c x.table L + 1 + 2 * s.samples)
        (if x.shape.masksAhead then 0 else 1) x.shape.choice.masksRide)

/-- The rounds of a shared chain: the test on the table with its proximity tests, then SEAL. Written
as [SEAL] alone where the plans' sizes do not follow; the plan is then refused. -/
def sharedChainList (s : Setting) (c : Scope) (codes : Codes) (x : LinSized) : List RoundSpec :=
  ((linSizeOf codes x).map (linSharedTests s c x)).getD [] ++ [sealRound]

/-- The rounds of a second chain: the request's own proximity test. The chain has no SEAL. -/
def secondChainList (s : Setting) (c : Scope) (x : LinSized) : List RoundSpec :=
  ioppList s c x.own.stages (2 + 3 * s.samples) (if x.shape.masksAhead then 0 else 1)
    x.shape.choice.masksRide

section
variable {s : Setting} {c : Scope}

/-- SEAL. -/
theorem runs_seal : Runs s c 0 0 0 planSeal () [sealRound] 0 0 0 := runs_close _ _ _ _ _ _ _

/-- The analysis of the table. -/
theorem runs_table (T : TableSize) (b r a : Nat) :
    Runs s c b r a (planTable T) (tableAnalysis s T) [] b r a := by
  unfold planTable
  exact Runs.cast (runs_bind (runs_setting b r a) (runs_bind (runs_needs _ _ b r a)
    (runs_pure _ b r a))) (by simp)

/-- The entry for a table's own sample. -/
theorem runs_record (T : TableSize) (b r a : Nat) :
    Runs s c b r a (planRecord T) () (recordList s T) b r a := by
  unfold planRecord recordList
  exact Runs.cast (runs_bind (runs_setting b r a) (runs_bind (runs_table T b r a)
    (runs_bind (runs_scope b r a) (runs_push (.record _ _ _) trivial b r a)))) (by simp)

/-- The test on the table on the shared chain, before its proximity tests. -/
theorem runs_linShared (T : TableSize) (x : LinSize) :
    Runs s c 0 0 0 (planLinShared T x) (linColumns s c T x) (linSharedList s c T x) 0 0 0 := by
  unfold planLinShared
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_table T 0 0 0)
    (runs_bind (runs_close _ _ _ _ _ _ _) (runs_bind (runs_send _ _)
      (runs_bind (runs_positions _ _ 0 0 0) (runs_bind (runs_needs _ _ 0 0 0)
        (runs_bind (runs_close _ _ _ _ _ _ _) (runs_bind (runs_listed _ _ 0 0 0)
          (runs_bind (runs_send _ _) (runs_bind (runs_close _ _ _ _ _ _ _)
            (runs_pure _ 0 0 0))))))))))) (by simp [linSharedList, linColumns])

/-- A link before its proximity test. -/
theorem runs_link (T : TableSize) (u : SampleSize) :
    Runs s c 0 0 0 (planLink T u) (linkColumnsFirst s c T, linkColumnsFurther s c T)
      (linkBlockList s c T u) 0 0 0 := by
  unfold planLink
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_table T 0 0 0)
    (runs_bind (runs_close _ _ _ _ _ _ _) (runs_bind (runs_roots0 1 0)
      (runs_bind (runs_listOfGroups _ _ _ u.groups) (runs_bind (runs_close _ _ _ _ _ _ _)
        (runs_bind (runs_answers0 _ 0) (runs_bind (runs_closeNone _ _ _ _)
          (runs_bind (runs_positions _ _ 0 0 0) (runs_bind (runs_positions _ _ 0 0 0)
            (runs_bind (runs_needs _ _ 0 0 0) (runs_bind (runs_close _ _ _ _ _ _ _)
              (runs_bind (runs_listed _ _ 0 0 0) (runs_bind (runs_close _ _ _ _ _ _ _)
                (runs_pure _ 0 0 0)))))))))))))))
    (by simp [linkBlockList, linkColumnsFirst, linkColumnsFurther, linkFirstAgree])

/-- The rounds of an entry's chain. -/
theorem runs_linkPlan (x : LinkSized) :
    Runs s c 0 0 0 (linkPlan x) () (entryChainList s c x) 0 0 0 := by
  unfold linkPlan
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_record x.table 0 0 0)
    (runs_bind (runs_link _ _) (runs_bind (runs_needs _ _ 0 0 0) (runs_iopp _ _ _ _)))))
    (by simp [entryChainList])

/-- The test on the table on the shared chain, with its proximity tests. -/
theorem runs_linPlanShared (codes : Codes) (x : LinSized) :
    Runs s c 0 0 0 (linPlanShared codes x) ()
      (((linSizeOf codes x).map (linSharedTests s c x)).getD []) 0 0 0 := by
  unfold linPlanShared
  refine Runs.cast (runs_bind (runs_setting 0 0 0) (runs_must (L := linSharedTests s c x) ?_))
    (by simp)
  intro L
  exact Runs.cast (runs_bind (runs_linShared x.table L) (runs_bind (runs_needs _ _ 0 0 0)
    (runs_ite (v := ()) (w := ())
      (fun _ => runs_bind runs_split (runs_bind (runs_iopp _ _ _ _) (runs_iopp _ _ _ _)))
      (fun _ => runs_iopp _ _ _ _)))) (by simp [linSharedTests])

/-- The request's own proximity test on a second chain. -/
theorem runs_linPlanSecond (x : LinSized) :
    Runs s c 0 0 0 (linPlanSecond x) () (secondChainList s c x) 0 0 0 := by
  unfold linPlanSecond
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_iopp _ _ _ _)) (by simp [secondChainList])

end

/-- What a finished plan that holds has, against a list of descriptions: the setting; the rounds of
the list; what `close` has tested of each round with a verifier's message (`RoundSpec.Good`); each
round holds in the planner's reckoning. -/
structure PlanIs (P : Planned) (s : Setting) (c : Scope) (l : List RoundSpec) : Prop where
  set : P.set = s
  rounds : P.rounds = l.map (·.round s c)
  good : ∀ y ∈ l, y.Good s c
  holds : ∀ y ∈ l, roundHolds s (capped s) (y.round s c) = true

/-- `finishHeld_rounds`, as one record. -/
theorem planIs_of {s : Setting} {c : Scope} {x : Planning Unit} {l : List RoundSpec}
    {b' r' a' : Nat} {P : Planned} (hx : Runs s c 0 0 0 x () l b' r' a')
    (h : finishHeld s c x = .ok P) : PlanIs P s c l :=
  ⟨(finishHeld_rounds hx h).1, (finishHeld_rounds hx h).2.1, (finishHeld_rounds hx h).2.2.1,
    (finishHeld_rounds hx h).2.2.2⟩

/-- The entries of the plan as it is written in a chain's parameter bytes. -/
theorem PlanIs.entries {P : Planned} {s : Setting} {c : Scope} {l : List RoundSpec}
    (h : PlanIs P s c l) : P.plan.entries = l.map fun y => (y.round s c).entry := by
  show P.rounds.map (·.entry) = _
  rw [h.rounds, List.map_map]
  rfl

/-- What the routine of a shared chain has found: the sizes that the plans read were there, and the
number of columns is the one in the shape. -/
theorem knows_linPlanShared {s : Setting} {c : Scope} (codes : Codes) (x : LinSized) :
    Knows s c 0 0 0 (linPlanShared codes x)
      (∃ L, linSizeOf codes x = some L ∧ linColumns s c x.table L = x.shape.fold.columns) := by
  unfold linPlanShared
  refine knows_snd (runs_setting 0 0 0) (knows_must fun L => ?_)
  exact (knows_snd (runs_linShared x.table L) (knows_fst (knows_needs _ _ 0 0 0))).mono
    fun h => by simpa using h

/-- What the routine of an entry's chain has found: the numbers of columns are those in the shape.
-/
theorem knows_linkPlan {s : Setting} {c : Scope} (x : LinkSized) :
    Knows s c 0 0 0 (linkPlan x)
      (linkColumnsFirst s c x.table = x.shape.columnsFirst ∧
        linkColumnsFurther s c x.table = x.shape.columnsFurther) := by
  unfold linkPlan
  exact (knows_snd (runs_setting 0 0 0) (knows_snd (runs_record x.table 0 0 0)
    (knows_snd (runs_link _ _) (knows_fst (knows_needs _ _ 0 0 0))))).mono
    fun h => by simpa using h

/-- The plan of a shared chain. -/
theorem sharedPlan_rounds {s : Setting} {codes : Codes} {x : LinSized} {P : Planned}
    (h : sharedPlan s codes x = .ok P) :
    PlanIs P s (if x.lines.oneTime then .once else .shared)
      (sharedChainList s (if x.lines.oneTime then .once else .shared) codes x) :=
  planIs_of (runs_bind (runs_linPlanShared codes x) runs_seal) h

/-- The plan of a shared chain, with the sizes L that the plans read: they were there; the number of
columns is the one in the shape; and the list is written at L, with SEAL as its last member. -/
theorem sharedPlan_is {s : Setting} {codes : Codes} {x : LinSized} {P : Planned}
    (h : sharedPlan s codes x = .ok P) :
    ∃ L, linSizeOf codes x = some L ∧
      linColumns s (if x.lines.oneTime then .once else .shared) x.table L =
        x.shape.fold.columns ∧
      PlanIs P s (if x.lines.oneTime then .once else .shared)
        (linSharedTests s (if x.lines.oneTime then .once else .shared) x L ++ [sealRound]) := by
  obtain ⟨L, hL, hc⟩ := finishHeld_knows (knows_fst (knows_linPlanShared codes x)) h
  refine ⟨L, hL, hc, ?_⟩
  have := sharedPlan_rounds h
  unfold sharedChainList at this
  rw [hL] at this
  exact this

/-- The plan of a second chain. -/
theorem secondPlan_rounds {s : Setting} {x : LinSized} {P : Planned}
    (h : secondPlan s x = .ok P) :
    PlanIs P s (if x.lines.oneTime then .once else .request)
      (secondChainList s (if x.lines.oneTime then .once else .request) x) :=
  planIs_of (runs_linPlanSecond x) h

/-- What a proximity test's routine has found: the test has two stages at least. -/
theorem knows_iopp {s : Setting} {c : Scope} (st : List StageSize) (rows firstMaskRoots : Nat)
    (masksRide : Bool) :
    Knows s c 0 0 0 (planIopp st rows firstMaskRoots masksRide) (2 ≤ st.length) := by
  unfold planIopp
  exact (knows_fst (knows_needs _ _ 0 0 0)).mono fun h => by simpa using h

/-- The plan of a second chain, and its test has two stages at least. -/
theorem secondPlan_is {s : Setting} {x : LinSized} {P : Planned} (h : secondPlan s x = .ok P) :
    PlanIs P s (if x.lines.oneTime then .once else .request)
      (secondChainList s (if x.lines.oneTime then .once else .request) x) ∧
      2 ≤ x.own.stages.length := by
  refine ⟨secondPlan_rounds h, finishHeld_knows ?_ h⟩
  unfold linPlanSecond
  exact knows_snd (runs_setting 0 0 0) (knows_iopp _ _ _ _)

/-- The plan of an entry's chain, as `configure` (OnBytes/Params/Configure.lean) and `entrySized`
make it: its list, and the numbers of columns are those in the shape. -/
theorem linkPlan_is {s : Setting} {c : Scope} {x : LinkSized} {P : Planned}
    (h : finishHeld s c (linkPlan x) = .ok P) :
    PlanIs P s c (entryChainList s c x) ∧ linkColumnsFirst s c x.table = x.shape.columnsFirst ∧
      linkColumnsFurther s c x.table = x.shape.columnsFurther :=
  ⟨planIs_of (runs_linkPlan x) h, finishHeld_knows (knows_linkPlan x) h⟩

/-- The sizes of the test on the table hold the lines that they were made from. -/
theorem linSized_lines {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) : x.lines = L := by
  unfold linSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨⟨x1, y1, z1⟩, _, h⟩ := opt_bind h
  replace h := opt_guard h
  obtain ⟨stU, _, h⟩ := opt_bind h
  obtain ⟨stO, h⟩ := opt_either h
  obtain ⟨stW, _, h⟩ := opt_bind h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h

/-- The plan of an entry's chain. -/
theorem entrySized_rounds {l : Lines} {x : LinkSized} {codes : Codes} {P : Planned}
    (h : entrySized l = .ok (x, codes, P)) :
    PlanIs P (settingOf l) .once (entryChainList (settingOf l) .once x) := by
  unfold entrySized at h
  obtain ⟨T, _, h⟩ := exc_bind h
  obtain ⟨⟨x', codes'⟩, _, h⟩ := exc_bind h
  obtain ⟨P', hP, h⟩ := exc_bind h
  cases h
  exact planIs_of (runs_linkPlan x) hP

end OnBytes.Params

#print axioms OnBytes.Params.runs_link
#print axioms OnBytes.Params.PlanIs.entries
#print axioms OnBytes.Params.sharedPlan_is
#print axioms OnBytes.Params.secondPlan_is
#print axioms OnBytes.Params.linkPlan_is
#print axioms OnBytes.Params.linSized_lines
#print axioms OnBytes.Params.sharedPlan_rounds
#print axioms OnBytes.Params.secondPlan_rounds
#print axioms OnBytes.Params.entrySized_rounds
#print axioms OnBytes.Params.runs_record
#print axioms OnBytes.Params.runs_linShared
