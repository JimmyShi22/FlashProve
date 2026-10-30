-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TwoTypesLaw.lean: the prover's side of a proximity test at two
types X and X' of the value that the parts pass on. If the two jobs are the same job (`JobAlike r`,
`RunAlike r`, TwoTypes.lean), the two halves' rounds are related (`HalfAlike`,
Johnson/Desc/ProofFile/Honest/AlikeLots.lean); and no move changes the passed-on value.

  `testHalf_two_plain`   `HalfAlike` of `proverSideOfProximityTest J` and `proverSideOfProximityTest J'` under `JobAlike r J J'`, for
                 the family of relations `fun _ => MidBy (StateBy r)`, which does not count the
                 challenges heard. This is the form for a chain that starts after challenges have
                 been heard: `ProversAlike.meet` (Johnson/Desc/ProofFile/Honest/AlikeChain.lean)
                 asks the family at 0 of such a start
  `testHalf_two`   the same for the family `AtFront (StateBy r) bs`, which counts the challenges
                 heard and asks that none was heard at the start: the form for a first chain
  `testHalf_hands`   for every reader q and every move of `proverSideOfProximityTest J`: `q (mv.hand t) = q t.own`.
                 No hypothesis
  `lightHalf_two`, `lightHalfOf_two`, `mixed_two`   the same as `testHalf_two` for `lightHalf`
                 (PartsBy.lean), for `lightHalfOf` (PartsByJob.lean), and for `proverSideOfProximityTest R.toTest`
                 beside `lightHalfOf R'`; each also with the ending `_plain`
  `lightHalf_hands`, `lightHalfOf_hands`   the same as `testHalf_hands`
  `testAll_two`  under `JobAlike`, `testAll` returns the same value at fronts related by `FrontBy r`
  `reOwn_alike`, `RunJob.reOwn_alike`   the jobs made by `reOwn g` satisfy the relations if r x x'
                 implies x = g x'
  `reOwn_alike_unit`, `RunJob.reOwn_alike_unit`   at X = Unit they do for every r
  `toTest_alike`, `toTest_reOwn`   `RunJob.toTest` carries `RunAlike` to `JobAlike`, and commutes
                 with `reOwn`

By what. Every move of both parts is `moveAt J rd i` (Parts.lean) for some round number i. Its
message is cut out of `testAll`, and it passes on `t.own` unchanged. After the two jobs' parameters
are identified, `proverSideOfProximityTest J'` is `proverSideOfProximityTest J` with other moves (`reRow`), and `half_of_re`
(Johnson/Desc/ProofFile/Honest/AlikeHalf.lean) or `member_re` (AlikeRow.lean beside it) applies.
`lightHalf J` equals `proverSideOfProximityTest J`, and `lightHalfOf R` equals `proverSideOfProximityTest R.toTest`, for every job
(`lightHalf_eq`, PartsByLaw.lean; `lightHalfOf_eq`, PartsByJobLaw.lean). So the six theorems on
`lightHalf`, `lightHalfOf` and the mixed pair are the two on `proverSideOfProximityTest` rewritten, with
`toTest_alike`: they say nothing more of `runBy`.

Limits.
- `HalfAlike` relates the two halves' rounds: the same refusals, the same messages, related states.
  If the chain bs has no block at the half's place, its second clause is empty. For a relation r
  that never holds, hypothesis and conclusion are empty together.
- The hypotheses `JobAlike` and `RunAlike` are the caller's to prove. The relation on states is
  `StateBy r` alone, and r sees the two passed-on values only.
- The lemmas that carry a check on a job R (`StagesOk`, `RunJob.rowsFit`, `ManyJob.layFits`) to
  `R.reOwn g` are in TwoTypesFit.lean.
- `restIdx`, the list of the second part's round numbers, is a definition of this file, used in
  statements alone.
- Nothing follows on what a verifier decides. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.TwoTypes
import Johnson.Desc.ProofFile.Honest.K12.PartsByLaw
import Johnson.Desc.ProofFile.Honest.K12.PartsByJobLaw
import Johnson.Desc.ProofFile.Honest.AlikeHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block)

variable {S Cl V W X X' C Q : Type}

/-! ## 1 The jobs made by `reOwn` -/

theorem frontVia_eq (g : X' → X) (r : X → X' → Prop) (hr : ∀ x x', r x x' → x = g x')
    (fr : Front X) (fr' : Front X') (h : FrontBy r fr fr') : frontVia g fr' = fr := by
  obtain ⟨hd, x, sn⟩ := fr
  obtain ⟨hd', x', sn'⟩ := fr'
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : hd = hd' := h1
  have e2 : x = g x' := hr x x' h2
  have e3 : sn = sn' := h3
  subst e1 e2 e3
  rfl

theorem reOwn_alike (g : X' → X) (r : X → X' → Prop) (hr : ∀ x x', r x x' → x = g x')
    (J : TestJob W X) : JobAlike r J (J.reOwn g) where
  p := rfl
  members := rfl
  fresh := rfl
  rec₀ := fun w fr fr' h => by
    show J.rec₀ w fr = J.rec₀ w (frontVia g fr')
    rw [frontVia_eq g r hr fr fr' h]
  rows₀ := fun w fr fr' h => by
    show J.rows₀ w fr = J.rows₀ w (frontVia g fr')
    rw [frontVia_eq g r hr fr fr' h]
  trees₀ := fun w fr fr' h => by
    show J.trees₀ w fr = J.trees₀ w (frontVia g fr')
    rw [frontVia_eq g r hr fr fr' h]

theorem reOwn_alike_unit (r : Unit → X' → Prop) (J : TestJob W Unit) :
    JobAlike r J (J.reOwn fun _ => ()) :=
  reOwn_alike (fun _ => ()) r (fun _ _ _ => rfl) J

theorem RunJob.reOwn_alike (g : X' → X) (r : X → X' → Prop) (hr : ∀ x x', r x x' → x = g x')
    (R : RunJob W X) : RunAlike r R (R.reOwn g) where
  p := rfl
  members := rfl
  fresh := rfl
  trees := rfl
  rec₀ := fun w fr fr' h => by
    show R.rec₀ w fr = R.rec₀ w (frontVia g fr')
    rw [frontVia_eq g r hr fr fr' h]
  rows := fun w fr fr' h => by
    show R.rows w fr = R.rows w (frontVia g fr')
    rw [frontVia_eq g r hr fr fr' h]

theorem RunJob.reOwn_alike_unit (r : Unit → X' → Prop) (R : RunJob W Unit) :
    RunAlike r R (R.reOwn fun _ => ()) :=
  RunJob.reOwn_alike (fun _ => ()) r (fun _ _ _ => rfl) R

theorem toTest_alike {r : X → X' → Prop} {R : RunJob W X} {R' : RunJob W X'}
    (h : RunAlike r R R') : JobAlike r R.toTest R'.toTest where
  p := h.p
  members := h.members
  fresh := h.fresh
  rec₀ := h.rec₀
  rows₀ := fun w fr fr' hf => by
    show (fun mem => readPS R.s₀ (R.rows w fr mem)) = fun mem => readPS R'.s₀ (R'.rows w fr' mem)
    have e : R.s₀ = R'.s₀ := by
      unfold RunJob.s₀
      rw [h.p]
    rw [e, h.rows w fr fr' hf]
  trees₀ := fun _ _ _ _ => by
    show (fun (_ : ℕ → Stretch) P => R.trees.map fun T => treeOf R.s₀ T P) =
      fun _ P => R'.trees.map fun T => treeOf R'.s₀ T P
    have e : R.s₀ = R'.s₀ := by
      unfold RunJob.s₀
      rw [h.p]
    rw [e, h.trees]

theorem toTest_reOwn (g : X' → X) (R : RunJob W X) : (R.reOwn g).toTest = R.toTest.reOwn g := rfl

/-! ## 2 What the test shows -/

theorem testAll_two {r : X → X' → Prop} {J : TestJob W X} {J' : TestJob W X'}
    (h : JobAlike r J J') (w : W) (fr : Front X) (fr' : Front X') (hf : FrontBy r fr fr')
    (K : TestCoins) (D : ℕ → Fmt.Drawn) : testAll J w fr K D = testAll J' w fr' K D := by
  obtain ⟨p, mem, fsh, rec₀, rows₀, trees₀⟩ := J
  obtain ⟨p', mem', fsh', rec₀', rows₀', trees₀'⟩ := J'
  have e1 : p = p' := h.p
  have e2 : mem = mem' := h.members
  have e3 : fsh = fsh' := h.fresh
  have e4 : rec₀ w fr = rec₀' w fr' := h.rec₀ w fr fr' hf
  have e5 : rows₀ w fr = rows₀' w fr' := h.rows₀ w fr fr' hf
  have e6 : trees₀ w fr = trees₀' w fr' := h.trees₀ w fr fr' hf
  subst e1 e2 e3
  simp only [testAll, TestJob.first, TestJob.recB, TestJob.laid, TestJob.s₀, e4, e5, e6]

theorem msgAt_two {r : X → X' → Prop} {J : TestJob W X} {J' : TestJob W X'}
    (h : JobAlike r J J') (w : W) (fr : Front X) (fr' : Front X') (hf : FrontBy r fr fr')
    (K : TestCoins) (D : ℕ → Fmt.Drawn) (i : ℕ) : msgAt J w fr K D i = msgAt J' w fr' K D i := by
  have e : depthAt J i = depthAt J' i := by
    unfold depthAt
    rw [h.p, h.fresh]
  unfold msgAt
  rw [testAll_two h w fr fr' hf K D, e]

/-! ## 3 The moves -/

/-- The moves of a list of round numbers, at the two jobs, say the same from related states and lead
to related states. -/
theorem moves_two {r : X → X' → Prop} {J : TestJob W X} {J' : TestJob W X'} (h : JobAlike r J J')
    (rd : C → TestCoins) (c : C) :
    ∀ (is : List ℕ) (t : State W X) (t' : State W X') (seen : List Fmt.RoundView), StateBy r t t' →
      MovesTo c (StateBy r) (is.map (moveAt J rd)) (is.map (moveAt J' rd)) t t' seen
  | [], _, _, _, q => q
  | i :: is, ⟨w, hd, x⟩, ⟨w', hd', x'⟩, seen, q => by
    obtain ⟨q1, q2, q3⟩ := q
    have e1 : w = w' := q1
    have e2 : hd = hd' := q2
    have e3 : r x x' := q3
    subst e1 e2
    refine ⟨fun o => ?_, fun d e => moves_two h rd c is _ _ _ ⟨rfl, rfl, e3⟩⟩
    have key := msgAt_two h w ⟨hd.take (hd.length - i), x, (⟨seen, o⟩ : Seen).front i⟩
      ⟨hd.take (hd.length - i), x', (⟨seen, o⟩ : Seen).front i⟩ ⟨rfl, e3, rfl⟩ (rd c)
      (fun n => (hd.drop (hd.length - i)).getD n ⟨[], [], [], none⟩) i
    exact congrArg Except.ok key

/-- The round numbers of the second part's moves. -/
def restIdx (st : List Fmt.M1.Stage) : List ℕ :=
  ((List.range (st.length - 1)).flatMap fun j =>
    (if j = 0 then []
      else (List.range (1 + (st.getD j default).k)).map fun i => roundOf st j + i) ++
      (List.range 2).map fun i => roundOf st j + 1 + (st.getD j default).k + i) ++
    (List.range 2).map fun i => roundOf st (st.length - 1) + i

theorem restPart_moves (J : TestJob W X) :
    (restPart J : Part V W X).moves = (restIdx J.p.nums.stages).map (moveAt J (restCoins J)) := by
  show ((List.range (J.p.nums.stages.length - 1)).flatMap fun j =>
      (if j = 0 then [] else foldMoves J (restCoins J) j) ++ switchMoves J (restCoins J) j) ++
    baseMoves J (restCoins J) = _
  unfold restIdx foldMoves switchMoves baseMoves movesFrom
  rw [List.map_append, List.map_flatMap, List.map_map]
  refine congrArg (· ++ _)
    (congrArg (fun F => (List.range (J.p.nums.stages.length - 1)).flatMap F) (funext fun j => ?_))
  rw [List.map_append, List.map_map]
  by_cases hj : j = 0
  · rw [if_pos hj, if_pos hj]
    rfl
  · rw [if_neg hj, if_neg hj, List.map_map]
    rfl

theorem movesFrom_map (J : TestJob W X) (rd : C → TestCoins) (a n : ℕ) :
    movesFrom J rd a n = ((List.range n).map fun i => a + i).map (moveAt J rd) := by
  unfold movesFrom
  rw [List.map_map]
  rfl

theorem movesFrom_two {r : X → X' → Prop} {J : TestJob W X} {J' : TestJob W X'}
    (h : JobAlike r J J') (rd : C → TestCoins) (a n : ℕ) (c : C) (t : State W X) (t' : State W X')
    (seen : List Fmt.RoundView) (q : StateBy r t t') :
    MovesTo c (StateBy r) (movesFrom J rd a n) (movesFrom J' rd a n) t t' seen := by
  rw [movesFrom_map, movesFrom_map]
  exact moves_two h rd c _ t t' seen q

theorem movesFrom_length (J : TestJob W X) (rd : C → TestCoins) (a n : ℕ) :
    (movesFrom J rd a n).length = n := by
  unfold movesFrom
  rw [List.length_map, List.length_range]

/-! ## 4 The half at two types -/

/-- Under `JobAlike`, `proverSideOfProximityTest J'` is `proverSideOfProximityTest J` with other moves, and the two rows of moves are
related part by part (`RowTo`, Johnson/Desc/ProofFile/Honest/AlikeRow.lean). -/
theorem testHalf_row {r : X → X' → Prop} {J : TestJob W X} {J' : TestJob W X'}
    (h : JobAlike r J J') :
    ∃ R : ReRow X' (proverSideOfProximityTest J : Placed V W X).parts,
      (proverSideOfProximityTest J' : Placed V W X') =
          ⟨(proverSideOfProximityTest J : Placed V W X).place, reRow (proverSideOfProximityTest J : Placed V W X).parts R⟩ ∧
        RowTo (StateBy r) (proverSideOfProximityTest J : Placed V W X).parts R := by
  obtain ⟨p, mem, fsh, rec₀, rows₀, trees₀⟩ := J
  obtain ⟨p', mem', fsh', rec₀', rows₀', trees₀'⟩ := J'
  have e1 : p = p' := h.p
  have e2 : mem = mem' := h.members
  have e3 : fsh = fsh' := h.fresh
  subst e1 e2 e3
  have hrest : ∀ (c : (restPart (V := V) ⟨p, mem, fsh, rec₀, rows₀, trees₀⟩).Coins) (t : State W X)
      (t' : State W X') (seen : List Fmt.RoundView), StateBy r t t' →
      MovesTo c (StateBy r) (restPart (V := V) ⟨p, mem, fsh, rec₀, rows₀, trees₀⟩).moves
        (restPart (V := V) ⟨p, mem, fsh, rec₀', rows₀', trees₀'⟩).moves t t' seen := by
    intro c t t' seen q
    rw [restPart_moves, restPart_moves]
    exact moves_two h _ c _ t t' seen q
  have lrest : (restPart (V := V) ⟨p, mem, fsh, rec₀', rows₀', trees₀'⟩).moves.length =
      (restPart (V := V) ⟨p, mem, fsh, rec₀, rows₀, trees₀⟩).moves.length := by
    have a := congrArg List.length
      (restPart_moves (V := V) (⟨p, mem, fsh, rec₀', rows₀', trees₀'⟩ : TestJob W X'))
    have b := congrArg List.length
      (restPart_moves (V := V) (⟨p, mem, fsh, rec₀, rows₀, trees₀⟩ : TestJob W X))
    exact (a.trans (List.length_map _)).trans (b.trans (List.length_map _)).symm
  cases fsh with
  | none =>
    exact ⟨((firstPart (V := V) ⟨p, mem, none, rec₀', rows₀', trees₀'⟩).moves,
        (restPart (V := V) ⟨p, mem, none, rec₀', rows₀', trees₀'⟩).moves, ()), rfl,
      ⟨(movesFrom_length _ _ _ _).trans (movesFrom_length _ _ _ _).symm,
        fun c t t' seen q => movesFrom_two h _ _ _ c t t' seen q⟩, ⟨lrest, hrest⟩, True.intro⟩
  | some a =>
    exact ⟨((firstPart (V := V) ⟨p, mem, some a, rec₀', rows₀', trees₀'⟩).moves,
        (restPart (V := V) ⟨p, mem, some a, rec₀', rows₀', trees₀'⟩).moves, ()), rfl,
      ⟨(movesFrom_length _ _ _ _).trans (movesFrom_length _ _ _ _).symm,
        fun c t t' seen q => movesFrom_two h _ _ _ c t t' seen q⟩, ⟨lrest, hrest⟩, True.intro⟩

/-- The half at two types, for the family of relations that counts the challenges heard. -/
theorem testHalf_two (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (bs : List (Block S Cl)) (r : X → X' → Prop) (J : TestJob W X)
    (J' : TestJob W X') (h : JobAlike r J J') :
    HalfAlike B rows look v bs (AtFront (StateBy r) bs) (proverSideOfProximityTest J) (proverSideOfProximityTest J') := by
  obtain ⟨R, e, hR⟩ := testHalf_row (V := V) h
  rw [e]
  exact half_of_re B rows look v bs (StateBy r) _ R hR

/-- The half at two types, for the family of relations that does not count. -/
theorem testHalf_two_plain (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (bs : List (Block S Cl)) (r : X → X' → Prop) (J : TestJob W X)
    (J' : TestJob W X') (h : JobAlike r J J') :
    HalfAlike B rows look v bs (fun _ => MidBy (StateBy r)) (proverSideOfProximityTest J) (proverSideOfProximityTest J') := by
  obtain ⟨R, e, hR⟩ := testHalf_row (V := V) h
  rw [e]
  refine ⟨rfl, fun _ b _ hp => ?_⟩
  exact member_re B rows look v b [proverSideOfProximityTest J] [⟨(proverSideOfProximityTest J : Placed V W X).place, reRow _ R⟩]
    (StateBy r) (proverSideOfProximityTest J) R (by simp only [List.find?_cons, hp])
    (by simp only [List.find?_cons, hp]) hR

/-! ## 5 No move changes the passed-on value -/

theorem movesFrom_hands (J : TestJob W X) (rd : C → TestCoins) (a n : ℕ) :
    ∀ mv ∈ movesFrom J rd a n, ∀ t, mv.hand t = t.own := by
  intro mv hmv t
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hmv
  rfl

theorem firstPart_hands (J : TestJob W X) :
    ∀ mv ∈ (firstPart J : Part V W X).moves, ∀ t, mv.hand t = t.own := by
  obtain ⟨p, mem, fsh, rec₀, rows₀, trees₀⟩ := J
  cases fsh with
  | none => exact movesFrom_hands _ _ _ _
  | some a => exact movesFrom_hands _ _ _ _

theorem restPart_hands (J : TestJob W X) :
    ∀ mv ∈ (restPart J : Part V W X).moves, ∀ t, mv.hand t = t.own := by
  rw [restPart_moves]
  intro mv hmv t
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hmv
  rfl

/-- No move of the half changes what a reader q reads of the passed-on value. -/
theorem testHalf_hands (q : X → Q) (J : TestJob W X) :
    ∀ p ∈ (proverSideOfProximityTest J : Placed V W X).parts, ∀ mv ∈ p.moves, ∀ t, q (mv.hand t) = q t.own := by
  intro p hp
  have hp' : p ∈ [(firstPart J : Part V W X), restPart J] := hp
  rcases List.mem_cons.1 hp' with rfl | h2
  · exact fun mv hmv t => congrArg q (firstPart_hands J mv hmv t)
  · obtain rfl := List.mem_singleton.1 h2
    exact fun mv hmv t => congrArg q (restPart_hands J mv hmv t)

/-! ## 6 The guarded halves -/

theorem lightHalf_two (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (bs : List (Block S Cl)) (r : X → X' → Prop) (J : TestJob W X)
    (J' : TestJob W X') (h : JobAlike r J J') :
    HalfAlike B rows look v bs (AtFront (StateBy r) bs) (lightHalf J) (lightHalf J') := by
  rw [lightHalf_eq, lightHalf_eq]
  exact testHalf_two B rows look v bs r J J' h

theorem lightHalf_two_plain (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (v : Option V) (bs : List (Block S Cl)) (r : X → X' → Prop)
    (J : TestJob W X) (J' : TestJob W X') (h : JobAlike r J J') :
    HalfAlike B rows look v bs (fun _ => MidBy (StateBy r)) (lightHalf J) (lightHalf J') := by
  rw [lightHalf_eq, lightHalf_eq]
  exact testHalf_two_plain B rows look v bs r J J' h

theorem lightHalfOf_two (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (bs : List (Block S Cl)) (r : X → X' → Prop) (R : RunJob W X)
    (R' : RunJob W X') (h : RunAlike r R R') :
    HalfAlike B rows look v bs (AtFront (StateBy r) bs) (lightHalfOf R) (lightHalfOf R') := by
  rw [lightHalfOf_eq, lightHalfOf_eq]
  exact testHalf_two B rows look v bs r _ _ (toTest_alike h)

theorem lightHalfOf_two_plain (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (v : Option V) (bs : List (Block S Cl)) (r : X → X' → Prop)
    (R : RunJob W X) (R' : RunJob W X') (h : RunAlike r R R') :
    HalfAlike B rows look v bs (fun _ => MidBy (StateBy r)) (lightHalfOf R) (lightHalfOf R') := by
  rw [lightHalfOf_eq, lightHalfOf_eq]
  exact testHalf_two_plain B rows look v bs r _ _ (toTest_alike h)

/-- `proverSideOfProximityTest R.toTest` at X beside `lightHalfOf R'` at X'. -/
theorem mixed_two (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (bs : List (Block S Cl)) (r : X → X' → Prop) (R : RunJob W X)
    (R' : RunJob W X') (h : RunAlike r R R') :
    HalfAlike B rows look v bs (AtFront (StateBy r) bs) (proverSideOfProximityTest R.toTest) (lightHalfOf R') := by
  rw [lightHalfOf_eq]
  exact testHalf_two B rows look v bs r _ _ (toTest_alike h)

theorem mixed_two_plain (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (bs : List (Block S Cl)) (r : X → X' → Prop) (R : RunJob W X)
    (R' : RunJob W X') (h : RunAlike r R R') :
    HalfAlike B rows look v bs (fun _ => MidBy (StateBy r)) (proverSideOfProximityTest R.toTest)
      (lightHalfOf R') := by
  rw [lightHalfOf_eq]
  exact testHalf_two_plain B rows look v bs r _ _ (toTest_alike h)

theorem lightHalf_hands (q : X → Q) (J : TestJob W X) :
    ∀ p ∈ (lightHalf J : Placed V W X).parts, ∀ mv ∈ p.moves, ∀ t, q (mv.hand t) = q t.own := by
  rw [lightHalf_eq]
  exact testHalf_hands q J

theorem lightHalfOf_hands (q : X → Q) (R : RunJob W X) :
    ∀ p ∈ (lightHalfOf R : Placed V W X).parts, ∀ mv ∈ p.moves, ∀ t,
      q (mv.hand t) = q t.own := by
  rw [lightHalfOf_eq]
  exact testHalf_hands q R.toTest

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.frontVia_eq
#print axioms ProofFile.Honest.K12.Light.reOwn_alike
#print axioms ProofFile.Honest.K12.Light.reOwn_alike_unit
#print axioms ProofFile.Honest.K12.Light.RunJob.reOwn_alike
#print axioms ProofFile.Honest.K12.Light.RunJob.reOwn_alike_unit
#print axioms ProofFile.Honest.K12.Light.toTest_alike
#print axioms ProofFile.Honest.K12.Light.toTest_reOwn
#print axioms ProofFile.Honest.K12.Light.testAll_two
#print axioms ProofFile.Honest.K12.Light.msgAt_two
#print axioms ProofFile.Honest.K12.Light.moves_two
#print axioms ProofFile.Honest.K12.Light.restPart_moves
#print axioms ProofFile.Honest.K12.Light.movesFrom_map
#print axioms ProofFile.Honest.K12.Light.movesFrom_two
#print axioms ProofFile.Honest.K12.Light.movesFrom_length
#print axioms ProofFile.Honest.K12.Light.testHalf_row
#print axioms ProofFile.Honest.K12.Light.testHalf_two
#print axioms ProofFile.Honest.K12.Light.testHalf_two_plain
#print axioms ProofFile.Honest.K12.Light.movesFrom_hands
#print axioms ProofFile.Honest.K12.Light.firstPart_hands
#print axioms ProofFile.Honest.K12.Light.restPart_hands
#print axioms ProofFile.Honest.K12.Light.testHalf_hands
#print axioms ProofFile.Honest.K12.Light.lightHalf_two
#print axioms ProofFile.Honest.K12.Light.lightHalf_two_plain
#print axioms ProofFile.Honest.K12.Light.lightHalfOf_two
#print axioms ProofFile.Honest.K12.Light.lightHalfOf_two_plain
#print axioms ProofFile.Honest.K12.Light.mixed_two
#print axioms ProofFile.Honest.K12.Light.mixed_two_plain
#print axioms ProofFile.Honest.K12.Light.lightHalf_hands
#print axioms ProofFile.Honest.K12.Light.lightHalfOf_hands
#print axioms ProofFile.Honest.K12.Light.restIdx
