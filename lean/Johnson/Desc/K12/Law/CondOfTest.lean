-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CondOfTest.lean: the condition of the law of a proximity test (the kind K12),
`K12Condition` (Johnson/Desc/K12/Law/ChainHolds.lean), from one test on numbers of
Johnson/Bridge/TestsAtWritten.lean (`TestAt.ok`), asked at the place's own test. Definitions,
statements and proofs.

Why. `k12Condition_native` (Johnson/Desc/K12/Law/SmallCut.lean) has the condition from four Booleans
of this folder. Johnson/Bridge/ has a test of its own on the same numbers: a proximity test behind
its batching as one object, `TestAt`, with `TestAt.ok`; it is evaluated in the kernel at written
lists (`tests_ok`) and as a function of the planner's records (Johnson/Bridge/PlanTests.lean). By
their own heads these files are tied to no place of a description. This file ties them.
Main names:
  `foldAt`, `lastAt`, `switchAt`: a stage of the place as a place of Johnson/Bridge/.
  `testOf rad B p`: the `TestAt` made of the place's own stages and bits of work, at radii and
    brackets that are handed in.
  `OkFrom`, `okFrom_aux`, `okFrom_of_test`: all tests of all places, along the stages.
    `stageJ_of_okFrom`: they give `Sg.StageJ` at every stage.
  `roundB_of`, `roundB_gen`, `roundB_one`: a yes of `roundB` (SmallOfPlaces.lean) from the numbers.
    `cardQ`: the extension field has `Cb.Gl.p ^ 3` elements. `pTwo`: the format's prime is
    `Cb.Gl.p`. `q_pos`: that number is not 0. `brB_fold`, `brB_last`: the brackets' clause off
    `good`. `epsE_facts`: six numbers of a fold's first entry, with a root more or without.
  `step_small`, `last_small`, `walk_small`: the clauses of `smallOk` from `priced`, clause by
    clause, at the declared rounds as `H2U.roundsOfNums` makes them (MadeRounds.lean,
    SpendMade.lean).
  `made_of_planOk`: what the block's test on the plan gives of the made and the written rounds.
  `k12Condition_of_test`: `testOf rad B p = some T`, `T.ok = true`, the test on the plan of
    `proximityTestKind guardedProximityTestParts p` and `pubOk p K` give
    `K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p K (2⁻¹ ^ 128)`.
The place whose first fold sends its own mask is covered: nothing asks that the fold's first round
is the format's `rEps`; `step_small` goes at the entry as it is made, with a root more or without.
It stands over files of Johnson/Bridge/, and so over Cb/Bridge/CodeListRSProved.lean and
the files under ThirdParty/, adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15). It takes no run of their text; it calls their names.
Limits: no place is shown here at which `T.ok` says yes. rad and B are functions of a stage's
numbers. The limits of the condition stand: one round's share of its written verifier messages, test
bits among them: W of the 128 bits are work; no sum over rounds; the round "BAT" stands in front of
the chain and is not in it; of the chain, not of the block. No soundness is claimed. Nothing on
hiding.

-/
import Johnson.Bridge.TestsAtWritten
import Johnson.Desc.K12.Law.SmallOfPlaces
import Johnson.Desc.K12.Law.SpendMade

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Bridge (Br FoldedPlace SwitchPlace LastPlace TestAt switchesOf)
open Fmt.M1 (rEps rTwo rSeed rCs rLambda rBase laterRounds wMid)
open H2K.Made (Op wr epsE lay_stage lay_base layW_inv layW_rep kEps kTwo kSeed kCs kLam kBase
  epsE_name Fit Sz)
open scoped ENNReal

variable (rad : Sg → ℕ) (B : Sg → Br × Br)

/-- A stage of the place that is folded, as a place of Johnson/Bridge/FoldPriced.lean. -/
def foldAt (a : Fmt.M1.Stage) : FoldedPlace :=
  ⟨sgOf a, rad (sgOf a), (B (sgOf a)).1, (B (sgOf a)).2⟩

/-- The place's last stage, with the place's bits of work. -/
def lastAt (w : ℕ) (a : Fmt.M1.Stage) : LastPlace :=
  ⟨sgOf a, rad (sgOf a), w, (B (sgOf a)).1, (B (sgOf a)).2⟩

/-- The code switch between two neighbours. -/
def switchAt (w : ℕ) (a b : Fmt.M1.Stage) : SwitchPlace :=
  ⟨sgOf a, sgOf b, rad (sgOf a), rad (sgOf b), w⟩

/-- **The place's own test**, as the object of Johnson/Bridge/TestsAtWritten.lean. -/
def testOf (p : P12) : Option TestAt :=
  p.nums.stages.getLast?.map fun z =>
    ⟨p.nums.stages.dropLast.map (foldAt rad B), lastAt rad B p.nums.work z⟩

/-- All tests of all places, along the stages. -/
def OkFrom (w : ℕ) : Fmt.M1.Stage → List Fmt.M1.Stage → Prop
  | a, [] => (lastAt rad B w a).good = true ∧ (lastAt rad B w a).priced = true
  | a, b :: rest => (foldAt rad B a).good = true ∧ (foldAt rad B a).priced = true ∧
      (switchAt rad w a b).good = true ∧ (switchAt rad w a b).priced = true ∧ OkFrom w b rest

theorem okFrom_aux (w : ℕ) : ∀ (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage),
    (((a :: rest).dropLast.map (foldAt rad B)).all fun x => x.good && x.priced) = true →
    ((switchesOf w ((a :: rest).map fun x => (sgOf x, rad (sgOf x)))).all
      fun x => x.good && x.priced) = true →
    (∀ z, (a :: rest).getLast? = some z →
      (lastAt rad B w z).good = true ∧ (lastAt rad B w z).priced = true) →
    OkFrom rad B w a rest
  | [], a, _, _, h3 => h3 a rfl
  | b :: rest, a, h1, h2, h3 => by
    rw [List.dropLast_cons₂, List.map_cons, List.all_cons, Bool.and_eq_true,
      Bool.and_eq_true] at h1
    rw [List.map_cons, List.map_cons] at h2
    unfold switchesOf at h2
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at h2
    exact ⟨h1.1.1, h1.1.2, h2.1.1, h2.1.2, okFrom_aux w rest b h1.2
      (by rw [List.map_cons]; exact h2.2)
          (fun z hz => h3 z (by rw [List.getLast?_cons_cons]; exact hz))⟩

theorem okFrom_of_test (p : P12) (T : TestAt) (hT : testOf rad B p = some T) (hok : T.ok = true)
    (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hs : p.nums.stages = a :: rest) :
    OkFrom rad B p.nums.work a rest := by
  unfold testOf at hT
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hT
  simp only [TestAt.ok, Bool.and_eq_true] at hok
  have hst : (TestAt.stages ⟨p.nums.stages.dropLast.map (foldAt rad B),
      lastAt rad B p.nums.work z⟩) = p.nums.stages.map fun x => (sgOf x, rad (sgOf x)) := by
    have e := List.dropLast_append_getLast? z hz
    conv => rhs; rw [← e]
    simp [TestAt.stages, foldAt, lastAt, List.map_map, Function.comp_def]
  have h2 := hok.1.2
  unfold TestAt.switches at h2
  rw [hst, hs] at h2
  refine okFrom_aux rad B _ rest a (by rw [← hs]; exact hok.1.1) h2 ?_
  intro z' hz'
  rw [← hs, hz] at hz'
  obtain rfl := Option.some.inj hz'
  exact hok.2

/-- One written round and a count, from the numbers. -/
theorem roundB_of (w : WR) (count N : ℕ) (hlog : w.entry.logN ≤ 64)
    (hnz : w.entry.drawNZ ≤ w.entry.drawE) (hw : w.entry.drawE = 0 ∨ w.entry.work + 66 ≤ 128)
    (hN : nVals (Fmt.dsOf w.entry w.kind) = N) (hN0 : 0 < N)
    (hc : count * 2 ^ 193 + 3 * (w.entry.drawE + w.entry.drawNZ) * N ≤
      N * 2 ^ (w.entry.work + 65)) : roundB w count = true := by
  unfold roundB
  rw [hN]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨hlog, hnz⟩, hw⟩, hN0⟩, hc⟩

/-- The same, with the entry's three numbers named. -/
theorem roundB_gen (w : WR) (count N E Z W : ℕ) (hE : w.entry.drawE = E) (hZ : w.entry.drawNZ = Z)
    (hW : w.entry.work = W) (hlog : w.entry.logN ≤ 64) (hnz : Z ≤ E) (hw : E = 0 ∨ W + 66 ≤ 128)
    (hN : nVals (Fmt.dsOf w.entry w.kind) = N) (hN0 : 0 < N)
    (hc : count * 2 ^ 193 + 3 * (E + Z) * N ≤ N * 2 ^ (W + 65)) : roundB w count = true :=
  roundB_of w count N hlog (by rw [hE, hZ]; exact hnz) (by rw [hE, hW]; exact hw) hN hN0
    (by rw [hE, hZ, hW]; exact hc)

theorem cardQ : Fintype.card GE = Cb.Gl.p ^ 3 := Cb.Gl.gl_card.2.1

theorem pTwo : Fmt.Fld.two.p = Cb.Gl.p := by decide +kernel

theorem q_pos : 0 < Cb.Gl.p ^ 3 := by rw [← cardQ]; exact Fintype.card_pos

/-- A round that draws one element and nothing else, without work. -/
theorem roundB_one (w : WR) (count : ℕ) (hE : w.entry.drawE = 1) (hZ : w.entry.drawNZ = 0)
    (hP : w.entry.poss = 0) (hT : w.entry.trits = 0) (hL : w.entry.logN = 0)
    (hW : w.entry.work = 0) (hk1 : w.kind ≠ .seeds) (hk2 : w.kind ≠ .sealed)
    (hc : count * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65)) :
    roundB w count = true :=
  roundB_of w count (Cb.Gl.p ^ 3) (by omega) (by omega) (Or.inr (by omega))
    ((Johnson.Bridge.nVals_one (d := w.rd) hE hZ hP hT hk1 hk2).trans cardQ) q_pos
    (by rw [hE, hZ, hW]; exact hc)

variable {rad B}

theorem brB_fold {a : Fmt.M1.Stage} (h : (foldAt rad B a).good = true) :
    brB (sgOf a) (rad (sgOf a)) (B (sgOf a)) = true := by
  simp only [FoldedPlace.good, Bool.and_eq_true] at h
  unfold brB
  rw [Bool.and_eq_true]
  exact ⟨h.1.2, h.2⟩

theorem brB_last {w : ℕ} {a : Fmt.M1.Stage} (h : (lastAt rad B w a).good = true) :
    brB (sgOf a) (rad (sgOf a)) (B (sgOf a)) = true := by
  simp only [LastPlace.good, Bool.and_eq_true] at h
  unfold brB
  rw [Bool.and_eq_true]
  exact ⟨h.1.2, h.2⟩

theorem epsE_facts (own seen : Bool) : (epsE own seen).drawE = 1 ∧ (epsE own seen).drawNZ = 0 ∧
    (epsE own seen).poss = 0 ∧ (epsE own seen).trits = 0 ∧ (epsE own seen).logN = 0 ∧
    (epsE own seen).work = 0 := by
  cases own <;> cases seen <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The six clauses at a stage that is folded and switched, at the rounds as they are made. -/
theorem step_small {a b : Fmt.M1.Stage} {w : ℕ} (own seen : Bool) (tree W : ℕ) (x : List Op)
    (t1 t3 t4 : Option Fmt.Shape) (hb : b.h ≤ b.k) (ha : a.C.a ≤ 64)
    (h1 : (foldAt rad B a).good = true) (h2 : (foldAt rad B a).priced = true)
    (h4 : (switchAt rad w a b).priced = true) :
    ok (stepCl (sgOf a) (sgOf b) (rad (sgOf a)) (rad (sgOf b)) (B (sgOf a))
      (wr ⟨epsE own seen, [], []⟩ .join t1) (wr ⟨(rTwo "FOLD round").entry, [], []⟩ .elems none)
      (wr ⟨(rSeed b).entry, [], []⟩ .seeds t3)
      (wr ⟨(rCs w a tree W).entry, [], x⟩ .positions t4)) = true := by
  have e : (sgOf b).st = b := by rw [sgOf_st]; exact stN_eq hb
  have hpl := FoldedPlace.priced_plain h2
  have hcp : (foldAt rad B a).cntPlain =
      (B (sgOf a)).1.N + (sgOf a).lstJ (rad (sgOf a)) * 2 := rfl
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := epsE_facts own seen
  simp only [stepCl, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨brB_fold h1, ?_, ?_, ?_, ?_, ?_⟩
  · refine roundB_one _ _ f1 f2 f3 f4 f5 f6 (by show Fmt.Kind.join ≠ _; decide)
      (by show Fmt.Kind.join ≠ _; decide) (Nat.le_trans ?_ hpl)
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by rw [hcp]; omega)) _
  · rw [hcp] at hpl
    exact roundB_one _ _ rfl rfl rfl rfl rfl rfl (by show Fmt.Kind.elems ≠ _; decide)
      (by show Fmt.Kind.elems ≠ _; decide) hpl
  · rw [Bool.or_eq_true]
    by_cases h0 : (sgOf a).h = 0
    · exact Or.inl (decide_eq_true h0)
    · have hm := FoldedPlace.priced_mask h2 h0
      have hcm : (foldAt rad B a).cntMask = (B (sgOf a)).1.N +
          (bZof (sgOf a) (rad (sgOf a)) (B (sgOf a)) + bZof (sgOf a) (rad (sgOf a)) (B (sgOf a))) +
          (sgOf a).lstJ (rad (sgOf a)) * 2 := rfl
      rw [hcm] at hm
      exact Or.inr (roundB_one _ _ rfl rfl rfl rfl rfl rfl (by show Fmt.Kind.elems ≠ _; decide)
        (by show Fmt.Kind.elems ≠ _; decide) hm)
  · have p1 := SwitchPlace.priced1 h4
    simp only [SwitchPlace.cnt1, SwitchPlace.n1, SwitchPlace.lst, switchAt, e] at p1
    have hN : nVals (Fmt.dsOf (rSeed b).entry (rSeed b).kind) =
        (Cb.Gl.p ^ 3) ^ b.na * (Cb.Gl.p ^ 3 - 1) := by
      rw [Johnson.Bridge.dsOf_rSeed, nVals_seed, cardQ]
    refine roundB_gen _ _ ((Cb.Gl.p ^ 3) ^ b.na * (Cb.Gl.p ^ 3 - 1)) (b.na + 1) 1 0 rfl rfl rfl
      (Nat.zero_le _) (by omega) (Or.inr (by omega)) hN (Johnson.Bridge.seeds_pos _ cardQ _) ?_
    rw [Nat.choose_two_right, pTwo, e]
    exact p1
  · have p2 := SwitchPlace.priced2 h4
    have p3 := SwitchPlace.priced3 h4
    simp only [SwitchPlace.cnt2, SwitchPlace.n2, SwitchPlace.lst, switchAt] at p2 p3
    refine roundB_gen _ _ ((2 ^ a.C.a) ^ a.t * Cb.Gl.p ^ 3) 1 0 w rfl rfl rfl ha (by omega)
      (Or.inr p3)
          (Johnson.Bridge.nVals_posOne (d := (wr ⟨(rCs w a tree W).entry, [], x⟩ .positions t4).rd)
        rfl rfl rfl (by show Fmt.Kind.positions ≠ _; decide)
        (by show Fmt.Kind.positions ≠ _; decide) _ cardQ)
      (Nat.mul_pos (by positivity) q_pos) ?_
    rw [pTwo]
    exact p2

/-- The three clauses at the last stage. -/
theorem last_small {a : Fmt.M1.Stage} {w : ℕ} (tree : ℕ) (x : List Op)
    (t1 t2 : Option Fmt.Shape) (ha : a.C.a ≤ 64)
    (h1 : (lastAt rad B w a).good = true) (h2 : (lastAt rad B w a).priced = true) :
    ok (lastCl (sgOf a) (rad (sgOf a)) (B (sgOf a)) (wr ⟨rLambda.entry, [], []⟩ .elems t1)
      (wr ⟨(rBase w a tree).entry, [], x⟩ .positions t2)) = true := by
  simp only [lastCl, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨brB_last h1, ?_, ?_⟩
  · have hl := LastPlace.priced_lambda h2
    have hcl : (lastAt rad B w a).exc + (lastAt rad B w a).lst = (B (sgOf a)).1.N +
        bZof (sgOf a) (rad (sgOf a)) (B (sgOf a)) + (sgOf a).lstJ (rad (sgOf a)) := rfl
    rw [hcl] at hl
    exact roundB_one _ _ rfl rfl rfl rfl rfl rfl (by show Fmt.Kind.elems ≠ _; decide)
      (by show Fmt.Kind.elems ≠ _; decide) hl
  · have hb := LastPlace.priced_base h2
    simp only [lastAt] at hb
    exact roundB_gen _ _ ((2 ^ a.C.a) ^ a.t) 0 0 w rfl rfl rfl ha (Nat.le_refl _) (Or.inl rfl)
      (nVals_positions (d := (wr ⟨(rBase w a tree).entry, [], x⟩ .positions t2).rd) rfl rfl rfl
        (by show Fmt.Kind.positions ≠ _; decide) (by show Fmt.Kind.positions ≠ _; decide))
      (by positivity) hb

/-- The walk over the written rounds. -/
theorem walk_small (own : Bool) (work : ℕ) : ∀ (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage)
    (seen : Bool) (j tree W : ℕ) (ls : List (List Op)) (R : List Fmt.DeclaredRound)
    (sh : List Fmt.Shape) (l : List WR), (rest = [] → seen = true) →
    H2U.layOpens own seen (laterRounds work tree W a rest) ls = some R → layW R sh = some l →
    Fit a rest → (∀ s ∈ a :: rest, s.h ≤ s.k) → OkFrom rad B work a rest →
    ok (smallCl rad B j a rest l) = true
  | [], a, seen, j, tree, W, ls, R, sh, l, hs, h, hl, hF, _, hO => by
    obtain rfl := hs rfl
    obtain ⟨x, _, _, rfl⟩ := lay_base own work tree W a ls R h
    obtain ⟨t1, l1, sh1, rfl, hl1⟩ := layW_inv _ .elems kLam hl
    obtain ⟨t2, l2, sh2, rfl, hl2⟩ := layW_inv _ .positions kBase hl1
    have hn : l2 = [] := by
      unfold layW at hl2
      cases sh2 with
      | nil => exact (Option.some.inj hl2).symm
      | cons _ _ => cases hl2
    subst hn
    unfold smallCl
    rw [ok_tag]
    exact last_small tree x t1 t2 (Nat.le_trans hF.1 (by decide)) hO.1 hO.2
  | b :: rest, a, seen, j, tree, W, ls, R, sh, l, _, h, hl, hF, hk, hO => by
    obtain ⟨hz, hka, h1k, hF'⟩ := hF
    obtain ⟨o1, o2, _, o4, hO'⟩ := hO
    obtain ⟨x, t, R', _, _, h', rfl⟩ := lay_stage own seen work tree W a b rest ls R h
    rw [List.cons_append] at hl
    obtain ⟨t1, l1, sh1, rfl, hl1⟩ := layW_inv _ .join (by rw [epsE_name]; exact kEps) hl
    rw [layW_rep _ .elems kTwo rfl] at hl1
    obtain ⟨l2, hl2, rfl⟩ := Option.map_eq_some_iff.1 hl1
    obtain ⟨t3, l3, sh3, rfl, hl3⟩ := layW_inv _ .seeds kSeed hl2
    obtain ⟨t4, l4, sh4, rfl, hl4⟩ := layW_inv _ .positions kCs hl3
    obtain ⟨n, hn⟩ : ∃ n, a.k = n + 1 := ⟨a.k - 1, by omega⟩
    have hkk : kk a = n + 1 := by
      unfold kk
      omega
    rw [hn, List.replicate_succ, List.cons_append]
    unfold smallCl
    have hd : ∀ (wT wS wC : WR), (wT :: (List.replicate n wT ++ wS :: wC :: l4)).drop (kk a) =
        wS :: wC :: l4 := by
      intro wT wS wC
      rw [hkk, ← List.cons_append, ← List.replicate_succ]
      exact List.drop_left' (by simp)
    simp only [hd]
    rw [ok_append, ok_tag, Bool.and_eq_true]
    exact ⟨step_small own seen tree W x t1 t3 t4
        (hk b (List.mem_cons_of_mem _ List.mem_cons_self)) (Nat.le_trans hz.1 (by decide)) o1 o2 o4,
      walk_small own work rest b true (j + 1) (tree + 1) (wMid b) t R' sh4 l4 (fun _ => rfl) h' hl4
        hF' (fun s hs => hk s (List.mem_cons_of_mem _ hs)) hO'⟩

theorem stageJ_of_okFrom (w : ℕ) : ∀ (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage),
    OkFrom rad B w a rest → ∀ x ∈ a :: rest, (sgOf x).StageJ (rad (sgOf x))
  | [], a, h, x, hx => by
    obtain rfl := List.mem_singleton.1 hx
    exact LastPlace.stageJ h.1
  | b :: rest, a, h, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact FoldedPlace.stageJ h.1
    · exact stageJ_of_okFrom w rest b h.2.2.2.2 x hx

/-- What the block's test on the plan gives of the made and the written rounds. -/
theorem made_of_planOk {Cl : Type} (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Cl).planOk = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (ls : List (List Op))
      (R : List Fmt.DeclaredRound) (sh : List Fmt.Shape) (w0 : WR) (w : List WR),
      p.nums.stages = a :: rest ∧ rest ≠ [] ∧
      H2U.layOpens p.nums.ownMask false (laterRounds p.nums.work 0 0 a rest) ls = some R ∧
      layW R sh = some w ∧ writtenOf p.nums = some (w0 :: w) ∧ Fit a rest ∧
      ∀ s ∈ a :: rest, s.h ≤ s.k := by
  obtain ⟨rds, hr, hlen⟩ := H2K.Made.rounds_of_planOk guardedProximityTestParts p hp
  have hsz := H2K.Made.sizes_of_planOk guardedProximityTestParts p hp
  obtain ⟨a, rest, w0, w, hs, hw, _⟩ := H2K.Made.written_made p rds hr hlen
    (fun s hs => (hsz s hs).2)
  obtain ⟨s, next, rest', R, hs', hR, rfl⟩ := H2K.Made.rounds_top p.nums rds hr
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hs.symm.trans hs')
  have hw' := hw
  unfold writtenOf at hw'
  rw [hr, Option.bind_some] at hw'
  obtain ⟨t0, l0, sh0, e0, hl0⟩ := layW_inv _ .elems H2K.Made.kBat hw'
  obtain ⟨_, rfl⟩ := List.cons.inj e0
  have hp' := hp
  unfold proximityTestKind at hp'
  split at hp'
  · rename_i first rest'' rs os h1 h2 h3
    obtain rfl := Option.some.inj (h2.symm.trans hr)
    obtain ⟨rfl, rfl⟩ := List.cons.inj (h1.symm.trans hs)
    simp only [Block.andThen, Bool.and_eq_true] at hp'
    have hz := hp'.1.1.1.1
    unfold sizesOk at hz
    simp only [Bool.and_eq_true] at hz
    have h32 : ∀ x ∈ p.nums.stages, x.C.a ≤ 32 := by
      rw [hs]
      refine H2K.Made.small_later p _ _ _ _ false 0 0 0 _ R _ (fun h => by cases h) hR ?_ hp'.2.2
      rw [List.map_drop, List.map_fst_zip (Nat.le_of_eq hlen.symm)]
      rfl
    exact ⟨_, _, _, R, sh0, w0, w, hs, by simp, hR, hl0, hw,
      H2K.Made.fit_of_ok _ _ _ _ (by rw [← hs]; exact hz.2) (by rw [← hs]; exact h32),
      fun x hx => (hsz x (by rw [hs]; exact hx)).2⟩
  · cases hp'

/-- **The tie**: a yes of the test on numbers at the place's own test gives the condition. -/
theorem k12Condition_of_test {Cl : Type} (rad : Sg → ℕ) (B : Sg → Br × Br) (p : P12) (K : Codes)
    (T : TestAt) (hT : testOf rad B p = some T) (hok : T.ok = true)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Cl).planOk = true) (hpub : pubOk p K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p K ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨a, rest, ls, R, sh, w0, w, hs, hne, hR, hl, hw, hF, hk⟩ := made_of_planOk p hp
  have hO := okFrom_of_test rad B p T hT hok a rest hs
  refine condition_of rad B p K hpub (H2K.Made.spendOk_of_planOk p hp)
    (codesAt_joh rad _ (by rw [hs]; exact stageJ_of_okFrom _ rest a hO)) ?_
  unfold smallOk smallAll
  rw [hs, hw]
  exact walk_small _ _ rest a false 0 0 0 ls R sh w (fun h => absurd h hne) hR hl hF hk hO

end H2K.Pub

#print axioms H2K.Pub.k12Condition_of_test
