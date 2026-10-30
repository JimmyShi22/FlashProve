-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyFallGood.lean: theorems about the toy example of
Honest/Law/ToyFall.lean: `Good` (Honest/Side.lean) at its eight sides; the eight as the field `good`
of `Owed` (Honest/Owed.lean) at one value of `Sides`, which holds two falls: one at a sub-protocol
with a round and a part, whose side has it, and one at a sub-protocol without a round. Each rejects
where the verifier's state, which depends on a coin of the run's, is so. The theorems are about
these files' own made-up objects alone. None is one of the library's goals.

  1  `fallT`, `fallWf`, `vSideWf`, `vRow…`, `Gv`   the falls; the lists as one `Sides`; `#guard`
     lines over `runC`: which parts are called, and that "called" decides something at these coins:
     the echo's condition at its entry is false there after a rejection, where the echo is not
     called (the condition, not at all coins: where the echo's word of the carried blocks is 0 it
     holds at the substitute too)
  2  `vWf_plays`, `vWf_acc`   the two fields at the side with a fall of its own: the hypothesis of
     `acc` on the fall is used (without it `acc` is false: said here without a theorem)
  3  `good_vA` … `good_vE`, `vside_…`, `good_rowV`, `tests_yes`, `tests_no`, `tests_step_yes`,
     `tests_step_no`   `Good` at the eight sides; the lists; the fall without a side

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

`pre` is a bound letter: each `Good` holds at every `pre`: no part here reads the opened columns,
and `exact` is proved without its hypothesis on the field `opened`. `good_rowV` has the field beside
each A and B by `Lettered.goodAt_withField` (Honest/FieldFree.lean).

Limits.
  * A toy example.
  * The second fall is at a sub-protocol without a side: no field of `Good` reads it; what is proved
    of it is that its test is that sub-protocol's own decision and step, both ways.
  * The stated shares are the greater of the two exact counts over the field, and are compared with
    nothing.
  * That a part after a rejection is never called, and that the echo's condition fails there, is
    evaluated at three lists, not proved.
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `vWf_plays`, `vWf_acc`.
  * No part of the example reads what it is handed as `Seen`, so none reads the field `opened`: what
    the hypotheses here ask of that field is met for free. Of a prover with a part that reads the
    columns nothing is shown here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyFallWhole
import Johnson.Desc.ProofFile.Honest.Law.ToyGood
import Johnson.Desc.ProofFile.Honest.Owed
import Johnson.Desc.ProofFile.Honest.Shares

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Place Block FileDescription OpenedColumn itemOf roundsFit drawsMarkedNonzeroHaveNonzeroWords need)
open VerifiableInference.Desc.BlockToy (St tree₃ drawD orc)
open OnBytes.Slice (toF toE ofF ofE)
open Prob

/-! ## 1 The falls, the lists -/

/-- **The fall**, at the sub-protocol that rejects: the own test of "tests", on the state before it.
Its share: at each fixed input and coin the drawn element's first word has p values, p the field's
prime, which is 1 modulo 5: (p - 1) / 5 of them fall, or one more: the greater count is stated. -/
def fallT : Fall St :=
  { place := vbT.place
    test := fallQ
    share := ⟨3689348813882916865, 18446744069414584321⟩ }

/-- **A fall at a sub-protocol with a round and a part**: the own test of "weigh" on the weight, on
the state before it (`fallW`, Honest/Law/ToyFall.lean). Its share: as that of `fallT`: the drawn
first words that are 1 minus the total modulo 5. -/
def fallWf : Fall St :=
  { place := vpW, test := fallW, share := ⟨3689348813882916865, 18446744069414584321⟩ }

/-- The side of "weigh", with its fall: as `Lettered.side` builds it: the falls of the chain's list
that are at its place, as one. -/
def vSideWf : Side St Nat L L Nat Nat := { vSideW with fall := fallOf [fallWf, fallT] vpW }

/-- That is the own test of "weigh" on the weight. -/
theorem fall_W (s : St) (ds : List Fmt.Drawn) : vSideWf.fall s ds = fallW s ds := by
  have h : ([fallWf, fallT].filter fun f => f.place == vpW) = [fallWf] := by
    with_unfolding_all rfl
  have e : fallWf.test s ds = fallW s ds := rfl
  show (([fallWf, fallT].filter fun f => f.place == vpW).findSome? fun f => f.test s ds) =
    fallW s ds
  rw [h]
  simp only [List.findSome?, e]
  cases fallW s ds <;> rfl

def vRowA : Lettered Bv St Nat L L Nat Nat := ⟨vpA, vSideA.row, noTree, vAt, onAny, budAny⟩
def vRowB : Lettered Bv St Nat L L Nat Nat := ⟨vpB, vSideB.row, vAt, vAt, onAny, budAny⟩
def vRowS : Lettered Bv St Nat L L Nat Nat := ⟨vpS, vSideS.row, vAt, vSent, onAny, budOne⟩
def vRowD : Lettered Bv St Nat L L Nat Nat := ⟨vpD, vSideD.row, vSent, vSent, onAny, budAny⟩
def vRowM : Lettered Bv St Nat L L Nat Nat := ⟨vpM, vSideM.row, vSent, vSent, onAny, budAny⟩
def vRowW : Lettered Bv St Nat L L Nat Nat := ⟨vpW, vSideW.row, vSent, vSent, onAny, budAny⟩
def vRowL : Lettered Bv St Nat L L Nat Nat := ⟨vpL, vSideL.row, anyAt, vLate, onAny, budAny⟩

def vRowE : Lettered Bv St Nat L L Nat Nat := ⟨vpE, vSideE.row, vLate, anyAt, onEcho, budAny⟩

/-- The eight lists and the two falls, as one value of `Sides`. -/
def Gv : Sides Fv Bv Wit₀ UInt64 UInt64 Trace Nat Nat :=
  { first := [], shared := [], second := [vRowA, vRowB, vRowS, vRowD, vRowM, vRowW, vRowL, vRowE]
    falls₃ := [fallWf, fallT] }

#guard Gv.seated
-- the tests of Honest/Fall.lean on the falls: each is at a sub-protocol's place; no share has the
-- denominator 0
#guard Gv.fallsSeated && Gv.sharesOk Pv
-- `fallAt` (Honest/Fall.lean), over `runC`, at the states that the run itself computes:
-- 12 + 1: none; 12 + 3: at "tests"; 12 + 4: at "weigh"
#guard fallAt Gv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 1 6) == none
#guard fallAt Gv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 3 6) == some (vbT.place, "a weight is 0")
#guard fallAt Gv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 4 6) == some (vpW, "a weight is 1")
-- a run of Gv is rejected exactly where a named fall fires: five coins, five challenges
#guard five.all fun t => five.all fun χ =>
  ((runC Fv Bv (Gv.prover Pv) w₀ 7 5 (coinsV t 2 3 4 5 8 6) (ρv 0 χ 6)).toOption.map fun r =>
    r.ends.2.2.isNone) == some (fallAt Gv Pv w₀ 7 5 (coinsV t 2 3 4 5 8 6) (ρv 0 χ 6)).isSome
#guard (18446744069414584321 - 1) / 5 + 1 == 3689348813882916865 && 18446744069414584321 % 5 == 1
#guard sameOutcome (outcome Fv Bv (Gv.prover P₀) w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 1 6))
  (outcome Fv Bv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 1 6))

-- over the player that asks the description's own step (`runC`, Honest/Walk.lean): which parts are
-- called. 12 + 1: nobody rejects: all are. 12 + 3: "tests" rejects: "mid" and "weigh" are called,
-- "late" is never called. 12 + 4: "weigh" rejects: its own part is called, "late" is not
#guard ((runC Fv Bv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 1 6)).toOption.map fun r =>
  (r.called vaM, r.called vaW, r.called vaL, r.refused.2.2)) == some (true, true, true, none)
#guard ((runC Fv Bv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 3 6)).toOption.map fun r =>
  (r.called vaM, r.called vaW, r.called vaL, r.refused.2.2)) ==
    some (true, true, false, some vbT.place)
#guard ((runC Fv Bv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 4 6)).toOption.map fun r =>
  (r.called vaM, r.called vaW, r.called vaL, r.refused.2.2)) == some (true, true, false, some vpW)
-- **"called" decides something here.** The echo's condition at its entry, as a test, at the run's
-- own values (the carried coins are t = 1 and r' = 6; a(1) = 0): where nobody rejects the echo is
-- called and the condition holds; after a rejection the last round of `front` is the fixed
-- substitute (0, 0, 0): at these coins the condition is false, and the echo is not called: the
-- clause "at called parts alone" is what saves `Owed.owed` there: with called := fun _ => true it
-- would be false at this run (by the text of `Owed.owed`, Honest/Owed.lean; no line evaluates that;
-- there `Owed.owed` has besides no state: `midAtW` returns `none` after a rejection and `orRefused`
-- an error, at all coins: read off Honest/MidW.lean)
#guard ((runC Fv Bv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 1 6)).toOption.map fun r =>
  (r.called vaE, onEchoB (toF 0 + toF 6 + toF 1) (r.run.beforeAt [] vaE))) == some (true, true)
#guard ((runC Fv Bv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 3 6)).toOption.map fun r =>
  (r.called vaE, onEchoB (toF 0 + toF 6 + toF 1) (r.run.beforeAt [] vaE),
    onEchoB (toF 0) (r.run.beforeAt [] vaE))) == some (false, false, true)
#guard ((runC Fv Bv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 4 6)).toOption.map fun r =>
  (r.called vaE, onEchoB (toF 0 + toF 6 + toF 1) (r.run.beforeAt [] vaE))) == some (false, false)
-- after the rejection the round is produced all the same, as the fixed substitute
#guard ((runC Fv Bv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 3 6)).toOption.map fun r =>
  r.run.shownAt vaL) == some [⟨[.e (0, 0, 0)], []⟩]

/-! ## 2 The side with a fall of its own: the two fields -/

/-- **`plays` at the side of "weigh", at all coins, fall or not.** The field of `Good`, letter for
letter. -/
theorem vWf_plays : ∀ k s m E ds, vSent k s m E → drawsFit vSideWf.block.rounds ds = true →
    vSideWf.stopAt .own m.st.input m.loc ds = none →
    ∃ (c : RowCoins vSideWf.half.parts) (y : List Played × Mid L Nat) (cols : List OpenedColumn),
      lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideWf.block.place vSideWf.half.parts 0 = .ok c ∧
      play (vSideWf.half.steps vSideWf.block (Face.own.sees m.st.input) c) ds [] m = .ok y ∧
      fillCols (readsOf 2 Fv.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree vSideWf.block.rounds
        ds) [] = .ok cols ∧
      ∀ s' n, vSideWf.block.step Fv.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s', n) →
        vSent k s' (y.2.took cols) (E.add y.1) := vW_plays

/-- **`acc` at the side of "weigh": the hypothesis "the place's fall returns `none`" is used**:
there the weight is not 1, and the sub-protocol's own step accepts. The field of `Good`, letter for
letter. -/
theorem vWf_acc : ∀ k s m E ds, vSent k s m E → drawsFit vSideWf.block.rounds ds = true →
    vSideWf.stopAt .own m.st.input m.loc ds = none → vSideWf.fall s ds = none →
    ∀ (c : RowCoins vSideWf.half.parts) (y : List Played × Mid L Nat) (cols : List OpenedColumn),
      lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideWf.block.place vSideWf.half.parts 0 = .ok c →
      play (vSideWf.half.steps vSideWf.block (Face.own.sees m.st.input) c) ds [] m = .ok y →
      fillCols (readsOf 2 Fv.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree vSideWf.block.rounds
        ds) [] = .ok cols →
      ∃ s' n, vSideWf.block.step Fv.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s', n) := by
  intro k s m E ds _ hd _ hf
  have hw : weighOk s = true := by
    cases h : weighOk s with
    | true => rfl
    | false =>
      have hf' : (if weighOk s = true then none else some "a weight is 1") = none :=
        (fall_W s ds).symm.trans hf
      rw [if_neg (by rw [h]; exact Bool.false_ne_true)] at hf'
      cases hf'
  exact vW_yes k s m E ds hd hw

/-! ## 3 `Good` at the eight sides; the lists; the fall without a side -/

/-- **`Good` at the first owner's side.** About this folder's own made-up objects alone; none of the
library's goals. So the others below. -/
theorem good_vA {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own vSideA Bv (orderOf Fv) 2 Fv.lastChainFirstTreeNumber noTree vAt onAny budAny :=
  ⟨rfl, plays_of_whole vA_whole, acc_of_whole vA_whole,
    fun u hu ca m front ds asks hO hs _ => vA_exact u hu ca m front ds asks hO hs, vA_fresh⟩
theorem good_vB {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own vSideB Bv (orderOf Fv) 2 Fv.lastChainFirstTreeNumber vAt vAt onAny budAny :=
  ⟨rfl, plays_of_whole vB_whole, acc_of_whole vB_whole,
    fun u hu ca m front ds asks hO hs _ => vB_exact u hu ca m front ds asks hO hs, vB_fresh⟩
theorem good_vS {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own vSideS Bv (orderOf Fv) 2 Fv.lastChainFirstTreeNumber vAt vSent onAny budOne :=
  ⟨rfl, plays_of_whole vS_whole, acc_of_whole vS_whole,
    fun u hu ca m front ds asks hO hs _ => vS_exact u hu ca m front ds asks hO hs, vS_fresh⟩
theorem good_vD {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own vSideD Bv (orderOf Fv) 2 Fv.lastChainFirstTreeNumber vSent vSent onAny budAny :=
  ⟨rfl, plays_of_whole vD_whole, acc_of_whole vD_whole,
    fun u hu ca m front ds asks hO hs _ => vD_exact u hu ca m front ds asks hO hs, vD_fresh⟩
theorem good_vM {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own vSideM Bv (orderOf Fv) 2 Fv.lastChainFirstTreeNumber vSent vSent onAny budAny :=
  ⟨rfl, plays_of_whole vM_whole, acc_of_whole vM_whole,
    fun u hu ca m front ds asks hO hs _ => vM_exact u hu ca m front ds asks hO hs, vM_fresh⟩
/-- **`Good` at the side with a fall of its own.** -/
theorem good_vW {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own vSideWf Bv (orderOf Fv) 2 Fv.lastChainFirstTreeNumber vSent vSent onAny budAny :=
  ⟨rfl, vWf_plays, vWf_acc,
    fun u hu ca m front ds asks hO hs _ => vW_exact u hu ca m front ds asks hO hs, vW_fresh⟩
theorem good_vL {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own vSideL Bv (orderOf Fv) 2 Fv.lastChainFirstTreeNumber anyAt vLate onAny budAny :=
  ⟨rfl, plays_of_whole vL_whole, acc_of_whole vL_whole,
    fun u hu ca m front ds asks hO hs _ => vL_exact u hu ca m front ds asks hO hs, vL_fresh⟩

theorem good_vE {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own vSideE Bv (orderOf Fv) 2 Fv.lastChainFirstTreeNumber vLate anyAt onEcho budAny :=
  ⟨rfl, plays_of_whole vE_whole, acc_of_whole vE_whole,
    fun u hu ca m front ds asks hO hs _ => vE_exact u hu ca m front ds asks hO hs, vE_fresh⟩

theorem vside_A : vRowA.side Fv.second.blocksInOrder Gv.falls₃ = some vSideA := rfl
theorem vside_B : vRowB.side Fv.second.blocksInOrder Gv.falls₃ = some vSideB := rfl
theorem vside_S : vRowS.side Fv.second.blocksInOrder Gv.falls₃ = some vSideS := rfl
theorem vside_D : vRowD.side Fv.second.blocksInOrder Gv.falls₃ = some vSideD := rfl
theorem vside_M : vRowM.side Fv.second.blocksInOrder Gv.falls₃ = some vSideM := rfl
theorem vside_W : vRowW.side Fv.second.blocksInOrder Gv.falls₃ = some vSideWf := rfl
theorem vside_L : vRowL.side Fv.second.blocksInOrder Gv.falls₃ = some vSideL := rfl
theorem vside_E : vRowE.side Fv.second.blocksInOrder Gv.falls₃ = some vSideE := rfl

/-- **The field `good` of `Owed` (Honest/Owed.lean) at the lists `Gv`**, letter for letter. About
this folder's own made-up objects alone; none of the library's goals. -/
theorem good_rowV :
    (∀ r ∈ Gv.first, (r.withField 0 0 Fv.first.blocksInOrder [] 0).goodAt (earlierOf Fv 0) .own
        Fv.first.blocksInOrder (orderOf Fv) 0 0 Gv.falls₁) ∧
    (∀ r ∈ Gv.shared, (r.withField 1 0 Fv.shared.blocksInOrder [] 0).goodAt (earlierOf Fv 1) .shared
        Fv.shared.blocksInOrder (orderOf Fv) 1 0 Gv.falls₂) ∧
    ∀ r ∈ Gv.second, ∀ base skip,
      (r.withField 2 Fv.lastChainFirstTreeNumber Fv.second.blocksInOrder base skip).goodAt (earlierOf Fv 2) .own
        Fv.second.blocksInOrder (orderOf Fv) 2 Fv.lastChainFirstTreeNumber Gv.falls₃ := by
  refine ⟨fun r hL => absurd hL List.not_mem_nil, fun r hL => absurd hL List.not_mem_nil,
    fun r hL base skip => ?_⟩
  rcases List.mem_cons.1 hL with rfl | hL
  · refine Lettered.goodAt_withField fun σ hσ => ?_
    obtain rfl := Option.some.inj (vside_A.symm.trans hσ)
    exact good_vA
  rcases List.mem_cons.1 hL with rfl | hL
  · refine Lettered.goodAt_withField fun σ hσ => ?_
    obtain rfl := Option.some.inj (vside_B.symm.trans hσ)
    exact good_vB
  rcases List.mem_cons.1 hL with rfl | hL
  · refine Lettered.goodAt_withField fun σ hσ => ?_
    obtain rfl := Option.some.inj (vside_S.symm.trans hσ)
    exact good_vS
  rcases List.mem_cons.1 hL with rfl | hL
  · refine Lettered.goodAt_withField fun σ hσ => ?_
    obtain rfl := Option.some.inj (vside_D.symm.trans hσ)
    exact good_vD
  rcases List.mem_cons.1 hL with rfl | hL
  · refine Lettered.goodAt_withField fun σ hσ => ?_
    obtain rfl := Option.some.inj (vside_M.symm.trans hσ)
    exact good_vM
  rcases List.mem_cons.1 hL with rfl | hL
  · refine Lettered.goodAt_withField fun σ hσ => ?_
    obtain rfl := Option.some.inj (vside_W.symm.trans hσ)
    exact good_vW
  rcases List.mem_cons.1 hL with rfl | hL
  · refine Lettered.goodAt_withField fun σ hσ => ?_
    obtain rfl := Option.some.inj (vside_L.symm.trans hσ)
    exact good_vL
  · obtain rfl := List.mem_singleton.1 hL
    refine Lettered.goodAt_withField fun σ hσ => ?_
    obtain rfl := Option.some.inj (vside_E.symm.trans hσ)
    exact good_vE

/-- The fall's test is the sub-protocol's own decision: where it returns `none`, "tests" accepts. -/
theorem tests_yes (s : St) (ds : List Fmt.Drawn) (h : fallT.test s ds = none) :
    vbT.decide s [] [] = .ok s := by
  cases hw : weightOk s with
  | true =>
    show (if weightOk s = true then Except.ok s else _) = _
    rw [if_pos hw]
  | false =>
    have h' : (if weightOk s = true then none else some "a weight is 0") = none := h
    rw [if_neg (by rw [hw]; exact Bool.false_ne_true)] at h'
    cases h'

/-- And where it returns something, "tests" rejects. -/
theorem tests_no (s : St) (ds : List Fmt.Drawn) (h : fallT.test s ds ≠ none) :
    vbT.decide s [] [] = .error "a weight is 0" := by
  cases hw : weightOk s with
  | false =>
    show (if weightOk s = true then _ else Except.error "a weight is 0") = _
    rw [if_neg (by rw [hw]; exact Bool.false_ne_true)]
  | true =>
    refine absurd ?_ h
    show (if weightOk s = true then none else some "a weight is 0") = none
    rw [if_pos hw]

/-- The same of the sub-protocol's step, which is what `runC` asks: where the fall returns `none` it
accepts and leaves the state. -/
theorem tests_step_yes (s : St) (ds : List Fmt.Drawn) (h : fallT.test s ds = none) :
    vbT.step Fv.lastChainFirstTreeNumber s [] [] = .ok (s, 0) :=
  VerifiableInference.Desc.Block.step_ok.2
    ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, tests_yes s ds h,
      by with_unfolding_all rfl⟩

/-- And where the fall returns something the step rejects. -/
theorem tests_step_no (s : St) (ds : List Fmt.Drawn) (h : fallT.test s ds ≠ none) :
    ¬ ∃ s' n, vbT.step Fv.lastChainFirstTreeNumber s [] [] = .ok (s', n) := by
  rintro ⟨s', n, hst⟩
  have hd : vbT.decide s [] [] = .ok s' := (VerifiableInference.Desc.Block.step_ok.1 hst).2.2.1
  rw [tests_no s ds h] at hd
  cases hd

end ProofFile.Honest.Toy

#print axioms ProofFile.Honest.Toy.fall_W
#print axioms ProofFile.Honest.Toy.vWf_plays
#print axioms ProofFile.Honest.Toy.vWf_acc
#print axioms ProofFile.Honest.Toy.good_vA
#print axioms ProofFile.Honest.Toy.good_vB
#print axioms ProofFile.Honest.Toy.good_vS
#print axioms ProofFile.Honest.Toy.good_vD
#print axioms ProofFile.Honest.Toy.good_vM
#print axioms ProofFile.Honest.Toy.good_vW
#print axioms ProofFile.Honest.Toy.good_vL
#print axioms ProofFile.Honest.Toy.good_vE
#print axioms ProofFile.Honest.Toy.vside_A
#print axioms ProofFile.Honest.Toy.vside_B
#print axioms ProofFile.Honest.Toy.vside_S
#print axioms ProofFile.Honest.Toy.vside_D
#print axioms ProofFile.Honest.Toy.vside_M
#print axioms ProofFile.Honest.Toy.vside_W
#print axioms ProofFile.Honest.Toy.vside_L
#print axioms ProofFile.Honest.Toy.vside_E
#print axioms ProofFile.Honest.Toy.good_rowV
#print axioms ProofFile.Honest.Toy.tests_yes
#print axioms ProofFile.Honest.Toy.tests_no
#print axioms ProofFile.Honest.Toy.tests_step_yes
#print axioms ProofFile.Honest.Toy.tests_step_no
#print axioms ProofFile.Honest.Toy.fallT
#print axioms ProofFile.Honest.Toy.fallWf
#print axioms ProofFile.Honest.Toy.vSideWf
#print axioms ProofFile.Honest.Toy.vRowA
#print axioms ProofFile.Honest.Toy.vRowB
#print axioms ProofFile.Honest.Toy.vRowS
#print axioms ProofFile.Honest.Toy.vRowD
#print axioms ProofFile.Honest.Toy.vRowM
#print axioms ProofFile.Honest.Toy.vRowW
#print axioms ProofFile.Honest.Toy.vRowL
#print axioms ProofFile.Honest.Toy.vRowE
#print axioms ProofFile.Honest.Toy.Gv
