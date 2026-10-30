-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/StageCaps.lean: every stage of the three proximity tests of the test on the table
is in order for the planner's routines (StageOk); and so is every stage that solveStages or
solveTest returns, if the first stage has at most 131 row variables of either kind and, for
solveStages, its group fits (GroupFit) and every line of the choice is in range (StageCap); for
solveTest, the line is in range (GroupCap) and the shape's two codes have logN at most 32. A proof's
last test and the test of a key's proof of the ranges: OnBytes/Params/Fit/SizedParts.lean.

StageOk (OnBytes/Params/Fit/FitSmall.lean) asks of a stage's group: the main code's logN is at most
64, and the variables of the cube of a sample on its rows are at most 2^32.
OnBytes/Params/Fit/SolveCap.lean says that every solved group has the lengths and the row variables
of the shape that went in, and messages no longer than its codes; the lengths are a line's, at most
2^32. So what is left to bound are the row variables of each test's first stage. For the test on the
table they follow from the numbers of rows (OnBytes/Params/Fit/LinRows.lean). For the two other
tests they are taken as premises here.

Main theorems.
 - stageOk_of_fit: a group that fits, with at most 131 row variables of either kind.
 - stages_ok: the stages that solveStages returns, from the first stage's.
 - lin_stages: the three tests of what linSized returns.
 - solveTest_stages: the stages that solveTest returns.
 - kh_of_stages: ioppStages copies each stage's two numbers of row variables.

What is asked: the ranges of the lines (GroupCap, OnBytes/Params/Fit/LinesCap.lean) and LinNums.
None is shown here. Nothing on soundness. For proofs only; the program does not import this file.

-/
import OnBytes.Params.Fit.FitSmall
import OnBytes.Params.Fit.LinRows
import OnBytes.Params.Fit.SolveCap

set_option autoImplicit false

namespace OnBytes.Params

/-- A group that fits, with few row variables, is in order. -/
theorem stageOk_of_fit {y : StageSize} (hf : GroupFit y.g) (hk : y.g.k ≤ 131)
    (hh : y.g.h ≤ 131) : StageOk y := by
  obtain ⟨⟨n1, l1⟩, _, l2⟩ := hf
  refine ⟨by omega, ?_⟩
  have c1 : clog2 y.g.main.ell ≤ 32 := clog2_pow_le l1
  have c2 : clog2 y.g.mask.ell ≤ 32 := clog2_pow_le l2
  have g : (164 : Nat) ≤ 2 ^ 32 := by norm_num
  unfold stageCubeBits
  dsimp only
  split
  · have : max (y.g.k + clog2 y.g.main.ell) (y.g.h + clog2 y.g.mask.ell) ≤ 163 :=
      Nat.max_le.2 ⟨by omega, by omega⟩
    omega
  · omega

/-- The stages that solveStages returns. -/
theorem stages_ok {s : Setting} {scope : Scope} {first : GroupSize}
    {firstT : Nat} {choice : List StageLine} {st : List StageSize}
    (hc : ∀ c ∈ choice, StageCap c)
    (h : solveStages s scope first firstT choice = some st) (hf : GroupFit first)
    (hk : first.k ≤ 131) (hh : first.h ≤ 131) : ∀ y ∈ st, StageOk y := by
  intro y hy
  rcases solveStages_fit hc h y hy with e | ⟨f, k8, h8⟩
  · exact stageOk_of_fit (e ▸ hf) (e ▸ hk) (e ▸ hh)
  · exact stageOk_of_fit f (by omega) (by omega)

/-- A group that was solved from a line's shape with few row variables. -/
theorem fit_withBits {line : GroupLine} {b : Nat × Nat} {g : GroupSize} (C : GroupCap line)
    (S : Solves (withBits line b) g) (h1 : b.1 ≤ 131) (h2 : b.2 ≤ 131) :
    GroupFit g ∧ g.k ≤ 131 ∧ g.h ≤ 131 := by
  have hN : (withBits line b).main.logN ≤ 32 := C.logN
  have hZ : (withBits line b).mask.logN ≤ 32 := Nat.le_trans C.mask C.logN
  refine ⟨fit_of_solves S hN hZ, ?_, ?_⟩
  · rw [S.k]
    exact h1
  · rw [S.h]
    exact h2

/-- **The three tests of what linSized returns.** -/
theorem lin_stages {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes} {x : LinSized}
    (h : linSized s L T codes = some (x, c)) (N : LinNums s L T) (CF : GroupCap L.folded)
    (CO : GroupCap L.omega) (CW : GroupCap L.own) :
    (∀ t ∈ x.own.stages, StageOk t) ∧ (∀ t ∈ x.folded.stages, StageOk t) ∧
      ∀ t ∈ x.omega.stages, StageOk t := by
  obtain ⟨G, X, Y, Z, a, b, stU, stO, stW, gF, gO, gW, hT, hU, hO, hW, eF, eO, eW, hv, _⟩ :=
    linSized_parts h
  obtain ⟨sX, sY, sZ⟩ := linTurns_solves 33 {} {} {} (X, Y, Z) hT
  have rU := rows_linU N
  have rO := rows_linOmega N
  have rW := rows_linW N hv
  have rS : FewRows (linSplitMsg s) := rows_linSplitMsg
  have rI := rows_linInput N
  have bF : (linGroupBits (if linSplit L then [linU s L T, linSplitMsg s]
      else [linU s L T, linOmega s L])).1 ≤ 131 ∧
      (linGroupBits (if linSplit L then [linU s L T, linSplitMsg s]
        else [linU s L T, linOmega s L])).2 ≤ 131 := by
    split
    · exact linGroupBits_le (show 2 ≤ 3 by omega) (by
        intro m hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · exact rU
        · exact rS)
    · exact linGroupBits_le (show 2 ≤ 3 by omega) (by
        intro m hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · exact rU
        · exact rO)
  have bO := linGroupBits_le (ms := [linOmega s L, linSplitMsg s]) (show 2 ≤ 3 by omega) (by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact rO
    · exact rS)
  have bW := linGroupBits_le (ms := [linInput s L, linW s L T, linOmega s L])
    (show 3 ≤ 3 by omega) (by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact rI
    · exact rW
    · exact rO)
  rw [gF] at sX
  rw [gW] at sZ
  obtain ⟨fX, kX, hX⟩ := fit_withBits CF sX bF.1 bF.2
  obtain ⟨fZ, kZ, hZ⟩ := fit_withBits CW sZ bW.1 bW.2
  rw [eF, eO, eW]
  refine ⟨stages_ok CW.stages hW fZ kZ hZ, stages_ok CF.stages hU fX kX hX, ?_⟩
  rcases hO with ⟨hs, hO⟩ | rfl
  · have sY' := sY hs
    rw [gO] at sY'
    obtain ⟨fY, kY, hY⟩ := fit_withBits CO sY' bO.1 bO.2
    exact stages_ok CO.stages hO fY kY hY
  · intro t ht
    cases ht

/-- The stages that solveTest returns, from the shape's lengths and row variables. -/
theorem solveTest_stages {s : Setting} {scope : Scope} {line : GroupLine} {load : GroupLoad}
    {draws : Nat → Nat} {shape : GroupSize} {t : TestSizes} (C : GroupCap line)
    (h : solveTest s scope line load draws shape = some t) (hN : shape.main.logN ≤ 32)
    (hZ : shape.mask.logN ≤ 32) (hk : shape.k ≤ 131) (hh : shape.h ≤ 131) :
    ∀ y ∈ t.stages, StageOk y := by
  unfold solveTest at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨st, hst, h⟩ := opt_bind h
  cases h
  have S := solveGroup_solves hx
  exact stages_ok C.stages hst (fit_of_solves S hN hZ) (by rw [S.k]; exact hk)
    (by rw [S.h]; exact hh)

/-- ioppStages copies the two numbers of row variables of each stage. -/
theorem kh_of_stages : ∀ (st : List StageSize) (codes : Codes),
    (ioppStages st codes).1.map (fun t => (t.k, t.h)) = st.map fun y => (y.g.k, y.g.h)
  | [], _ => rfl
  | y :: rest, codes => by
    unfold ioppStages
    simp only [List.map_cons]
    rw [kh_of_stages rest]

end OnBytes.Params
