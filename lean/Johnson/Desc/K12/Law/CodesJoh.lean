-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CodesJoh.lean: the field `codes` of `K12Condition`
(Johnson/Desc/K12/Law/ChainHolds.lean: `CodesAt`) at the library's Johnson letters, from a yes of
`johOk` (Johnson/Desc/K12/Law/JohOk.lean). Statements and proofs.

So `K12Condition` at these letters wants, beside three Booleans, its field `small` alone. It is of
the chain of a proximity test (the kind K12), not of the block.
Main names:
  `stagesJ_of_walk`: the clauses of `johOk` give `Sg.StageJ` at every stage of the place, at the
    radius r.
  `codesAt_joh`: `Sg.StageJ` at every stage gives `CodesAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad` of the
    stages: term for term as the library's `Chain.okAt_joh` pays `Chain.OkAt` (`baseCodes_joh`,
    `foldNums_joh`, `Sg.listJ_of`, `Sg.StageJ.counts`), with the theorem on codes laid in
    (`Cb.Gl.bchks46At`, Cb/Bridge/GlCodesProved.lean).
  `codes_of_johOk`: `johOk p r = true` gives `CodesAt` at the radii `fun s => r s.st` and the
    place's stages.
  `k12Condition_joh`: `pubOk p K`, `spendOk p`, `johOk p r` and the field `small` give
    `K12Condition` at these letters and radii.
Limits: `small` is a premise: the facts on codes are paid here, the sizes of the counts are not. r
is a letter: which radius a plan means at a stage is not said. The theorem on codes rests on the
files under ThirdParty/, adapted from ArkLib and Mathlib (lean/LIMITS.md, L15). No soundness is
claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.ChainJoh
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open scoped ENNReal

theorem stagesJ_of_walk (r : Fmt.M1.Stage → ℕ) : ∀ (l : List Fmt.M1.Stage) (j : ℕ),
    ok (johWalk r j l) = true →
    ∀ x ∈ l, (sgOf x).StageJ (r (sgOf x).st)
  | [], _, _, _, hx => by cases hx
  | a :: rest, j, h, x, hx => by
    unfold johWalk at h
    rw [ok_append, ok_tag, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact stageJ_of_L h.1
    · exact stagesJ_of_walk r rest (j + 1) h.2 x hx'

/-- `Sg.StageJ` at every stage pays `CodesAt` at the Johnson letters. -/
theorem codesAt_joh (rad : Sg → ℕ) : ∀ l : List Fmt.M1.Stage,
    (∀ x ∈ l, (sgOf x).StageJ (rad (sgOf x))) →
    CodesAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad l
  | [], _ => trivial
  | [a], h => by
    have hS := h a (List.mem_singleton.2 rfl)
    exact baseCodes_joh hS.sized hS.joh (hS.counts Cb.Gl.bchks46At)
  | a :: b :: rest, h => by
    have hS := h a List.mem_cons_self
    have hN := h b (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ⟨hS.joh.1, foldNums_joh hS.sized hS.joh (hS.counts Cb.Gl.bchks46At),
      Sg.listJ_of (Sg.fit_cIn hN.sized) hN.joh,
      codesAt_joh rad (b :: rest) fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

/-- A yes of `johOk` pays `CodesAt` at the place's stages. -/
theorem codes_of_johOk (r : Fmt.M1.Stage → ℕ) (p : P12) (hj : johOk p r = true) :
    CodesAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) p.nums.stages :=
  codesAt_joh _ _ (stagesJ_of_walk r p.nums.stages 0 hj)

/-- The condition at the Johnson letters wants, beside three Booleans, `small` alone. -/
theorem k12Condition_joh (r : Fmt.M1.Stage → ℕ) (p : P12) (K : Codes) (εs : ℝ≥0∞)
    (hp : pubOk p K = true)
    (hs : spendOk p = true) (hj : johOk p r = true)
    (hsmall :
        ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR)
        (c : Chain (sgOf a)),
      p.nums.stages = a :: rest → writtenOf p.nums = some (w0 :: l) →
      chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l = some c →
      Err.Below c.err εs) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) p K εs :=
  ⟨hp, hs, codes_of_johOk r p hj, hsmall⟩

end H2K.Pub

#print axioms H2K.Pub.codes_of_johOk
#print axioms H2K.Pub.k12Condition_joh
