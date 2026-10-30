-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/All.lean: the honest side of the kind "lookup" (K3). The
two fillings of a lookup's summands yield the same lists at every stage of the row. Conditional on
the four hypotheses below. One theorem, the definition of one hypothesis, two small lemmas.

Terms. Honest/K3/GLOSSARY.md. In this file: the row of a lookup takes its summands as a letter
(`LookJobs`, Honest/K3/Stages.lean). One filling reads them off the specification, in the library's
field (`specJobsAt`, Honest/K3/JobsSpec.lean): of it the specification's statements speak. The other
folds tables of the program's elements (`fastJobs`, Honest/K3/JobsFast.lean): it can be run.

What is shown.
  `stages_agree`: at every stage of the row that is a masked sumcheck the three functions of the two
    fillings give the same lists of the program's elements, word for word: the round polynomial
    behind fewer challenges than the stage has variables; the polynomial in Y and the end values
    behind as many challenges as it has variables.
  `PtsSized`: the hypothesis on the points' sizes.
  `tie_mem`, `split_mem`: the number of a tie's or a split's stage of the row is in range. The same
    two statements stand, with the same proofs, as `tie_lt` and `split_lt` in
    Honest/K3/Law/Steps.lean.

Hypotheses that remain.
  `H`: `Sized f v p` (Honest/K3/FastLaw/Tie.lean): one part of 2 ^ v keys, v at least 1; from 2 to
    2 ^ mu planes; the shift's words are below the prime.
  `A`: `FactorFits f row pads p` (Tie.lean): the face's public factor, read in the field, is the
    library's `padFac` at the table's rows and the padding by rows.
  `Z`: `PtsSized f v p`: each point has as many coordinates as its stage has variables.
  `hO`: the face's order at each level of the key tree lists that level's variables, each once.
  `hs`: (in `tie_mem`, `split_mem`) the stage is one of the row's.

How the proof goes. It puts together Honest/K3/FastLaw/Tie.lean (the tie), InY.lean (the end values
and the polynomial in Y at the levels and the bits) and Rounds.lean (the round polynomials).

Users. `real_agree` (Honest/K3/FastLaw/Real.lean).

Limits. Whether the hypotheses hold at the face of a proof file's lookup is not shown in this file.
`FactorFits` there is shown in `factor_real` (Real.lean), conditional on the library's test on the
shape. The specification's filling is the one at numbers made of the face (`numsOf`), not the one at
a proof file's own numbers (`specJobsF`); Real.lean leads from the first to the second. Nothing is
said at other lengths of the lists of challenges. No statement of this file says that either filling
is right.
An instance, with all hypotheses met together: Honest/K3/FastLaw/AllToy.lean [not in this library]
(by evaluation). The equations by evaluation, at one small synthetic lookup:
Honest/K3/JobsFastIsSpec.lean [not in this library].
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.InY
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Rounds
import Johnson.Desc.ProofFile.Honest.K3.HeardLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open OnBytes (E)

/-- **The hypothesis on the points' sizes**: each point has as many coordinates as its stage has
variables. -/
structure PtsSized (f : LFace) (v : Nat) (p : Pts) : Prop where
  key : ∀ m < v, (p.keyPt 0 m).size = m
  tab : ∀ l ≤ f.d, (p.tabPt l).size = f.mu + l
  zero : p.zeroPt.size = f.mu + f.d

theorem tie_mem {f : LFace} {j : Nat} (hs : Stage.tie j ∈ stages f) : j < f.planes - 1 := by
  unfold stages at hs
  by_cases hc : f.shifted = true <;> simp [hc] at hs <;> exact hs

theorem split_mem {f : LFace} {i : Nat} (hs : Stage.split i ∈ stages f) :
    i < f.parts.length - 1 := by
  unfold stages at hs
  by_cases hc : f.shifted = true <;> simp [hc] at hs <;> exact hs

/-- **Conditional on `Sized f v p`, `FactorFits f row pads p`, `PtsSized f v p` and the key orders
being permutations: at every stage of the row that is a masked sumcheck the two fillings yield the
same lists.** An instance, with all hypotheses met together: Honest/K3/FastLaw/AllToy.lean
[not in this library] (by evaluation); the equations by evaluation: Honest/K3/JobsFastIsSpec.lean
[not in this library]. -/
theorem stages_agree (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden)
    (p : Pts) {v : Nat} (H : Sized f v p) (A : FactorFits f row pads p) (Z : PtsSized f v p)
    (hO : ∀ m < v, (f.orders 0 m).Perm (List.range m)) :
    ∀ s ∈ stages f, ∀ k, s.call f = some k →
      (∀ rs : List E, rs.length < k.vs.length →
        ((fastJobs f row).job s).round w p rs = ((specJobsAt f row pads).job s).round w p rs) ∧
      (∀ rs mk : List E, rs.length = k.vs.length →
        ((fastJobs f row).job s).inY w p rs mk = ((specJobsAt f row pads).job s).inY w p rs mk ∧
          ((fastJobs f row).job s).ends w p rs = ((specJobsAt f row pads).job s).ends w p rs) := by
  intro s hs k hk
  cases s with
  | shift => exact absurd hk (by simp [Stage.call])
  | alpha => exact absurd hk (by simp [Stage.call])
  | join => exact absurd hk (by simp [Stage.call])
  | keyLine i m => exact absurd hk (by simp [Stage.call])
  | tabLine l => exact absurd hk (by simp [Stage.call])
  | zero => exact absurd hk (by simp [Stage.call])
  | tie j =>
    have hj : j + 2 ≤ f.planes := by
      have := tie_mem hs
      omega
    exact ⟨fun rs _ => tie_round f row pads w p j rs, fun rs mk _ =>
      ⟨tie_inY f row pads w p H A hj rs mk, tie_ends f row pads w p H hj rs⟩⟩
  | split i =>
    have := split_mem hs
    rw [H.parts] at this
    exact absurd this (by simp)
  | key i m =>
    obtain ⟨x, hx, hi, hm⟩ := mem_key hs
    rw [H.parts] at hx
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    obtain rfl : i = 0 := hi
    have hm' : m < v := hm
    have hk' : k.vs.length = m := by
      have e : k = levelCall m := (Option.some.inj hk).symm
      rw [e]
      simp [levelCall, VerifiableInference.Desc.First.ProdV.levelVars]
    rw [hk']
    exact ⟨fun rs hl => key_round f row pads w p H hm' rs (hO m hm') (Z.key m hm') hl,
      fun rs mk hx => ⟨key_inY f row pads w p H hm' (hO m hm') rs mk hx,
        key_ends f row pads w p H hm' (hO m hm') rs hx⟩⟩
  | tab l =>
    have hl := mem_tab hs
    have hk' : k.vs.length = f.mu + l := by
      have e : k = levelCall (f.mu + l) := (Option.some.inj hk).symm
      rw [e]
      simp [levelCall, VerifiableInference.Desc.First.ProdV.levelVars]
    rw [hk']
    exact ⟨fun rs h => tab_round f row pads w p H hl rs (Z.tab l (by omega)) h,
      fun rs mk hx => ⟨tab_inY f row pads w p H hl rs mk hx, tab_ends f row pads w p H hl rs hx⟩⟩
  | leaves =>
    have hk' : k.vs.length = f.mu + f.d := by
      have e := (Option.some.inj hk).symm
      rw [e]
      simp [VerifiableInference.Desc.K3.leafVars]
    rw [hk']
    exact ⟨fun rs h => leaves_round f row pads w p H rs (Z.tab f.d (le_refl _)) h,
      fun rs mk _ => ⟨leaves_inY f row pads w p rs mk, leaves_ends f row pads w p rs⟩⟩
  | bits =>
    have hk' : k.vs.length = f.mu + f.d := by
      have e := (Option.some.inj hk).symm
      rw [e]
      simp [VerifiableInference.Desc.K3.bitsCall]
    rw [hk']
    exact ⟨fun rs h => bits_round f row pads w p H rs Z.zero h,
      fun rs mk hx => ⟨bits_inY f row pads w p H rs mk hx, bits_ends f row pads w p H rs hx⟩⟩

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.tie_mem
#print axioms ProofFile.Honest.K3.FastLaw.split_mem
#print axioms ProofFile.Honest.K3.FastLaw.stages_agree
