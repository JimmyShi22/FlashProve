-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Step8.lean: a yes of the proximity test's block holds `combineAt` at the record
in front. Statements and proofs.

Guard (c) of `guardedProximityTestParts` (`combOk`, Johnson/Desc/K12/JoinGuarded.lean) stands in front of the batching. So
a yes of the block gives the test `combineAt` (Johnson/Desc/Means/TestsB.lean) at the statement
behind the test's beginning, the layout in front and the rows that the test takes in: what the law
of what the batched rows mean asks of the record.
Main names:
  `comb_of_ok`: from `combOk t = true`, the group G0 under t.g and `t.st.layout t.g = some Ly`:
    combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true.
  `combOk_of_decide`: a yes of the decision of `proximityTestKind guardedProximityTestParts p` at t0 gives `combOk t0 = true`: the
    front leaves the record as it is, and guard (c) is the first line of the batching's part.
  `combOk_of_step`: the same of `Block.step`.
  `comb_of_step`: a yes of the step, the group and the layout give `combineAt` at these letters.
Limits: it holds only since `guardedProximityTestParts` has guard (c). No file is known that brings the verifier to a
record at which that guard refuses: see the head of Johnson/Desc/K12/JoinGuarded.lean. No soundness is
claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.K12.FrameLaws
import Johnson.Desc.K12.Law.FoldKeeps

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok)

theorem comb_of_ok (t : T12) (h : combOk t = true) (G0 : Group) (Ly : GroupLayout)
    (hG : t.st.groups[t.g]? = some G0) (hL : t.st.layout t.g = some Ly) :
    Means.combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true := by
  unfold combOk at h
  rw [hG, hL] at h
  exact h

theorem combOk_of_decide (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t0 rs gs = .ok tE) : combOk t0 = true := by
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' : (do
        need "(f): the plan's count of roots in front of the test is not the record's"
          (p.nums.free == t0.roots)
        let t' ← (frontJ p).decide t0 [] []
        need "(p): the record's codes or the place's rounds fail a public clause of the chain"
          (H2K.Pub.pubOk p t'.st.codes)
        pure t') = Except.ok tF := hfr
    obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
    obtain ⟨t', h1, hfr'⟩ := bind_ok hfr'
    obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
    cases hfr'
    unfold frontJ at h1
    dsimp only at h1
    split at h1
    · obtain ⟨_, _, h1⟩ := bind_ok h1
      cases h1
      rfl
    · cases h1
  subst hF
  unfold guardedProximityTestParts ranged at hbat
  dsimp only at hbat
  obtain ⟨_, _, hbat⟩ := bind_ok hbat
  obtain ⟨_, hc, _⟩ := bind_ok hbat
  exact needD_ok hc

theorem combOk_of_step (p : P12) (t0 tE : T12) (F n : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).step F t0 rs cols = .ok (tE, n)) : combOk t0 = true := by
  obtain ⟨_, _, hdec⟩ := Prox.step_ok F _ t0 tE rs cols n h
  exact combOk_of_decide p t0 tE _ _ hdec

theorem comb_of_step (p : P12) (t0 tE : T12) (F n : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).step F t0 rs cols = .ok (tE, n)) (G0 : Group)
    (Ly : GroupLayout) (hG : t0.st.groups[t0.g]? = some G0) (hL : t0.st.layout t0.g = some Ly) :
    Means.combineAt (begun t0.st t0.g G0) t0.g ⟨Ly, runRows t0.st G0⟩ = true :=
  comb_of_ok t0 (combOk_of_step p t0 tE F n rs cols h) G0 Ly hG hL

end H2K.JointK

#print axioms H2K.JointK.combOk_of_decide
#print axioms H2K.JointK.comb_of_step
