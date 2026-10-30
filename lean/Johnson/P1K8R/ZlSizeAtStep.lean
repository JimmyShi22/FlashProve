-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ZlSizeAtStep.lean: the proofs of the three statements of
Johnson/P1K8R/ZlSizeAtStepStatement.lean, to the letter. Lemmas; none of the library's goals.

A FURTHER TEXT. THE ROAD OF `zlSize_at_decision` FROM `decideBy_more` TO "ls + lt ≤ z.1.size" IS
SOME SEVEN LINES OF THE PROOF OF THE LIBRARY's `core_of_kind` (Johnson/Desc/Reads/HeardSizes.lean),
WRITTEN A FURTHER TIME: that lemma ends in a structure of 21 clauses under premises that are not
wanted here, and hands the bound out nowhere.

How. `zlSize_at_decision`: a yes of the decision (`decideBy_more`): the kind's letters are read in
front, the ledger is laid, what was heard is laid. The letters (`given_ok`,
Johnson/Desc/Kinds/Law/FromGiven.lean): the lookup's points z pass the kind's test; at call 0
(`call_get`, Call.lean) the key point has lJ + lt coordinates and ends as z.1 does: so ls + lt ≤
z.1.size (`size_of_tail`, Johnson/Desc/Reads/RunIsLean.lean). z.1 is the point of what the lookup
left at the state in front; laying the ledger keeps that reader's answer (`putFork?_ok`,
Johnson/Desc/Kinds/Law/HeardAt.lean; `S.look_putFork`, Johnson/Desc/First/StateLedger.lean);
`setHeard_form` (HeardBack.lean): what is laid as heard is `heardOf` of that field, whose Zl is the
last ls + lt coordinates of its point; `last_size` (Johnson/Desc/Reads/PointCuts.lean).
`lsFits_in_scope`: the floor is 27 (`keyFloor_in_scope`, Johnson/Goal/Meaning/HeadForInScope.lean);
the kind's number of columns at call 0 is 18 (`kind_cols`, HeadColsScope.lean), as `cols_in_scope`
takes it; ls is 6.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.ZlSizeAtStepStatement
import Johnson.Desc.Reads.RunIsLean
import Johnson.Desc.Kinds.Law.HeardAt
import Johnson.Desc.Kinds.Law.HeardBack
import Johnson.Desc.First.StateLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads (size_of_tail)
open VerifiableInference.Reads.AtSeat (decideBy_more)

/-- **Behind the decision's yes the point x.Zl has ls + lt coordinates.** -/
theorem zlSize_at_decision : ZlSizeAtDecision := by
  intro h iU3 work rounds hear weights s0 s2 rs hd hls
  obtain ⟨g0, H, F, left, s1, s2', hg, -, e1, e2, hs2⟩ := decideBy_more hd
  have hs2' : s2 = s2' := hs2
  subst hs2'
  obtain ⟨z, y, hz1, -, hP, -⟩ := Came.given_ok _ _ _ _ hg
  have hz : h.ls + h.lt ≤ z.1.size := by
    obtain ⟨p1, p2⟩ := hP 0 _ (Came.call_get (by decide))
    exact size_of_tail (z.2 0) z.1 p1 p2 hls
  obtain ⟨g, hg0, rfl⟩ : ∃ g, s0.lookHeard? = some g ∧
      z = (g.zx, fun c => g.zk.getD c #[]) := by
    have e : (s0.lookHeard?.map fun G => (G.zx, fun c => G.zk.getD c #[])) = some z := hz1
    obtain ⟨g, a, b⟩ := Option.map_eq_some_iff.1 e
    exact ⟨g, a, b.symm⟩
  obtain ⟨o1, G, ho1, hG, rfl⟩ := setHeard_form h iU3 e2
  have e1' : s1 = s0.putFork F := putFork?_ok e1
  have hl1 : s1.lookHeard? = some g := by
    rw [e1', VerifiableInference.Desc.First.S.look_putFork]
    exact hg0
  have hGg : G = g := by
    unfold VerifiableInference.Desc.First.S.lookHeard? at hl1
    rw [ho1] at hl1
    by_cases hop : o1.opened = true
    · have k : o1.lookHeard = some g := by
        have k0 : (if o1.opened = true then o1.lookHeard else none) = some g := hl1
        rw [if_pos hop] at k0
        exact k0
      exact Option.some.inj (hG.symm.trans k)
    · have k0 : (if o1.opened = true then o1.lookHeard else none) = some g := hl1
      rw [if_neg hop] at k0
      cases k0
  subst hGg
  refine ⟨_, _, rfl, rfl, ?_⟩
  exact VerifiableInference.Reads.last_size G.zx hz

/-- **The same at the kind's block at S**: its decision is the kind's, by its text. -/
theorem zlSize_at_block : ZlSizeAtBlock := by
  intro h iU3 work l s s' rs gs hd hls
  exact zlSize_at_decision h iU3 work (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) s
    s' rs hd hls

/-- **The premise holds in scope.** -/
theorem lsFits_in_scope : LsFitsInScope := by
  intro Z pp lay X hZ hR h
  have N := InScope.numbers_in_scope hZ hR h
  have e6 : X.hS.la - X.hS.lt = 6 := by rw [N.la, N.lt]
  rw [_root_.Meaning.HeadS.keyFloor_in_scope hZ hR h,
    InScope.kind_cols (sizesOf X.hS) N.lt e6 N.d N.V 0 (by decide)]
  show X.hS.la - X.hS.lt ≤ 18
  rw [e6]
  decide

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.zlSize_at_decision
#print axioms P1K8.zlSize_at_block
#print axioms P1K8.lsFits_in_scope
