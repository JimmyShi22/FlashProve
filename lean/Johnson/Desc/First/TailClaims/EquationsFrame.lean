-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsFrame.lean: what stays of the link's ledger from the making of
the list "K8.equations" to the end of the adding: the batching element, the plan's number of claims,
and of the arrays everything but the values of the virtual rows' weights L (treesFrame: so each
array's kind, its numbers R and K, and how many virtual rows it has).

Statements and proofs. No routine of `verify-on-bytes` is named. USED OF THE FILES UNDER OnBytes/,
ON RECORDS AND PLAIN DATA ALONE: the record Fork, treesFrame (OnBytes/Model/HideLaws.lean).
Main names:
  tame_tie, tame_read, tame_weights, tame_all: every routine of Equations.lean changes of the record
    the side alone and only lays claims behind the list.
  eq_side: the record that "K8.equations" returns is the record handed in but for the side.
  eq_link: where the ledger handed in has one coefficient a slot: behind the adding of any list to the
    returned one: the batching element, the plan's number, the count of claims, "one coefficient a
    slot", the arrays' frame.
Limits: from a yes alone. Nothing on the weights L.

-/
import Johnson.Desc.First.TailClaims.EquationsOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc

theorem tame_tie (tl : HTailF2) (mu : Nat) : Tame (eqTie tl mu) := by
  unfold eqTie
  repeat (first
    | exact Tame.pure _
    | exact Tame.get _ _
    | exact Tame.emit _
    | apply Tame.bind
    | (show ∀ _, Tame _; intro _)
    | (dsimp only))

theorem tame_read (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E) :
    Tame (eqRead tl Fn sg laid sums) := by
  unfold eqRead
  repeat (first
    | exact Tame.pure _
    | exact Tame.get _ _
    | exact Tame.ask _ _
    | exact Tame.mustAs _ _
    | exact Tame.testAs _ _
    | exact Tame.emit _
    | apply Tame.bind
    | (show ∀ _, Tame _; intro _)
    | (dsimp only)
    | split)

theorem tame_weights (tl : HTailF2) : Tame (eqWeights tl) := by
  unfold eqWeights
  exact Tame.bind (Tame.ask _ _) fun _ => Tame.get _ _

theorem tame_all (tl : HTailF2) (funs : Array HFun) : Tame (eqAll tl funs) := by
  unfold eqAll
  repeat (first
    | exact Tame.pure _
    | exact Tame.claims
    | exact Tame.mustAs _ _
    | exact Tame.testAs _ _
    | exact Tame.get _ _
    | exact Tame.ask _ _
    | exact tame_keys _
    | exact tame_counts _
    | exact tame_weights _
    | exact tame_tie _ _
    | exact tame_read _ _ _ _ _
    | apply Tame.forInList
    | apply Tame.forInArray
    | apply Tame.ite
    | apply Tame.bind
    | (show ∀ _ _, Tame _; intro _ _)
    | (show ∀ _, Tame _; intro _)
    | (dsimp only)
    | split)

/-- The record that "K8.equations" returns is the record handed in but for the side (slots, marks). -/
theorem eq_side {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) : OnlySide F F1 := by
  unfold equations at h
  cases e : eqAll tl funs front (F, #[]) with
  | error x => rw [e] at h; cases h
  | ok x =>
    rw [e] at h
    obtain ⟨tlx, Fx, arr⟩ := x
    obtain rfl : Fx = F1 := congrArg (fun y => y.2.1) (Except.ok.inj h)
    exact (tame_all tl funs _ _ _ _ e).1

/-- **What stays along the link.** From the record F at which the list is made to the record G behind
the adding of any list l to the record that the run returns. -/
theorem eq_link {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 G : Fork}
    {cls l : List Claim} (hs : F.LS.size = F.ns)
    (h : equations front tl funs F = .ok (tl', F1, cls)) (hadd : addAll F1 l = some G) :
    F1.trees = F.trees ∧ F1.theta = F.theta ∧ G.theta = F.theta ∧
      G.planClaimsF = F.planClaimsF ∧ G.nClaim = F.nClaim + l.length ∧ G.LS.size = G.ns ∧
      treesFrame G.trees = treesFrame F.trees := by
  have os := eq_side h
  have s1 : F1.LS.size = F1.ns := by
    rw [os.LS, os.ns]
    exact hs
  obtain ⟨o, n, s⟩ := addAll_keeps l F1 G s1 hadd
  exact ⟨os.trees, os.theta, o.theta.trans os.theta, o.plan.trans os.plan,
    by rw [n, os.nClaim], s, by rw [o.trees, os.trees]⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.tame_all
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_side
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_link
