-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/RunsCore.lean: WHAT K4's TWO RUNS OF CLAIMS LEAVE OF THE LEDGER AS IT IS. A
definition, statements and proofs. What it is for: the law of the batching asks of every run of
claims that the ledger's sums, the batching element, the number of claims added and the plan's
number stay (its premise RunOk, Johnson/Desc/First/Batch/Law/Gather.lean: the clause on the core).

`Core F G`: G has eleven of F's fifteen fields: the arrays with their weights, the number of slots,
the next slot, the coefficients on the slots, the constant, the number of claims added, the batching
element and whether it is drawn, the plan's number of claims, the marks of the weights handed out,
and whether the door is shut. The four that it leaves open: what was shown under each slot (vp), the
factors (mf), the marks of the filled slots (gotF), and the list of owed claims (owed).
`hide_core`, `hideRun_core`, `paid_core`: putting values under slots, and marking an owed claim as
added, keep these eleven. `formsFrontWith_core`, `formsBack_core`: so do K4's two listings of
claims.
`front_core`, `back_core`: so do the block's runs "front" and "back", at a seat whose laying and
reading of the ledger fit.

With `front_later`, `back_later` (Johnson/Desc/First/K4/LedgerKeeps.lean): of three of the four open
fields (vp, mf, gotF), what lies under a slot that was filled stays; of owed nothing is said. What
the runs DO write stands as equations in `formsFrontWith_some`, `formsBack_some`
(OnBytes/Desc/First/K4/ClaimsLaws.lean): the hiding coefficients of three sumchecks (shown 0, factor
-1), and marks on owed claims.

The proofs of `hideSteps_core` and `hideRun_core` follow `hideSteps_sum` and `sums_hideRun` of the
file Johnson/Road/HeadTheta.lean [not in this library], whose `SameSum` has six of the eleven.

Limits. At a seat, a letter: at the carried record: Johnson/Desc/First/K4/RunsAtS.lean. One
direction, from a return. Nothing on the forms' values. Nothing on soundness.

-/
import Johnson.Desc.First.K4.LedgerKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc

/-- G has eleven of F's fields: all but vp, mf, gotF and owed. -/
structure Core (F G : Fork) : Prop where
  trees : G.trees = F.trees
  ns : G.ns = F.ns
  next : G.next = F.next
  LS : G.LS = F.LS
  c0 : G.c0 = F.c0
  nClaim : G.nClaim = F.nClaim
  theta : G.theta = F.theta
  thetaDrawnF : G.thetaDrawnF = F.thetaDrawnF
  planClaimsF : G.planClaimsF = F.planClaimsF
  kapMapF : G.kapMapF = F.kapMapF
  doorShutF : G.doorShutF = F.doorShutF

theorem Core.refl (F : Fork) : Core F F := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Core.trans {F G H : Fork} (a : Core F G) (b : Core G H) : Core F H :=
  ⟨b.trees.trans a.trees, b.ns.trans a.ns, b.next.trans a.next, b.LS.trans a.LS, b.c0.trans a.c0,
    b.nClaim.trans a.nClaim, b.theta.trans a.theta, b.thetaDrawnF.trans a.thetaDrawnF,
    b.planClaimsF.trans a.planClaimsF, b.kapMapF.trans a.kapMapF, b.doorShutF.trans a.doorShutF⟩

/-- Marking an owed claim as added. -/
theorem paid_core (F : Fork) (i : Nat) : Core F (F.paid i) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Putting a hidden value under a slot. -/
theorem hide_core {F G : Fork} {j : Nat} {s k : E} (h : F.hide j s k = some G) : Core F G := by
  unfold Fork.hide at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h

theorem hideSteps_core (k : E) : ∀ (l : List E) (p q : Nat × Fork),
    l.foldlM (Fork.hideStep k) p = some q → Core p.2 q.2
  | [], p, q, h => by
    have e : p = q := by simpa using h
    rw [e]
    exact Core.refl _
  | y :: l, p, q, h => by
    rw [List.foldlM_cons] at h
    cases hq : Fork.hideStep k p y with
    | none => simp [hq] at h
    | some p1 =>
      rw [hq] at h
      have h2 : l.foldlM (Fork.hideStep k) p1 = some q := by simpa using h
      have a := hideSteps_core k l p1 q h2
      obtain ⟨j, G⟩ := p
      have h3 : (G.hide j y k).map (fun H => (j + 1, H)) = some p1 := hq
      cases hh : G.hide j y k with
      | none => simp [hh] at h3
      | some H =>
        rw [hh] at h3
        have e : (j + 1, H) = p1 := by simpa using h3
        rw [← e] at a
        exact (hide_core hh).trans a

/-- Putting a run of hidden values under slots. -/
theorem hideRun_core {F G : Fork} {first : Nat} {v : Array E} {k : E}
    (h : F.hideRun first v k = some G) : Core F G := by
  unfold Fork.hideRun at h
  rw [← Array.foldlM_toList] at h
  cases hq : v.toList.foldlM (Fork.hideStep k) (first, F) with
  | none => simp [hq] at h
  | some x =>
    rw [hq] at h
    have e : x.2 = G := by simpa using h
    have a := hideSteps_core k v.toList (first, F) x hq
    rw [e] at a
    exact a

/-- **Listing the claims in front keeps the eleven.** -/
theorem formsFrontWith_core {rows : Bool} {P : Pub} {g : Nat} {o : Own} {F G : Fork}
    {fs : Array Aff} (h : formsFrontWith rows P g o F = some (fs, G)) : Core F G := by
  obtain ⟨_, _, _, F1, F2, _, _, _, _, r1, r2, e⟩ := formsFrontWith_some h
  have l12 := (hideRun_core r1).trans (hideRun_core r2)
  rw [e]
  refine l12.trans ?_
  split
  · exact (paid_core F2 _).trans (paid_core _ _)
  · exact paid_core F2 _

/-- **Listing the claims behind keeps the eleven.** -/
theorem formsBack_core {o : Own} {F G : Fork} {fs : Array Aff}
    (h : formsBack o F = some (fs, G)) : Core F G := by
  obtain ⟨F1, _, r1, e⟩ := formsBack_some h
  rw [e]
  exact (hideRun_core r1).trans (paid_core F1 _)

/-- **The run "front" keeps the eleven**, at a seat whose laying and reading of the ledger fit. -/
theorem front_core {T : Type} (L : Seat T) (hL : ∀ (s : T) (F : Fork), L.fork (L.setFork s F) = F)
    (p : Par) (run : Nat → T → Except String (List Aff × T))
    (hr : (block L p).claims.lookup "front" = some run) {n : Nat} {s s' : T} {cl : List Aff}
    (h : run n s = .ok (cl, s')) : Core (L.fork s) (L.fork s') := by
  obtain ⟨o, fs, F, _, hf, _, e⟩ := (front_ok L p run hr n s s' cl).mp h
  rw [e, hL]
  unfold frontOf at hf
  split at hf
  · exact formsFrontWith_core hf
  · exact formsFrontWith_core hf

/-- **The run "back" keeps the eleven**, at such a seat. -/
theorem back_core {T : Type} (L : Seat T) (hL : ∀ (s : T) (F : Fork), L.fork (L.setFork s F) = F)
    (p : Par) (run : Nat → T → Except String (List Aff × T))
    (hr : (block L p).claims.lookup "back" = some run) {n : Nat} {s s' : T} {cl : List Aff}
    (h : run n s = .ok (cl, s')) : Core (L.fork s) (L.fork s') := by
  obtain ⟨o, fs, F, _, hf, _, e⟩ := (back_ok L p run hr n s s' cl).mp h
  rw [e, hL]
  exact formsBack_core hf

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.front_core
#print axioms OnBytes.Desc.First.K4.back_core
