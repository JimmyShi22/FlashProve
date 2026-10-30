-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/BudBoth.lean: BOTH MEMBERS OF A PROXIMITY TEST (the kind K12)
AT ONE CONDITION AND ONE BOUND ON THE POSITIONS ASKED, so that both members' sentences and both
debts can stand at one list of the frame (`Lettered`, Johnson/Desc/ProofFile/Honest/Rule.lean).
Statements and proofs; no definition: the bound is `budBoth` (Sim/ExactFirstOwn.lean).

Why. A list of the frame has one bound, and it is used twice, in opposite senses. In the frame's
sentence at a member (`ExactMember`, Johnson/Desc/ProofFile/Honest/Small/Field.lean) it is a
hypothesis: a narrower bound makes the sentence weaker. In `BudDebts`
(Johnson/Desc/ProofFile/Honest/Law/OwedRule.lean) and in `Lettered.owedAt` it is a debt: a narrower
bound is harder to pay. `testBud` (Sim/Row.lean) has at number 1 the count `budRest`, under which
the second member's sentence is proved by nobody. `budBoth` has there the containment `budOpened`
(Sim/ExactPlan.lean), under which it is proved (`exact_free_trees`, Sim/TreesExact.lean). The first
member's sentence is had at `budBoth` outright: `exact_first_job` (Sim/ExactFirstOwn.lean) at every
condition; `exact_first` (Sim/ExactFirst.lean) at every condition and every bound. The statements on
the first member that name `testBud` are corollaries of these. This file moves no count.

  `both_rest`    at number 1 `budBoth` is `budOpened`
  `both_of`      `budBoth` at any number: from the first member's clause where the number is 0 and
                 the containment where it is 1; elsewhere nothing is owed. The challenges and the
                 positions are letters: so it serves both forms of the debt
  `first_owes_nothing`   where the fresh table has come earlier the first member owes nothing
  `exact_rest_both`   the second member's sentence at `onFreeT` and `budBoth`
  `exact_both_own`, `exact_both_earlier`   both members' sentences at that one condition and that
                 one bound: where the first fold sends its own table; where the table has come
                 earlier
  `owed_bud_both`   the first conjunct of `Lettered.owedAt` at every member, in its letters, from
                 the two bounds at a run's own challenges and positions. General in the chain
  `owed_bud_both_O`   at the test on G_omega, under the head

By what. `exact_bud` (Sim/FirstPubOwnAtHead.lean); `bud_filled_O`
(Sim/BudAtRun.lean); `side_is_testSide` (Sim/BudOwnIsDebt.lean); `side_place` (Law/OwedRule.lean).

Limits.
- `exact_both_own` HOLDS EMPTILY AT G_omega, THE PLACE FOR WHICH IT IS NAMED: its premise `PubTiesT`
  has the field `reach`, which gives `ownMask = false` (`reach_gives_trees`, Sim/TreesReach.lean);
  there `ownMask` is true (`no_pubTies_O`, Sim/DebtAtO.lean). So "both members at one condition and
  one bound" has content in the arm where the fresh table has come earlier (`exact_both_earlier`)
  alone. Where the first fold sends its own table the second member has no sentence with content, at
  any bound (Sim/TreesExact.lean's first limit).
- NOT "PAID AT O AND U". At both places the bound at number 1 is a named premise (h1). At a run
  `bud_rest_at_run` (Sim/BudRestAtRun.lean) concludes it under public premises; which of these the
  head pays at G_omega: Sim/DebtAtO.lean. At number 0 it is paid at O (`bud_filled_O`) and owed by
  nobody at U.
- THE SECOND MEMBER's SENTENCE STAYS THE NARROWER ONE: at positions asked among those that the next
  reading round samples. That `budOpened` gives the count `budRest`: `rest_of_opened`
  (Sim/BudCount.lean), not here.
- `BudDebts`, the debt at every list of challenges that is due: Sim/DebtBoth.lean and
  Sim/DebtAtO.lean, not here.
- A conditional with no member: nothing shows that `ready` or `runC` returns at such a prover.
- At a state on entry that is the job's own letter `rec₀`, not shown to be the verifier's.
- The first member's sentence never without `formPubB` (h ≤ k); `Js.p = J.p` = the place's.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesExact
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubOwnAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block Place)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

variable {S Cl V W X Pb : Type}

/-! ## 1 What `budBoth` (Sim/ExactFirstOwn.lean) is, number by number -/

theorem both_rest (Js : SimJob Pb) (ds : List Fmt.Drawn) (asks : List (List (List ℕ))) :
    budBoth Js 1 ds asks ↔ budOpened Js.p.nums.stages 1 ds asks := by
  unfold budBoth
  exact ⟨fun h => h.2, fun h => ⟨fun e => absurd e Nat.one_ne_zero, h⟩⟩

/-- **It is paid at a number n by the first member's clause where n = 0 and by the containment where
n = 1; at every other number nothing is owed.** One lemma for both forms of the debt: at a run's own
challenges and positions (`Lettered.owedAt`) and at every list of challenges that is due
(`BudDebts`). -/
theorem both_of (J : TestJob W X) (Js : SimJob Pb) (hp : Js.p = J.p) (n : ℕ) (ds : List Fmt.Drawn)
    (asks : List (List (List ℕ))) (h0 : n = 0 → testBud Js 0 ds asks)
    (h1 : n = 1 → budOpened J.p.nums.stages 1 ds asks) : budBoth Js n ds asks := by
  unfold budBoth
  refine ⟨fun e => (h0 e).1 rfl, ?_⟩
  unfold budOpened
  intro e
  have h := h1 e
  unfold budOpened at h
  rw [hp]
  exact h rfl

/-- Where the fresh table has come earlier the first member owes nothing. -/
theorem first_owes_nothing (Js : SimJob Pb) (ho : Js.own = false) (ds : List Fmt.Drawn)
    (asks : List (List (List ℕ))) : testBud Js 0 ds asks := by
  unfold testBud
  refine ⟨fun _ h => ?_, fun e => absurd e Nat.zero_ne_one⟩
  rw [ho] at h
  cases h

/-! ## 2 The sentence at both members, at ONE condition and ONE bound -/

/-- The second member's: `exact_free_trees` through `exact_bud`. -/
theorem exact_rest_both (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : OnBytes.Codes) (chain firstTree : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (T : PubTiesT J Js K os.length)
    (To : OpenTies J Js chain os) :
    ExactMember φ σ chain firstTree (onFreeT φ J Js K chain os) (budBoth Js) (restMember J Js) := by
  refine exact_bud (fun ds asks hb => ?_) (exact_free_trees φ σ J Js K chain firstTree os T To)
  have h1 := (both_rest Js ds asks).1 hb
  rw [T.place] at h1
  exact h1

/-- **Both, where the first fold sends its own table.** The first member's is `exact_first_job`, as
it stands. AT A PLACE WHOSE `ownMask` IS TRUE NO `PubTiesT` EXISTS (`reach_gives_trees`,
Sim/TreesReach.lean): the second member's half is empty there. -/
theorem exact_both_own (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : OnBytes.Codes) (chain firstTree : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hfr : J.fresh.isNone = true) (T₀ : FirstPubOwn J Js)
    (T : PubTiesT J Js K os.length) (To : OpenTies J Js chain os) :
    ∀ u ∈ [firstMember J Js, restMember J Js],
      ExactMember φ σ chain firstTree (onFreeT φ J Js K chain os) (budBoth Js) u := by
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu'
  · exact exact_first_job φ σ J Js chain firstTree _ hfr T₀
  · rcases List.mem_cons.1 hu' with rfl | hu''
    · exact exact_rest_both φ σ J Js K chain firstTree os T To
    · cases hu''

/-- **Both, where the fresh table has come earlier.** The first member's is `exact_first`, as it
stands. -/
theorem exact_both_earlier (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : OnBytes.Codes) (chain firstTree : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hfr : J.fresh.isNone = false) (T₀ : FirstPub J Js)
    (T : PubTiesT J Js K os.length) (To : OpenTies J Js chain os) :
    ∀ u ∈ [firstMember J Js, restMember J Js],
      ExactMember φ σ chain firstTree (onFreeT φ J Js K chain os) (budBoth Js) u := by
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu'
  · exact exact_first φ σ J Js chain firstTree _ _ hfr T₀
  · rcases List.mem_cons.1 hu' with rfl | hu''
    · exact exact_rest_both φ σ J Js K chain firstTree os T To
    · cases hu''

/-! ## 3 The debt at a run: the first conjunct of `Lettered.owedAt`, at every member -/

/-- General in the chain and the run. No word on which members the side has. -/
theorem owed_bud_both {Bk : ProverCoinCounts} (L : Lettered Bk S Cl V W X Pb) (bs : List (Block S Cl))
    (J : TestJob W X) (Js : SimJob Pb) (hp : Js.p = J.p) (hbud : L.bud = budBoth Js) (r : Run)
    (h0 : testBud Js 0 (r.drawnAt ⟨L.place, 0⟩) (r.askedAt ⟨L.place, 0⟩))
    (h1 : budOpened J.p.nums.stages 1 (r.drawnAt ⟨L.place, 1⟩) (r.askedAt ⟨L.place, 1⟩)) :
    ∀ σ, L.side bs = some σ → ∀ u ∈ σ.members,
      L.bud u.number (r.drawnAt ⟨L.place, u.number⟩) (r.askedAt ⟨L.place, u.number⟩) := by
  intro σ _ u _
  rw [hbud]
  refine both_of J Js hp u.number _ _ (fun e => ?_) fun e => ?_
  · rw [e]
    exact h0
  · rw [e]
    exact h1

/-- **At the test on G_omega, under the head**: the premises of `owed_bud_O` (Sim/BudAtRun.lean),
with `budBoth Js` for `testBud Js`, at every member; and h1: `budOpened` at the second member at
this run: a named premise. -/
theorem owed_bud_both_O (h : P5J.AtMg o Z D r₀ Zp Np cF) (hO : (fourOf Np).O = some pO)
    {W₀ Rc Ky Tr X₀ Y : Type} (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀)
    (hp : J.p = pO) (hJ : Js.p = pO) {Bk : ProverCoinCounts}
    (L : Lettered Bk (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js) (hbud : L.bud = budBoth Js)
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hρ : ρ.due (P5J.F0T o Zp Np cF) = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (g : Placed Empty (Common W₀ Rc Ky) X₀)
    (hg : (P.shared.find? fun g => g.place == L.place) = some g)
    (hparts : g.parts = [firstPart J, restPart J])
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (h1 : budOpened J.p.nums.stages 1 (r.run.drawnAt ⟨L.place, 1⟩) (r.run.askedAt ⟨L.place, 1⟩)) :
    ∀ σ, L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
      L.bud u.number (r.run.drawnAt ⟨L.place, u.number⟩) (r.run.askedAt ⟨L.place, u.number⟩) := by
  intro σ hσ
  have hσ' : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js [] = some σ :=
    (side_is_testSide L J Js hpl hrow _).symm.trans hσ
  have hsp : σ.block.place = L.place := side_place hσ
  have h0 : testBud Js 0 (r.run.drawnAt ⟨L.place, 0⟩) (r.run.askedAt ⟨L.place, 0⟩) := by
    rw [← hsp] at hg ⊢
    exact bud_filled_O h hO Js J hp hJ [] σ hσ' hρ hR g hg hparts hrun
  exact owed_bud_both L _ J Js (hJ.trans hp.symm) hbud r.run h0 h1 σ hσ

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.both_rest
#print axioms ProofFile.Honest.K12.Light.both_of
#print axioms ProofFile.Honest.K12.Light.first_owes_nothing
#print axioms ProofFile.Honest.K12.Light.exact_rest_both
#print axioms ProofFile.Honest.K12.Light.exact_both_own
#print axioms ProofFile.Honest.K12.Light.exact_both_earlier
#print axioms ProofFile.Honest.K12.Light.owed_bud_both
#print axioms ProofFile.Honest.K12.Light.owed_bud_both_O
