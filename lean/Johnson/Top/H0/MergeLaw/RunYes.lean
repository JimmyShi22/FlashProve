-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RunYes.lean: behind the merge's yes its run of claims says yes; what the yes
does to the ledger's marks. Theorems with their proofs.

Why. A filling of the table of joints' item "forms" reads a run's forms off the run itself, called
at the border's record (Johnson/Desc/First/Batch/ReaderOf.lean): where the run refuses there, the
sentence is false and its test on the record fails. So the block that opens "merged" owes: at the
record that it puts out the run says yes.

Main names:
  `pscRow_returns`: where its test passes and the run of values goes under the slots, the library's
    `Fl.pscRow` returns. The way back from `pscRow_inv` (Hear.lean).
  `decide_marks`: at a yes of the merge's decision: the sumcheck's state that is left passes
    `pscRow`'s test; its window begins at the next free slot in front; and, under the ledger's sizes
    (`Sized`), where nothing at or above the next slot is filled in front (`FreeAbove`,
    OnBytes/Tie/Pv/Psc/PscRoom.lean): behind: the sizes; again nothing at or above the next slot is
    filled; the window's 2 lk + 2 slots are free and lie beneath the number of slots.
  `run_yes_behind`: so `headMergeClaim` says yes at the record behind, with the one claim
    `wo.p.rowForm wo.fvp {}`.

Limits. `FreeAbove` in front is a premise: a promise that somebody in front has to make and keep.
hlen (the walk has 2 lk + 2 entries) is a premise here; `ClosedSays` (Closed.lean) and `BehindOk`
(Here.lean) give it behind a yes. At the very record behind the merge alone: that the run still says
yes at a later record, behind other blocks, is not said. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Keeps
import OnBytes.Tie.Pv.Psc.PscRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (E zeroE oneE subE)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.Model (Fork Psc WsForkOut)
open OnBytes.PscRun (Later Filled Sized FreeAbove hideRun_ok hideRun_returns)
open VerifiableInference.Desc (Claim)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headMergeClaim)

/-- Where its test passes and the run of values goes under the slots, `pscRow` returns. -/
theorem pscRow_returns {p : Psc} {S0 : E} {kept : OnBytes.Model.Aff} {F G : Fork} {t : Tape}
    (hm : (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true)
    (hG : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G) :
    Fl.pscRow p S0 kept F t = some ((p.rowForm S0 kept, { p with rowMade := true }), G, t) := by
  unfold Fl.pscRow
  show Fl.andThen (Fl.must _) _ F t = _
  unfold Fl.andThen Fl.must
  rw [hm]
  show Fl.andThen (Fl.change _) _ F t = _
  unfold Fl.andThen Fl.change
  simp only [hG, Option.map_some]
  rfl

/-- **What the merge's yes does to the marks.** Under the sizes, and where nothing at or above the
next slot is filled in front: behind the yes the sumcheck's window of slots is free and lies beneath
the number of slots, and again nothing at or above the next slot is filled. -/
theorem decide_marks {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') :
    ∃ a a' wo, s.here = .head a ∧ s'.here = .head a' ∧ a'.wo = some wo ∧
      (!wo.p.rowMade && wo.p.started && !wo.p.vars.isEmpty && wo.p.r.size == wo.p.vars.size) = true
          ∧
      wo.p.first = a.F.next ∧
      (Sized a.F → FreeAbove a.F →
        Sized a'.F ∧ FreeAbove a'.F ∧
          ∀ j, wo.p.first ≤ j → j < wo.p.first + (2 * P.lay.lk + 2) → j < a'.F.ns ∧ ¬ Filled a'.F j)
      := by
  obtain ⟨a, a', tp, F, claim, x, wo, e1, e2, _, _, e5, _, hm, hF, _, _, _⟩ := decide_inv h
  obtain ⟨_, _, _, _, _, v, _, _, _, _, qs, hq, _, _, _, _, _, _, _, _, hr, hsFv, hhide, _, _,
      hvars,
    hfirst, _, hst, hrm, _⟩ := mergeHear_inv hm
  refine ⟨a, a', wo, e1, e2, e5, ?_, hfirst, ?_⟩
  · have h1 : wo.p.vars.size = P.lay.lk + 1 := by
      rw [← Array.length_toList, hvars]
      simp
    have h2 : wo.p.r.size = P.lay.lk + 1 := by
      rw [← Array.length_toList, hr]
      simp [hq]
    have h3 : wo.p.vars.isEmpty = false := by
      rw [Array.isEmpty_iff_size_eq_zero.not.mpr (by omega) |> Bool.eq_false_iff.mpr]
    simp [hst, hrm, h1, h2, h3]
  · intro hz hfree
    have hz' : Sized ({ a.F with next := a.F.next + 1 + 2 * P.lay.lk + 2 } : Fork) := hz
    obtain ⟨hsame, hzF, r3, r4⟩ := hideRun_ok _ F _ _ _ hz' hhide
    obtain ⟨q1, _, _, _, _⟩ := r3 0 (by simp)
    have hns : F.ns = a.F.ns := hsame.ns
    have hnext : F.next = a.F.next + 1 + 2 * P.lay.lk + 2 := hsame.next
    rw [hF]
    refine ⟨hzF, ?_, ?_⟩
    · intro j hj hf
      have hj' : a.F.next + 1 + 2 * P.lay.lk + 2 ≤ j := by
        rw [← hnext]
        exact hj
      exact hfree j (by omega) ((r4 j (Or.inr (by simp; omega))).2.2.1 hf)
    · intro j j1 j2
      rw [hfirst] at j1 j2
      refine ⟨?_, fun hf => hfree j j1 ((r4 j (Or.inl (by omega))).2.2.1 hf)⟩
      show j < F.ns
      rw [hns]
      have : wo.sFv + 0 < a.F.ns := q1
      omega

/-- **BEHIND THE MERGE's YES ITS RUN OF CLAIMS SAYS YES**, at the very record that the merge puts
out: under the ledger's sizes in front, where nothing at or above the next slot is filled there. -/
theorem run_yes_behind {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (a : HeadOwn) (ha : s.here = .head a) (hz : Sized a.F)
    (hfree : FreeAbove a.F) (wo : WsForkOut) (a' : HeadOwn) (ha' : s'.here = .head a')
    (hwo : a'.wo = some wo) (hlen : wo.p.walk.1.length = 2 * P.lay.lk + 2) (n : ℕ) :
    ∃ s₃, headMergeClaim n s' = .ok ([{ form := wo.p.rowForm wo.fvp {} }], s₃) := by
  obtain ⟨b, b', wo', e1, e2, e5, hm, _, hall⟩ := decide_marks h
  have eb : b = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  subst eb
  have eb' : b' = a' := by
    rw [ha'] at e2
    exact (Here.head.inj e2).symm
  subst eb'
  have ew : wo' = wo := by
    rw [hwo] at e5
    exact (Option.some.inj e5).symm
  subst ew
  obtain ⟨hz', _, hwin⟩ := hall hz hfree
  obtain ⟨G, hG⟩ := hideRun_returns (F := b'.F) wo'.p.first
    (Array.replicate wo'.p.walk.1.length zeroE) (subE zeroE oneE) hz'.2.2 (by
      intro i hi
      rw [Array.size_replicate, hlen] at hi
      exact hwin _ (Nat.le_add_right _ _) (by omega))
  refine ⟨{ s' with here := .head { b' with F := G } }, ?_⟩
  unfold headMergeClaim
  rw [ha']
  simp only [hwo, VerifiableInference.Desc.named, pscRow_returns hm hG, bind, Except.bind, pure,
    Except.pure]

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.decide_marks
#print axioms VerifiableInference.Desc.First.MergeLaw.run_yes_behind
