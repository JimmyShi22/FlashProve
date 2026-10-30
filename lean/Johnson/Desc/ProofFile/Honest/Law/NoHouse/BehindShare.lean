-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BehindShare.lean: THE RUNS' SHARE AT «BEHIND THE
BATCHING», PAID FROM THE LIBRARY, AT THE LIBRARY's HEAD. `behind_state`
(Honest/Law/NoHouse/BehindPays.lean) took the library's `LinkShare`, which asks of BOTH of a link's
orders, and is shown of no link. This member runs the order behind the batching alone. The library's
`after_rests_layers`, `_attention`, `_head` (Johnson/Desc/First/Link/Law/AfterRests.lean) say: every
run of that order stands in every relation that the eight known runs keep, from THREE TIES on the
runs' names; these ties are fields of `LayersTies`, `AttTies`, `HeadTies`, which the library's
`ties_layers_mg`, `ties_att_mg`, `ties_head_mg` (Johnson/LPFK9R/SortTiesAtMg.lean) pay at the head,
at the very link that the head's data name. So: (1) from «every run behind stands in whatever the
eight keep»: what a yes of `runBehind` leaves; `keepsBehind` (with `AL` and «no mark in front»); «rw
rides»; (2) that sentence at the head, at every link that stands at its sort (`hseg`).

WHAT THIS IS. Conditional lemmas on the library's definitions: calls. None of the library's goals.

  1  `after_state`, `after_keeps`, `after_num`, `after_rows`
  2  `after_share_head`, `behind_rw_head`

THE FOUR RELATIONS THAT ARE SPENT, each the library's: `rests_rb` (RbRuns.lean); `rests_rest9`
(Rest9.lean) through `relRests_of_field`; `rests_fork sized_rests` (SizedRides.lean); `rests_num`
(NumRuns.lean), with `rowsFit_iff` (RwRides.lean) and `hrw_at`
(Johnson/LPFK9R/FactsAtConstant.lean).

Limits. THE FULL SIZE ALONE, and the format's second hash function alone, in 2. This file proves nothing
about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindRows
import Johnson.Desc.First.Link.Law.AfterRests
import Johnson.Desc.First.Link.Law.NumRuns
import Johnson.Desc.First.Link.Law.RwRides
import Johnson.LPFK9R.SortTiesAtMg
import Johnson.LPFK9R.FactsAtConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Link Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L (numOf rowsAt)
open VerifiableInference.Desc.LinkJoin (Rb rest9 ledgerOk RunRests AtAfter SegAt rb_behind
  rest_behind ledger_behind runRests_of_rel relRests_of_field rests_rb rests_rest9 rests_fork
  sized_rests rests_num holds_runBehind rowsFit_iff after_rests_layers after_rests_attention
  after_rests_head)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 From «every run behind stands in whatever the eight known runs keep» -/

/-- **What a yes of the runs behind the batching leaves.** -/
theorem after_state (Lk : Link S Claim)
    (A : ∀ B : S → S → Prop, RunRests B → ∀ o ∈ Lk.orderAfter, ∀ run, AtAfter Lk o run →
      ∀ e e₁, run e = .ok e₁ → B e e₁) (s s' : S)
    (h : Lk.runBehind s = .ok s') : Rb s s' ∧
      (∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) ∧
      (ledgerOk s = true → ledgerOk s' = true) := by
  have hst := behind_step Lk h 0
  exact ⟨rb_behind Lk (A Rb (runRests_of_rel rests_rb)) _ _ _ _ _ _ hst,
    fun L₀ F₀ t₀ => rest_behind L₀ F₀ t₀ Lk
      (A _ (runRests_of_rel (relRests_of_field (rests_rest9 L₀ F₀ t₀)))) _ _ _ _ _ _ hst,
    ledger_behind Lk (A _ (rests_fork sized_rests)) _ _ _ _ _ _ hst⟩

/-- **`keepsBehind`.** AL: `rows_share_head` (Honest/Law/NoHouse/BehindRows.lean) pays it. -/
theorem after_keeps (Lk : Link S Claim)
    (A : ∀ B : S → S → Prop, RunRests B → ∀ o ∈ Lk.orderAfter, ∀ run, AtAfter Lk o run →
      ∀ e e₁, run e = .ok e₁ → B e e₁) (s s' : S)
    (AL : ∀ o ∈ Lk.orderAfter, ∀ run, AtAfter Lk o run → ∀ e e₁, run e = .ok e₁ →
      behindLeaves e e₁)
    (h0 : s.failed = none) (h : Lk.runBehind s = .ok s') : keepsBehind s s' := by
  obtain ⟨R, r9, -⟩ := after_state Lk A s s' h
  exact ⟨R, r9, R.failed.trans h0, rows_runBehind Lk AL s s' h⟩

/-- The plan's number, the tables and the blanked state of the range proof are as they were. -/
theorem after_num (Lk : Link S Claim)
    (A : ∀ B : S → S → Prop, RunRests B → ∀ o ∈ Lk.orderAfter, ∀ run, AtAfter Lk o run →
      ∀ e e₁, run e = .ok e₁ → B e e₁) (s s' : S)
    (h : Lk.runBehind s = .ok s') (v : OnBytes.Model.HTailF2) : numOf v s' = numOf v s :=
  holds_runBehind (fun e => numOf v e = numOf v s) Lk
    (fun o ho run hl e e₁ hr hx => (A _ (rests_num v) o ho run hl e e₁ hr).trans hx) s s' h rfl

/-- **The test on the round's rows rides forward.** -/
theorem after_rows (Lk : Link S Claim)
    (A : ∀ B : S → S → Prop, RunRests B → ∀ o ∈ Lk.orderAfter, ∀ run, AtAfter Lk o run →
      ∀ e e₁, run e = .ok e₁ → B e e₁) (s s' : S)
    (h : Lk.runBehind s = .ok s') (rows : Nat)
    (hr : VerifiableInference.Desc.K9.rowsFit rows s = true) :
    VerifiableInference.Desc.K9.rowsFit rows s' = true := by
  have u : OnBytes.Model.HTailF2 := {}
  have e := after_num Lk A s s' h u
  refine (rowsFit_iff rows u s').2 fun tlb funs n hn => ?_
  exact (rowsFit_iff rows u s).1 hr tlb funs n (e.symm.trans hn)

/-! ## 2 At the library's head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT EVERY LINK OF THE HEAD THAT STANDS AT ITS SORT (`hseg`): every run behind the batching
stands in whatever the eight known runs keep.** -/
theorem after_share_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (hm : m < 25)
    {Lk : Link S Claim} (hlk : h.𝔇.lk m = some Lk) (hseg : SegAt m (IM.subAt m) Lk) :
    ∀ B : S → S → Prop, RunRests B → ∀ o ∈ Lk.orderAfter, ∀ run, AtAfter Lk o run →
      ∀ e e₁, run e = .ok e₁ → B e e₁ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro B R
  cases hs : IM.subAt m with
  | layers =>
    obtain ⟨p4, X, -, -, T⟩ := LPFK9.ties_layers_mg h O m hm hs Lk hlk
    rw [hs] at hseg
    exact after_rests_layers R hseg T.tLs T.tFree T.tTests
  | attention =>
    obtain ⟨Xl, A, X, -, -, -, -, T⟩ := LPFK9.ties_att_mg h O m hm hs Lk hlk
    rw [hs] at hseg
    exact after_rests_attention R hseg T.tLs T.tTests
  | head =>
    obtain ⟨iU3, X, -, -, T⟩ := LPFK9.ties_head_mg h O m hm hs Lk hlk
    rw [hs] at hseg
    exact after_rests_head R hseg T.tLs T.tTests

/-- **«rw rides» at the head.** -/
theorem behind_rw_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (hm : m < 25)
    {Lk : Link S Claim} (hlk : h.𝔇.lk m = some Lk) (hseg : SegAt m (IM.subAt m) Lk) (s s' : S)
    (hy : Lk.runBehind s = .ok s') (hr : h.𝔇.rw m s = true) : h.𝔇.rw m s' = true := by
  obtain ⟨-, p, -, -, hp, -, -⟩ := LPFK9.sits_at_constant h.toAtMg m hm
  rw [LPFK9.hrw_at h m p hp] at hr ⊢
  exact after_rows Lk (after_share_head h hm hlk hseg) s s' hy p.rows hr

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.after_state
#print axioms ProofFile.Honest.FirstThread.after_keeps
#print axioms ProofFile.Honest.FirstThread.after_num
#print axioms ProofFile.Honest.FirstThread.after_rows
#print axioms ProofFile.Honest.FirstThread.after_share_head
#print axioms ProofFile.Honest.FirstThread.behind_rw_head
