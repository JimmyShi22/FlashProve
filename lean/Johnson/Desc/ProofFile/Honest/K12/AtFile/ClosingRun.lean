-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingRun.lean: at the first chain's closing proximity test,
from the test on the book: the two parts' readers agree, at the job and at the job patched at a stand.

  `agree_job`       `agree_of_ties` (K12/AgreeBook.lean) at a job that is a letter
  `agree_at_L`      the readers agree, at every job with `jobL`'s fresh table, members and rows

By what. `agree_of_ties`; `rowsL_congr` (ClosingJob.lean).

Limits.
- hT, `tiesB` at the book, is `hT_head_L` (AtFullSide/K12/TiesAtHeadL.lean) at the maker's book.
- A stand of the thread is not spoken of here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingJob
import Johnson.Desc.ProofFile.Honest.K12.HalfSteps
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K12 (P12)
open H2K.Pub (sgOf)
open Johnson.Prover.Link (μOf)
open ProofFile.Honest.K12.AtProof (jobL rowsL membersL freshL rowsL_congr)

variable {V W X : Type}

/-- `agree_of_ties` at a job that is a letter, its word on the fresh table a premise. -/
theorem agree_job (J : TestJob W X) (f : Addr × ℕ) (hfr : J.fresh = some f) (B : ProverCoinCounts)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (h : lendRow B rows look J.p.place [(firstPart J : Part V W X), restPart J] 0 = .ok c) (w : W)
    (fr : Front X) (hT : tiesB B J.p.place J.members.length = true)
    (hk : J.s₀.k = (sgOf J.s₀).h + (sgOf J.s₀).g)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf J.s₀) (J.rows₀ w fr mem) = μOf (sgOf J.s₀) (J.rows₀ w fr mem')) :
    Agree J w fr J.s₀ (firstRd J c.1) (restCoins J c.2.1) := by
  cases J with
  | mk p ms fresh r ro tr =>
    have e : fresh = some f := hfr
    subst e
    exact agree_of_ties p ms f r ro tr B rows look c h w fr hT hk hrows

variable {W₀ Rc Xi Tr Y : Type}

/-- **The two parts' readers agree**, at every job with the closing job's fresh table, members and
rows, whatever its state on entry. -/
theorem agree_at_L (q : P12) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) (J : TestJob (Local W₀ Rc Xi Tr) Y)
    (hfr : J.fresh = AtProof.freshL p) (hm : J.members = membersL p)
    (hr : J.rows₀ = rowsL D readers closing p) (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart J : Part V (Local W₀ Rc Xi Tr) Y), restPart J])
    (h : lendRow B rows look J.p.place
      [(firstPart J : Part V (Local W₀ Rc Xi Tr) Y), restPart J] 0 = .ok c)
    (w : Local W₀ Rc Xi Tr) (fr : Front Y) (hT : tiesB B J.p.place J.members.length = true)
    (hk : J.s₀.k = (sgOf J.s₀).h + (sgOf J.s₀).g) :
    Agree J w fr J.s₀ (firstRd J c.1) (restCoins J c.2.1) := by
  refine agree_job J _ hfr B rows look c h w fr hT hk fun mem mem' e => ?_
  rw [hr, rowsL_congr D readers closing p w fr (mem := mem) (mem' := mem') (hm ▸ e)]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.agree_job
#print axioms ProofFile.Honest.K12.agree_at_L
