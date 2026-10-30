-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RngHeadPaid.lean: under the library's hypothesis
`P5J.AtMgA` the closed test `rngWrittenB` (Honest/K3/Law/Thread/RngHead.lean) accepts; so the two
theorems of that file that bear "rngWrittenB = true" as a hypothesis hold under `P5J.AtMgA` alone.
Theorems.

Terms. Honest/K3/GLOSSARY.md; Honest/K3/Law/Thread/RngHead.lean.

What is shown.
  `rngWritten_of_head`: under `P5J.AtMgA`: rngWrittenB = true.
  `rng_head`: `rng_head_of` without its hypothesis `hW`. It has the statement of `rng_at` (see
    below), from which it is proved by way of the closed test, and of `rng_head_paid`
    (Honest/K3/Law/Thread/RngWrittenHolds.lean).
  `site_digits`: `site_digits_of` without its hypothesis `hW`. It has the statement of
    `site_at_all_fifty` (Honest/K3/Law/Thread/SiteAllFifty.lean) and of `site_digits_paid`
    (RngWrittenHolds.lean).

Hypotheses that remain. `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean). `hl`:
(in the last two) the link's number is below 25.

How the proof goes. No reduction by Lean's kernel of the closed test. `rng_at`
(Johnson/AtFull/Shape/SitesAtHead.lean) states under `P5J.AtMgA` that `rngIn`
returns a number at every link below 25, at the public part's own table of stretches; `cuts_head`
says that this table is the written one.

Limits. `rngWrittenB` is a closed term, in which no letter of `h` stands; still it is shown here
under `h` alone: no instance of `P5J.AtMgA` is exhibited in this file, so "rngWrittenB = true"
without a hypothesis does not follow from it. `rngWritten_holds` (RngWrittenHolds.lean) proves that,
without a hypothesis. On
public data alone. At the full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngHead
import Johnson.AtFull.Shape.SitesAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Shape (rng_at)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under `P5J.AtMgA` the closed test accepts.** Conditional on `P5J.AtMgA`. No instance of this
hypothesis is exhibited in this file. -/
theorem rngWritten_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : rngWrittenB = true := by
  unfold rngWrittenB rngAllB
  rw [← cuts_head h]
  exact List.all_eq_true.2 fun l hl => rng_at h l (List.mem_range.1 hl)

/-- `rng_head_of` without `hW`. Conditional on `P5J.AtMgA`. -/
theorem rng_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    (rngIn ((spotsOf Zp.cuts).getD []) l).isSome = true :=
  rng_head_of h (rngWritten_of_head h) l hl

/-- `site_digits_of` without `hW`: a site at every link below 25, of either sort. Conditional on
`P5J.AtMgA`. -/
theorem site_digits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (d : Bool) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = d ∧ s.at_.place = IM.k3Place l d ∧
      s.at_.place ∈ P5J.At.ps :=
  site_digits_of h (rngWritten_of_head h) l hl d

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.rngWritten_of_head
#print axioms ProofFile.Honest.K3.Law.AtThr.rng_head
#print axioms ProofFile.Honest.K3.Law.AtThr.site_digits
