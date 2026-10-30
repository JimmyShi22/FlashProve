-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RngHead.lean: under the library's hypothesis `P5J.AtMgA`
the public part's table of stretches is the written table; so the 25 public tests that
`site_there_head` (Honest/K3/Law/Thread/SiteThereHead.lean) leaves at the digits narrow to one
closed test, in which no letter of a public file stands. Two definitions; theorems; two tests by
evaluation.

Terms. Honest/K3/GLOSSARY.md. In this file: the public part's table of stretches is its field cuts.
The written table is `cutWritten` (Johnson/AtFull/Cut/CutWrittenLit.lean).

What is shown.
  `cuts_head`: Zp.cuts is `cutWritten`: a theorem.
  `rngAllB cs`: (definition) the test at a table cs: `rngIn` (Honest/K3/Lot.lean) returns a number
    at each of the 25 links.
  `rngAll_at`: what an acceptance of it gives, link by link.
  `rngWrittenB`: (definition) the closed test: `rngAllB` at the written table.
  `rng_head_of`: where the closed test accepts, `rngIn` returns a number at the public part's own
    table, at every link below 25.
  `site_digits_of`: hence `site_there_head` with the closed test in the place of its hypothesis on
    the table.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hW`: (in the last two theorems) rngWrittenB = true.
  `hl`: the link's number is below 25.
  `h`: (in `rngAll_at`) rngAllB cs = true.

How the proof goes. The proofs call the library's `P5J.AtMg.plans_written`
(Johnson/P5J/NumbersAtHead.lean), `H2K5.Row.cuts_of_plans` and `H2K5.Row.asBy`
(Johnson/Desc/First/Att/Row/K5FrontOne.lean).

Users. Honest/K3/Law/Thread/RngWrittenHolds.lean and Honest/K3/Law/Thread/RngHeadPaid.lean import
this file.

Limits. In this file the closed test is evaluated, not proved. Lean's evaluator finds it true when
this file is compiled (the first of the two `#guard` lines); the second shows that it can fail:
without the row "G0.4.call" it is false. "rngWrittenB = true" remains a hypothesis of the last two
theorems: Lean's kernel does not decide it: its reduction gets stuck in `String.splitOn`, by which
the table's places are numbered (`headOf`, Johnson/Desc/ProofFile/Places.lean). Since: `rng_at`
(Johnson/AtFull/Shape/SitesAtHead.lean) states under `P5J.AtMgA`, without the
closed test, that `rngIn` returns a number at every link below 25.
Since, too:
`rngWritten_holds` (Honest/K3/Law/Thread/RngWrittenHolds.lean) proves rngWrittenB = true, without a
hypothesis, by a way round that reduction; `rng_head_paid` and `site_digits_paid` there are the last
two theorems without `hW`. On public data alone. At the full size alone: that limit comes with
`P5J.AtMgA`. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThereHead
import Johnson.P5J.NumbersAtHead
import Johnson.Desc.First.Att.Row.K5FrontOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain)
open Johnson.AtFull.Cut (cutWritten)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- At a table of stretches: `rngIn` returns a number at each of the 25 links. -/
def rngAllB (cs : List VerifiableInference.Desc.First.Cut) : Bool :=
  (List.range 25).all fun l => (rngIn ((spotsOf cs).getD []) l).isSome

/-- What an acceptance gives, link by link. -/
theorem rngAll_at (cs : List VerifiableInference.Desc.First.Cut) (h : rngAllB cs = true) (l : Nat)
    (hl : l < 25) : (rngIn ((spotsOf cs).getD []) l).isSome = true :=
  List.all_eq_true.1 h l (List.mem_range.2 hl)

/-- **The closed test**: at the written table. -/
def rngWrittenB : Bool := rngAllB cutWritten

#guard rngWrittenB
#guard !rngAllB (cutWritten.filter fun c => c.look != "G0.4.call")

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under `P5J.AtMgA` the public part's table of stretches is the written table.** -/
theorem cuts_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : Zp.cuts = cutWritten :=
  H2K5.Row.cuts_of_plans (H2K5.Row.asBy h.laid.pub) (congrArg (·.1) h.toAtMg.plans_written)

/-- Where the closed test accepts, `rngIn` returns a number at the public part's own table.
Conditional on `P5J.AtMgA` and the closed test. -/
theorem rng_head_of (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hW : rngWrittenB = true)
    (l : Nat) (hl : l < 25) : (rngIn ((spotsOf Zp.cuts).getD []) l).isSome = true := by
  rw [cuts_head h]
  exact rngAll_at cutWritten hW l hl

/-- **A site at every link below 25, of either sort.** Conditional on `P5J.AtMgA` and the closed
test. No instance of these hypotheses is exhibited in this file. -/
theorem site_digits_of (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hW : rngWrittenB = true)
    (l : Nat) (hl : l < 25) (d : Bool) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = d ∧ s.at_.place = IM.k3Place l d ∧
      s.at_.place ∈ P5J.At.ps :=
  site_there_head h l hl d fun _ => rng_head_of h hW l hl

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.rngAll_at
#print axioms ProofFile.Honest.K3.Law.AtThr.cuts_head
#print axioms ProofFile.Honest.K3.Law.AtThr.rng_head_of
#print axioms ProofFile.Honest.K3.Law.AtThr.site_digits_of
