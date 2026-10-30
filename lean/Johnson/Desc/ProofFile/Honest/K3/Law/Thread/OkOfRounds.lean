-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/OkOfRounds.lean: the library's test on rounds
`okRoundsE` (Johnson/Top/H/K3LawKind.lean) yields `Good.Ok` (Honest/K3/Good/Levels.lean): every
sampled element's words are below the prime. So the clause on eps of
Honest/K3/Law/Thread/DigitsHeardLink.lean holds under the library's own test. Theorems; no
definition.

Terms. Honest/K3/GLOSSARY.md. In this file: eps is a field of the leaves' sumcheck in what was
heard.

What is shown.
  `ok_of_okRoundsE`: okRoundsE rs = true gives Good.Ok rs.
  `digits_heard_okE`: `digits_heard_site` (Honest/K3/Law/Thread/DigitsHeardLink.lean) with the
    clause on eps stated outright, where `okRoundsE` accepts.

Hypotheses that remain, in `digits_heard_okE`.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hs`, `hl`, `hd`: s is a site of the public part; its link is below 25; it is on the digits (`hl`
    follows from `h` and `hs`: `link_lt_head`, Honest/K3/Law/Thread/LinkLtHead.lean).
  Inside the statement: the member at the border, its accepting step, and `okRoundsE rs = true`.

Limits. Those of Honest/K3/Law/Thread/DigitsHeardLink.lean. At which rounds `okRoundsE` has been
seen to accept is not stated here. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsHeardLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain OpenedColumn)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (okRoundsE)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- **The library's test on rounds yields `Good.Ok`.** -/
theorem ok_of_okRoundsE (rs : List Fmt.RoundView) (h : okRoundsE rs = true) : Good.Ok rs := by
  intro r hr y hy
  have h1 := List.all_eq_true.1 h r hr
  exact List.all_eq_true.1 (Bool.and_eq_true_iff.1 h1).2 y hy

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- `digits_heard_site` with the clause on eps stated outright. Conditional on `P5J.AtMgA`, the site
and the library's test on the rounds. No instance of these hypotheses is exhibited in this file. -/
theorem digits_heard_okE (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link < 25) (hd : s.digits = true) :
    ∀ blk, cF.blocksInOrder[borderOf s.link true]? = some blk →
      ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
        blk.step ft sj rs c = .ok (sj', n) → okRoundsE rs = true →
        ∃ tl g, sj'.tl? = some tl ∧ tl.heard = some g ∧
          OpenSame g (lookHeardAt s.shape 0 (rs.map (·.drawn))) ∧
          g.cEnd.ents.isEmpty = true ∧ g.leaves.start.ents.isEmpty = true ∧
          g.leaves.eps = one rs (firstRound s.at_.face .leaves) := by
  intro blk hblk ft sj sj' n rs c hstep hok
  obtain ⟨tl, g, t1, t2, W, c1, l1, l2⟩ :=
    digits_heard_site h s hs hl hd blk hblk ft sj sj' n rs c hstep
  exact ⟨tl, g, t1, t2, W, c1, l1, l2 (ok_of_okRoundsE rs hok)⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.ok_of_okRoundsE
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_heard_okE
