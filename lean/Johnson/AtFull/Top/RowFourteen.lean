-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/RowFourteen.lean: THE FOURTEENTH ENTRY TEST's YES, FROM WRITTEN VALUES, WITH NO
USE OF protocolDataWellFormed. The test `rowsMadeB Z` (Johnson/Desc/First/Link/RowsRun.lean) asks that the rows of
the sendings can be made of what the proof file's public part Z holds, and that in the first proof
chain's rows one shape has one radius. General in Z. Calls alone: nothing is evaluated here. A law
file; no running text imports it.

Why. Where the verifier has fourteen entry tests, the proof file's seat returns only where this test
accepts, and `protocolDataWellFormed` accepts only where that seat returns. The library's laws that tie the test to
the arms and the written rows (`rowsMade_eq`, `rowsRead_of_yes`,
Johnson/Desc/First/Link/Law/RowsRunLaws.lean; `TocR.rowsRead_of_live`) take an accept of `protocolDataWellFormed`
as a premise: on the road to «protocolDataWellFormed accepts at the stored full-size files» that is a circle. By
its own text the test is `firstRun` at Z's own planner's value and arms: so neither `protocolDataWellFormed`, nor
the return of verify-on-bytes's planner, nor the pin `madePinnedAt`, nor the scope is wanted.

Statements.
  `rowsMadeB_of_written`: the four fields of Z's planner's value that do not hang on the digest are
    the written ones · its seven lists of sendings return, the fifth being the written `proofSends0`
    · the arms' test `armsB` accepts at Z's public data · the closed test `rowsWB` accepts ⊢
    rowsMadeB Z = true.
  `rowsMadeB_of_arms`: the same where `ProofFile.pubPlain` returns Z at the second hash function: the
    sendings' premise is then Z.made.proof.1 = proofSends0 (`sends_of_pub`,
    Johnson/HB/LLHARD/RadiiInScope.lean).
  `rowsMadeB_in_scope`: the same in the goals' scope, from an accept of the pin `madePinnedAt` in
    the two equations' place (`made_in_scope`, `sends_in_scope`,
    Johnson/Goal/Numbers/MadeInScope.lean). On the road to «protocolDataWellFormed accepts» the pin must then be
    paid at the value, not out of `P5J.pins_of_laid`, which stands behind protocolDataWellFormed.
  `arms_of_public`: the public data in what `ProofFile.pubPlain` returns are what `publicOfO` returns: so
    an accept of `armsB` at the second is one at the first.
How: `TocR.returns_of_B` · `rowsFrom_four`, `rowsFrom_congr` · `arm_at`, `links_W`, `groups_W` ·
`arms_give` (Johnson/AtFull/Made/ArmsGive.lean) · `first_block`, `calls_say` · `radii_written` ·
`P5T.radOne_of_radii` · `firstRun_eq`, `oneRadius_eq` · `ProofFile.Law.pub_public`.

Limits. EVERY PREMISE IS A PREMISE: NONE IS SHOWN HERE AT ANY FILES. `rowsWB = true` is closed. It
is a theorem of its own, in a file that this one does not import
(`rowsWB_true`, Johnson/AtFull/Rows/Rows.lean): out of closed facts that Lean's kernel bears
piece by piece. Asked whole, the kernel has not borne it. That the premises can be met together is
EVALUATED, NOT PROVED: by a sheet for Lean's evaluator, which is not in this repository: at what
`ProofFile.pubPlain` returns at the stored full-size files, the pin, `armsB` and `rowsWB` accept (so the
two equations hold there, by `made_in_scope` and `sends_in_scope`), and so does the test itself. No
negative test stands here: the library's `radOne_rejects` and `radii_rejects_short` bite the two
closed facts beneath. The test's text is one on the grounds with thirteen and with fourteen entry
tests; that the verifier asks it is not said here. The full size alone. Nothing on soundness.

-/
import Johnson.TocR.RowsReadOfFour
import Johnson.Desc.First.Link.Law.RowsRunLaws
import Johnson.HB.LLHARD.RadiiInScope
import Johnson.HB.LLHARD.RadOneWritten
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.AtFull.Made.ArmsGive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open Johnson.G.MadeFree (Free Hung freeOf)
open VerifiableInference.Number (sendsFrom)
open VerifiableInference.PlanWritten (proofSizedFull publicOfO madePinnedAt)
open VerifiableInference.PlanWritten.Joined (writtenMade made_in_scope sends_in_scope)
open VerifiableInference.Desc.LinkJoin

/-- **The fourteenth entry test accepts, from written values: no use of protocolDataWellFormed.** -/
theorem rowsMadeB_of_written {Z : ProofFile.Pub} {k0 k1 k2 e p1 p2 : ChainSends}
    (e1 : freeOf Z.made.p.chains.made = writtenMade)
    (hs : sendsFrom Z.made.p.chains.made = .ok [k0, k1, k2, e, proofSends0, p1, p2])
    (ha : armsB Z.made.p.X = true) (K : rowsWB = true) : rowsMadeB Z = true := by
  obtain ⟨R, hR⟩ := TocR.returns_of_B K
  obtain ⟨-, hN⟩ := Johnson.AtFull.Made.arms_give ha
  have eS : Z.made.p.chains.made.sized = writtenMade.sized := congrArg Free.sized e1
  have hl : Z.made.p.chains.made.sized.proof.request.link.length = 25 := by
    rw [eS]
    exact links_W
  have hr : rowsFrom Z.made.p.chains.made (List.replicate 25 1) 13 (armOf Z.made.p.X) =
      .ok R := by
    rw [rowsFrom_four (c := Z.made.p.chains.made) (c' := writtenMade.at Hung.none)
      (congrArg Free.sized e1) (congrArg Free.key e1) (congrArg Free.proof e1)
      (congrArg Free.entry e1), ← hR]
    unfold rowsW
    exact rowsFrom_congr _ _ _ fun j hj => arm_at ha j (by
      have := groups_W
      exact this ▸ hj)
  obtain ⟨a0, a1, a2, a3, p0, a5, a6, q, hs', hq, hrad⟩ :=
    first_block hr fun _ _ hc => calls_say hc
  have ep : p0 = proofSends0 := by
    have t := Except.ok.inj (hs'.symm.trans hs)
    simp only [List.cons.injEq] at t
    exact t.2.2.2.2.1
  rw [eS, ep] at hq
  have w := radii_written
  rw [show packChain recordSet "proof" 0 (samplesP0 proofSizedFull) proofSends0 = .ok q from hq]
    at w
  have hcol : (P5T.firstRows R).map (·.sampled) = radsFull := by
    rw [hrad]
    exact Option.some.inj w
  have hr' : rowsFrom Z.made.p.chains.made (List.replicate 25 1) (12 + 1) (armOf Z.made.p.X) =
      .ok R := hr
  unfold rowsMadeB
  rw [hl, hN, firstRun_eq, hr']
  show oneRadius ((P5T.firstRows R).flatMap (·.sampled)) = true
  rw [oneRadius_eq]
  exact P5T.radOne_of_radii hcol

/-- **The same where the plain road returns Z.** -/
theorem rowsMadeB_of_arms {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Z)
    (e1 : freeOf Z.made.p.chains.made = writtenMade) (es : Z.made.proof.1 = proofSends0)
    (ha : armsB Z.made.p.X = true) (K : rowsWB = true) : rowsMadeB Z = true := by
  obtain ⟨k0, k1, k2, e, hs⟩ := sends_of_pub h
  rw [es] at hs
  exact rowsMadeB_of_written e1 hs ha K

/-- **In the goals' scope, from the pin.** -/
theorem rowsMadeB_in_scope {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (ha : armsB Z.made.p.X = true) (K : rowsWB = true) : rowsMadeB Z = true := by
  have hroad : ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z := h
  exact rowsMadeB_of_arms h (made_in_scope hW hroad hy)
    (congrArg (·.1) (sends_in_scope hW hroad hy)) ha K

/-- **The arms' test at the public data that the plain road holds.** -/
theorem arms_of_public {o : VerifierAndGoals.SecondHashFunctionType} {pol lay KL : ByteArray}
    {X₀ : OnBytes.Model.Verify.Public} (hX : publicOfO o pol KL (some lay) = .ok X₀)
    (ha : armsB X₀ = true) {Zq : ProofFile.Pub} (hq : ProofFile.pubPlain o pol lay KL = .ok Zq) :
    armsB Zq.made.p.X = true := by
  have h := ProofFile.Law.pub_public (show ProofFile.pureRoad.pub o pol lay KL = .ok Zq from hq)
  obtain rfl : X₀ = Zq.p.X := Except.ok.inj (hX.symm.trans h)
  exact ha

end AtFull.Top

#print axioms AtFull.Top.rowsMadeB_of_written
#print axioms AtFull.Top.rowsMadeB_of_arms
#print axioms AtFull.Top.rowsMadeB_in_scope
#print axioms AtFull.Top.arms_of_public
