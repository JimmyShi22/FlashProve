-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Behind/PromiseStatement.lean: BEHIND A YES OF THE MERGE's DECISION, UNDER THE
LIBRARY's HYPOTHESIS ON THE PUBLIC FILES (`P5J.AtMgA`) AT THE FULL SIZE: NO MARK · THE PROMISE's SIX
BOOLS AT BORDER 347 · "THE SAMPLES ARE HELD" THERE · WHAT THE PUBLIC ITEMS THAT ARE OPEN THERE SAY
BESIDE THEIR BOOLS: FROM THE SAME FOUR AT BORDER 346 AND THREE NAMED FACTS ON THE STATE IN FRONT:
STATEMENTS ALONE: two definitions of propositions. NOTHING IS PROVED IN THIS FILE, and neither is
one of the library's goals: they are lemmas' statements. No thread of the honest side's frame, no
prover and no oracle string stands in them.

Why. The library has the promise behind the merge from the promise in front (`merge_t2_full`,
Johnson/Top/H0/MergeLaw/SecondTieFull.lean) at the composed meaning, with "the stored table
decodes", "every sampled tree shows its leaves" and "no collision" among what is promised: sentences
on oracle strings, which an honest side's frame does not hold. What is left of the promise without
these three is said here, in the letters `IM.XK` (Johnson/IMR/HandsDef.lean) at `P1K2.EQ`
(Johnson/P1K2R/TieTwo.lean), `samplesHeld` (Johnson/Desc/First/Borders.lean) and `pubP`.

  `RunsPassOfTests`      the eighteen fields of `RunsPass`
                         (Johnson/Top/H0/MergeLaw/KeepAtMerge.lean) across the decision's yes:
                         `runsPass_at_merge` (RunsPassAtMerge.lean of that folder) with the two
                         tests that it draws out of the table's condition (`ledgerB`; `lookOutC` at
                         the lookup on the calls) as premises in that condition's stead
  `PromiseBehindMerge`   the four behind from the four in front; the three facts on the state in
                         front: `MergeFront` (EntryFront.lean of that folder) · `Speaks` at the
                         head's link · `leavesLenB`

Limits. THE THREE FACTS ARE PREMISES; so are the four in front and the yes. The hypothesis is a
premise; it stands at the earlier hash. AT THE DECISION, not yet at the seated member's step.
Nothing on any property.
-/
import Johnson.K11R.LawAtMg
import Johnson.P1K2R.TieTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Behind
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Link Claim Wit)
open VerifiableInference.Desc.Sound (MgData mgAll CellsQ MsgT Mem linksFull psFull)
open VerifiableInference.Desc.First (S Meaning samplesHeld ledgerB)
open VerifiableInference.Desc.First.Look (lookOutC)
open VerifiableInference.Desc.First.MergeLaw (MergeFront Speaks leavesLenB RunsPass RunsAre)
open P5J (AtMgA mgAtAll TS)

/-- The statement on the runs. The letters: those of `runsPass_at_merge`. Not proved here; a lemma's
statement, none of the library's goals. -/
def RunsPassOfTests : Prop :=
  ∀ (Xi P Tok : Type) (rows cols nR : ℕ) (X : OnBytes.Model.Verify.Public)
    (D : MgData Xi P Tok rows cols nR X) (Pm : HeadMergeP) (l : Link S Claim) (iU3 lm : ℕ)
    (a b : S) (rs : List Fmt.RoundView),
    D.lk 24 = some l → RunsAre l X iU3 lm → headMergeDecide Pm a rs = .ok b →
    ledgerB a = true → lookOutC D.pubD.d3 24 false a = true → Speaks l a →
    leavesLenB a = true → RunsPass (D.Rd 24) Pm a b

/-- The statement on the promise. Not proved here; a lemma's statement, none of the library's goals.
-/
def PromiseBehindMerge : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl)
    (xM : Mem) (R ni : ℕ) (z : ProofFile.InstPub) (s s' : S) (rs : List Fmt.RoundView),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    cF.links[24]? = some Lk →
    headMergeDecide (K11.parOf Zp Bs.G₀) s rs = .ok s' →
    MergeFront (h.𝔇.N.group 24) xM R ni s → Speaks Lk s → leavesLenB s = true →
    s.failed = none →
    IM.XK h.𝔇.N linksFull psFull (P1K2.EQ (mgAtAll h) linksFull psFull z) 346 s = true →
    samplesHeld h.𝔇.N (mgAtAll h) (IM.openAt linksFull psFull 346) (z, s) = true →
    (∀ q ∈ P1K2.pubAt (mgAtAll h) linksFull psFull 346, (mgAtAll h).pubP q (z, s)) →
    s'.failed = none ∧
      IM.XK h.𝔇.N linksFull psFull (P1K2.EQ (mgAtAll h) linksFull psFull z) 347 s' = true ∧
      samplesHeld h.𝔇.N (mgAtAll h) (IM.openAt linksFull psFull 347) (z, s') = true ∧
      ∀ q ∈ P1K2.pubAt (mgAtAll h) linksFull psFull 347, (mgAtAll h).pubP q (z, s')

end Johnson.Desc.First.ForkMerge.Behind

#print axioms Johnson.Desc.First.ForkMerge.Behind.RunsPassOfTests
#print axioms Johnson.Desc.First.ForkMerge.Behind.PromiseBehindMerge
