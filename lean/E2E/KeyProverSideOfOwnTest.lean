-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyProverSideOfOwnTest.lean: the prover's side of the key file's own proximity test (the test of its last
chain): the job `jobKW` (E2E/KeyJobW.lean) at the state on entry `doorW`
(Johnson/Desc/ProofFile/Honest/K12/DoorLast.lean) of the key file's description; the pair of parts
behind the guard; and a test that says whether the state on entry fell back on its default. It is
HalfW.lean and AtHandW.lean (Johnson/Desc/ProofFile/Honest/K12/AtProof/) at the key file's
description.

  pWK            the test's numbers, as the chain lays them
  doorKW         the state on entry: doorW at Key.descriptionFromSource, at the seat's own way in
  jobKWAt, proverSideOfGuardedSending   the job; its pair behind the guard (K12/FieldGuard.lean)
  jobKWAt_rec    its state on entry is doorKW
  door_key_at_called, atHandKW_at_run   at a called part of the key's last chain, at a run of the
                 walk, the default is not taken: door_last_at_called and atHandW at Key.descriptionFromSource
  atHandKW_reads the test reads the instance and what is seen alone

Parameters: JI, JW (the two sendings' jobs, with their data), A, lift, ask. No value of KeyParts is
named here; `withTests` (E2E/TheHonestProver.lean) lays `proverSideOfGuardedSending` as the field `own` of the offline
prover's senders. By K1's types the two sendings read one input here; that a prover's sendings are
these two is not shown here.

Limits.
- Those of HalfW.lean and AtHandW.lean. The two theorems at a run speak of the walk (`runC`,
  `midAtW`) and are conditional: on hpl, hR, S, hrun and hc; `atHandKW_at_run` on hpre too: that the
  blocks in front are those that the door takes. That a move lays a front of the form that they name
  is not shown here. hpl is the field `plan` of `KeyNamed` (E2E/KeyProtocolOverDescription.lean). hpre does not
  hold by rfl: the third block's place reads proximityTestKind's match at Pl.W (Johnson/Desc/K12/Frame.lean); no
  proof of it is given here.
- The door's default stands in its text: `idleT12`, a state of defaults that reads no input.
- All letters are free here, and no test on the shape stands around the pair: see `proverSideOfGuardedSending`'s
  docstring.
- No layFits at this test. Nothing on whether a row that the test reads is the row that the sender
  sent.
- What the state on entry reads: the head of E2E/KeyJobW.lean. On hiding nothing is said of this
  test: `atHandKW_reads` says what the test reads, and no more; the sentence in AtHandW.lean's head
  on its test's verdict speaks of the proof file's test.
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeyJobW
import Johnson.Desc.Key.Desc
import Johnson.Desc.ProofFile.Honest.K12.AtProof.AtHandW
import Johnson.Desc.ProofFile.Honest.K12.FieldGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLay
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.Key (descriptionFromSource Xi Claim Source LaterPlaces)
open VerifiableInference.Desc.K12 (P12 T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Local Placed StandsAt ready runC
  midAtW Front)
open ProofFile.Honest.K14 (SendPub Ask)
open ProofFile.Honest.K12 (proverSideOfProximityTest TestJob)
open ProofFile.Honest.K12.Light (ManyJob doorW atHandLast door_last_at_called atHand_of_try
  enterOwn_returns colsOpened)
open ProofFile.Honest.K12.AtProof (placeW idleT12 atHandW atHandW_reads)

/-- The numbers of the key's own test, as the chain lays them. -/
abbrev pWK (Pl : LaterPlaces) : P12 := H2U.proximityTestParametersAt placeW Pl.W

/-- **The state on entry at the key's own test.** -/
abbrev doorKW {W₀ Rc Tr Y : Type} (X : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) :
    Local W₀ Rc Xi Tr → Front Y → T12 :=
  doorW (descriptionFromSource X N Pl) (·.x) enterOwn placeW idleT12

section
variable {W₀ Rc Tr Y Wd : Type}

/-- **The job.** n₁: the first chain's rounds, as the description has them. -/
def jobKWAt (X : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (JI JW : ProofFile.Honest.K1.SendJob Wd Y) (A : SendPub) (lift : Local W₀ Rc Xi Tr → Wd)
    (ask : Local W₀ Rc Xi Tr → Ask) : ManyJob (Local W₀ Rc Xi Tr) Y :=
  jobKW (pWK Pl) (doorKW X N Pl) JI JW A lift ask
    ((descriptionFromSource X N Pl).first.blocksInOrder.flatMap (·.rounds)).length

/-- **The pair behind the guard.** Its letters are free here, and no test on the shape stands around
it: where `ask` is `askOf`, it reads `rowsOf`, which lays an entry of the weights' matrix where a
pad is due at a shape whose matrix's places run into the pads
(Johnson/Desc/ProofFile/Honest/K14/Parts.lean); `LinShape.ok` refuses such a shape. `withTests`
(E2E/TheHonestProver.lean) lays the pair at the senders' own letters. At `thePartsAt` the shape is
the key's, which passes that test at public files that pass the head's test: read off
`sourced_of_ok`, `third_public` and `linOk_ok`, which no one theorem joins. -/
def proverSideOfGuardedSending {V : Type} (X : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (JI JW : ProofFile.Honest.K1.SendJob Wd Y) (A : SendPub) (lift : Local W₀ Rc Xi Tr → Wd)
    (ask : Local W₀ Rc Xi Tr → Ask) : Placed V (Local W₀ Rc Xi Tr) Y :=
  (proverSideOfProximityTest (jobKWAt X N Pl JI JW A lift ask).toRun.toTest :
    Placed V (Local W₀ Rc Xi Tr) Y).needsField

/-- Its state on entry. -/
theorem jobKWAt_rec (X : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (JI JW : ProofFile.Honest.K1.SendJob Wd Y) (A : SendPub) (lift : Local W₀ Rc Xi Tr → Wd)
    (ask : Local W₀ Rc Xi Tr → Ask) :
    (jobKWAt X N Pl JI JW A lift ask).toRun.toTest.rec₀ = doorKW X N Pl := rfl

end

/-- **At the key file's description and the seat's way in, at a called part of the last chain of a
run, the door is at hand** at every front of that form. That a move lays such a front is the
caller's. -/
theorem door_key_at_called {W₀ Rc Ky Tr X₀ Y V Pb : Type} {X : Source} {N : H2U.PlaceNums}
    {Pl : LaterPlaces} {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi}
    {c : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC (descriptionFromSource X N Pl)}
    (hpl : (descriptionFromSource X N Pl).planOk = true)
    (hR : ready (descriptionFromSource X N Pl) Bk P w₀ rc x c = .ok R)
    (σ : Side S₃ Claim V (Local W₀ Rc Xi Tr) Y Pb)
    (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block S₃ Claim)) (i : ℕ)
    (S : StandsAt (descriptionFromSource X N Pl).second.blocksInOrder R.second σ u pre t i)
    (hrun : runC (descriptionFromSource X N Pl) Bk P w₀ rc x c ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (tr : Tr),
      midAtW (descriptionFromSource X N Pl) Bk P w₀ rc x c ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      m.seen.length = ((descriptionFromSource X N Pl).first.blocksInOrder.flatMap (·.rounds)).length +
        ((descriptionFromSource X N Pl).shared.blocksInOrder.flatMap (·.rounds)).length +
        (pre.flatMap (·.rounds)).length + i ∧
      ∀ {W : Type} (xOf : W → Xi) (w : W) (fr : Front Y) (k : ℕ), xOf w = x →
        ((descriptionFromSource X N Pl).first.blocksInOrder.flatMap (·.rounds)).length +
          ((descriptionFromSource X N Pl).shared.blocksInOrder.flatMap (·.rounds)).length +
          (pre.flatMap (·.rounds)).length ≤ k →
        fr.seen.rounds = m.seen.take k → fr.seen.opened = m.opened →
          atHandLast (descriptionFromSource X N Pl).first.blocksInOrder (descriptionFromSource X N Pl).shared.blocksInOrder pre
            (descriptionFromSource X N Pl).lastChainFirstTreeNumber
            (fun w => (descriptionFromSource X N Pl).start₁ ((descriptionFromSource X N Pl).pub (xOf w)))
            (fun w => (descriptionFromSource X N Pl).start₂ ((descriptionFromSource X N Pl).pub (xOf w)))
            (fun w => (descriptionFromSource X N Pl).start₃ ((descriptionFromSource X N Pl).pub (xOf w)))
            enterOwn colsOpened w fr = true := by
  obtain ⟨m, -, -, -, s, -, tr, hm, hin, hl, -, -, -, -, -, hd⟩ :=
    door_last_at_called hpl hR σ u pre t i S hrun hc
  refine ⟨m, tr, hm, hin, hl, fun xOf w fr k hx hk hfr hop => ?_⟩
  exact atHand_of_try _ _ _ _ _ _ _ _ _ w fr
    (hd xOf w enterOwn fr k hx hk hfr hop) (enterOwn_returns s)

/-- **At a called part of the key's last chain the default is not taken**, at every front of that
form, at the test's place. hpre: the blocks in front are those that doorW takes. -/
theorem atHandKW_at_run {W₀ Rc Ky Tr X₀ Y V Pb : Type} {X : Source} {N : H2U.PlaceNums}
    {Pl : LaterPlaces} {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi}
    {c : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC (descriptionFromSource X N Pl)}
    (hpl : (descriptionFromSource X N Pl).planOk = true)
    (hR : ready (descriptionFromSource X N Pl) Bk P w₀ rc x c = .ok R)
    (σ : Side S₃ Claim V (Local W₀ Rc Xi Tr) Y Pb)
    (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block S₃ Claim)) (i : ℕ)
    (S : StandsAt (descriptionFromSource X N Pl).second.blocksInOrder R.second σ u pre t i)
    (hpre : (descriptionFromSource X N Pl).second.blocksInOrder.takeWhile (·.place != placeW) = pre)
    (hrun : runC (descriptionFromSource X N Pl) Bk P w₀ rc x c ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y,
      midAtW (descriptionFromSource X N Pl) Bk P w₀ rc x c ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.seen.length = ((descriptionFromSource X N Pl).first.blocksInOrder.flatMap (·.rounds)).length +
        ((descriptionFromSource X N Pl).shared.blocksInOrder.flatMap (·.rounds)).length +
        (pre.flatMap (·.rounds)).length + i ∧
      ∀ (fr : Front Y) (k : ℕ),
        ((descriptionFromSource X N Pl).first.blocksInOrder.flatMap (·.rounds)).length +
          ((descriptionFromSource X N Pl).shared.blocksInOrder.flatMap (·.rounds)).length +
          (pre.flatMap (·.rounds)).length ≤ k →
        fr.seen.rounds = m.seen.take k → fr.seen.opened = m.opened →
          atHandW (descriptionFromSource X N Pl) (·.x) enterOwn placeW m.st.input fr = true := by
  obtain ⟨m, tr, hm, hin, hl, hd⟩ := door_key_at_called hpl hR σ u pre t i S hrun hc
  refine ⟨m, hm, hl, fun fr k hk hfr hop => ?_⟩
  have e := hd (fun w : Local W₀ Rc Xi Tr => w.x) m.st.input fr k (by rw [hin]) hk hfr hop
  unfold atHandW
  rw [hpre]
  exact e

/-- **The test reads of the input the instance alone, and of the front what is seen alone.** -/
theorem atHandKW_reads {W₀ Rc Tr Y : Type} (X : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (w w' : Local W₀ Rc Xi Tr) (fr fr' : Front Y) (hp : w.x = w'.x) (hs : fr.seen = fr'.seen) :
    atHandW (descriptionFromSource X N Pl) (·.x) enterOwn placeW w fr =
      atHandW (descriptionFromSource X N Pl) (·.x) enterOwn placeW w' fr' :=
  atHandW_reads _ _ _ _ _ _ _ _ (congrArg _ hp) hs

end AtPublicFiles.KeyLay

#print axioms AtPublicFiles.KeyLay.pWK
#print axioms AtPublicFiles.KeyLay.doorKW
#print axioms AtPublicFiles.KeyLay.jobKWAt
#print axioms AtPublicFiles.KeyLay.proverSideOfGuardedSending
#print axioms AtPublicFiles.KeyLay.jobKWAt_rec
#print axioms AtPublicFiles.KeyLay.door_key_at_called
#print axioms AtPublicFiles.KeyLay.atHandKW_at_run
#print axioms AtPublicFiles.KeyLay.atHandKW_reads
