-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/TailAtW.lean:
THE TAIL AT rowsW's WRITTEN VALUES, FROM SEVEN CLOSED FACTS, ONE A CHAIN. Definitions and theorems.
A law file; no running text imports it.
  `twL0` … `twL6`   the seven chains of twinsL (Twin.lean), by name.   `twinsL_is`: twinsL is their
                    list: by rfl.
  `k0N`, `k1N`, `k2N`   the key file's three chains of sendings, made along the runs of the written
                    plans: in the manner of p0R (Johnson/AtFull/Sends/ProofFirst.lean);
                    the entry's is enR (Johnson/AtFull/Sends/ProofLater.lean).
  `tailPassB r c`   r returns, and at what it returns the chain c passes the tail.   `tailPass_ok`.
  `k0N_ok`, `k1N_ok`, `k2N_ok`   where these return, so do the steps that sendsFrom_of_parts needs
                    (Johnson/AtFull/Made/SendsLedger.lean), at the plans themselves (by oneOf_walk).
  `tailL_of_facts`  MAIN: seven closed facts ⊢ (tailFrom cW sW (twinsL cW (List.replicate 25 1)
                    13)).toOption.isSome = true: the premise ht of rows_of_partsL, to the letter.
Limits. NO CLOSED FACT IS HERE: the seven premises of tailL_of_facts are owed, each in a file of its
own. It stands on p0_W, p1_W, p2_W of Johnson/AtFull/Sends/ (closed facts by the kernel) and on
sendsFrom_of_parts. At the written values alone. twL0 and twL4 are light twins (Twin.lean). Nothing
on what a radius means. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.TailCut
import Johnson.AtFull.Rows.Twin
import Johnson.AtFull.Rows.AtW
import Johnson.AtFull.Sends.SendsW
import Johnson.Desc.First.Link.Law.RowsRunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open Johnson.G.Runs (valRuns)
open Johnson.AtFull.Sends (W enR p0_W p1_W p2_W)
open Johnson.AtFull.Made (sendsFrom_of_parts)
open VerifiableInference.Number.ByRuns (proofThree keyThree)

def twL0 : Johnson.G.Chain := twinOf cW.sized.set "key" 0 .once (key0L cW)
def twL1 : Johnson.G.Chain :=
  twinOf cW.sized.set "key" 1 (scOf cW.sized.key.once .shared) (key1R cW)
def twL2 : Johnson.G.Chain :=
  twinOf cW.sized.set "key" 2 (scOf cW.sized.key.once .request) (key2R cW)
def twL3 : Johnson.G.Chain := twinOf cW.sized.set "entry" 0 .once (entryR cW)
def twL4 : Johnson.G.Chain :=
  twinOf cW.sized.set "proof" 0 .request (proof0L cW (List.replicate 25 1) 13)
def twL5 : Johnson.G.Chain :=
  twinOf cW.sized.set "proof" 1 (scOf cW.sized.proof.batch .shared) (proof1R cW)
def twL6 : Johnson.G.Chain :=
  twinOf cW.sized.set "proof" 2 (scOf cW.sized.proof.batch .request) (proof2R cW)

theorem twinsL_is :
    twinsL cW (List.replicate 25 1) 13 = [twL0, twL1, twL2, twL3, twL4, twL5, twL6] := rfl

/-- The key file's first chain's sendings, made along the runs. -/
def k0N : Except String ChainSends :=
  (wSend W.sized.key.once.shape).bind fun w1 =>
    oneOfN "key" 0 W.sized.key.codes
      ([⟨"the index-mask message", [W.sized.key.once.input]⟩,
        ⟨"the multiplicities", (Wf.messageOf W.sized.key.ranges.x).toList⟩] ++
        ioppSends "the ranges' test" W.sized.set.samples W.sized.key.ranges.x.choice.masksRide 1
          W.sized.key.ranges.x.stages ++ [w1]) (valRuns keyThree.A.recs keyThree.A.runs)

/-- Its second chain's. -/
def k1N : Except String ChainSends :=
  (linSharedSends W.sized.key.once.shape W.sized.set.samples).bind fun s1 =>
    oneOfN "key" 1 W.sized.key.codes s1 (valRuns keyThree.B.recs keyThree.B.runs)

/-- Its third chain's. -/
def k2N : Except String ChainSends :=
  oneOfN "key" 2 W.sized.key.codes (ioppSends "the own test" W.sized.set.samples
    W.sized.key.once.shape.choice.masksRide 1 W.sized.key.once.shape.testOwn)
    (valRuns keyThree.C.recs keyThree.C.runs)

/-- r returns, and at what it returns the chain passes the tail. -/
def tailPassB (r : Except String ChainSends) (c : Johnson.G.Chain) : Bool :=
  match r with
  | .ok d => chainTailB sW c d
  | .error _ => false

theorem tailPass_ok {r : Except String ChainSends} {c : Johnson.G.Chain}
    (h : tailPassB r c = true) : ∃ d, r = .ok d ∧ chainTailB sW c d = true := by
  cases r with
  | error e => exact nomatch h
  | ok d => exact ⟨d, rfl, h⟩

set_option maxRecDepth 100000 in
theorem k0N_ok {K0 : ChainSends} (h : k0N = .ok K0) :
    ∃ w1, wSend W.sized.key.once.shape = .ok w1 ∧
      oneOf "key" 0 W.sized.key.codes
        ([⟨"the index-mask message", [W.sized.key.once.input]⟩,
          ⟨"the multiplicities", (Wf.messageOf W.sized.key.ranges.x).toList⟩] ++
          ioppSends "the ranges' test" W.sized.set.samples W.sized.key.ranges.x.choice.masksRide 1
            W.sized.key.ranges.x.stages ++ [w1]) keyThree.A.plan = .ok K0 := by
  unfold k0N at h
  cases hw : wSend W.sized.key.once.shape with
  | error e =>
    rw [hw] at h
    exact nomatch h
  | ok w1 =>
    rw [hw] at h
    exact ⟨w1, rfl, (oneOf_walk _ _ _ _ keyThree.A).trans h⟩

theorem k1N_ok {K1 : ChainSends} (h : k1N = .ok K1) :
    ∃ s1, linSharedSends W.sized.key.once.shape W.sized.set.samples = .ok s1 ∧
      oneOf "key" 1 W.sized.key.codes s1 keyThree.B.plan = .ok K1 := by
  unfold k1N at h
  cases hw : linSharedSends W.sized.key.once.shape W.sized.set.samples with
  | error e =>
    rw [hw] at h
    exact nomatch h
  | ok s1 =>
    rw [hw] at h
    exact ⟨s1, rfl, (oneOf_walk _ _ _ _ keyThree.B).trans h⟩

theorem k2N_ok {K2 : ChainSends} (h : k2N = .ok K2) :
    oneOf "key" 2 W.sized.key.codes (ioppSends "the own test" W.sized.set.samples
      W.sized.key.once.shape.choice.masksRide 1 W.sized.key.once.shape.testOwn) keyThree.C.plan =
      .ok K2 :=
  (oneOf_walk _ _ _ _ keyThree.C).trans h

/-- **The tail returns at the written values: from seven closed facts, one a chain.** -/
theorem tailL_of_facts (f0 : tailPassB k0N twL0 = true) (f1 : tailPassB k1N twL1 = true)
    (f2 : tailPassB k2N twL2 = true) (f3 : tailPassB enR twL3 = true)
    (f4 : chainTailB sW twL4 proofSendsFull.1 = true)
    (f5 : chainTailB sW twL5 proofSendsFull.2.1 = true)
    (f6 : chainTailB sW twL6 proofSendsFull.2.2 = true) :
    (tailFrom cW sW (twinsL cW (List.replicate 25 1) 13)).toOption.isSome = true := by
  obtain ⟨K0, e0, t0⟩ := tailPass_ok f0
  obtain ⟨K1, e1, t1⟩ := tailPass_ok f1
  obtain ⟨K2, e2, t2⟩ := tailPass_ok f2
  obtain ⟨En, e3, t3⟩ := tailPass_ok f3
  obtain ⟨w1, a1, b0⟩ := k0N_ok e0
  obtain ⟨s1, a2, b1⟩ := k1N_ok e1
  obtain ⟨w2, a3, b4⟩ := p0_W
  obtain ⟨s2, a4, b5⟩ := p1_W
  have hs : Johnson.G.sendsFrom W = .ok [K0, K1, K2, En, proofSendsFull.1, proofSendsFull.2.1,
      proofSendsFull.2.2] :=
    sendsFrom_of_parts (c := W) (k0 := keyThree.A.plan) (k1 := keyThree.B.plan)
      (k2 := keyThree.C.plan) (p0 := proofThree.A.plan) (p1 := proofThree.B.plan)
      (p2 := proofThree.C.plan) rfl rfl a1 a2 a3 a4 b0 b1 (k2N_ok e2) e3 b4 b5 p2_W
  rw [twinsL_is]
  exact tail_of_seven (c := cW) ((sendsFrom_same cW).symm.trans hs) t0 t1 t2 t3 f4 f5 f6

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.twinsL_is
#print axioms VerifiableInference.Desc.LinkJoin.tailPass_ok
#print axioms VerifiableInference.Desc.LinkJoin.k0N_ok
#print axioms VerifiableInference.Desc.LinkJoin.k1N_ok
#print axioms VerifiableInference.Desc.LinkJoin.k2N_ok
#print axioms VerifiableInference.Desc.LinkJoin.tailL_of_facts
