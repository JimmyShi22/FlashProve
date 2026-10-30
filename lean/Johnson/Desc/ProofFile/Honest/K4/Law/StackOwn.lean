-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackOwn.lean: CONDITIONAL.

What is here. The batched sumcheck's own claim is worth 0 on the honest part's rounds, AT THE HONEST
JOB: the joining of FlatStack.lean (the claim's worth, at a free job), StackCube.lean (four of the
five premises on the job, from its fitting the call) and StackFinAt.lean (the verifier's summand is
the job's on what was sent).

  `stack_own`   **the own claim is worth 0**

Limits. At the reading `Reading.gl`. THREE THINGS STAY HYPOTHESES: THE START (hσ: the start form is
worth the reading of the cube's total); hsides (the two numbers which the verifier's function makes
of the true end values read as the two long vectors' extensions at the challenges); THE SIX TIES
between the honest side and the verifier (hv, he, hzt, hom, hsh, hPy with hPT). Beside them: the
challenges fit the call; the part, played alone, makes the rounds, which the tape holds; the world
holds the part's hiding coins under the sumcheck's own slots; the maker of the job's data returns
and the job fits its call; the verifier's text returns, from a sized ledger. The maker of the part's
job is a free letter that returns the honest job at this entry: that it is the row's is not said
here. No example of the premises together is known. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatStack
import Johnson.Desc.ProofFile.Honest.K4.Law.StackCube
import Johnson.Desc.ProofFile.Honest.K4.Law.StackFinAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Fork World powers)
open OnBytes.Model.Layer (HeardStack callsTS nEndT)
open OnBytes.PscRun (Sized)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Tape)
open OnBytes.Road (pt)
open OnBytes.Desc.First.P1 (tapeEps)
open OnBytes.Desc.First.K4 (engFl hearStack)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.Part.MaskedSum
open ProofFile.Honest.SumLaw

variable {V W X : Type}

/-- **The batched sumcheck's own claim is worth 0 on the honest part's rounds, at the honest job.**
job: the maker of the part's job; D: the data of the honest job that it returns at this entry. tp:
the tape, the batching round first. -/
theorem stack_own (name endName : String) {P : OnBytes.Model.Layer.Pub}
    {v : OnBytes.Model.Layer.Env} {H : OnBytes.Model.Layer.Heard} {NCLp : ℕ} {Q : K4Pub}
    {w : K4In} {p : Pts} {shownT : Array E} {D : StackData}
    (job : W → Front X → Option Job)
    (c : SumCoins name endName
      (k4SumJob (k4PlainShape Q.hp.lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job))
    (st : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (F : Fork) (Wd : World GE) {G : Fork} {tp u : Tape} {K : HeardStack}
    (hd : drawsOk ((k4SumJob (k4PlainShape Q.hp.lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job).callAt
      st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName
      (k4SumJob (k4PlainShape Q.hp.lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job)) c st seen ds =
        some rounds)
    (hs : ∀ i, i < ownSlots ((k4SumJob (k4PlainShape Q.hp.lamS 2 (2 + (1 + P.y.LamM) + NCLp))
      job).callAt st.input (frontOf st seen)).all → Wd.slot (F.next + i) = hidingCoin c i)
    (hD : stackData Q w p shownT = some D) (hlam : D.S.Q.hp.lamS = Q.hp.lamS)
    (hj : job st.input (frontOf st seen) = some (jobStackOn D))
    (hfit : k4JobFits (k4PlainShape Q.hp.lamS 2 (2 + (1 + P.y.LamM) + NCLp)) (jobStackOn D) =
      true)
    (hF : hearStack engFl P v H Q.hp.lamS NCLp F tp = some (K, G, u)) (hS : Sized F)
    (hT : TapeIs (tp.drop 1) rounds)
    (hσ : ∀ C, OnBytes.Desc.First.K4.joinStart engFl v H (powers (tapeEps tp) 2) F (tp.drop 1) =
      some (C, F, tp.drop 1) → C.value Reading.gl Wd = Reading.gl.val (jobStackOn D).cube.total)
    (hsides : ∀ (rb : Array E) (l : List E), rb.size = D.S.Q.hp.lamS → D.endsAt rb = some l →
      ∃ x, D.sidesOn rb l.toArray = some x ∧
        Reading.gl.val x.1 = Blocks.ext D.S.Q.hp.lamS
          (fun i => Reading.gl.val (D.SA.getD i zeroE)) (pt Reading.gl rb.reverse) ∧
        Reading.gl.val x.2 = Blocks.ext D.S.Q.hp.lamS
          (fun i => Reading.gl.val (D.SB.getD i zeroE)) (pt Reading.gl rb.reverse))
    (hPy : P.y = Q.P.y) (hPT : callsTS P = callsTS Q.P)
    (hv : OnBytes.Desc.First.K4.Honest.envOf Q p = some v) (he : p.fo.e = H.fo.e)
    (hzt : ztOf Q p = H.ztF) (hom : p.om = powers (tapeEps tp) 2)
    (hsh : ∀ tT a, H.tT = some tT →
      ((Array.range (nEndT P.y)).mapM fun i => F.shown (tT.sEnd + i)) = some a → a = shownT) :
    K.rowS.value Reading.gl Wd = 0 := by
  have hfit' : k4JobFits (k4PlainShape D.S.Q.hp.lamS 2 (2 + (1 + P.y.LamM) + NCLp))
      (jobStackOn D) = true := by
    rw [hlam]
    exact hfit
  have hn0 : (jobStackOn D).cube.n = Q.hp.lamS := hlam
  obtain ⟨rv, s, _, _, es, hKr, hw⟩ := stack_worth (V := V) name endName job c st seen ds
    rounds F Wd hd ha hs (jobStackOn D) hj hfit hF hS hT hσ rfl
    (fun rs hr => stack_hn hfit' rs hr) (fun rs => stack_hP D rs _) (fun rs => stack_hA D rs)
    (fun rs hr => stack_hE hfit' (by omega) hsides rs hr)
  rw [hw, hn0, es, stack_hfin hD hF hS hPy hPT hv he hzt hom hsh _ hKr, sub_self, mul_zero]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.stack_own
