-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeValues15.lean: THE KEY FILE's FIRST CHAIN: WHAT THE FRAME's RULE ASKS OF THE VALUES AT
THE RANGES' PROXIMITY TEST COMES DOWN TO ONE TEST: where a thread stands at the border in front of
that test, in the goals' scope, the named test on values of E2E/KeyShapeFirstAll.lean's letters
accepts as soon as its last clause does. A join: calls. NOTHING IS SHOWN OF ANY PROVER.

  `gRng_six`: under E2E/KeyShapeFullTies.lean's six equations the ranges' test's guard returns at
    `T15`.
  `vals15_is`: under them the letters' named test at number 15 is E2E/KeyRangesReturns.lean's
    `vRng`.
  `pre_len`: in scope fifteen sub-protocols stand in front of that test.
  **`values15`**: at a thread at the border 15, in scope: from `valsK12` alone. By
    E2E/KeyRangesShape15.lean's `shape15_of_thr` and E2E/KeyMarksThr.lean's `vRng_of_thr`: CALLED.

Limits.
- `valsK12` stays: it runs the test's own parts and asks the base case's whole decision: the algebra
  is all owed.
- That a thread stands at that border is a premise.
- Another road ends at the same number: E2E/KeyRangesSeated.lean's `accepted_ranges`, which does not
  go through `valsK12`; no statement ties the two; where that one is taken this file's premise is
  owed by nobody.


-/
import E2E.KeyShapeFirstMore
import E2E.KeyRangesShape15
import E2E.KeyMarksThr

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open ProofFile.Honest
open H2K.Member (nKRFull)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces rangesParams)
open ProofFile.Honest.Sh (valsK12)

/-- Under the six equations the ranges' test's guard returns at the term in front of it. -/
theorem gRng_six {Q : Pub1} (h : Six Q) : gRng Q nKRFull T15 = .ok T16 := by
  have e0 : Q = ⟨Q.one, Q.set⟩ := rfl
  have e1 : gRng ⟨Q.one, Q.set⟩ nKRFull T15 = gRng ⟨normOne Q.one, Q.set⟩ nKRFull T15 := rfl
  rw [e0, e1, norm_six h, h.set]
  exact step15

/-- Under the six equations the letters' named test at number 15 is the ranges' test's. -/
theorem vals15_is {Q : Pub1} (h : Six Q) (cs : Codes) (D : List Fmt.DeclaredRound)
    (told : List ProofFile.Root) (N : H2U.PlaceNums) : (Z₁A Q cs D told N).vals 15 = vRng N := by
  show vOf ((gvAll₁ Q cs D told N (vRng N)).map (·.2)) 15 = vRng N
  rw [snd_six h]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- In scope fifteen sub-protocols stand in front of the ranges' test. -/
theorem pre_len (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) :
    (H2K.JointK.keyFirstPre X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N).length = 15 := by
  obtain ⟨bw, hw, -, -, -⟩ := public_first_sourced hs scope
  obtain ⟨-, -, -, hlen, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  have e := congrArg List.length (flat₁_cut (pubOf X) X.Y.D.1 X.Y.told.1 N bw hw)
  have hlen' : (flat₁ (pubOf X) X.Y.D.1 X.Y.told.1 N).length = 19 := hlen
  rw [hlen', List.length_append] at e
  have e' : 19 = (H2K.JointK.keyFirstPre X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N).length + 4 := e
  omega

/-- **At a thread at the border 15, in scope: the named test on values from its last clause alone.**
-/
theorem values15 {V W Xh Pb : Type} {Bk : ProverCoinCounts} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    {k : Coins Bk} {e : (keyFileDescription X N P).S₁} {m : Mid W Xh} {E : Env} (h : Thr T₁ 15 k e m E)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hv : valsK12 (rangesParams N) (rangesState e) rs gs = true) :
    (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N).vals 15 e rs gs = true := by
  have h6 := six_sourced hs scope
  have hN := nums_sourced hs scope
  have e15 := shape15_of_thr hs scope T₁ hbs hbeg h
  have hg : gRng (pubOf X) N (sh₁B (pubOf X) CF e) = .ok T16 := by
    rw [e15, hN]
    exact gRng_six h6
  rw [vals15_is h6]
  exact vRng_of_thr (pubOf X) CF (pre_len hs scope) T₁ hbs hbeg h N hg rs gs hv

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.gRng_six
#print axioms AtPublicFiles.AtFiles.Full.vals15_is
#print axioms AtPublicFiles.AtFiles.Full.pre_len
#print axioms AtPublicFiles.AtFiles.Full.values15
