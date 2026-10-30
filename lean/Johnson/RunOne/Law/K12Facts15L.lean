-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15L.lean: THE ERRORS AT WHICH THE PROXIMITY TEST's LAW STANDS AT A SEAT LIE BELOW THE CAP: each round's count is at most 2⁻¹²⁸ of that round's own written verifier messages: FROM TWO TESTS ON THE PLAN, WITHOUT "the place's chain is there". Statements with proofs. GENERAL IN THE PLACE. IT PAYS NO FIELD OF THE KEY FILE's TABLES.
OBJECT. The pair (batV0 π r * the batching's round's weight, errJ π r dt) (Johnson/Desc/K12/Coin/GameJ.lean) over a stretch dB :: dt that is like the place's written rounds.
USER. Johnson/RunOne/Law/K12Facts15LS.lean (the premise Le15 of row 1.15).
LETTERS. π, the radii r, the brackets B, dB, dt: free.
WHY WITHOUT THE CHAIN. errJ is, by its own text, the list of zeros where the place's stages and written rounds make no chain. So the test that holds the written rounds against a state's codes (pubOk), which the kind's files' condition asks so that the chain is there, is not needed for a bound on errJ.

  smallOk_of_test: the test on the chain's counts says yes where the place's own test on numbers (its stages, radii, brackets and bits of work) is a test that says yes, and the block's test on the plan does. The last lines of k12Condition_of_test (Johnson/Desc/K12/Law/CondOfTest.lean), as a statement of their own: they do not spend pubOk.
  zero_below: the list of zeros is below every bound.
  pair_below: the statement.
  pair_le_cap: so the pair lies at or below the cap at 128.
Limits. One round at a time: no sum over rounds. The written verifier messages hold the bits of work. That a count bounds a prover's chance is the law's. It stands over files of Johnson/Bridge/ (see those files' heads on what they rest). Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.K12.Coin.LawAtO
import Johnson.Desc.K12.Coin.GameJ
import Johnson.Desc.K12.Law.BatValsPayAt
import Johnson.Desc.K12.Law.CondOfTest
import OnBytes.Flat.CarrySBelow
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Facts15
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open H2K.Pub (sgOf writtenOf WR chainFrom batV0 batPriceOk smallOk smallAll testOf made_of_planOk okFrom_of_test walk_small small_of_ok)
open Johnson.Bridge (Br TestAt)
open OnBytes.Flat (wT toRD card_wT)
open scoped ENNReal

/-- **The test on the chain's counts, from the place's own test on numbers and the block's test on the plan.** -/
theorem smallOk_of_test {Cl : Type} (rad : Sg → ℕ) (B : Sg → Br × Br) (p : P12) (T : TestAt)
    (hT : testOf rad B p = some T) (hok : T.ok = true)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Cl).planOk = true) : smallOk rad B p = true := by
  obtain ⟨a, rest, ls, R, sh, w0, w, hs, hne, hR, hl, hw, hF, hk⟩ := made_of_planOk p hp
  have hO := okFrom_of_test rad B p T hT hok a rest hs
  unfold smallOk smallAll
  rw [hs, hw]
  exact walk_small _ _ rest a false 0 0 0 ls R sh w (fun h => absurd h hne) hR hl hF hk hO

theorem zero_below : ∀ (s : Shape) (b : ℝ≥0∞), Err.Below (Err.zero s) b
  | [], _ => trivial
  | _ :: s, b => ⟨by simp, zero_below s b⟩

/-- **Each round's count is at most 2⁻¹²⁸ of its own written verifier messages.** -/
theorem pair_below (π : P12) (r : Fmt.M1.Stage → ℕ) (B : Sg → Br × Br) (dB : RDT) (dt : List RDT)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hsm : smallOk (fun s => r s.st) B π = true) (hpr : batPriceOk π r 128 = true)
    (hl : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l)) :
    Err.Below (s := uLT (ckP .two) (dB :: dt))
      (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨a, rest, _, _, _, _, _, hs, _, _, _, _, _, _⟩ := made_of_planOk π hp
  have hb := H2K.Pin.batBelow_like π r 128 a rest hs dB dt hl hpr
  obtain ⟨w0, l, hw, hlike⟩ := hl
  cases hlike with
  | cons hB hT =>
    refine ⟨?_, ?_⟩
    · show ((batV0 π r * (bsRound .two dB.entry dB.kind).w : ℕ) : ℝ≥0∞) ≤
        (2 : ℝ≥0∞)⁻¹ ^ 128 * (Fintype.card (wT dB).Chal : ℝ≥0∞)
      rw [card_wT]
      exact hb
    · cases hc : chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l with
      | none =>
        have eJ : errJ π r dt = Err.zero _ := by
          unfold errJ
          rw [hs, hw]
          dsimp only
          rw [hc]
        rw [eJ]
        exact zero_below _ _
      | some c =>
        have eJ : errJ π r dt = errOfList (uLT (ckP .two) dt) (errList _ c.errL) := by
          unfold errJ
          rw [hs, hw]
          dsimp only
          rw [hc]
        rw [eJ]
        exact below_like dt l hT c.rds (chainFrom_rds _ rest a l c hc) c.errL _
          (Chain.errL_below c _ (small_of_ok _ B π hsm a rest w0 l c hs hw hc))

/-- So the pair lies at or below the cap at 128. -/
theorem pair_le_cap (π : P12) (r : Fmt.M1.Stage → ℕ) (B : Sg → Br × Br) (dB : RDT) (dt : List RDT)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hsm : smallOk (fun s => r s.st) B π = true) (hpr : batPriceOk π r 128 = true)
    (hl : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l)) :
    Err.le ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) : Err (uLT (ckP .two) (dB :: dt)))
      (Err.cap 128 (uLT (ckP .two) (dB :: dt))) :=
  Err.le_cap_of_below_inv 128 _ (pair_below π r B dB dt hp hsm hpr hl)

end Johnson.RunOne.Law.K12Facts15

#print axioms Johnson.RunOne.Law.K12Facts15.smallOk_of_test
#print axioms Johnson.RunOne.Law.K12Facts15.zero_below
#print axioms Johnson.RunOne.Law.K12Facts15.pair_below
#print axioms Johnson.RunOne.Law.K12Facts15.pair_le_cap
