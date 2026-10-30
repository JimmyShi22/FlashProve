-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/TvAll.lean: THE VERIFIER's OWN COUNT OF QUERIES tVC AT THE NAMED WIRE wireAll
(JoinAll.lean), with free numbers: a twin of tVB_data | tVB_le_of (CompileK/Counts.lean:281-306,
:411-423): tVC ≤ 2 + (ro + 3 + o (d + 1) + 3 (depthReq + 1)): ro bounds the rounds of the three
protocols, o the announced openings, d the depths of all trees; the 2 are the two seeds' queries.

-/
import Johnson.RecCompile.JoinAll
import CompileK.Counts

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cms
open Iop Rom Prob Hiop
open scoped ENNReal

theorem length_grind' (Nn : Type) [Inhabited Nn] :
    ∀ (s : Shape) (g : GBits s), (s.grind Nn g).length = s.length
  | [], _ => rfl
  | _ :: s, (_, g) => congrArg (· + 1) (length_grind' Nn s g)

theorem tVC_wireAll_le {lam : ℕ} (Nn : Type) [Inhabited Nn] {C : ConfigurationWithOutOfDomainSample} (S : SubsR C)
    (dT : S.lhr.offline.shape.Draws lam) (dL : S.lhr.link.shape.Draws lam)
    (dB : S.lhr.onlineBatch.loc.shape.Draws lam)
    (pT : S.lhr.offline.shape.IsPoint) (pL : S.lhr.link.shape.IsPoint)
    (pB : S.lhr.onlineBatch.loc.shape.IsPoint) (nT : S.lhr.offline.shape.NumPos pT)
    (nL : S.lhr.link.shape.NumPos pL) (nB : S.lhr.onlineBatch.loc.shape.NumPosB S.lhr.onlineBatch.ann pB)
    (z : S.lhr.Symbol) (oT oL oB K depthReq : ℕ) (D : GrData Nn) (g : S.Bits) (ro o d : ℕ)
    (hr : S.lhr.offline.shape.length + S.lhr.link.shape.length + S.lhr.onlineBatch.loc.shape.length ≤ ro)
    (ho : oT + oL + oB ≤ o) (hE : Nat.clog 2 S.lhr.wordLength ≤ d) (hT : S.lhr.offline.shape.dpLoc pT ≤ d)
    (hL : S.lhr.link.shape.dpLoc pL ≤ d) (hB : S.lhr.onlineBatch.loc.shape.dpB S.lhr.onlineBatch.ann pB ≤ d) :
    tVC (wireAll Nn S dT dL dB pT pL pB nT nL nB z oT oL oB K depthReq D g) ≤ 2 + (ro + 3 + o * (d + 1) + 3 * (depthReq + 1)) := by
  show 2 + (((((S.lhr.offline.shape.pull (Samplers.ofDraws _ dT)).grind Nn (g.TR.pull _)).length + 1 +
        (oT * (max (Nat.clog 2 S.lhr.wordLength)
            (RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofLocalD lam K S.lhr.offline.shape pT dT nT)) + 1) +
          (depthReq + 1))) +
      (((S.lhr.link.shape.pull (Samplers.ofDraws _ dL)).grind Nn (g.LR.pull _)).length + 1 +
        (oL * (max (Nat.clog 2 S.lhr.wordLength)
            (RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofLocalD lam K S.lhr.link.shape pL dL nL)) + 1) +
          (depthReq + 1)))) +
      (((S.lhr.onlineBatch.loc.shape.pull (Samplers.ofDraws _ dB)).grind Nn (g.BR.pull _)).length + 1 +
        (oB * (max (Nat.clog 2 S.lhr.wordLength)
            (RoundsQueryLayout.maxDepth _ _
              (RoundsQueryLayout.ofDraws lam K S.lhr.onlineBatch.loc.shape S.lhr.onlineBatch.ann pB dB nB)) + 1) +
          (depthReq + 1)))) ≤ _
  rw [length_grind', length_grind', length_grind', Shape.length_pull, Shape.length_pull,
    Shape.length_pull, maxDepth_ofLocalD, maxDepth_ofLocalD, maxDepth_ofDraws]
  have a1 := Nat.mul_le_mul_left oT (Nat.succ_le_succ (max_le hE hT))
  have a2 := Nat.mul_le_mul_left oL (Nat.succ_le_succ (max_le hE hL))
  have a3 := Nat.mul_le_mul_left oB (Nat.succ_le_succ (max_le hE hB))
  have a4 := Nat.mul_le_mul_right (d + 1) ho
  rw [Nat.add_mul, Nat.add_mul] at a4
  simp only [Nat.succ_eq_add_one] at a1 a2 a3
  omega

end Compile.Batch.Cms

#print axioms Compile.Batch.Cms.tVC_wireAll_le
