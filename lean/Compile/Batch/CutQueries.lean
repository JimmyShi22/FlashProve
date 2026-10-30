-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CutQueries.lean: what a typed query costs over the one hash function f after the four
steps (splitting, Compile/Batch/CutFit.lean; state expansion, Rom/StateFirst.lean; only the blocks
below nb t i are expanded, Compile/Batch/CutDraws.lean; the query encoding of
Compile/Batch/CutImpl.lean): for 2 ≤ W.K and under `Test0`, a failed proof-of-work attempt that is
not the last weighs exactly one (words of this library: lean/GLOSSARY.md).

  `Rom.queryBound_cutA_overOne`  Generic. Let u x q = (the blocks of the oracle x under the query
                                 encoding) + (the expansion queries that the rule needD makes at
                                 most) · (the blocks of the oracle dr, Rom/StateFirst.lean), and
                                 `wCut C1 need u` (Rom/SpecCut.lean) what a typed query costs over
                                 the second family, if a query there costs u: if on every path of
                                 the typed algorithm the weights wCut C1 need u add up to at most t,
                                 the algorithm after the four steps makes at most t queries to f.
  `uF nb K`, `wF W nb`  That u and that weight at `implCS`. wF W nb o q r bounds what the typed
                        query (o, q) with the answer r costs committer and prover.
  `wF_fail`, `wF_kept`  For 2 ≤ W.K, under `Test0`: a failed attempt that is not the last weighs
                        exactly one; at every other Fiat-Shamir query wF = 1 + (2 + (nb t i − 1)):
                        the first block (in a round without proof-of-work bits it is block 0 of the
                        verifier message: a call on the whole query); the state (two calls); a call
                        on (state, counter) for each block 1, .., nb t i − 1.

Limits: over f the result is "at most", not "exactly". `wF_fail` and `wF_kept` are equations on the
weight; `queryBound_CSO` says that the program after the four steps makes at most as many queries to
f as the weights add up to. That the program queries the first block at every query, and nothing
more where the rule says no, is the splitting step's definition. The same fact as an equation on the
program, for every fixed f, in the mean over the coins: the general form is not shown in this file.
Its application to the committer and the prover at the query encoding `implCS`, and the form query
by query, are not in this library. No bound on the weights wF of committer or prover is proved here.
A call counts as one however long its string; the string of a first block and of a state holds the
whole typed query. The verifier runs under "always": every Fiat-Shamir query of the verifier costs
what `wF_kept` gives (neither stated nor proved in this library).
-/
import Compile.Batch.CutDraws
import Compile.Batch.CutImpl
import Compile.Batch.KeptCut

set_option autoImplicit false

noncomputable section

namespace Rom

variable {S : OSpec} {lam : ℕ} {α : Type}

/-- The queries to f after the four steps, under the hypotheses below. -/
theorem queryBound_cutA_overOne (C1 : ∀ o, OCut (S.Rng o))
    (C2 : ∀ x, Link lam ((cutSpec S C1).Rng x)) (m' : OracleCoding (stSpec (cutSpec S C1) lam C2) lam)
    (need : NeedCut C1) (needD : NeedA (cutSpec S C1) lam)
    (nd : (x : (cutSpec S C1).ι) → (cutSpec S C1).Dom x → ℕ) (hb : needD.Below nd) (c : OComp S α)
    (t : ℕ) (h : c.CostBoundV
      (wCut C1 need fun x q => m'.blocks (.inl x) + nd x q * m'.blocks (.inr ())) t) :
    (((c.cut C1 need).stateFirstA C2 needD).overOne m').QueryBound t :=
  queryBound_stateFirstA_overOne m' needD nd hb _ t (cutCost _ _ _ _ _ _ _ h)

end Rom

namespace Compile.Batch
open Iop Rom ZKCP

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- what a query to an oracle of the split family costs over f: its blocks, and a call for each
expansion query -/
def uF (nb : Tag → ℕ → ℕ) (K : ℕ) (x : (cutSpec (spec lam K L) (cutFS lam K L)).ι)
    (q : (cutSpec (spec lam K L) (cutFS lam K L)).Dom x) : ℕ :=
  blkCS K (.inl x) + nDraws nb x q * blkCS K (.inr ())

/-- the weight that bounds what a typed query costs C and P over f -/
def wF (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) : (o : OracleName) → domOf lam L o → rngOf lam W.K o → ℕ :=
  wCut (cutFS lam W.K L) (needT W) (uF nb W.K)

theorem nFront_two : ∀ {K : ℕ}, 2 ≤ K → nFront K = 1
  | _ + 2, _ => rfl

theorem nRest_two : ∀ {K : ℕ}, 2 ≤ K → nRest K = 2
  | _ + 2, _ => rfl

theorem isWhole_fb_two : ∀ {K : ℕ}, 2 ≤ K → (cutFb lam K).isWhole = false
  | _ + 2, _ => rfl

variable (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ)

/-- For 2 ≤ W.K, under `Test0`: a failed attempt that is not the last weighs exactly one. -/
theorem wF_fail (hK : 2 ≤ W.K) (hT : Test0 W) {t : Tag} {q : FbIn lam L t}
    {r : rngOf lam W.K (.fb t)} (hf : failsAt W t q r.1 = true) : wF W nb (.fb t) q r = 1 := by
  unfold wF wCut
  rw [needT_of_fails W hT hf]
  show nFront W.K + 0 * _ + (if ((cutFb lam W.K).isWhole || !false) = true then 0 else _) = 1
  rw [nFront_two hK]
  simp

/-- under `Test0`, the rule queries the rest at every Fiat-Shamir query that is no failed attempt
before the last -/
theorem needT_of_kept (hT : Test0 W) {t : Tag} {q : FbIn lam L t}
    {r : rngOf lam W.K (.fb t)} (hf : ¬ failsAt W t q r.1 = true) :
    needT W (.fb t) q ((cutFS lam W.K L (.fb t)).front r) = true := by
  unfold failsAt at hf
  show (match tryInfoT W t q.plain with
    | some x => x.1 (fun _ => frontBl lam W.K ((cutFb lam W.K).front r)) || x.2
    | none => true) = true
  cases hx : tryInfoT W t q.plain with
  | none => rfl
  | some x =>
    rw [hx] at hf
    have h1 : ¬ (!x.1 r.1 && !x.2) = true := hf
    have h0 : 0 < W.K := (hT t _ x hx).1
    show (x.1 (fun _ => frontBl lam W.K ((cutFb lam W.K).front r)) || x.2) = true
    rw [frontBl_front W.K h0 r, ← (hT t _ x hx).2 r.1 (fun _ => r.1 ⟨0, h0⟩) fun _ => rfl]
    cases h2 : x.1 r.1 <;> cases h3 : x.2 <;> simp [h2, h3] at h1 ⊢

/-- For 2 ≤ W.K, under `Test0`: every Fiat-Shamir query that is no failed attempt before the last:
the first block, the state, the expansion queries. -/
theorem wF_kept (hK : 2 ≤ W.K) (hT : Test0 W) {t : Tag} {q : FbIn lam L t}
    {r : rngOf lam W.K (.fb t)} (hf : ¬ failsAt W t q r.1 = true) :
    wF W nb (.fb t) q r = 1 + (2 + (nb t q.round - 1)) := by
  unfold wF wCut
  rw [needT_of_kept W hT hf]
  show nFront W.K + 0 * _ +
      (if ((cutFb lam W.K).isWhole || !true) = true then 0
        else nRest W.K + (nb t q.round - 1) * 1) = _
  rw [nFront_two hK, nRest_two hK, isWhole_fb_two hK]
  simp

/-- at an oracle other than `fb t`: the blocks of its answer -/
theorem wF_whole {o : OracleName} (ho : ∀ t, o ≠ .fb t) (q : domOf lam L o) (r : rngOf lam W.K o) :
    wF W nb o q r = blk W.K o := by
  unfold wF wCut
  rw [isWhole_cutFS (lam := lam) (L := L) ho]
  show blkCS W.K (.inl (.inl o)) + nDraws nb (.inl o) q * _ + 0 = _
  rw [blkCS_whole (lam := lam) (L := L) o (isWhole_cutFS ho)]
  show blk W.K o + 0 * _ + 0 = _
  omega

/-- A bound on the weights wF of a typed algorithm bounds its queries to f. -/
theorem queryBound_CSO (c : StrCode (RealPtsCS lam W.K L)) (cG : StrCode (GhostPts lam W.K L))
    {α : Type} (a : TypedOracleComputation lam W.K L α) (t : ℕ) (h : a.CostBoundV (wF W nb) t) :
    (((a.cut (cutFS lam W.K L) (needT W)).stateFirstA (linksS lam W.K L) (needD nb)).overOne
      (implCS lam W.K L c cG)).QueryBound t :=
  queryBound_cutA_overOne _ _ (implCS lam W.K L c cG) (needT W) (needD nb)
    (nDraws nb) (needD_below nb) a t h

end Compile.Batch
