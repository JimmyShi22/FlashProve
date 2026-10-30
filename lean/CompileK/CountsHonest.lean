-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/CountsHonest.lean: upper bounds on how many queries the honest committer and the honest
prover of the compiled scheme make to the one random oracle.

Statements and proofs. Generic: any interface, any wire with `W.OK` (Iop/BatchWire.lean): the laws
of a wire in which no round has a search for a nonce.
The compiled scheme is `Gen.withW Wn (argBKE W WP p)` (`argBKE`: Compile/Batch/StarKE.lean), over
typed oracles; a coding m (`OracleCoding`, Rom/Family.lean) puts it over one oracle (`schemeOverOneHashFunction`).

Main names:
  `cC W p`, `cP W n`: the counts `cCBW`, `cPUW` (Compile/Batch/OneCallCostR.lean) at "a failed try
    1, a Fiat-Shamir query K + 2" (it has K + 1 blocks: the count is one too high for each): natural
    numbers, by recursion on the shapes.
  `cost_C`, `cost_PU`: under `Std m` and `W.OK` the typed algorithms `C` (Compile/Batch/Star.lean)
    and `PU` (Compile/Batch/StarU.lean: free empty slots; n requests) cost at most cC W p and cP W n
    blocks on every path.
  `queryBound_C_one`, `queryBound_P_one`: the same bounds, under `W.OK`, on the queries of the
    committer and the prover of `schemeOverOneHashFunction m (Gen.withW Wn (argBKE W WP p))`, for every coding m
    that cuts answers in the standard way (`Std m`, Compile/Batch/NeedTable.lean).




Why: over one oracle a typed query costs as many queries as its answer has blocks
(`queryBound_overOne_of_cost`, Rom/Cost.lean). Compile/Batch/OneCallCostS.lean bounds committer and
prover (`costV_C`, `costV_PU`), under `W.OKG` and `NbPos W nb`, for every weight that may look at
query and answer and meets `TryW` (among its clauses: never more than the rule `ruleT W nb m` asks,
Compile/Batch/SpecOneCall.lean). It was made for an exit that reads only the blocks that are needed
(`OComp.overOneA`, Rom/SpecOverOneA.lean). Under `Std m` and `W.OK`, at the table "all blocks"
(`nbAll`), that rule asks all blocks of every answer (`numA_all`), so these bounds hold for the
weight `m.blocks`, which is what a typed query costs under `schemeOverOneHashFunction`.

Limits: the bounds of this file are upper bounds on every path; it says nothing on a lower bound.
It says nothing on the verifier (`tVB`, Compile/Batch/SpecBinding.lean, written out in
CompileK/Counts.lean, counts typed queries), and nothing on running time.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Counts
import Compile.Batch.OneCallCostS
import Compile.Batch.CutQueriesSum
import Rom.Cost
import Rom.OneOfCount
import CompileK.Main

set_option autoImplicit false

namespace Rom

/-- If every oracle's range is nonempty, a bound for weights that may look at query and answer gives
one for smaller weights that look at the oracle alone. -/
theorem OComp.CostBoundV.toCost {S : OSpec} [∀ o, Nonempty (S.Rng o)] {α : Type}
    {wt : (o : S.ι) → S.Dom o → S.Rng o → ℕ} {w : S.ι → ℕ}
    (hw : ∀ o q r, w o ≤ wt o q r) {c : OComp S α} :
    ∀ {t : ℕ}, c.CostBoundV wt t → c.CostBound w t := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    intro t h
    obtain ⟨r0⟩ := (inferInstance : Nonempty (S.Rng o))
    obtain ⟨t0, h0, -⟩ := h r0
    have := hw o q r0
    refine ⟨t - w o, by omega, fun r => ?_⟩
    obtain ⟨t', h1, h2⟩ := h r
    have := hw o q r
    exact (ih r h2).mono (by omega)

end Rom

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.Batch.Need (Std)
open Compile.Batch.OneCall

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

theorem tryInfo_none_of_ok {K : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OK s A W → ∀ z, tryInfo s A W z = none
  | [], _, _, _, z => z.elim
  | _ :: _, (_, _), (w, _), h, .inl (.inl α) => by
      show (w.gr0.map _) = none
      rw [h.1.gr0_none]
      rfl
  | _ :: _, (_, _), (w, _), h, .inl (.inr α) => by
      show (w.grJ.map _) = none
      rw [h.1.grJ_none]
      rfl
  | _ :: s, (_, A), (_, W), h, .inr z => tryInfo_none_of_ok s A W h.2 z

variable {W : QueryLayout lam L}

theorem tryInfoT_none (hW : W.OK) : ∀ t z, tryInfoT W t z = none
  | .test, z => tryInfo_none_of_ok _ _ _ hW.T.sh z
  | .link, z => tryInfo_none_of_ok _ _ _ hW.Lk.sh z
  | .onl, z => tryInfo_none_of_ok _ _ _ hW.B.sh z

theorem test0_of_ok (hW : W.OK) : Test0 W := fun t z x h => by
  rw [tryInfoT_none hW] at h
  cases h

/-- Under `Std m` and `W.OK` (in such a wire no round has a search for a nonce) the rule "all
blocks" asks all blocks of every answer. -/
theorem numA_all {m : OracleCoding (spec lam W.K L) lam} (hm : Std m) (hW : W.OK) (o : OracleName)
    (q : domOf lam L o) (r : rngOf lam W.K o) :
    numA m (ruleT W (nbAll W.K) m) o q r = m.blocks o := by
  by_cases ho : ∀ t, o ≠ .fb t
  · exact numA_all_other hm ho q r
  · obtain ⟨t, ht⟩ := not_forall.1 ho
    obtain rfl : o = .fb t := not_not.1 ht
    rw [numA_all_kept hm (test0_of_ok hW) t q r (by unfold failsAt; rw [tryInfoT_none hW]; simp)]
    exact (hm.blocks (.fb t)).symm

/-! ## The honest committer and the honest prover, over one oracle -/

section Cost
variable (WP : WireBP L) (p : Params) {m : OracleCoding (spec lam W.K L) lam}

/-- what the honest committer costs at most, in blocks: a Fiat-Shamir query is counted with K + 2
(it has K + 1 blocks) (`cost_C`, under `Std m` and `W.OK`) -/
def cC (W : QueryLayout lam L) (p : Params) : ℕ := cCBW W p 1 fun _ _ => W.K + 1 + 1
/-- what the honest prover costs at most on a batch with n requests (`cost_PU`, under `Std m` and
`W.OK`) -/
def cP (W : QueryLayout lam L) (n : ℕ) : ℕ := cPUW W 1 (fun _ _ => W.K + 1 + 1) n

theorem cost_C (hm : Std m) (hW : W.OK) (i : I) : (C W WP p i).CostBound m.blocks (cC W p) :=
  (costV_C WP p (tryW_numA (nb := nbAll W.K) hm (test0_of_ok hW)) hW.toG (nbPos_all W) i).toCost
    fun o q r => le_of_eq (numA_all hm hW o q r).symm

theorem cost_PU (hm : Std m) (hW : W.OK) (k : ISK lam L) (b : List (X × Unit)) :
    (PU W WP p k b).CostBound m.blocks (cP W b.length) :=
  (costV_PU WP p (tryW_numA (nb := nbAll W.K) hm (test0_of_ok hW)) hW.toG (nbPos_all W) k b).toCost
    fun o q r => le_of_eq (numA_all hm hW o q r).symm

variable (Wn : Type)

/-- The honest committer of the compiled scheme, over one oracle. -/
theorem queryBound_C_one (hm : Std m) (hW : W.OK) (i : I) :
    ((schemeOverOneHashFunction m (Gen.withW Wn (argBKE W WP p))).C i).QueryBound (cC W p) :=
  queryBound_overOne_of_cost m
    ((C W WP p i).bind fun o => .pure ((o.1, linksOf (keyOf o.2.1)), o.2)) _
    (OComp.CostBound.bind (t := 0) (fun _ => OComp.CostBound.pure _ 0) (cost_C WP p hm hW i))

/-- The honest prover of the compiled scheme, over one oracle, on a batch with n requests. -/
theorem queryBound_P_one (hm : Std m) (hW : W.OK) (k : ISK lam L) (b : List (X × Wn)) :
    ((schemeOverOneHashFunction m (Gen.withW Wn (argBKE W WP p))).P k b).QueryBound (cP W b.length) := by
  have h := cost_PU WP p hm hW k (Gen.forgetW b)
  rw [show (Gen.forgetW b).length = b.length from List.length_map _] at h
  have h1 : (PKE W WP p k (Gen.forgetW b)).CostBound m.blocks (cP W b.length + 0) :=
    OComp.CostBound.bind (t := 0) (fun _ => OComp.CostBound.pure _ 0) h
  have h2 : ((Gen.withW Wn (argBKE W WP p)).P k b).CostBound m.blocks (cP W b.length + 0 + 0) :=
    OComp.CostBound.bind (t := 0) (fun _ => OComp.CostBound.pure _ 0) h1
  exact queryBound_overOne_of_cost m _ _ h2

end Cost

/-! ## For the compiler's data -/

section Data
variable {L₀ : BatchProtocol I X} (D : DataK L₀ lam) (Wn : Type) (Se : SerLHB L₀)

theorem cP_mono (W : QueryLayout lam L) {n n' : ℕ} (h : n ≤ n') : cP W n ≤ cP W n' :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

end Data

end Compile.Batch
