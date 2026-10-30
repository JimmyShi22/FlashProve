-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteURefStarG.lean: for every fixed family of oracle functions, the three events
"bad" of the instrumented honest run of the scheme with free empty slots (no query for an empty
slot; `runAllBUX`, Compile/Batch/StarUX.lean) have the distributions of the small experiments `RT`,
`RL`, `RBU` (the third under `W.OKG`, the format `Fmt`, and if request number a is x). For wire
records that may have proof-of-work bits (words of this library: lean/GLOSSARY.md).

    theorem lawTUG : Spec.lawTUG, lawLUG : Spec.lawLUG, lawBUG : Spec.lawBUG
    (Compile/Batch/SpecCompleteUG.lean)

  Part 1  The instrumented run as one program with tokens; a distribution for every fixed copy is
          one for the sampled copy.
  Part 2  The three distributions (`lawTUG`, `lawLUG`, `lawBUG`).

From Compile/Batch/CompleteRefStarG.lean: all lemmas on the committer. From
Compile/Batch/CompleteURef.lean: `lawS_proveBUX`: under the hypotheses of its statement, the hash
blocks of a slot with a request have the distribution that they have in `proveOU`. Here: the event
of a slot depends on the hash blocks of that slot only (`badAt_getD`). So `lawBUG` uses that request
number a is x (the base scheme's lawBG, which is not in this library, does not).

Notation: `LawS f c vs φ μ` (Compile/Batch/CompleteRef.lean): a proposition: μ is the distribution
of φ of the output and the final store of the erased program c, started with the store vs, over its
coins, for fixed oracle functions; `St lam K L α` (Compile/Batch/TokTree.lean):
`Step (spec lam K L) (split lam K L) α`: a token program (`Step`, Rom/Defer.lean; the head of
Compile/Batch/Prover.lean); `erase` (Compile/Star.lean): forget the rules: tokens are strings, kept
in a list; fresh = sample; marked = query; reveal = read; `realF f` (Compile/Batch/SpecLoop.lean):
the oracle functions that answer the ghost name fbw t k as fb t; `mkX`
(Compile/Batch/CompleteRefStarG.lean): the output of the instrumented run, from the outputs of the
committer and the prover; `RT`, `RL` (`Ref.RT`, `Ref.RL`, Compile/Batch/CompleteRefDefs.lean): a
fresh node and its Test; two fresh nodes and the Link from the first to the second; `RBU`
(Compile/Batch/CompleteURefDefs.lean): a fresh node and one batch on it; `fun _ => true`: the
argument `fr` of `PpUX`, `PpJUX` (Compile/Batch/StarUX.lean): `ℕ → Bool`: for which requests a proof
string is made at all; the scheme has fr = true everywhere (the head of Compile/Batch/Star.lean); a
node (`nodeO`, Compile/Batch/CompleteRefDefs.lean): a fresh encoding of i and the root of its tree;
`t`: a `Tag` (Compile/Oracles.lean): test, link or onl.

Limits: nothing on probabilities over the oracles (Compile/Batch/CompleteUUnifG.lean).
-/
import Compile.Batch.CompleteRefStarG
import Compile.Batch.CompleteURef
import Compile.Batch.CompleteURefNoGhost
import Compile.Batch.SpecCompleteUG

noncomputable section

namespace Compile.Batch.RefStarUG
open Iop Rom Prob Compile.Batch.Cmpl Compile.Batch.Ref Compile.Batch.RefU Compile.Batch.RefStarG

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (f : Fam (spec lam W.K L)) (i : I)

/-! ## Part 1. The instrumented run -/

/-- the batch, once the copy is sampled -/
def PpAtUX (k : IskH lam L) (xs : List X) (j : ℕ) :
    St lam W.K L (List (Prf lam L) × XP lam W.K L.maxBatchSize) :=
  (drawT WP.perm).bind fun σ =>
    (PpJUX W WP p k (fun _ => true) xs j σ).bind fun o => Step.pure (o.1, (j, σ, o.2))

/-- the committer, then the prover on the copy j -/
def runAtUX (xs : List X) (j : ℕ) :
    St lam W.K L ((IVK lam L × List (Prf lam L)) × RunX lam W.K L) :=
  (CpX W WP p i).bind fun o => (PpAtUX W WP p o.1.2 xs j).bind fun πs => Step.pure (mkX W o πs)

/-- the committer, then the prover -/
def runAllSUX (xs : List X) : St lam W.K L ((IVK lam L × List (Prf lam L)) × RunX lam W.K L) :=
  (CpX W WP p i).bind fun o =>
    (PpUX W WP p o.1.2 (fun _ => true) xs).bind fun πs => Step.pure (mkX W o πs)

/-- A distribution that holds for every fixed copy holds for the uniformly chosen copy. -/
theorem law_runAllSUX {β : Type} (xs : List X)
    {φ : (IVK lam L × List (Prf lam L)) × RunX lam W.K L → List Bits → β} {μ : PMF β}
    (h : ∀ j : Fin (p.M + 1), LawS f (runAtUX W WP p i xs j.val) [] φ μ) :
    LawS f (runAllSUX W WP p i xs) [] φ μ := by
  have e1 : ∀ j : Fin (p.M + 1),
      (((erase (CpX W WP p i) []).runEager f).bind fun o =>
            (erase ((PpAtUX W WP p o.1.1.2 xs j.val).bind fun πs => Step.pure (mkX W o.1 πs))
              o.2).runEager f).map
          (fun o => φ o.1 o.2) = μ := fun j => by
    have := h j
    unfold LawS runAtUX at this
    rwa [erase_bind, OComp.runEager_bind] at this
  unfold LawS runAllSUX
  rw [erase_bind, OComp.runEager_bind]
  have e2 : (fun o : ((IVK lam L × IskH lam L) × XC lam W.K) × List Bits =>
    (erase ((PpUX W WP p o.1.1.2 (fun _ => true) xs).bind fun πs => Step.pure (mkX W o.1 πs))
      o.2).runEager f)
      = fun o => (unif (Fin (p.M + 1))).bind fun j =>
        (erase ((PpAtUX W WP p o.1.1.2 xs j.val).bind fun πs => Step.pure (mkX W o.1 πs))
            o.2).runEager f := rfl
  rw [e2, Prob.bind_comm, PMF.map_bind]
  simp only [e1, PMF.bind_const]

/-- What the instrumented run outputs beside key and proofs is what one program with tokens outputs,
under the family that answers the ghost names `fbw t k` as fb t. -/
theorem map_runAllBUX {β : Type} (b : List (X × Unit)) (φ : RunX lam W.K L → β) :
    ((runAllBUX W WP p i b).runEager f).map (fun z => φ z.2) =
      ((erase (runAllSUX W WP p i (b.map Prod.fst)) []).runEager (realF f)).map fun o =>
        φ o.1.2 := by
  simp only [runAllBUX, CX, PUX, OComp.runEager_bind, realQ_eager I X lam W.K L, CtokX, PtokUX,
    runAllSUX, mkX, erase_bind, erase_pure, OComp.runEager, PMF.pure_bind, PMF.bind_bind,
    PMF.map_bind, PMF.pure_map]

/-! ## Part 2. The three distributions -/

/-- the event of a slot depends on the hash blocks of that slot only -/
theorem badAt_getD {K : ℕ} {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
    (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (w : Wt) (x : Y)
    (n : ℕ) (bss : List (List (Blk lam K))) :
    badAt Q H wq wp w x n bss = badAt Q H wq wp w x 0 [bss.getD n []] := rfl

/-- with the copy fixed, the prover outputs the number of that copy -/
theorem tri_PpAtUX_leaf (k : IskH lam L) (xs : List X) (j : ℕ) (vs : List Bits) :
    Tri f (PpAtUX W WP p k xs j) vs fun πs _ => πs.2.1 = j :=
  Tri.bind (tri_true' _ vs) fun _ vs0 _ =>
    Tri.bind (tri_true' _ vs0) fun _ _ _ => tri_pure_iff.2 rfl

variable (hf : RealFam f)
include hf

theorem law_runAtUX_test (xs : List X) (j : ℕ) :
    LawS f (runAtUX W WP p i xs j) [] (fun z _ => z.2.badT WP) ((Ref.RT W WP p i).runEager f) := by
  have h := LawS.bind
    (ψ := fun (z : (IVK lam L × List (Prf lam L)) × RunX lam W.K L) (_ : List Bits) => z.2.badT WP)
    (ν := PMF.pure) (g := fun o => (PpAtUX W WP p o.1.2 xs j).bind fun πs => Step.pure (mkX W o πs))
    (law_CpX_test W WP p f i hf []) (tri_true' _ [])
    fun o vs1 _ => lawS_const (Tri.bind (tri_true' _ vs1) fun πs vs2 _ => tri_pure_iff.2 rfl)
  rw [PMF.bind_pure] at h
  exact h

theorem law_runAtUX_link (xs : List X) {j : ℕ} (hj : j < p.M + 1) :
    LawS f (runAtUX W WP p i xs j) [] (fun z _ => z.2.badL WP) ((Ref.RL W WP p i).runEager f) := by
  have h := LawS.bind
    (ψ := fun (z : (IVK lam L × List (Prf lam L)) × RunX lam W.K L) (_ : List Bits) => z.2.badL WP)
    (ν := PMF.pure) (g := fun o => (PpAtUX W WP p o.1.2 xs j).bind fun πs => Step.pure (mkX W o πs))
    (law_CpX_link W WP p f i hf [] hj) (tri_true' _ []) fun o vs1 _ => by
      have hT : Tri f
          ((PpAtUX W WP p o.1.2 xs j).bind fun πs =>
            (Step.pure (mkX W o πs) :
              St lam W.K L ((IVK lam L × List (Prf lam L)) × RunX lam W.K L)))
          vs1 fun z _ => z.2.badL WP = (runC W o j).badL WP :=
        Tri.bind (tri_PpAtUX_leaf W WP p f o.1.2 xs j vs1) fun πs vs2 h =>
          tri_pure_iff.2 (badL_congr W WP (z := (mkX W o πs).2) (z' := runC W o j) rfl rfl h)
      exact lawS_const hT
  rw [PMF.bind_pure] at h
  exact h

theorem law_runAtUX_bat (hW : W.OKG) (hF : L.onlineBatch.ann.Fmt) (xs : List X) {j : ℕ} (hj : j < p.M + 1)
    (a : Fin L.maxBatchSize) (x : X) (hx : xs[a.val]? = some x) :
    LawS f (runAtUX W WP p i xs j) [] (fun z _ => z.2.badB WP a x)
      ((RBU W WP p i xs a x).runEager f) := by
  have h := LawS.bind
    (ψ := fun (z : (IVK lam L × List (Prf lam L)) × RunX lam W.K L) (_ : List Bits) =>
        z.2.badB WP a x)
    (ν := fun s : Option (L.EncodingRandomness × Dig lam) => match s with
      | some nd => (batOU W WP p i xs a x nd).runEager f
      | none => PMF.pure true)
    (g := fun o => (PpAtUX W WP p o.1.2 xs j).bind fun πs => Step.pure (mkX W o πs))
    (law_CpX_node W WP p f i [] hj) (tri_CpX_idx W WP p f i []) fun o vs1 hi => ?_
  · rw [PMF.bind_map] at h
    unfold RBU
    rw [OComp.runEager_bind]
    exact h
  · cases hlf : o.1.2.leaves[j]? with
    | none =>
      refine lawS_const
        (Tri.bind (tri_PpAtUX_leaf W WP p f o.1.2 xs j vs1) fun πs vs2 h => tri_pure_iff.2 ?_)
      show RunX.badB WP (⟨o.1.2, o.2.1, o.2.2, πs.2.1, πs.2.2.1, πs.2.2.2⟩ : RunX lam W.K L) a x =
        true
      unfold RunX.badB
      simp only [h, hlf]
    | some lf =>
      show LawS f _ vs1 _ ((batOU W WP p i xs a x (lf.node.r, lf.node.tree.root)).runEager f)
      unfold batOU PpAtUX
      rw [runEager_drawO_bind]
      show LawS f
        ((drawT WP.perm).bind fun σ =>
          ((PpJUX W WP p o.1.2 (fun _ => true) xs j σ).bind fun o' =>
              Step.pure (o'.1, (j, σ, o'.2))).bind
            fun πs => Step.pure (mkX W o πs))
        vs1 _ _
      refine lawS_drawT_bind f WP.perm _ vs1 _ _ fun rσ => ?_
      generalize WP.perm.e rσ = σ
      unfold PpJUX
      rw [hlf, hi, OComp.runEager_bind]
      simp only [Step.bind_assoc']
      have e : (((proveOU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
              (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq [lf.node.tree.root]
              (i, lf.node.r) (slotsOfReq σ xs)).runEager
            f).bind fun bss =>
              (OComp.pure
                (badAt L.onlineBatch L.honestOnlineBatchProver W.B WP.B (i, lf.node.r) x
                  (σ a).val bss) : TypedOracleComputation lam W.K L Bool).runEager f) =
          (((proveOU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
                (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq [lf.node.tree.root]
                (i, lf.node.r) (slotsOfReq σ xs)).runEager f).map
              fun bss => bss.getD (σ a).val []).bind
            fun bl => PMF.pure (badAt L.onlineBatch L.honestOnlineBatchProver W.B WP.B (i, lf.node.r) x 0 [bl]) := by
        rw [PMF.bind_map]
        rfl
      refine LawS.congr ?_ e.symm
      refine LawS.bind
        (lawS_proveBUX f p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
          (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq [lf.node.tree]
          (i, lf.node.r) hf hF (slotFlags σ fun _ => true) (slotsOfReq σ xs)
          (Or.inl (by rw [← hW.slots]; simp [slotsOfReq])) (σ a).val x
          (by rw [getElem?_slotsOfReq, hx]) vs1)
        (tri_true' _ vs1) fun o' vs2 _ => ?_
      refine (lawS_pure _ _ _).congr ?_
      show PMF.pure (RunX.badB WP (⟨o.1.2, o.2.1, o.2.2, j, σ, o'.2⟩ : RunX lam W.K L) a x) =
        PMF.pure _
      unfold RunX.badB
      simp only [hlf, hi]
      rfl

end Compile.Batch.RefStarUG

namespace Compile.Batch
open Iop Rom Prob RefStarUG Ref RefU

/-- Test is bad with the distribution of `RT` (a fresh node and its Test), for fixed oracle
functions. -/
theorem lawTUG : Spec.lawTUG := by
  intro I X lam L W WP p f i b
  rw [map_runAllBUX W WP p f i b (fun z => z.badT WP),
    ← runEager_realF_of_noGhost (noGhost_RT W WP p i) f]
  exact law_runAllSUX W WP p (realF f) i _ fun j =>
    law_runAtUX_test W WP p (realF f) i (Cmpl.realFam_realF f) _ j.val

/-- The Link of the sampled copy is bad with the distribution of `RL` (two fresh nodes and their
Link), for fixed oracle functions. -/
theorem lawLUG : Spec.lawLUG := by
  intro I X lam L W WP p f i b
  rw [map_runAllBUX W WP p f i b (fun z => z.badL WP),
    ← runEager_realF_of_noGhost (noGhost_RL W WP p i) f]
  exact law_runAllSUX W WP p (realF f) i _ fun j =>
    law_runAtUX_link W WP p (realF f) i (Cmpl.realFam_realF f) _ j.isLt

/-- Under `W.OKG`, `Fmt`, and if request number a is x: the slot of a request is bad with the
distribution of `RBU` (a fresh node and one batch of the prover with free empty slots on it), for
fixed oracle functions. -/
theorem lawBUG : Spec.lawBUG := by
  intro I X lam L W WP p hW hF f i b a x hx
  rw [map_runAllBUX W WP p f i b (fun z => z.badB WP a x),
    ← runEager_realF_of_noGhost (noGhost_RBU W WP p i _ a x) f]
  exact law_runAllSUX W WP p (realF f) i _ fun j =>
    law_runAtUX_bat W WP p (realF f) i (Cmpl.realFam_realF f) hW hF _ j.isLt a x hx

end Compile.Batch
