-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PrunedFacts.lean: for one proof string: what the verifier with the strict-format check
(`verifyOneProtocol`) accepts, the verifier for proof strings with pruned Merkle paths (`verifyBO`) accepts
after pruning; and, for a well-formed wire record with `ExtInj`, what `verifyBO` accepts, `verifyOneProtocol`
accepts after filling. (Words of this library: lean/GLOSSARY.md.)

Definitions: Compile/Batch/Verifier.lean (`verifyOneProtocol`, `checkPrunedOpenings`, forests), Compile/Batch/Pruned.lean
(`verifyBC`, `verifyBO`, `pruneO`, `refill`, `fillO`). `AccLe a b` (Compile/GenLe.lean): b accepts
whenever a does: for every family of oracle functions, b returns true with at least the probability
with which a does; and if a accepts on a trace (`RunsIn`), so does b.

  Part 1  `runForests` does not read the paths of its checks (`Forest.erase`, `runForests_erase`)
  Part 2  the forests, the strict-format check and the end `afterBC` of a proof string with other
          paths (`forestsOf_withPaths`, `strictBB_withPaths`, `afterBC_withPaths`,
          `verifyBC_withPaths`): `verifyBC` does not read the paths in the openings
  Part 3  `plan_forestsOf`. Pruning goes through the leaves at which the proof string holds an
          opening, the verifier through the leaves that it reads and whose component has a root. If
          the proof string passes the strict-format check and no opening is missing, these are the
          same leaves in the same order
  Part 4  `accLe_prune`: AccLe (verifyOneProtocol .. π) (verifyBO .. (pruneO wq π)). The two are one program
          unless a path of π has a wrong length, and then `verifyOneProtocol` rejects
  Part 5  the plan of a refilled proof string; `accLe_fill`: AccLe (verifyBO .. π') (verifyOneProtocol ..
          (fillO wq π')), for a well-formed wire record (`wq.OKG`) on which different positions of
          the external strings have different numbers (`ExtInj`). The two are one program unless
          π'.sibs has a wrong length, and then `verifyBO` rejects

Notation:
  `π.withPaths P1 P2`: the proof string π with other paths in its openings; `reP f P`: the openings
    f with their paths replaced by those of P (Compile/Batch/Verifier.lean); `pathJ posAt P j`: the
    path of P at the position of leaf j (Compile/Batch/ForestSound.lean)
  `Check`: one check of an opening in a tree over oracles: leaf input, number of the leaf, path,
    root, and the depth of the tree; `Forest`: the checks in some trees of one depth ("a forest";
    mostly one tree): each check with the number of its tree (e.1) (Compile/Batch/Verifier.lean)
  `checksComp`, `checksOpt`: the checks that the read positions of one component of one round call
    for; `strictComp`: the strict-format check of one component; `mkTr`: a transcript from the proof
    string (the same file)
  `ρ`, `rts`, `ph`: what the chain returns; `rts`: an `RootsOfChain lam s`: for each round what the chain
    yields for the shared component (rt.1), and for the slot's component (rt.2); the endings 0 and
    J: of the shared, and of a slot's, component
  `wq.OKG`: `ProtocolQueryLayout.OKG` (Iop/BatchWire.lean); among its clauses: for each round `WireRB.OKG`: the
    laws of the wire of a round that may have a test
-/
import Compile.Batch.Pruned
import Compile.Batch.ForestSound
import Compile.GenLe

noncomputable section

namespace Compile.Batch
open Iop Rom Octopus Compile.GenLe

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Part 1. `runForests` does not read paths -/

/-- the forest with empty paths -/
def Forest.erase (F : Forest lam L) : Forest lam L :=
  ⟨F.depth, F.treeRoot, F.cs.map fun e => (e.1, e.2.withPath [])⟩

theorem leavesV_erase :
    ∀ cs : List (ℕ × Check lam L),
      leavesV (K := K) (cs.map fun e => (e.1, e.2.withPath [])) = leavesV cs
  | [] => rfl
  | e :: es => by
      simp only [List.map_cons, leavesV, leavesV_erase es]
      rfl

theorem Forest.idx_erase (F : Forest lam L) : F.erase.idx = F.idx := by
  simp only [Forest.idx, Forest.erase, List.map_map]
  rfl

theorem Forest.need_erase (F : Forest lam L) : F.erase.need = F.need := by
  unfold Forest.need
  rw [Forest.idx_erase]
  rfl

theorem runForest_erase (F : Forest lam L) (s : List (Dig lam)) :
    runForest (K := K) F.erase s = runForest F s := by
  unfold runForest
  rw [Forest.idx_erase]
  show (leavesV (F.cs.map fun e => (e.1, e.2.withPath [])) >>= _) = _
  rw [leavesV_erase]
  rfl

theorem runForests_erase :
    ∀ (Fs : List (Forest lam L)) (s : List (Dig lam)),
      runForests (K := K) (Fs.map Forest.erase) s = runForests Fs s
  | [], _ => rfl
  | F :: Fs, s => by
      simp only [List.map_cons, runForests, runForest_erase, Forest.need_erase, runForests_erase Fs]

theorem needF_erase (Fs : List (Forest lam L)) : needF (Fs.map Forest.erase) = needF Fs := by
  unfold needF
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun F _ => Forest.need_erase F

theorem flatF_erase :
    ∀ Fs : List (Forest lam L), flatF (Fs.map Forest.erase) = (flatF Fs).map fun c => c.withPath []
  | [] => rfl
  | F :: Fs => by
      rw [List.map_cons, flatF_cons, flatF_cons, List.map_append, flatF_erase Fs]
      simp only [Forest.erase, List.map_map]
      rfl

/-- what this file uses of the check `usedUp` ("used up exactly"): a list of the right length passes
it; a list that passes is not too short. (That it is not too long either is used by the statement on
sizes: Compile/Batch/SizeO.lean.) -/
theorem usedUp_of_length {n : ℕ} {s : List (Dig lam)} (h : s.length = n) : usedUp n s := by
  unfold usedUp
  omega

theorem usedUp.le {n : ℕ} {s : List (Dig lam)} (h : usedUp n s) : n ≤ s.length := by
  unfold usedUp at h
  omega

/-- `runForests` does not read beyond the digests that it takes -/
theorem runForests_take :
    ∀ (Fs : List (Forest lam L)) (s : List (Dig lam)),
      runForests (K := K) Fs (s.take (needF Fs)) = runForests Fs s
  | [], _ => rfl
  | F :: Fs, s => by
      have e : needF (F :: Fs) = F.need + needF Fs := by simp [needF]
      have e1 : (s.take (F.need + needF Fs)).take F.need = s.take F.need := by
        rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
      have e2 : (s.take (F.need + needF Fs)).drop F.need = (s.drop F.need).take (needF Fs) := by
        rw [List.drop_take, Nat.add_sub_cancel_left]
      simp only [runForests]
      rw [e, e1, e2, runForests_take Fs]

/-- the conditions of afterBC on the checks: how many, leaf numbers, depths -/
def condC {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    (wq : ProtocolQueryLayout lam K Q) (Fs : List (Forest lam L)) : Prop :=
  (flatF Fs).length ≤ wq.nOpen ∧
  (flatF Fs).all (fun c => decide (c.j < 2 ^ c.depth) && decide (c.depth ≤ wq.maxDepth)) = true

section Same
variable {Fs Fs' : List (Forest lam L)} (h : Fs'.map Forest.erase = Fs.map Forest.erase)
include h

theorem runForests_same (s : List (Dig lam)) : runForests (K := K) Fs' s = runForests Fs s := by
  rw [← runForests_erase Fs', h, runForests_erase]

theorem needF_same : needF Fs' = needF Fs := by
  rw [← needF_erase Fs', h, needF_erase]

theorem condC_same {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) :
    condC wq Fs' ↔ condC wq Fs := by
  have e : (flatF Fs').map (fun c => c.withPath []) = (flatF Fs).map fun c => c.withPath [] := by
    rw [← flatF_erase, h, flatF_erase]
  have key : ∀ l : List (Check lam L),
      (l.length ≤ wq.nOpen ∧
        l.all (fun c => decide (c.j < 2 ^ c.depth) && decide (c.depth ≤ wq.maxDepth)) = true) ↔
      ((l.map fun c => c.withPath []).length ≤ wq.nOpen ∧
        (l.map fun c => c.withPath []).all
            (fun c => decide (c.j < 2 ^ c.depth) && decide (c.depth ≤ wq.maxDepth)) = true) := by
    intro l
    rw [List.length_map, List.all_map]
    rfl
  unfold condC
  rw [key (flatF Fs'), key (flatF Fs), e]

end Same

/-! ## Part 2. A proof string with other paths -/

theorem opt_cases {α β : Type} (φ : α → β) {o o' : Option α} (h : o'.map φ = o.map φ) :
    (o' = none ∧ o = none) ∨ ∃ a a', o = some a ∧ o' = some a' ∧ φ a' = φ a := by
  cases o <;> cases o'
    <;> simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at h
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨_, _, rfl, rfl, h⟩

theorem map_erase_split (pr : Bool) (F : Forest lam L) :
    (F.split pr).map Forest.erase = F.erase.split pr := by
  cases pr with
  | true => rfl
  | false =>
    simp only [Forest.split, Bool.false_eq_true, if_false, Forest.erase, List.map_map]
    rfl

/-- one round of forestsB -/
def forestsStep (p0 pJ : Bool) (d0 dJ : ℕ) (r0 rJ : ℕ → Dig lam)
    (o0 oJ : Option (List (Check lam L))) (o2 : Option (List (Forest lam L))) :
    Option (List (Forest lam L)) :=
  match o0, oJ, o2 with
  | some a, some b, some c =>
    some (Forest.split p0 ⟨d0, r0, a.map fun c => (0, c)⟩ ++
        (Forest.split pJ ⟨dJ, rJ, b.map fun c => (0, c)⟩ ++ c))
  | _, _, _ => none

theorem erase_mk_zero (d : ℕ) (r : ℕ → Dig lam) {a a' : List (Check lam L)}
    (h : (a'.map fun c => c.withPath []) = a.map fun c => c.withPath []) :
    (⟨d, r, a'.map fun c => (0, c)⟩ : Forest lam L).erase =
      (⟨d, r, a.map fun c => (0, c)⟩ : Forest lam L).erase := by
  have := congrArg (List.map fun c : Check lam L => ((0 : ℕ), c)) h
  simp only [List.map_map] at this
  simp only [Forest.erase, List.map_map, Forest.mk.injEq, true_and]
  exact this

theorem forestsStep_erase (p0 pJ : Bool) (d0 dJ : ℕ) (r0 rJ : ℕ → Dig lam)
    {o0 o0' oJ oJ' : Option (List (Check lam L))} {o2 o2' : Option (List (Forest lam L))}
    (h0 : o0'.map (List.map fun c => c.withPath []) = o0.map (List.map fun c => c.withPath []))
    (hJ : oJ'.map (List.map fun c => c.withPath []) = oJ.map (List.map fun c => c.withPath []))
    (h2 : o2'.map (List.map Forest.erase) = o2.map (List.map Forest.erase)) :
    (forestsStep p0 pJ d0 dJ r0 rJ o0' oJ' o2').map (List.map Forest.erase) =
      (forestsStep p0 pJ d0 dJ r0 rJ o0 oJ o2).map (List.map Forest.erase) := by
  rcases opt_cases _ h0 with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, e0⟩
  · rfl
  · rcases opt_cases _ hJ with ⟨rfl, rfl⟩ | ⟨b, b', rfl, rfl, eJ⟩
    · rfl
    · rcases opt_cases _ h2 with ⟨rfl, rfl⟩ | ⟨c, c', rfl, rfl, e2⟩
      · rfl
      · simp only [forestsStep, Option.map_some, List.map_append, map_erase_split,
          erase_mk_zero d0 r0 e0, erase_mk_zero dJ rJ eJ, e2]

theorem checksOpt_reP_erase {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Option (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (P : r.Pos → List (Dig lam)) :
    (checksOpt posAt depth emb rt isRead (reP f P)).map (List.map fun c => c.withPath []) =
      (checksOpt posAt depth emb rt isRead f).map (List.map fun c => c.withPath []) := by
  rw [checksOpt_reP, Option.map_map]
  congr 1
  funext cs
  simp only [Function.comp_apply, List.map_map]
  rfl

/-- One tree: the checks of openings with other paths are the same checks, up to the paths. -/
theorem checksComp_reP_erase {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (P : r.Pos → List (Dig lam))
    (js : List ℕ) :
    (checksComp posAt depth emb rt isRead (reP f P) js).map (List.map fun c => c.withPath []) =
      (checksComp posAt depth emb rt isRead f js).map (List.map fun c => c.withPath []) := by
  rw [checksComp_reP, Option.map_map]
  congr 1
  funext cs
  simp only [Function.comp_apply, List.map_map]
  rfl

/-- The trees of one component from number k on: tree by tree, with depth and root kept, the checks
of openings with other paths are the same checks, up to the paths. -/
theorem checksTrees_reP_erase {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (P : r.Pos → List (Dig lam)) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)),
      (checksTrees posAt emb isRead (reP f P) k ds rt).map
          (List.map fun z => (z.1, z.2.1, z.2.2.map fun c => c.withPath [])) =
        (checksTrees posAt emb isRead f k ds rt).map
          (List.map fun z => (z.1, z.2.1, z.2.2.map fun c => c.withPath []))
  | _, [], _ => by simp only [checksTrees]
  | _, _ :: _, [] => by simp only [checksTrees]
  | k, d :: ds, c :: cs => by
      simp only [checksTrees]
      rcases opt_cases _ (checksComp_reP_erase (posAt k) d emb c isRead f P (List.range (2 ^ d)))
        with ⟨e1, e2⟩ | ⟨a, a', e2, e1, ea⟩
      · rw [e1, e2]
      · rcases opt_cases _ (checksTrees_reP_erase posAt emb isRead f P (k + 1) ds cs)
          with ⟨e3, e4⟩ | ⟨b, b', e4, e3, eb⟩
        · rw [e1, e2, e3, e4]
        · rw [e1, e2, e3, e4]
          simp only [Option.map_some, List.map_cons, ea, eb]

/-- The forests of the trees of one component, with their paths emptied, are the forests of the same
trees' checks with their paths emptied. -/
theorem map_erase_forestsOfTrees (pr : Bool) :
    ∀ l : List (ℕ × Dig lam × List (Check lam L)),
      (forestsOfTrees pr l).map Forest.erase =
        forestsOfTrees pr (l.map fun z => (z.1, z.2.1, z.2.2.map fun c => c.withPath []))
  | [] => rfl
  | z :: l => by
      have ih := map_erase_forestsOfTrees pr l
      have e : (⟨z.1, fun _ => z.2.1, z.2.2.map fun c => (0, c)⟩ : Forest lam L).erase =
          ⟨z.1, fun _ => z.2.1, (z.2.2.map fun c => c.withPath []).map fun c => (0, c)⟩ := by
        simp only [Forest.erase, List.map_map]
        rfl
      unfold forestsOfTrees at ih ⊢
      rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append, ih,
        map_erase_split, e]

theorem forestsB_reP :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (emb : (p : OPos s) → OSym s p → Body L)
        (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))) (P : OPos s → List (Dig lam)),
      (forestsB s A W emb rts isRead (reP f P)).map (List.map Forest.erase) =
        (forestsB s A W emb rts isRead f).map (List.map Forest.erase)
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, f, P =>
      forestsStep_erase w.pr0 w.prJ w.depth0 w.depthJ
        (fun _ => rt.1.join.getD default) (fun _ => rt.2.join.getD default)
        (checksOpt_reP_erase w.posAt0 w.depth0 (fun p => emb (.inl p)) rt.1.join
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) fun p => P (.inl p))
        (checksOpt_reP_erase w.posAtJ w.depthJ (fun p => emb (.inl p)) rt.2.join
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) fun p => P (.inl p))
        (forestsB_reP s A W (fun p => emb (.inr p)) rts (fun p => isRead (.inr p))
          (fun p => f (.inr p)) fun p => P (.inr p))

theorem checksExtW_reP {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) (P : E.Pos → List (Dig lam)) :
    ∀ ps : List E.Pos,
      (checksExtW we emb cms isRead (reP g P) ps).map (List.map fun e => (e.1, e.2.withPath [])) =
        (checksExtW we emb cms isRead g ps).map (List.map fun e => (e.1, e.2.withPath []))
  | [] => rfl
  | p :: ps => by
      have ih := checksExtW_reP we emb cms isRead g P ps
      simp only [checksExtW]
      split_ifs
      · unfold reP at ih ⊢
        cases g p with
        | none => rfl
        | some op =>
          cases h1 : checksExtW we emb cms isRead
              (fun p => (g p).map fun op => ⟨op.sym, op.salt, P p⟩) ps <;>
          cases h2 : checksExtW we emb cms isRead g ps <;> rw [h1, h2] at ih <;>
          simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at ih ⊢
          simp only [List.map_cons, ih]
          rfl
      · exact ih

section String
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
  (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
  (P1 : OPos Q.loc.shape → List (Dig lam)) (P2 : E.Pos → List (Dig lam)) (ρ : Rho Q.loc.shape)
  (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam)

/-- the last step of forestsOf -/
def forestsEnd (oA oB : Option (List (Forest lam L))) : Option (List (Forest lam L)) :=
  match oA, oB with
  | some a, some b => some (a ++ b)
  | _, _ => none

theorem forestsEnd_erase {oA oA' oB oB' : Option (List (Forest lam L))}
    (hA : oA'.map (List.map Forest.erase) = oA.map (List.map Forest.erase))
    (hB : oB'.map (List.map Forest.erase) = oB.map (List.map Forest.erase)) :
    (forestsEnd oA' oB').map (List.map Forest.erase) =
      (forestsEnd oA oB).map (List.map Forest.erase) := by
  rcases opt_cases _ hA with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, eA⟩
  · rfl
  · rcases opt_cases _ hB with ⟨rfl, rfl⟩ | ⟨b, b', rfl, rfl, eB⟩
    · rfl
    · simp only [forestsEnd, Option.map_some, List.map_append, eA, eB]

/-- The forests of a proof string with other paths are its forests, up to the paths. -/
theorem forestsOf_withPaths :
    (forestsOf Q wq embS embE cms x (π.withPaths P1 P2) ρ rts).map (List.map Forest.erase) =
      (forestsOf Q wq embS embE cms x π ρ rts).map (List.map Forest.erase) := by
  refine forestsEnd_erase (forestsB_reP _ _ _ _ _ _ _ _) ?_
  unfold forestExt
  have h := checksExtW_reP wq.ext embE cms
    (fun p => @decide (p ∈ Q.loc.extReads x ρ) (@Finset.decidableMem _ wq.ext.dec _ _))
    π.ext P2 wq.ext.all
  show ((checksExtW wq.ext embE cms _ (reP π.ext P2) wq.ext.all).map _).map _ =
    ((checksExtW wq.ext embE cms _ π.ext wq.ext.all).map _).map _
  rw [Option.map_map, Option.map_map]
  have := congrArg
    (Option.map fun cs =>
      Forest.split wq.ext.pr (⟨wq.ext.depth, fun t => cms.getD t default, cs⟩ : Forest lam L)) h
  rw [Option.map_map, Option.map_map] at this
  have e : (List.map Forest.erase ∘
        fun cs =>
          Forest.split wq.ext.pr (⟨wq.ext.depth, fun t => cms.getD t default, cs⟩ : Forest lam L)) =
      ((fun cs =>
          Forest.split wq.ext.pr (⟨wq.ext.depth, fun t => cms.getD t default, cs⟩ : Forest lam L)) ∘
        List.map fun e => (e.1, e.2.withPath [])) :=
    funext fun cs => map_erase_split _ _
  rw [e]
  exact this

theorem strictComp_reP (sMT : ℕ) {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (hr : Bool) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (P : r.Pos → List (Dig lam)) :
    strictComp sMT posAt depth hr isRead (reP f P) = strictComp sMT posAt depth hr isRead f := by
  unfold strictComp reP
  congr 1
  funext j
  cases posAt j with
  | none => rfl
  | some p =>
    dsimp only
    generalize f p = o
    cases o <;> rfl

/-- The strict-format check of the trees of one component does not read the openings' paths. -/
theorem strictTrees_reP (sMT : ℕ) {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (P : r.Pos → List (Dig lam)) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)),
      strictTrees sMT posAt isRead (reP f P) k ds rt = strictTrees sMT posAt isRead f k ds rt
  | _, [], _ => by simp only [strictTrees]
  | k, _ :: ds, [] => by
      simp only [strictTrees, strictComp_reP, strictTrees_reP sMT posAt isRead f P (k + 1) ds []]
  | k, _ :: ds, _ :: cs => by
      simp only [strictTrees, strictComp_reP, strictTrees_reP sMT posAt isRead f P (k + 1) ds cs]

theorem strictSB_reP (sMT : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))) (P : OPos s → List (Dig lam)),
      strictSB sMT s A W rts isRead (reP f P) = strictSB sMT s A W rts isRead f
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), (rt, rts), isRead, f, P => by
      have h0 := strictComp_reP sMT w.posAt0 w.depth0 rt.1.join.isSome (fun p => isRead (.inl p))
        (fun p => f (.inl p)) fun p => P (.inl p)
      have hJ := strictComp_reP sMT w.posAtJ w.depthJ rt.2.join.isSome (fun p => isRead (.inl p))
        (fun p => f (.inl p)) fun p => P (.inl p)
      have h2 := strictSB_reP sMT s A W rts (fun p => isRead (.inr p))
        (fun p => f (.inr p)) fun p => P (.inr p)
      exact congrArg₂ (· && ·) (congrArg₂ (· && ·) h0 hJ) h2

theorem strictExt_reP (sMT : ℕ) (we : WireE E) (isRead : E.Pos → Bool)
    (g : E.Pos → Option (Opening lam E.Sym)) (P : E.Pos → List (Dig lam)) :
    strictExt sMT we isRead (reP g P) = strictExt sMT we isRead g := by
  unfold strictExt reP
  congr 1
  funext p
  cases g p <;> rfl

theorem strictBB_withPaths (sMT sFS : ℕ) :
    proofHasStrictFormat sMT sFS Q wq depthReq x (π.withPaths P1 P2) ρ rts ph =
      proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph := by
  unfold proofHasStrictFormat OneProtocolProof.withPaths
  dsimp only
  rw [strictSB_reP, strictExt_reP]

theorem afterF_withPaths (Fs : List (Forest lam L)) (s : List (Dig lam)) :
    afterF Q wq depthReq x (π.withPaths P1 P2) ρ rts ph Fs s =
      afterF Q wq depthReq x π ρ rts ph Fs s := by
  unfold afterF
  have e1 : (fun p => ((π.withPaths P1 P2).ext p).map Opening.sym) =
      fun p => (π.ext p).map Opening.sym := by
    funext p
    show ((π.ext p).map _).map _ = _
    cases π.ext p <;> rfl
  have e2 : mkTr Q.loc.shape Q.ann wq.sh rts (π.withPaths P1 P2).plains
        ρ (π.withPaths P1 P2).opens =
      mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens :=
    mkTr_reP _ _ _ _ _ _ _ _
  rw [e1, e2]
  rfl

/-- afterBC, written with condC -/
theorem afterBC_eq (s : List (Dig lam)) : afterBC Q wq embS embE depthReq cms x π s ρ rts ph =
    match forestsOf Q wq embS embE cms x π ρ rts with
    | some Fs =>
      open Classical in if condC wq Fs ∧ usedUp (needF Fs) s then
        afterF Q wq depthReq x π ρ rts ph Fs s
      else pure false
    | none => pure false := by
  unfold afterBC condC
  cases forestsOf Q wq embS embE cms x π ρ rts with
  | none => rfl
  | some Fs =>
    dsimp only
    split_ifs <;> rfl

/-- afterBC does not read the paths in the openings. -/
theorem afterBC_withPaths (s : List (Dig lam)) :
    afterBC Q wq embS embE depthReq cms x (π.withPaths P1 P2) s ρ rts ph =
      afterBC Q wq embS embE depthReq cms x π s ρ rts ph := by
  have h := forestsOf_withPaths Q wq embS embE cms x π P1 P2 ρ rts
  rw [afterBC_eq, afterBC_eq]
  cases h1 : forestsOf Q wq embS embE cms x (π.withPaths P1 P2) ρ rts with
  | none =>
    cases h2 : forestsOf Q wq embS embE cms x π ρ rts with
    | none => rfl
    | some Fs => rw [h1, h2] at h; exact absurd h (by simp)
  | some Fs' =>
    cases h2 : forestsOf Q wq embS embE cms x π ρ rts with
    | none => rw [h1, h2] at h; exact absurd h (by simp)
    | some Fs =>
      rw [h1, h2] at h
      have h' : Fs'.map Forest.erase = Fs.map Forest.erase := Option.some.inj h
      dsimp only
      rw [afterF_withPaths]
      unfold afterF
      rw [runForests_same h', needF_same h']
      have hc := condC_same h' wq
      by_cases hcd : condC wq Fs ∧ usedUp (needF Fs) s
      · rw [if_pos hcd, if_pos ⟨hc.2 hcd.1, hcd.2⟩]
      · rw [if_neg hcd, if_neg fun h => hcd ⟨hc.1 h.1, h.2⟩]

end String

/-- verifyBC does not read the paths in the openings. -/
theorem verifyBC_withPaths (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (P1 : OPos Q.loc.shape → List (Dig lam)) (P2 : E.Pos → List (Dig lam)) (s : List (Dig lam)) :
    verifyBC sMT sFS t Q wq embS embP xin embE depthReq cms x (π.withPaths P1 P2) s =
      verifyBC sMT sFS t Q wq embS embP xin embE depthReq cms x π s := by
  unfold verifyBC
  show (recomputeChainOfProof t Q wq embP xin cms x π).bind _ = _
  refine congrArg _ (funext fun r => ?_)
  rcases r with _ | ⟨ρ, rts, ph⟩
  · rfl
  · dsimp only
    rw [strictBB_withPaths, afterBC_withPaths]

/-! ## Part 3. When the leaves that the verifier reads are the leaves at which the proof string
holds an opening -/

/-- the forest as pruning sees it: its depth, the numbers of its leaves, their paths -/
def Forest.plan (F : Forest lam L) : Plan lam :=
  (F.depth, F.cs.map fun e => (e.1 * 2 ^ F.depth + e.2.j, e.2.path))

theorem Forest.need_eq (F : Forest lam L) : F.need = F.plan.need := by
  simp only [Forest.need, Forest.idx, Plan.need, Plan.idx, Forest.plan, List.map_map]
  rfl

theorem readsF_eq (Fs : List (Forest lam L)) :
    readsF Fs = (Fs.map Forest.plan).flatMap Plan.reads := by
  unfold readsF
  rw [List.flatMap_map]
  rfl

theorem needF_eq (Fs : List (Forest lam L)) :
    needF Fs = ((Fs.map Forest.plan).map Plan.need).sum := by
  unfold needF
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun F _ => Forest.need_eq F

theorem map_plan_split (pr : Bool) (F : Forest lam L) :
    (F.split pr).map Forest.plan = F.plan.split pr := by
  cases pr with
  | true => rfl
  | false =>
    simp only [Forest.split, Plan.split, Bool.false_eq_true, if_false, Forest.plan, List.map_map]
    rfl

theorem of_strictComp {sMT : ℕ} {r : Round} {posAt : ℕ → Option r.Pos} {depth : ℕ} {hr : Bool}
    {isRead : r.Pos → Bool} {f : (p : r.Pos) → Option (Opening lam (r.Sym p))}
    (h : strictComp sMT posAt depth hr isRead f = true) :
    ∀ j ∈ List.range (2 ^ depth),
      ∀ p, posAt j = some p → ∀ op, f p = some op → hr = true ∧ isRead p = true := by
  intro j hj p hp op hop
  have := List.all_eq_true.1 h j hj
  simp only [hp, hop, Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2⟩

theorem plan_checksComp {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (js : List ℕ) (cs : List (Check lam L)),
      (∀ j ∈ js, ∀ p, posAt j = some p → ∀ op, f p = some op → isRead p = true) →
      checksComp posAt depth emb rt isRead f js = some cs →
      cs.map (fun c => (0 * 2 ^ depth + c.j, c.path)) =
        js.filterMap fun j => (posAt j).bind fun p => (f p).map fun op => (j, op.path)
  | [], cs, _, h => by
      obtain rfl : [] = cs := Option.some.inj h
      rfl
  | j :: js, cs, hs, h => by
      have ih := fun cs' =>
        plan_checksComp posAt depth emb rt isRead f js cs' fun j' hj' =>
          hs j' (List.mem_cons_of_mem _ hj')
      simp only [checksComp] at h
      cases hp : posAt j with
      | none =>
        rw [hp] at h
        rw [List.filterMap_cons_none (by rw [hp]; rfl)]
        exact ih cs h
      | some p =>
        rw [hp] at h
        dsimp only at h
        cases hf : f p with
        | none =>
          rw [List.filterMap_cons_none (by rw [hp]; show (f p).map _ = none; rw [hf]; rfl)]
          split_ifs at h
          · rw [hf] at h; cases h
          · exact ih cs h
        | some op =>
          rw [if_pos (hs j List.mem_cons_self p hp op hf), hf] at h
          cases hc : checksComp posAt depth emb rt isRead f js with
          | none => rw [hc] at h; cases h
          | some cs' =>
            rw [hc] at h
            obtain rfl := Option.some.inj h
            rw [List.filterMap_cons_some (b := (j, op.path))
                  (by rw [hp]; show (f p).map _ = _; rw [hf]; rfl),
              List.map_cons, ih cs' hc]
            simp

theorem plan_checksOpt {sMT : ℕ} {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Option (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (cs : List (Check lam L)) (ra : ℕ → Dig lam)
    (hs : strictComp sMT posAt depth rt.isSome isRead f = true)
    (h : checksOpt posAt depth emb rt isRead f = some cs) :
    (⟨depth, ra, cs.map fun c => (0, c)⟩ : Forest lam L).plan = planComp posAt depth f := by
  unfold Forest.plan planComp
  dsimp only
  congr 1
  rw [List.map_map]
  cases rt with
  | none =>
    obtain rfl : [] = cs := Option.some.inj h
    symm
    refine List.filterMap_eq_nil_iff.2 fun j hj => ?_
    cases hp : posAt j with
    | none => rfl
    | some p =>
      cases hf : f p with
      | none => show (f p).map _ = none; rw [hf]; rfl
      | some op => exact absurd (of_strictComp hs j hj p hp op hf).1 (by simp)
  | some x =>
    exact plan_checksComp posAt depth emb x isRead f _ cs
      (fun j hj p hp op hop => (of_strictComp hs j hj p hp op hop).2) h

/-- One tree with its root: if the strict-format check passes and no opening is missing, the
verifier's forest is the one that pruning goes through. -/
theorem plan_of_checksComp {sMT : ℕ} {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (cs : List (Check lam L)) (ra : ℕ → Dig lam)
    (hs : strictComp sMT posAt depth true isRead f = true)
    (h : checksComp posAt depth emb rt isRead f (List.range (2 ^ depth)) = some cs) :
    (⟨depth, ra, cs.map fun c => (0, c)⟩ : Forest lam L).plan = planComp posAt depth f := by
  unfold Forest.plan planComp
  dsimp only
  congr 1
  rw [List.map_map]
  exact plan_checksComp posAt depth emb rt isRead f _ cs
    (fun j hj p hp op hop => (of_strictComp hs j hj p hp op hop).2) h

/-- One tree without a root: if the strict-format check passes, the plan has no entry. -/
theorem planComp_of_noRoot {sMT : ℕ} {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (hs : strictComp sMT posAt depth false isRead f = true) :
    planComp posAt depth f = (depth, []) := by
  unfold planComp
  congr 1
  refine List.filterMap_eq_nil_iff.2 fun j hj => ?_
  cases hp : posAt j with
  | none => rfl
  | some p =>
    cases hf : f p with
    | none => show (f p).map _ = none; rw [hf]; rfl
    | some op => exact absurd (of_strictComp hs j hj p hp op hf).1 (by simp)

/-- The trees of one component from number k on (`posAt n j`: the position at leaf j of tree number
n). The verifier has a forest for each tree with a depth and a root, pruning a plan for each depth.
If the strict-format check passes and no opening is missing: tree by tree the plans are those of the
verifier's forests, and where the roots have ended they have no entry. -/
theorem planTrees_of_checksTrees {sMT : ℕ} {r : Round} (pr : Bool)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)) (l : List (ℕ × Dig lam × List (Check lam L))),
      strictTrees sMT posAt isRead f k ds rt = true →
      checksTrees posAt emb isRead f k ds rt = some l →
      planTrees pr posAt f k ds =
        (l.map fun z =>
          (Forest.split pr
            (⟨z.1, fun _ => z.2.1, z.2.2.map fun c => (0, c)⟩ : Forest lam L)).map Forest.plan) ++
          (ds.drop rt.length).map fun d => Plan.split pr (d, [])
  | _, [], _, l, _, h => by
      simp only [checksTrees] at h
      cases h
      rw [List.drop_nil]
      rfl
  | k, d :: ds, [], l, hs, h => by
      simp only [strictTrees, Bool.and_eq_true] at hs
      simp only [checksTrees] at h
      cases h
      have ih := planTrees_of_checksTrees pr posAt emb isRead f (k + 1) ds [] [] hs.2
        (by cases ds <;> simp only [checksTrees])
      rw [planTrees, planComp_of_noRoot (posAt k) d isRead f hs.1, ih]
      rfl
  | k, d :: ds, c :: cs, l, hs, h => by
      simp only [strictTrees, Bool.and_eq_true] at hs
      simp only [checksTrees] at h
      split at h
      · rename_i a b ha hb
        obtain rfl := Option.some.inj h
        rw [planTrees, planTrees_of_checksTrees pr posAt emb isRead f (k + 1) ds cs b hs.2 hb,
          List.map_cons, map_plan_split, plan_of_checksComp (posAt k) d emb c isRead f a _ hs.1 ha]
        rfl
      · cases h

/-- The trees of one component from number k on, if the strict-format check passes and no opening is
missing: the plans of all trees, in one list, are the plans of the verifier's forests, and behind
them plans without entries, for the depths where the roots have ended. -/
theorem flatten_planTrees {sMT : ℕ} {r : Round} (pr : Bool) (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (k : ℕ) (ds : List ℕ) (rt : List (Dig lam))
    (l : List (ℕ × Dig lam × List (Check lam L)))
    (hs : strictTrees sMT posAt isRead f k ds rt = true)
    (h : checksTrees posAt emb isRead f k ds rt = some l) :
    (planTrees pr posAt f k ds).flatten =
      (forestsOfTrees pr l).map Forest.plan ++
        ((ds.drop rt.length).map fun d => Plan.split pr (d, [])).flatten := by
  rw [planTrees_of_checksTrees pr posAt emb isRead f k ds rt l hs h, List.flatten_append]
  unfold forestsOfTrees
  rw [List.map_flatMap, List.flatMap_def]

/-- The trees of one component from number k on, if the strict-format check passes and no opening is
missing: if every tree has its root (hl), the verifier's forests are those that pruning goes
through. -/
theorem plan_forestsOfTrees {sMT : ℕ} {r : Round} (pr : Bool) (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (k : ℕ) (ds : List ℕ) (rt : List (Dig lam))
    (l : List (ℕ × Dig lam × List (Check lam L))) (hl : ds.length ≤ rt.length)
    (hs : strictTrees sMT posAt isRead f k ds rt = true)
    (h : checksTrees posAt emb isRead f k ds rt = some l) :
    (forestsOfTrees pr l).map Forest.plan = (planTrees pr posAt f k ds).flatten := by
  rw [flatten_planTrees pr posAt emb isRead f k ds rt l hs h, List.drop_eq_nil_of_le hl]
  simp only [List.map_nil, List.flatten_nil, List.append_nil]

/-- Plans without entries, whole or split, read no digest. (Of forests without checks:
Compile/Batch/PrunedNil.lean.) -/
theorem reads_split_nil (pr : Bool) :
    ∀ es : List ℕ,
      ((es.map fun d => Plan.split pr ((d, []) : Plan lam)).flatten).flatMap Plan.reads = []
  | [] => rfl
  | d :: es => by
      have e : ∀ n : ℕ, Octopus.reads n ([] : List (ℕ × List (Dig lam))) = [] := fun n => by
        induction n with
        | zero => rfl
        | succ n ih => exact ih
      rw [List.map_cons, List.flatten_cons, List.flatMap_append, reads_split_nil pr es,
        List.append_nil]
      cases pr with
      | false => rfl
      | true => exact (List.append_nil _).trans (e d)

/-- Plans without entries, whole or split, need no digest. (Of forests without checks:
Compile/Batch/PrunedNil.lean.) -/
theorem needAll_split_nil (pr : Bool) :
    ∀ es : List ℕ, needAll ((es.map fun d => Plan.split pr ((d, []) : Plan lam)).flatten) = 0
  | [] => rfl
  | d :: es => by
      have e : ∀ n : ℕ, Octopus.need n [] = 0 := fun n => by
        induction n with
        | zero => rfl
        | succ n ih => exact (Nat.zero_add _).trans ih
      have ih := needAll_split_nil pr es
      unfold needAll at ih ⊢
      rw [List.map_cons, List.flatten_cons, List.map_append, List.sum_append, ih, Nat.add_zero]
      cases pr with
      | false => rfl
      | true => exact (Nat.add_zero _).trans (e d)

/-- The trees of one component from number k on, if the strict-format check passes and no opening is
missing, whether or not every tree has its root: pruning reads the digests that the verifier's
forests read. -/
theorem reads_forestsOfTrees {sMT : ℕ} {r : Round} (pr : Bool) (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (k : ℕ) (ds : List ℕ) (rt : List (Dig lam))
    (l : List (ℕ × Dig lam × List (Check lam L)))
    (hs : strictTrees sMT posAt isRead f k ds rt = true)
    (h : checksTrees posAt emb isRead f k ds rt = some l) :
    ((forestsOfTrees pr l).map Forest.plan).flatMap Plan.reads =
      (planTrees pr posAt f k ds).flatten.flatMap Plan.reads := by
  rw [flatten_planTrees pr posAt emb isRead f k ds rt l hs h, List.flatMap_append,
    reads_split_nil, List.append_nil]

/-- The trees of one component from number k on, if the strict-format check passes and no opening is
missing, whether or not every tree has its root: the plans need as many digests as the verifier's
forests. -/
theorem needAll_forestsOfTrees {sMT : ℕ} {r : Round} (pr : Bool) (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (k : ℕ) (ds : List ℕ) (rt : List (Dig lam))
    (l : List (ℕ × Dig lam × List (Check lam L)))
    (hs : strictTrees sMT posAt isRead f k ds rt = true)
    (h : checksTrees posAt emb isRead f k ds rt = some l) :
    needAll ((forestsOfTrees pr l).map Forest.plan) =
      needAll (planTrees pr posAt f k ds).flatten := by
  have e := needAll_split_nil (lam := lam) pr (ds.drop rt.length)
  rw [flatten_planTrees pr posAt emb isRead f k ds rt l hs h]
  unfold needAll at e ⊢
  rw [List.map_append, List.sum_append, e, Nat.add_zero]

theorem plan_forestsB {sMT : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (emb : (p : OPos s) → OSym s p → Body L)
        (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))) (Fs : List (Forest lam L)),
      strictSB sMT s A W rts isRead f = true →
      forestsB s A W emb rts isRead f = some Fs → Fs.map Forest.plan = planB s A W f
  | [], _, _, _, _, _, _, Fs, _, h => by
      obtain rfl : [] = Fs := Option.some.inj h
      rfl
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, f, Fs, hs, h => by
      simp only [strictSB, Bool.and_eq_true] at hs
      simp only [forestsB] at h
      split at h
      · rename_i a b c ha hb hc
        obtain rfl := Option.some.inj h
        rw [List.map_append, List.map_append, map_plan_split, map_plan_split,
          plan_checksOpt _ _ _ _ _ _ a _ hs.1.1 ha, plan_checksOpt _ _ _ _ _ _ b _ hs.1.2 hb,
          plan_forestsB s A W _ rts _ _ c hs.2 hc]
        rfl
      · cases h

theorem plan_checksExtW {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    ∀ (ps : List E.Pos) (cs : List (ℕ × Check lam L)),
      (∀ p ∈ ps, ∀ op, g p = some op → isRead p = true) →
      checksExtW we emb cms isRead g ps = some cs →
      cs.map (fun e => (e.1 * 2 ^ we.depth + e.2.j, e.2.path)) =
        ps.filterMap fun p => (g p).map fun op => (extIdx we p, op.path)
  | [], cs, _, h => by
      obtain rfl : [] = cs := Option.some.inj h
      rfl
  | p :: ps, cs, hs, h => by
      have ih := fun cs' =>
        plan_checksExtW we emb cms isRead g ps cs' fun p' hp' => hs p' (List.mem_cons_of_mem _ hp')
      simp only [checksExtW] at h
      cases hf : g p with
      | none =>
        rw [List.filterMap_cons_none (by rw [hf]; rfl)]
        split_ifs at h
        · rw [hf] at h; cases h
        · exact ih cs h
      | some op =>
        rw [if_pos (hs p List.mem_cons_self op hf), hf] at h
        cases hc : checksExtW we emb cms isRead g ps with
        | none => rw [hc] at h; cases h
        | some cs' =>
          rw [hc] at h
          obtain rfl := Option.some.inj h
          rw [List.filterMap_cons_some (b := (extIdx we p, op.path)) (by rw [hf]; rfl),
            List.map_cons, ih cs' hc]
          rfl

/-- If the proof string passes the strict-format check and no opening is missing (`forestsOf`
returns forests), the verifier's forests are those that pruning goes through. -/
theorem plan_forestsOf {sMT sFS : ℕ} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    {wq : ProtocolQueryLayout lam K Q} {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
    {embE : E.Sym → Body L} {depthReq : ℕ} {cms : List (Dig lam)} {x : Y} {π : OneProtocolProof lam Q}
    {ρ : Rho Q.loc.shape} {rts : RootsOfChain lam Q.loc.shape} {ph : Phase lam} {Fs : List (Forest lam L)}
    (hs : proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph = true)
    (h : forestsOf Q wq embS embE cms x π ρ rts = some Fs) :
    Fs.map Forest.plan = planOf wq π := by
  unfold proofHasStrictFormat at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨-, s3⟩, s4⟩, -⟩, -⟩ := hs
  unfold forestsOf at h
  split at h
  · rename_i A B hA hB
    obtain rfl := Option.some.inj h
    unfold forestExt at hB
    obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 hB
    unfold planOf
    rw [List.map_append, plan_forestsB _ _ _ _ _ _ _ A s3 hA, map_plan_split]
    congr 2
    unfold Forest.plan planExt
    dsimp only
    rw [plan_checksExtW wq.ext embE cms _ π.ext wq.ext.all cs (fun p hp op hop => ?_) hcs]
    have := List.all_eq_true.1 s4 p hp
    simp only [hop, Bool.and_eq_true] at this
    exact this.1
  · cases h

/-! ## Part 4. Pruning -/

section Prune
variable {sMT sFS : ℕ} {t : Tag} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {wq : ProtocolQueryLayout lam K Q}
  {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
  {embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)} {xin : Y → Option X}
  {embE : E.Sym → Body L} {depthReq : ℕ} {cms : List (Dig lam)} {x : Y} {π : OneProtocolProof lam Q}

theorem afterBO_le {ρ : Rho Q.loc.shape} {rts : RootsOfChain lam Q.loc.shape} {ph : Phase lam}
    (hs : proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph = true) :
    AccLe (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph)
      (afterBC Q wq embS embE depthReq cms x π (sibsOf wq π) ρ rts ph) := by
  rw [afterBC_eq]
  unfold checkPrunedOpenings
  cases hFs : forestsOf Q wq embS embE cms x π ρ rts with
  | none => exact AccLe.refl _
  | some Fs =>
    dsimp only
    have hr : readsF Fs = sibsOf wq π := by rw [readsF_eq, plan_forestsOf hs hFs]; rfl
    split_ifs with hc hc'
    · rw [hr]; exact AccLe.refl _
    · refine absurd
        ⟨⟨hc.1, List.all_eq_true.2 fun c hmem => ?_⟩,
          usedUp_of_length (by rw [← hr]; exact length_readsF Fs)⟩ hc'
      have := List.all_eq_true.1 hc.2 c hmem
      simp only [Check.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at this ⊢
      exact ⟨this.1.2, this.2⟩
    · exact AccLe.of_false _
    · exact AccLe.of_false _

theorem bare_pruneO (π : OneProtocolProof lam Q) :
    (pruneO wq π).bare = π.withPaths (fun _ => []) fun _ => [] := by
  unfold pruneO BPrfO.bare OneProtocolProof.withPaths reP
  dsimp only
  congr 1
  · funext p
    cases π.opens p <;> rfl
  · funext p
    cases π.ext p <;> rfl

/-- `verifyBO` on a pruned proof string: verifyBC on the proof string itself, with its pruned set of
digests -/
theorem verifyBO_pruneO :
    verifyBO sMT sFS t Q wq embS embP xin embE depthReq cms x (pruneO wq π) =
      verifyBC sMT sFS t Q wq embS embP xin embE depthReq cms x π (sibsOf wq π) := by
  unfold verifyBO
  rw [bare_pruneO, verifyBC_withPaths]
  rfl

/-- What `verifyOneProtocol` accepts, `verifyBO` accepts after pruning. -/
theorem accLe_prune :
    AccLe (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π)
      (verifyBO sMT sFS t Q wq embS embP xin embE depthReq cms x (pruneO wq π)) := by
  rw [verifyBO_pruneO]
  unfold verifyOneProtocol verifyBC
  refine AccLe.bind _ fun r => ?_
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact AccLe.refl _
  · dsimp only
    split_ifs with hs
    · exact afterBO_le hs
    · exact AccLe.refl _

end Prune

/-! ## Part 5. Filling -/

/-! ### Lists -/

theorem sublist_map_fst_filterMap
    {α β : Type} (key : α → ℕ) (g : α → Option (ℕ × β)) (hg : ∀ a x, g a = some x → x.1 = key a) :
    ∀ l : List α, ((l.filterMap g).map Prod.fst).Sublist (l.map key)
  | [] => List.Sublist.refl _
  | a :: l => by
      cases h : g a with
      | none =>
        rw [List.filterMap_cons_none h, List.map_cons]
        exact (sublist_map_fst_filterMap key g hg l).cons _
      | some x =>
        rw [List.filterMap_cons_some h, List.map_cons, List.map_cons, hg a x h]
        exact (sublist_map_fst_filterMap key g hg l).cons₂ _

/-- in a list of pairs without repeated keys, looking up the key of an entry finds the entry -/
theorem lookup_of_mem {β : Type} :
    ∀ (l : List (ℕ × β)), (l.map Prod.fst).Nodup → ∀ x ∈ l, l.lookup x.1 = some x.2
  | [], _, x, hx => by cases hx
  | (k, v) :: l, hn, x, hx => by
      rw [List.map_cons] at hn
      obtain ⟨h1, h2⟩ := List.nodup_cons.1 hn
      rcases List.mem_cons.1 hx with rfl | hx'
      · simp
      · have hne : (x.1 == k) = false := by
          rw [beq_eq_false_iff_ne]
          intro e
          have hm : x.1 ∈ l.map Prod.fst := List.mem_map_of_mem hx'
          rw [e] at hm
          exact h1 hm
        rw [List.lookup_cons, hne]
        exact lookup_of_mem l h2 x hx'

theorem map_eq_zip {β : Type} (φ : ℕ → β) :
    ∀ (js : List ℕ) (l : List β),
      l.length = js.length → (∀ x ∈ js.zip l, φ x.1 = x.2) → js.map (fun j => (j, φ j)) = js.zip l
  | [], _, _, _ => rfl
  | j :: js, [], h, _ => by simp at h
  | j :: js, a :: l, h, hφ => by
      rw [List.zip_cons_cons] at hφ ⊢
      rw [List.map_cons, hφ (j, a) List.mem_cons_self,
        map_eq_zip φ js l (by simpa using h) fun x hx => hφ x (List.mem_cons_of_mem _ hx)]

/-! ### Filled plans -/

theorem Plan.idx_filled (T : Plan lam) (s : List (Dig lam)) : (T.filled s).idx = T.idx := by
  unfold Plan.filled Plan.idx
  dsimp only
  exact List.map_fst_zip (by rw [length_fill])

theorem Plan.need_filled (T : Plan lam) (s : List (Dig lam)) : (T.filled s).need = T.need := by
  unfold Plan.need
  rw [Plan.idx_filled]
  rfl

theorem Plan.reads_filled (T : Plan lam) (s : List (Dig lam)) (h : T.need ≤ s.length) :
    (T.filled s).reads = s.take T.need :=
  reads_fill (Dig lam) T.1 T.idx s h

theorem Plan.length_filled (T : Plan lam) (s : List (Dig lam)) :
    ∀ x ∈ (T.filled s).2, x.2.length = (T.filled s).1 := fun x hx =>
  length_of_mem_fill T.1 T.idx s x.2 (List.of_mem_zip hx).2

theorem reads_filledAll :
    ∀ (Ts : List (Plan lam)) (s : List (Dig lam)),
      needAll Ts ≤ s.length → (filledAll Ts s).flatMap Plan.reads = s.take (needAll Ts)
  | [], s, _ => by simp [filledAll, needAll]
  | T :: Ts, s, h => by
      have e : needAll (T :: Ts) = T.need + needAll Ts := by simp [needAll]
      rw [e] at h ⊢
      rw [filledAll, List.flatMap_cons, Plan.reads_filled T s (by omega),
        reads_filledAll Ts (s.drop T.need) (by rw [List.length_drop]; omega), List.take_add]

theorem length_filledAll :
    ∀ (Ts : List (Plan lam)) (s : List (Dig lam)), ∀ T ∈ filledAll Ts s, ∀ x ∈ T.2, x.2.length = T.1
  | [], _, T, hT => by cases hT
  | T0 :: Ts, s, T, hT => by
      rcases List.mem_cons.1 hT with rfl | hT
      · exact Plan.length_filled T0 s
      · exact length_filledAll Ts _ T hT

theorem needAll_append (Ts Us : List (Plan lam)) :
    needAll (Ts ++ Us) = needAll Ts + needAll Us := by simp [needAll]

theorem filledAll_append :
    ∀ (Ts Us : List (Plan lam)) (s : List (Dig lam)),
      filledAll (Ts ++ Us) s = filledAll Ts s ++ filledAll Us (s.drop (needAll Ts))
  | [], Us, s => by simp [filledAll, needAll]
  | T :: Ts, Us, s => by
      have e : needAll (T :: Ts) = T.need + needAll Ts := by simp [needAll]
      simp only [List.cons_append, filledAll, filledAll_append Ts Us, e, List.drop_drop]

theorem idx_filledAll :
    ∀ (Ts : List (Plan lam)) (s : List (Dig lam)),
      ((filledAll Ts s).flatMap Prod.snd).map Prod.fst = Ts.flatMap Plan.idx
  | [], _ => rfl
  | T :: Ts, s => by
      rw [filledAll, List.flatMap_cons, List.flatMap_cons, List.map_append, idx_filledAll Ts]
      congr 1
      exact Plan.idx_filled T s

/-- the plan T with the paths φ -/
def Plan.re (φ : ℕ → List (Dig lam)) (T : Plan lam) : Plan lam := (T.1, T.idx.map fun j => (j, φ j))

theorem map_re_eq_filledAll (φ : ℕ → List (Dig lam)) :
    ∀ (Ts : List (Plan lam)) (s : List (Dig lam)),
      (∀ T ∈ filledAll Ts s, ∀ x ∈ T.2, φ x.1 = x.2) → Ts.map (Plan.re φ) = filledAll Ts s
  | [], _, _ => rfl
  | T :: Ts, s, h => by
      rw [List.map_cons, filledAll,
        map_re_eq_filledAll φ Ts (s.drop T.need) fun T' hT' => h T' (List.mem_cons_of_mem _ hT')]
      congr 1
      unfold Plan.re Plan.filled
      rw [map_eq_zip φ T.idx _ (length_fill _ _ _) (h (T.filled s) List.mem_cons_self)]

/-- The plans Ts with the paths that pathIn finds are the filled plans, if no leaf number occurs
twice. -/
theorem map_re_pathIn (Ts : List (Plan lam))
    (s : List (Dig lam)) (hn : (Ts.flatMap Plan.idx).Nodup) :
    Ts.map (Plan.re (pathIn Ts s)) = filledAll Ts s := by
  refine map_re_eq_filledAll _ Ts s fun T hT x hx => ?_
  unfold pathIn
  rw [lookup_of_mem _ (by rw [idx_filledAll]; exact hn) x (List.mem_flatMap.2 ⟨T, hT, hx⟩)]
  rfl

theorem flatMap_idx_split (pr : Bool) (T : Plan lam) : (T.split pr).flatMap Plan.idx = T.idx := by
  cases pr with
  | true => simp [Plan.split]
  | false =>
    simp only [Plan.split, Bool.false_eq_true, if_false, List.flatMap_map, Plan.idx]
    induction T.2 with
    | nil => rfl
    | cons x xs ih =>
      rw [List.flatMap_cons, List.map_cons, ih]
      rfl

theorem split_re (pr : Bool) (φ : ℕ → List (Dig lam)) (T : Plan lam) :
    (T.re φ).split pr = (T.split pr).map (Plan.re φ) := by
  cases pr with
  | true => rfl
  | false =>
    simp only [Plan.split, Bool.false_eq_true, if_false, Plan.re, Plan.idx, List.map_map]
    rfl

/-- one tree or forest: with the paths that pathIn finds, its plans are the filled plans, if no leaf
number occurs twice -/
theorem split_re_pathIn (pr : Bool) (T : Plan lam) (hn : T.idx.Nodup) (s : List (Dig lam)) :
    (T.re (pathIn (T.split pr) s)).split pr = filledAll (T.split pr) s := by
  rw [split_re, map_re_pathIn _ _ (by rw [flatMap_idx_split]; exact hn)]

/-! ### One tree over a component -/

theorem planComp_reP {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (P : r.Pos → List (Dig lam)) :
    planComp posAt depth (reP f P) = (planComp posAt depth f).re (pathJ posAt P) := by
  unfold planComp reP Plan.re Plan.idx
  dsimp only
  rw [List.map_map, List.map_filterMap]
  congr 1
  refine List.filterMap_congr fun j _ => ?_
  cases hp : posAt j with
  | none => rfl
  | some p =>
    show ((f p).map _).map _ = ((f p).map _).map _
    cases f p with
    | none => rfl
    | some op => simp only [Option.map_some, Function.comp_apply, pathJ, hp]

theorem idx_planComp_sublist {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    (planComp posAt depth f).idx.Sublist (List.range (2 ^ depth)) := by
  have h := sublist_map_fst_filterMap (α := ℕ) id (fun j => (posAt j).bind fun p => (f p).map fun op => (j, op.path)) (fun j x hx => by
    dsimp only at hx
    cases hp : posAt j with
    | none => rw [hp] at hx; cases hx
    | some p =>
      rw [hp] at hx
      obtain ⟨op, -, rfl⟩ := Option.map_eq_some_iff.1 hx
      rfl) (List.range (2 ^ depth))
  rwa [List.map_id] at h

theorem pos_of_mem_idx_planComp {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ j ∈ (planComp posAt depth f).idx, ∃ p, posAt j = some p := by
  intro j0 hj0
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hj0
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 hx
  cases hp : posAt j with
  | none => rw [hp] at hj; cases hj
  | some p =>
    rw [hp] at hj
    obtain ⟨op, -, rfl⟩ := Option.map_eq_some_iff.1 hj
    exact ⟨p, hp⟩

theorem Plan.re_congr {φ ψ : ℕ → List (Dig lam)} (T : Plan lam) (h : ∀ j ∈ T.idx, φ j = ψ j) :
    T.re φ = T.re ψ := by
  unfold Plan.re
  congr 1
  exact List.map_congr_left fun j hj => by rw [h j hj]

/-- the plans of one tree, if the paths at its positions are those that pathIn finds in s (not all
hypotheses are named here: see the statement below) -/
theorem planComp_filled {r : Round} (pr : Bool) (posAt : ℕ → Option r.Pos) (place : r.Pos → ℕ)
    (hpl : ∀ j p, posAt j = some p → place p = j) (depth : ℕ)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (P : r.Pos → List (Dig lam))
    (s : List (Dig lam))
    (hP : ∀ j p, posAt j = some p → P p = pathIn ((planComp posAt depth f).split pr) s (place p)) :
    (planComp posAt depth (reP f P)).split pr =
      filledAll ((planComp posAt depth f).split pr) s := by
  rw [planComp_reP,
    Plan.re_congr (ψ := pathIn ((planComp posAt depth f).split pr) s) _ fun j hj => ?_]
  · exact split_re_pathIn pr _ ((idx_planComp_sublist posAt depth f).nodup List.nodup_range) s
  · obtain ⟨p, hp⟩ := pos_of_mem_idx_planComp posAt depth f j hj
    unfold pathJ
    rw [hp]
    dsimp only
    rw [hP j p hp, hpl j p hp]

/-- entry number i of the plans from tree number k on: the plans of tree number k + i, if there is a
depth number i -/
theorem getElem?_planTrees {r : Round} (pr : Bool) (posAt : ℕ → ℕ → Option r.Pos)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (i : ℕ),
      (planTrees pr posAt f k ds)[i]? =
        ds[i]?.map fun d => (planComp (posAt (k + i)) d f).split pr
  | _, [], _ => by simp [planTrees]
  | _, _ :: _, 0 => by simp [planTrees]
  | k, _ :: ds, i + 1 => by
      rw [planTrees, List.getElem?_cons_succ, List.getElem?_cons_succ,
        getElem?_planTrees pr posAt f (k + 1) ds i, show k + 1 + i = k + (i + 1) by omega]

/-- The plans of the trees of one component, from tree number k on, after the paths in the openings
are replaced by P: the old plans, filled from s. `hpl`: a position at leaf j has place j. The last
hypothesis: at each position of tree number k + i, P is the path that `pathIn` finds in what is left
of s when the digests that the trees before it need are dropped. -/
theorem planTrees_filled {r : Round} (pr : Bool) (posAt : ℕ → ℕ → Option r.Pos) (place : r.Pos → ℕ)
    (hpl : ∀ k j p, posAt k j = some p → place p = j)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (P : r.Pos → List (Dig lam)) :
    ∀ (k : ℕ) (ds : List ℕ) (s : List (Dig lam)),
      (∀ i d, ds[i]? = some d → ∀ j p, posAt (k + i) j = some p →
        P p = pathIn ((planComp (posAt (k + i)) d f).split pr)
          (s.drop (needAll ((planTrees pr posAt f k ds).take i).flatten)) (place p)) →
      (planTrees pr posAt (reP f P) k ds).flatten = filledAll (planTrees pr posAt f k ds).flatten s
  | _, [], _, _ => rfl
  | k, d :: ds, s, hP => by
      have h0 := planComp_filled pr (posAt k) place (hpl k) d f P s fun j p hp => hP 0 d rfl j p hp
      have h1 := planTrees_filled pr posAt place hpl f P (k + 1) ds
        (s.drop (needAll ((planComp (posAt k) d f).split pr))) fun i e he j p hp => by
          have hk : k + 1 + i = k + (i + 1) := by omega
          rw [hk] at hp ⊢
          refine (hP (i + 1) e he j p hp).trans ?_
          have e1 : ((planTrees pr posAt f k (d :: ds)).take (i + 1)).flatten =
              (planComp (posAt k) d f).split pr ++
                ((planTrees pr posAt f (k + 1) ds).take i).flatten := rfl
          rw [e1, needAll_append, List.drop_drop]
      show (planComp (posAt k) d (reP f P)).split pr ++
          (planTrees pr posAt (reP f P) (k + 1) ds).flatten =
        filledAll ((planComp (posAt k) d f).split pr ++ (planTrees pr posAt f (k + 1) ds).flatten) s
      rw [filledAll_append, h0, h1]

/-! ### All trees -/

theorem planB_refPaths :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (f : (p : OPos s) → Option (Opening lam (OSym s p))) (sb : List (Dig lam)),
        planB s A W (reP f (refPaths s A W f sb)) = filledAll (planB s A W f) sb
  | [], _, _, _, _, _ => rfl
  | r :: s, (a, A), (w, W), hW, f, sb => by
      have h0 := planComp_filled w.pr0 w.posAt0 w.place
        (fun j p h => (hW.1.place_posAt0 j p h).2) w.depth0 (fun p => f (.inl p))
        (fun q => refPaths (r :: s) (a, A) (w, W) f sb (.inl q)) sb fun j p hp => by
          show (if a.own p then _ else _) = _
          rw [(hW.1.place_posAt0 j p hp).1]
          rfl
      have hJ := planComp_filled w.prJ w.posAtJ w.place (fun j p h => (hW.1.place_posAtJ j p h).2)
        w.depthJ (fun p => f (.inl p)) (fun q => refPaths (r :: s) (a, A) (w, W) f sb (.inl q))
        (sb.drop (needAll ((planComp w.posAt0 w.depth0 fun p => f (.inl p)).split w.pr0)))
        fun j p hp => by
          show (if a.own p then _ else _) = _
          rw [(hW.1.place_posAtJ j p hp).1]
          rfl
      have h2 := planB_refPaths s A W hW.2 (fun p => f (.inr p))
        (sb.drop (needAll ((planComp w.posAt0 w.depth0 fun p => f (.inl p)).split w.pr0) +
            needAll ((planComp w.posAtJ w.depthJ fun p => f (.inl p)).split w.prJ)))
      have key : ∀ (x0 xJ x2 y0 yJ y2 : List (Plan lam)),
          x0 = y0 → xJ = yJ → x2 = y2 → x0 ++ (xJ ++ x2) = y0 ++ (yJ ++ y2) := by
        rintro _ _ _ _ _ _ rfl rfl rfl; rfl
      refine (key _ _ _ _ _ _ h0 hJ h2).trans ?_
      simp only [planB, filledAll_append, List.drop_drop]

/-- different positions of the external strings have different numbers in the forest of their trees
-/
def ExtInj {E : ExtSpec} (we : WireE E) : Prop := (we.all.map (extIdx we)).Nodup

theorem planExt_reP {E : ExtSpec} (we : WireE E)
    (g : E.Pos → Option (Opening lam E.Sym)) (φ : ℕ → List (Dig lam)) :
    planExt we (reP g fun p => φ (extIdx we p)) = (planExt we g).re φ := by
  unfold planExt reP Plan.re Plan.idx
  dsimp only
  rw [List.map_map, List.map_filterMap]
  congr 1
  refine List.filterMap_congr fun p _ => ?_
  cases g p <;> rfl

theorem idx_planExt_sublist {E : ExtSpec} (we : WireE E) (g : E.Pos → Option (Opening lam E.Sym)) :
    (planExt we g).idx.Sublist (we.all.map (extIdx we)) :=
  sublist_map_fst_filterMap (extIdx we) (fun p => (g p).map fun (op : Opening lam E.Sym) => (extIdx we p, op.path)) (fun p x hx => by
    obtain ⟨op, -, rfl⟩ := Option.map_eq_some_iff.1 hx
    rfl) we.all

theorem planExt_filled {E : ExtSpec} (we : WireE E) (hi : ExtInj we)
    (g : E.Pos → Option (Opening lam E.Sym)) (s : List (Dig lam)) :
    (planExt we (reP g fun p => pathIn ((planExt we g).split we.pr) s (extIdx we p))).split we.pr =
      filledAll ((planExt we g).split we.pr) s := by
  rw [planExt_reP]
  exact split_re_pathIn _ _ ((idx_planExt_sublist we g).nodup hi) s

/-! ### The proof string -/

section Fill
variable {sMT sFS : ℕ} {t : Tag} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {wq : ProtocolQueryLayout lam K Q}
  {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
  {embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)} {xin : Y → Option X}
  {embE : E.Sym → Body L} {depthReq : ℕ} {cms : List (Dig lam)} {x : Y}

/-- under `wq.OKG`, `ExtInj`: the plan of a refilled proof string is the plan of the proof string,
each forest filled with its segment of s -/
theorem planOf_refill (hwq : wq.OKG) (hi : ExtInj wq.ext) (π : OneProtocolProof lam Q) (s : List (Dig lam)) :
    planOf wq (refill wq π s) = filledAll (planOf wq π) s := by
  unfold planOf
  rw [filledAll_append]
  show planB Q.loc.shape Q.ann wq.sh (reP π.opens (refPaths Q.loc.shape Q.ann wq.sh π.opens s)) ++
      (planExt wq.ext (reP π.ext _)).split wq.ext.pr = _
  rw [planB_refPaths _ _ _ hwq.sh, planExt_filled wq.ext hi]

/-- Under `wq.OKG`, `ExtInj`, if s is long enough: pruning a refilled proof string gives the digests
back: those that `runForests` takes. -/
theorem sibsOf_refill (hwq : wq.OKG) (hi : ExtInj wq.ext) (π : OneProtocolProof lam Q) (s : List (Dig lam))
    (h : needAll (planOf wq π) ≤ s.length) :
    sibsOf wq (refill wq π s) = s.take (needAll (planOf wq π)) := by
  unfold sibsOf
  rw [planOf_refill hwq hi, reads_filledAll _ _ h]

theorem afterBC_le_fill (hwq : wq.OKG) (hi : ExtInj wq.ext) {π : OneProtocolProof lam Q} {s : List (Dig lam)}
    {ρ : Rho Q.loc.shape} {rts : RootsOfChain lam Q.loc.shape} {ph : Phase lam}
    (hs : proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph = true) :
    AccLe (afterBC Q wq embS embE depthReq cms x π s ρ rts ph)
      (checkPrunedOpenings Q wq embS embE depthReq cms x (refill wq π s) ρ rts ph) := by
  rw [afterBC_eq]
  cases hFs : forestsOf Q wq embS embE cms x π ρ rts with
  | none => exact AccLe.of_false _
  | some Fs =>
    dsimp only
    split_ifs with hc
    · have hw : (forestsOf Q wq embS embE cms x (refill wq π s) ρ rts).map (List.map Forest.erase) =
          _ :=
        forestsOf_withPaths Q wq embS embE cms x π _ _ ρ rts
      rw [hFs] at hw
      obtain ⟨Fs', hFs', he⟩ := Option.map_eq_some_iff.1 hw
      have hs' : proofHasStrictFormat sMT sFS Q wq depthReq x (refill wq π s) ρ rts ph = true :=
        (strictBB_withPaths Q wq depthReq x π _ _ ρ rts ph sMT sFS).trans hs
      have hp' := plan_forestsOf hs' hFs'
      have hp := plan_forestsOf hs hFs
      have hn : needF Fs = needAll (planOf wq π) := by rw [needF_eq, hp]; rfl
      have hr : readsF Fs' = s.take (needF Fs') := by
        rw [readsF_eq, hp', needF_same he, hn]
        exact sibsOf_refill hwq hi π s (hn ▸ hc.2.le)
      have hok := (forestsOf_spec hFs').1
      have hcC := (condC_same he wq).2 hc.1
      have hcond : (flatF Fs').length ≤ wq.nOpen ∧
          (flatF Fs').all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) = true := by
        refine ⟨hcC.1, List.all_eq_true.2 fun c hmem => ?_⟩
        have h1 := List.all_eq_true.1 hcC.2 c hmem
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        obtain ⟨F, hF, hcF⟩ := List.mem_flatMap.1 hmem
        obtain ⟨e, he', rfl⟩ := List.mem_map.1 hcF
        have hT : F.plan ∈ filledAll (planOf wq π) s := by
          rw [← planOf_refill hwq hi, ← hp']
          exact List.mem_map_of_mem hF
        have h2 : e.2.path.length = F.depth :=
          length_filledAll _ _ _ hT (e.1 * 2 ^ F.depth + e.2.j, e.2.path)
            (List.mem_map_of_mem
              (f := fun e : ℕ × Check lam L => (e.1 * 2 ^ F.depth + e.2.j, e.2.path)) he')
        simp only [Check.wellFormed, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨h2.trans (hok F hF e he').1.symm, h1.1⟩, h1.2⟩
      unfold checkPrunedOpenings
      rw [hFs']
      dsimp only
      rw [if_pos hcond, hr]
      refine AccLe.of_eq ?_
      have e1 : afterF Q wq depthReq x (refill wq π s) ρ rts ph Fs' (s.take (needF Fs')) =
          afterF Q wq depthReq x π ρ rts ph Fs' (s.take (needF Fs')) :=
        afterF_withPaths Q wq depthReq x π _ _ ρ rts ph Fs' _
      rw [e1]
      unfold afterF
      rw [runForests_take, runForests_same he]
    · exact AccLe.of_false _

theorem verifyBC_le_fill (hwq : wq.OKG) (hi : ExtInj wq.ext) (π : OneProtocolProof lam Q) (s : List (Dig lam)) :
    AccLe (verifyBC sMT sFS t Q wq embS embP xin embE depthReq cms x π s)
      (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x (refill wq π s)) := by
  unfold verifyBC verifyOneProtocol
  show AccLe ((recomputeChainOfProof t Q wq embP xin cms x π).bind _) ((recomputeChainOfProof t Q wq embP xin cms x π).bind _)
  refine AccLe.bind _ fun r => ?_
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact AccLe.refl _
  · dsimp only
    have e : proofHasStrictFormat sMT sFS Q wq depthReq x (refill wq π s) ρ rts ph =
        proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph :=
      strictBB_withPaths Q wq depthReq x π _ _ ρ rts ph sMT sFS
    rw [e]
    split_ifs with hs
    · exact afterBC_le_fill hwq hi hs
    · exact AccLe.refl _

/-- Under `wq.OKG`, `ExtInj`: what `verifyBO` accepts, `verifyOneProtocol` accepts after filling. -/
theorem accLe_fill (hwq : wq.OKG) (hi : ExtInj wq.ext) (π : BPrfO lam Q) :
    AccLe (verifyBO sMT sFS t Q wq embS embP xin embE depthReq cms x π)
      (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x (fillO wq π)) :=
  verifyBC_le_fill hwq hi π.bare π.sibs

end Fill

end Compile.Batch
