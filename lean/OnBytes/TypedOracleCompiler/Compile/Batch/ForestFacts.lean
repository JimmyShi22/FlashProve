-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ForestFacts.lean: a second form of Compile/Batch/ForestFacts.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a second form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

What differs in this file from Compile/Batch/ForestFacts.lean, comments apart: statements:
`ok_of_checksOpt`, `Counts.reqCheck`; proofs alone: `map_flatF_forestsB`, `ok_forestsB`,
`Counts.afterF`; new here: `flatF_forestsT`. Every other declaration has that file's text.

The rest of this head is the head of Compile/Batch/ForestFacts.lean, to be read with these changes;
the files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that
name, this folder's.

Compile/Batch/ForestFacts.lean: lemmas on the joint verification of opened Merkle leaves, tree by
tree (`Forest`, `runForests`, `forestsOf`, `afterF`, `checkPrunedOpenings`: Compile/Batch/Verifier.lean) (words
of this library: lean/GLOSSARY.md).

  Part 1  The forests of `forestsOf` hold the checks of `checksB` and `checksExt`, in the same
          order, and satisfy `Forest.OK`: every check has the forest's depth and the root of its
          tree (`forestsOf_spec`). Where a check comes from: `inv_checksComp`, `inv_checksExtW`.
  Part 2  For every bound that adds up along bind (`Counts`, Compile/OctopusRom.lean) in which a
          query to a leaf or node oracle counts 1, `checkPrunedOpenings` costs at most nOpen (maxDepth + 1), and
          depthReq + 1 more if the chain has joined: no more than the bound of `afterB`
          (`Counts.afterBO`).
  Part 3  Soundness within a trace: `runForest_sound`, `runForests_sound`. The first: under `F.OK`,
          with leaf numbers below 2^depth: if the joint verification of a forest accepts from a
          trace, every check of the forest, with some other path of the right length
          (`Check.withPath`), accepts from the same trace. The second: the same for a list of
          forests.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier
import Compile.OctopusRom

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Octopus
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Part 1. The forests hold the old checks -/

theorem flatF_nil : flatF ([] : List (Forest lam L)) = [] := rfl
theorem flatF_cons (F : Forest lam L) (Fs : List (Forest lam L)) :
    flatF (F :: Fs) = F.cs.map Prod.snd ++ flatF Fs := by
  simp [flatF]
theorem flatF_append (Fs Gs : List (Forest lam L)) : flatF (Fs ++ Gs) = flatF Fs ++ flatF Gs := by
  simp [flatF]

theorem map_snd_zero (a : List (Check lam L)) : (a.map fun c => ((0 : ℕ), c)).map Prod.snd = a := by
  simp [List.map_map, Function.comp_def]

theorem flatF_split (pr : Bool) (F : Forest lam L) : flatF (F.split pr) = F.cs.map Prod.snd := by
  unfold Forest.split
  cases pr with
  | true => simp [flatF]
  | false =>
    simp only [Bool.false_eq_true, if_false, flatF, List.flatMap_map]
    induction F.cs with
    | nil => rfl
    | cons e es ih =>
      rw [List.flatMap_cons, List.map_cons, ih]
      rfl

/-- Here: the forests of the trees of a component hold the checks of these trees -/
theorem flatF_forestsT (pr : Bool) :
    ∀ l : List (ℕ × Dig lam × List (Check lam L)),
      flatF (forestsT pr l) = l.flatMap fun z => z.2.2
  | [] => rfl
  | z :: l => by
      have e : forestsT pr (z :: l) =
          Forest.split pr ⟨z.1, fun _ => z.2.1, z.2.2.map fun c => (0, c)⟩ ++ forestsT pr l := by
        simp [forestsT]
      rw [e, flatF_append, flatF_split, flatF_forestsT pr l, List.flatMap_cons]
      show (z.2.2.map fun c => ((0 : ℕ), c)).map Prod.snd ++ _ = _
      rw [map_snd_zero]

theorem map_flatF_forestsB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (emb : (p : OPos s) → OSym s p → Body L)
        (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))),
      (forestsB s A W emb rts isRead f).map flatF = checksB s A W emb rts isRead f
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, f => by
      have ih := map_flatF_forestsB
        s A W (fun p => emb (.inr p)) rts (fun p => isRead (.inr p)) (fun p => f (.inr p))
      simp only [forestsB, checksB, checksOpt]
      rw [← ih]
      cases checksTrees w.posAt0 (fun p => emb (.inl p))
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depth0 (rt.1.getD []) with
      | none => rfl
      | some a =>
        cases checksTrees w.posAtJ (fun p => emb (.inl p))
            (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depthJ (rt.2.getD []) with
        | none => rfl
        | some b =>
          cases forestsB s A W (fun p => emb (.inr p)) rts
              (fun p => isRead (.inr p)) (fun p => f (.inr p)) with
          | none => rfl
          | some c =>
            simp only [Option.map_some, flatF_append, flatF_forestsT, List.append_assoc]

theorem map_snd_checksExtW {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L)
    (cms : List (Dig lam)) (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    ∀ ps : List E.Pos,
      (checksExtW we emb cms isRead g ps).map (List.map Prod.snd) = checksExt we emb cms isRead g ps
  | [] => rfl
  | p :: ps => by
      have ih := map_snd_checksExtW we emb cms isRead g ps
      simp only [checksExtW, checksExt]
      rw [← ih]
      split_ifs
      · cases g p with
        | none => rfl
        | some op =>
          cases checksExtW we emb cms isRead g ps with
          | none => rfl
          | some cs => rfl
      · rfl

/-- the pruned Merkle paths of a forest have as many digests as its joint verification takes -/
theorem Forest.length_reads (F : Forest lam L) : F.reads.length = F.need := by
  unfold Forest.reads Forest.need Forest.idx
  rw [Octopus.length_reads, List.map_map]
  rfl

theorem length_readsF : ∀ Fs : List (Forest lam L), (readsF Fs).length = needF Fs
  | [] => rfl
  | F :: Fs => by
      have e : readsF (F :: Fs) = F.reads ++ readsF Fs := by simp [readsF]
      rw [e, List.length_append, Forest.length_reads, length_readsF Fs]
      simp [needF]

/-- every check of the forest has the forest's depth and the root of its tree -/
def Forest.OK (F : Forest lam L) : Prop :=
  ∀ e ∈ F.cs, e.2.depth = F.depth ∧ e.2.root = F.treeRoot e.1

theorem Forest.OK.split {F : Forest lam L} (h : F.OK) (pr : Bool) : ∀ G ∈ F.split pr, G.OK := by
  intro G hG
  unfold Forest.split at hG
  cases pr with
  | true =>
    obtain rfl := List.mem_singleton.1 hG
    exact h
  | false =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hG
    intro e' he'
    obtain rfl := List.mem_singleton.1 he'
    exact h e' he

theorem of_mem_checksComp {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (js : List ℕ) (cs : List (Check lam L)),
      checksComp posAt depth emb rt isRead f js = some cs → ∀ c ∈ cs, c.depth = depth ∧ c.root = rt
  | [], cs, h, c, hc => by
      obtain rfl : [] = cs := Option.some.inj h
      cases hc
  | j :: js, cs, h, c, hc => by
      simp only [checksComp] at h
      split at h
      · split_ifs at h
        · split at h
          · rename_i op cs' _ hcs
            obtain rfl := Option.some.inj h
            rcases List.mem_cons.1 hc with rfl | hc
            · exact ⟨rfl, rfl⟩
            · exact of_mem_checksComp posAt depth emb rt isRead f js cs' hcs c hc
          · cases h
        · exact of_mem_checksComp posAt depth emb rt isRead f js cs h c hc
      · exact of_mem_checksComp posAt depth emb rt isRead f js cs h c hc

theorem ok_of_checksOpt {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)) (l : List (ℕ × Dig lam × List (Check lam L))),
      checksTrees posAt emb isRead f k ds rt = some l → ∀ z ∈ l,
        Forest.OK (⟨z.1, fun _ => z.2.1, z.2.2.map fun c => (0, c)⟩ : Forest lam L)
  | _, [], _, l, h, z, hz => by
      simp only [checksTrees] at h
      cases h
      cases hz
  | _, _ :: _, [], l, h, z, hz => by
      simp only [checksTrees] at h
      cases h
      cases hz
  | k, d :: ds, x :: rt, l, h, z, hz => by
      simp only [checksTrees] at h
      split at h
      · rename_i a b ha hb
        obtain rfl := Option.some.inj h
        rcases List.mem_cons.1 hz with rfl | hz
        · intro e he
          obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
          exact of_mem_checksComp (posAt k) d emb x isRead f _ a ha c hc
        · exact ok_of_checksOpt posAt emb isRead f (k + 1) ds rt b hb z hz
      · cases h

theorem ok_forestsB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (emb : (p : OPos s) → OSym s p → Body L)
        (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))) (Fs : List (Forest lam L)),
      forestsB s A W emb rts isRead f = some Fs → ∀ F ∈ Fs, F.OK
  | [], _, _, _, _, _, _, Fs, h, F, hF => by
      obtain rfl : [] = Fs := Option.some.inj h
      cases hF
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, f, Fs, h, F, hF => by
      simp only [forestsB] at h
      split at h
      · rename_i a b c ha hb hc
        obtain rfl := Option.some.inj h
        rcases List.mem_append.1 hF with hF | hF
        · obtain ⟨z, hz, hF⟩ := List.mem_flatMap.1 hF
          exact (ok_of_checksOpt _ _ _ _ _ _ _ a ha z hz).split _ F hF
        · rcases List.mem_append.1 hF with hF | hF
          · obtain ⟨z, hz, hF⟩ := List.mem_flatMap.1 hF
            exact (ok_of_checksOpt _ _ _ _ _ _ _ b hb z hz).split _ F hF
          · exact ok_forestsB s A W _ rts _ _ c hc F hF
      · cases h

theorem ok_checksExtW {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    ∀ (ps : List E.Pos) (cs : List (ℕ × Check lam L)), checksExtW we emb cms isRead g ps = some cs →
      ∀ e ∈ cs, e.2.depth = we.depth ∧ e.2.root = cms.getD e.1 default
  | [], cs, h, e, he => by
      obtain rfl : [] = cs := Option.some.inj h
      cases he
  | p :: ps, cs, h, e, he => by
      simp only [checksExtW] at h
      split_ifs at h
      · split at h
        · rename_i op cs' _ hcs
          obtain rfl := Option.some.inj h
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨rfl, rfl⟩
          · exact ok_checksExtW we emb cms isRead g ps cs' hcs e he
        · cases h
      · exact ok_checksExtW we emb cms isRead g ps cs h e he

/-- Every check that `checksComp` returns is at a leaf that holds a position, and is determined by
its leaf number. -/
theorem inv_checksComp {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (js : List ℕ) (cs : List (Check lam L)), checksComp posAt depth emb rt isRead f js = some cs →
      ∀ c ∈ cs, ∃ p op, c.j ∈ js ∧ posAt c.j = some p ∧ isRead p = true ∧ f p = some op ∧
        c = ⟨⟨emb p op.sym, op.salt⟩, c.j, op.path, rt, depth⟩
  | [], cs, h, c, hc => by
      obtain rfl : [] = cs := Option.some.inj h
      cases hc
  | j :: js, cs, h, c, hc => by
      have up : (∃ p op, c.j ∈ js ∧ posAt c.j = some p ∧ isRead p = true ∧ f p = some op ∧
            c = ⟨⟨emb p op.sym, op.salt⟩, c.j, op.path, rt, depth⟩) →
          ∃ p op, c.j ∈ j :: js ∧ posAt c.j = some p ∧ isRead p = true ∧ f p = some op ∧
            c = ⟨⟨emb p op.sym, op.salt⟩, c.j, op.path, rt, depth⟩ :=
        fun ⟨p, op, h1, h2⟩ => ⟨p, op, List.mem_cons_of_mem _ h1, h2⟩
      simp only [checksComp] at h
      split at h
      · rename_i p hp
        split_ifs at h with hr
        · split at h
          · rename_i op cs' hop hcs
            obtain rfl := Option.some.inj h
            rcases List.mem_cons.1 hc with rfl | hc
            · exact ⟨p, op, List.mem_cons_self, hp, hr, hop, rfl⟩
            · exact up (inv_checksComp posAt depth emb rt isRead f js cs' hcs c hc)
          · cases h
        · exact up (inv_checksComp posAt depth emb rt isRead f js cs h c hc)
      · exact up (inv_checksComp posAt depth emb rt isRead f js cs h c hc)

/-- the same for the positions of the external strings -/
theorem inv_checksExtW {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    ∀ (ps : List E.Pos) (cs : List (ℕ × Check lam L)), checksExtW we emb cms isRead g ps = some cs →
      ∀ e ∈ cs, ∃ p op,
        p ∈ ps ∧ isRead p = true ∧ g p = some op ∧
        e = (we.which p,
            (⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
              cms.getD (we.which p) default, we.depth⟩ : Check lam L))
  | [], cs, h, e, he => by
      obtain rfl : [] = cs := Option.some.inj h
      cases he
  | p :: ps, cs, h, e, he => by
      have up : (∃ q op,
            q ∈ ps ∧ isRead q = true ∧ g q = some op ∧
            e = (we.which q,
                (⟨⟨emb op.sym, op.salt⟩, we.leaf q, op.path,
                  cms.getD (we.which q) default, we.depth⟩ : Check lam L))) →
          ∃ q op,
            q ∈ p :: ps ∧ isRead q = true ∧ g q = some op ∧
            e = (we.which q,
                (⟨⟨emb op.sym, op.salt⟩, we.leaf q, op.path,
                  cms.getD (we.which q) default, we.depth⟩ : Check lam L)) :=
        fun ⟨q, op, h1, h2⟩ => ⟨q, op, List.mem_cons_of_mem _ h1, h2⟩
      simp only [checksExtW] at h
      split_ifs at h with hr
      · split at h
        · rename_i op cs' hop hcs
          obtain rfl := Option.some.inj h
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨p, op, List.mem_cons_self, hr, hop, rfl⟩
          · exact up (inv_checksExtW we emb cms isRead g ps cs' hcs e he)
        · cases h
      · exact up (inv_checksExtW we emb cms isRead g ps cs h e he)

/-- The forests of a proof string satisfy `Forest.OK`, and their checks are the checks of
`checksB` followed by those of `checksExt`. -/
theorem forestsOf_spec {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {wq : ProtocolQueryLayout lam K Q}
    {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L} {embE : E.Sym → Body L}
    {cms : List (Dig lam)} {x : Y} {π : OneProtocolProof lam Q} {ρ : Rho Q.loc.shape} {rts : RootsOfChain lam Q.loc.shape}
    {Fs : List (Forest lam L)} (h : forestsOf Q wq embS embE cms x π ρ rts = some Fs) :
    (∀ F ∈ Fs, F.OK) ∧
    ∃ a b,
      checksB Q.loc.shape Q.ann wq.sh embS rts
          (fun p =>
            @decide (p ∈ Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann rts π.plains))
              (@Finset.decidableMem _ wq.decO _ _)) π.opens = some a ∧
      checksExt wq.ext embE cms
          (fun p => @decide (p ∈ Q.loc.extReads x ρ) (@Finset.decidableMem _ wq.ext.dec _ _))
          π.ext wq.ext.all = some b ∧
      flatF Fs = a ++ b := by
  unfold forestsOf at h
  split at h
  · rename_i A B hA hB
    obtain rfl := Option.some.inj h
    unfold forestExt at hB
    obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 hB
    refine ⟨fun F hF => ?_, flatF A, cs.map Prod.snd, ?_, ?_, ?_⟩
    · rcases List.mem_append.1 hF with hF | hF
      · exact ok_forestsB _ _ _ _ _ _ _ A hA F hF
      · exact Forest.OK.split (F := ⟨wq.ext.depth, fun t => cms.getD t default, cs⟩)
          (ok_checksExtW _ _ _ _ _ _ cs hcs) _ F hF
    · rw [← map_flatF_forestsB, hA]; rfl
    · rw [← map_snd_checksExtW, hcs]; rfl
    · rw [flatF_append, flatF_split]
  · cases h

/-! ## Part 2. What the walks cost -/

section Cost
variable {P : {α : Type} → TypedOracleComputation lam K L α → ℕ → Prop} (hP : Counts (typedOracleFamily lam K L) P)
  (hleaf : ∀ q, P (askTypedOracle (L := L) (K := K) OracleName.leaf q) 1)
  (hnode : ∀ q, P (askTypedOracle (L := L) (K := K) OracleName.node q) 1)

include hP hleaf in
theorem Counts.leavesV : ∀ cs : List (ℕ × Check lam L), P (leavesV (K := K) cs) cs.length
  | [] => hP.pure _ _
  | e :: es => by
      refine hP.mono
        (hP.bind (t := es.length + 0) (hleaf e.2.inp) fun d =>
          hP.bind (t := 0) (Counts.leavesV es) fun _ => hP.pure _ _) ?_
      simp only [List.length_cons]; omega

include hP hleaf hnode in
theorem Counts.runForest (F : Forest lam L) (s : List (Dig lam)) :
    P (runForest (K := K) F s) (F.cs.length * (F.depth + 1)) := by
  refine hP.mono
    (hP.bind (t := F.idx.length * F.depth + 0) (Counts.leavesV hP hleaf F.cs) fun v =>
      hP.bind (t := 0)
        (hP.octC (nd := hashTreeNode (K := K) (L := L)) (fun a b => hnode _) F.depth F.idx v s)
        fun _ => hP.pure _ _) ?_
  simp only [Forest.idx, List.length_map, Nat.mul_succ]; omega

include hP hleaf hnode in
theorem Counts.runForests (m : ℕ) :
    ∀ (Fs : List (Forest lam L)) (s : List (Dig lam)), (∀ c ∈ flatF Fs, c.depth ≤ m) →
      (∀ F ∈ Fs, F.OK) → P (runForests (K := K) Fs s) ((flatF Fs).length * (m + 1))
  | [], _, _, _ => hP.pure _ _
  | F :: Fs, s, h, hok => by
      have hF : F.cs.length * (F.depth + 1) ≤ F.cs.length * (m + 1) := by
        rcases hcs : F.cs with _ | ⟨e, es⟩
        · simp
        · refine Nat.mul_le_mul_left _ (Nat.succ_le_succ ?_)
          have he : e ∈ F.cs := by rw [hcs]; exact List.mem_cons_self
          rw [← (hok F List.mem_cons_self e he).1]
          exact h _ (by rw [flatF_cons]; exact List.mem_append_left _ (List.mem_map_of_mem he))
      refine hP.mono
        (hP.bind (t := (flatF Fs).length * (m + 1) + 0)
          (hP.mono (Counts.runForest hP hleaf hnode F _) hF) fun a =>
            hP.bind (t := 0)
              (Counts.runForests m Fs _
                (fun c hc => h c (by rw [flatF_cons]; exact List.mem_append_right _ hc))
                fun G hG => hok G (List.mem_cons_of_mem _ hG))
              fun _ => hP.pure _ _) ?_
      rw [flatF_cons, List.length_append, List.length_map, Nat.add_mul]; omega

variable (hrleaf : ∀ q, P (askTypedOracle (L := L) (K := K) OracleName.rleaf q) 1)
  (hrnode : ∀ q, P (askTypedOracle (L := L) (K := K) OracleName.rnode q) 1)

include hP in
theorem Counts.climbM {node : Dig lam → Dig lam → TypedOracleComputation lam K L (Dig lam)}
    (hn : ∀ a b, P (node a b) 1) :
    ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam), P (climbM node path j c) path.length
  | [], _, _ => hP.pure _ _
  | s :: ss, j, c => by
      rw [climbM_cons]
      refine hP.mono (hP.bind (Counts.lone hn j c s) fun u => Counts.climbM hn ss (j / 2) u) ?_
      simp only [List.length_cons]; omega

include hP hrleaf hrnode in
theorem Counts.reqCheck (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (c : Dig lam) (rs : Bits) :
    P (reqCheck (L := L) (K := K) depthReq rtreq slot path c rs) (depthReq + 1) := by
  unfold Compile.Batch.reqCheck
  split_ifs with h
  · refine hP.mono
      (hP.bind (t := path.length + 0) (hrleaf _) fun d =>
        hP.bind (t := 0)
          (Counts.climbM hP (node := rnodeV (K := K) (L := L)) (fun a b => hrnode _) path slot d)
          fun _ => hP.pure _ _) ?_
    omega
  · exact hP.pure _ _

/-- the cost of the check in the request tree: 0 if the chain has not joined -/
def reqCost (depthReq : ℕ) (ph : Phase lam) : ℕ := if ph.slotVal.isSome then depthReq + 1 else 0

include hP hleaf hnode hrleaf hrnode in
theorem Counts.afterF {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (depthReq : ℕ) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) (Fs : List (Forest lam L))
    (s : List (Dig lam)) (hlen : (flatF Fs).length ≤ wq.nOpen)
    (hd : ∀ c ∈ flatF Fs, c.depth ≤ wq.maxDepth) (hok : ∀ F ∈ Fs, F.OK) :
    P (afterF Q wq depthReq x π ρ rts ph Fs s)
      (wq.nOpen * (wq.maxDepth + 1) + reqCost depthReq ph) := by
  unfold Compile.Batch.afterF reqCost reqPart
  refine hP.bind
    (hP.mono (Counts.runForests hP hleaf hnode wq.maxDepth Fs s hd hok)
      (Nat.mul_le_mul_right _ hlen)) fun ok => ?_
  cases ph.slotVal with
  | none => exact hP.bind (s := 0) (t := 0) (hP.pure _ _) fun _ => hP.pure _ _
  | some c =>
    exact hP.mono
      (hP.bind (t := 0) (Counts.reqCheck hP hrleaf hrnode _ _ _ _ _ _) fun _ => hP.pure _ _)
      (Nat.le_of_eq (Nat.add_zero _))

include hP hleaf hnode hrleaf hrnode in
/-- Under the section's hypotheses: `checkPrunedOpenings` costs at most nOpen (maxDepth + 1) + `reqCost`: no
more than the bound of `afterB` (`detBound_afterB`, Compile/Batch/GlueTools.lean). -/
theorem Counts.afterBO {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    P (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph)
      (wq.nOpen * (wq.maxDepth + 1) + reqCost depthReq ph) := by
  unfold Compile.Batch.checkPrunedOpenings
  split
  · rename_i Fs hFs
    split_ifs with hc
    · refine Counts.afterF hP hleaf hnode hrleaf hrnode Q wq depthReq x π ρ rts ph Fs _ hc.1
        (fun c hmem => ?_) (forestsOf_spec hFs).1
      have := List.all_eq_true.1 hc.2 c hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    · exact hP.pure _ _
  · exact hP.pure _ _

theorem reqCost_le (depthReq : ℕ) (ph : Phase lam) : reqCost depthReq ph ≤ depthReq + 1 := by
  unfold reqCost
  split_ifs <;> omega

end Cost

/-! ## Part 3. Soundness within a trace -/

section Sound
variable {tr : Trace (typedOracleFamily lam K L)}

theorem runsIn_leavesV :
    ∀ (cs : List (ℕ × Check lam L)) (v : List (Dig lam)), RunsIn tr (leavesV (K := K) cs) v →
      v.length = cs.length ∧
      ∀ e ∈ cs.zip v, RunsIn tr (askTypedOracle (L := L) (K := K) OracleName.leaf e.1.2.inp) e.2
  | [], v, h => by
      obtain rfl : [] = v := runsIn_pure_iff.1 h
      exact ⟨rfl, fun e he => by simp at he⟩
  | c :: cs, v, h => by
      have h' : RunsIn tr
          ((askTypedOracle (L := L) (K := K) OracleName.leaf c.2.inp).bind fun d =>
            (leavesV cs).bind fun r => OComp.pure (d :: r)) v := h
      obtain ⟨d, hd, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
      obtain ⟨r, hr, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
      obtain rfl := runsIn_pure_iff.1 h3
      obtain ⟨i1, i2⟩ := runsIn_leavesV cs r hr
      refine ⟨by show r.length + 1 = cs.length + 1; rw [i1], fun e he => ?_⟩
      have he' : e ∈ (c, (show Dig lam from d)) :: cs.zip r := he
      rcases List.mem_cons.1 he' with rfl | he
      · exact hd
      · exact i2 e he

/-- a path verification of d steps depends only on the d lowest bits of the leaf number -/
theorem climbM_add_mul (nd : Dig lam → Dig lam → TypedOracleComputation lam K L (Dig lam)) :
    ∀ (path : List (Dig lam)) (t j : ℕ) (c : Dig lam),
      climbM nd path (t * 2 ^ path.length + j) c = climbM nd path j c
  | [], _, _, _ => rfl
  | s :: ss, t, j, c => by
      have e1 : (t * 2 ^ (s :: ss).length + j) % 2 = j % 2 := by
        rw [List.length_cons, pow_succ, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right]
      have e2 : (t * 2 ^ (s :: ss).length + j) / 2 = t * 2 ^ ss.length + j / 2 := by
        rw [List.length_cons, pow_succ, ← Nat.mul_assoc, Nat.add_comm,
          Nat.add_mul_div_right _ _ (by decide : 0 < 2), Nat.add_comm]
      rw [climbM_cons, climbM_cons, e2]
      unfold Octopus.lone
      rw [e1]
      simp only [climbM_add_mul nd ss t (j / 2)]

/-- Under `F.OK`, with leaf numbers below 2^depth: if the joint verification of a forest accepts
from a trace, every check of the forest, with some other path of the right length
(`Check.withPath`), accepts from the same trace. -/
theorem runForest_sound {F : Forest lam L} (hF : F.OK) (hj : ∀ e ∈ F.cs, e.2.j < 2 ^ F.depth)
    {s : List (Dig lam)} (h : RunsIn tr (runForest (K := K) F s) true) :
    ∀ e ∈ F.cs, ∃ path : List (Dig lam),
      path.length = e.2.depth ∧ RunsIn tr (runCheck (K := K) (e.2.withPath path)) true := by
  intro e he
  have h' : RunsIn tr
      ((leavesV (K := K) F.cs).bind fun v =>
        (octC hashTreeNode F.depth F.idx v s).bind fun out =>
          OComp.pure (((upN F.depth F.idx).zip out).all fun m => decide (m.2 = F.treeRoot m.1)))
      true := h
  obtain ⟨v, hv, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
  obtain ⟨out, hout, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
  have hall := runsIn_pure_iff.1 h3
  obtain ⟨l1, l2⟩ := runsIn_leavesV F.cs v hv
  obtain ⟨n, hn, hen⟩ := List.mem_iff_getElem.1 he
  have hnv : n < v.length := by rw [l1]; exact hn
  have hz : (e, v[n]) ∈ F.cs.zip v := by
    refine List.mem_iff_getElem.2 ⟨n, by simp [hn, hnv], ?_⟩
    simp [hen]
  have hz' : (e.1 * 2 ^ F.depth + e.2.j, v[n]) ∈ F.idx.zip v := by
    unfold Forest.idx
    rw [List.zip_map_left]
    exact List.mem_map.2 ⟨(e, v[n]), hz, rfl⟩
  obtain ⟨-, o2⟩ := octSound _ _ tr (hashTreeNode (K := K) (L := L)) F.depth F.idx v s out
    (by rw [l1, Forest.idx, List.length_map]) hout
  obtain ⟨path, hp, m, hm, hm1, hm2⟩ := o2 _ hz'
  have hm1' : m.1 = e.1 := by
    rw [hm1]
    show (e.1 * 2 ^ F.depth + e.2.j) / 2 ^ F.depth = e.1
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (hj e he), Nat.zero_add]
  have hroot : m.2 = e.2.root := by
    rw [(hF e he).2, ← hm1']
    exact of_decide_eq_true (List.all_eq_true.1 hall m hm)
  refine ⟨path, hp.trans (hF e he).1.symm, ?_⟩
  show RunsIn tr
    ((askTypedOracle (L := L) (K := K) OracleName.leaf e.2.inp).bind fun d =>
      (climbM hashTreeNode path e.2.j d).bind fun r => OComp.pure (decide (r = e.2.root))) true
  refine (runsIn_bind_iff _ _ _).2 ⟨v[n], l2 _ hz, (runsIn_bind_iff _ _ _).2 ⟨m.2, ?_, ?_⟩⟩
  · have := hm2
    simp only at this
    rw [← hp, climbM_add_mul] at this
    exact this
  · rw [hroot, decide_eq_true rfl]
    exact RunsIn.pure _

theorem runForests_sound :
    ∀ (Fs : List (Forest lam L)) (s : List (Dig lam)), (∀ F ∈ Fs, F.OK) →
      (∀ c ∈ flatF Fs, c.j < 2 ^ c.depth) → RunsIn tr (runForests (K := K) Fs s) true →
      ∀ c ∈ flatF Fs, ∃ path : List (Dig lam),
        path.length = c.depth ∧ RunsIn tr (runCheck (K := K) (c.withPath path)) true
  | [], _, _, _, _, c, hc => by cases hc
  | F :: Fs, s, hok, hj, h, c, hc => by
      have h' : RunsIn tr
          ((runForest (K := K) F (s.take F.need)).bind fun a =>
            (runForests Fs (s.drop F.need)).bind fun b => OComp.pure (a && b)) true := h
      obtain ⟨a, ha, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
      obtain ⟨b, hb, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
      obtain ⟨rfl, rfl⟩ := Bool.and_eq_true_iff.1 (runsIn_pure_iff.1 h3)
      rw [flatF_cons] at hc
      rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
        refine runForest_sound (hok F List.mem_cons_self) (fun e' he' => ?_) ha e he
        rw [← (hok F List.mem_cons_self e' he').1]
        exact hj _ (by rw [flatF_cons]; exact List.mem_append_left _ (List.mem_map_of_mem he'))
      · exact runForests_sound Fs _ (fun G hG => hok G (List.mem_cons_of_mem _ hG))
          (fun c hc => hj c (by rw [flatF_cons]; exact List.mem_append_right _ hc)) hb c hc

end Sound

end TypedOracleCompiler.Compile.Batch
