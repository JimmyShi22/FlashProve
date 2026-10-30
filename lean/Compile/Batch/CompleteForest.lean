-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteForest.lean: the honest prover's openings are accepted by the end `checkPrunedOpenings` of
the strict verifier (`verifyOneProtocol`), which verifies them forest by forest (`Forest`,
Compile/Batch/Verifier.lean) (words of this library: lean/GLOSSARY.md).

The statements are for fixed oracle functions, each under the hypotheses of its statement. The end
`checkPrunedOpenings` of the strict verifier (Compile/Batch/Verifier.lean) verifies all opened leaves of a tree
together, from pruned Merkle paths, where the wire record's flag says so (`pr0`, `prJ`,
Iop/BatchWire.lean; `pr`, Iop/Wire.lean), else one by one. That every single honest path is accepted
(Compile/Batch/CompleteOpen.lean) is not enough here: two accepted paths could disagree on a node
that they share, and the joint verification follows only one of them. Honest paths are read off one
tree.

  Part 1  `HonestForest`: all checks of a forest come from one function g from leaf numbers to leaf
          digests (`hpath`, `topG`, Hash/OctopusFacts.lean); `evalsTo_runForest`,
          `evalsTo_runForests`: then the verification accepts.
  Part 2  The forests of the honest proof string are honest: `honest_of_checksOpt`,
          `honest_forestsB` (token trees, `TTree`, Compile/Batch/TokTree.lean, over prover
          messages), `honest_forestExt` (trees over encoded indices; several trees are one forest).
  Part 3  `evalsTo_afterBO`: on the honest proof string `checkPrunedOpenings` accepts, from the hypotheses of
          `evalsTo_afterChain` (Compile/Batch/CompleteOpen.lean), hpl and hreq (see its statement).

Notation: `EvalsTo f x a` (Compile/MerkleRom.lean): a proposition: under the oracle functions f the
algorithm x returns a, whatever its coins; `vs`: a `List Bits`: the store: the list of strings for
which the tokens stand (the head of Compile/Batch/CompleteRef.lean); `RoundsOK`
(Compile/Batch/CompleteChain.lean): a proposition: the trees of all rounds of a local transcript are
kept correctly, relative to a store: tjs are the trees over the slot's components, t0s those over
the shared components, rts the roots as the verifier has them; `CompOK`
(Compile/Batch/CompleteChain.lean): a proposition: one component of one round: it has no tree and no
root; or the prover keeps its tree correctly, and the verifier has its root; `opT`
(Compile/Batch/CompleteOpen.lean): the honest opening of the position p in the token tree tr over (a
component of) the oracle o; `honestExt` (Compile/Batch/CompleteOpen.lean): the honest opening of an
external position; `ExtOK` (Compile/Batch/CompleteOpen.lean): a proposition: the external trees fit
the external strings; `depthReq`: a natural number; in `QueryLayout` (Iop/BatchWire.lean): depth of a
request tree: there are 2^depthReq slots.
-/
import Compile.Batch.CompleteOpen
import Compile.Batch.ForestFacts
import Compile.OctopusList

noncomputable section

namespace Compile.Batch.Cmpl
open Iop Rom Octopus

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L))

/-! ## Part 1. Honest forests pass -/

/-- The checks of the forest are read off one honest forest: g holds the leaf digests; every check
has the number of a leaf of its tree, its input hashes to the digest of its leaf, its path is the
honest path, and the root of its tree is the honest root. -/
def HonestForest (F : Forest lam L) : Prop :=
  ∃ g : ℕ → Dig lam, ∀ e ∈ F.cs,
    e.2.j < 2 ^ F.depth ∧
    leafFB f e.2.inp = g (e.1 * 2 ^ F.depth + e.2.j) ∧
    e.2.path = hpath (nodeFB f) F.depth g (e.1 * 2 ^ F.depth + e.2.j) ∧
    F.treeRoot e.1 = topG (nodeFB f) F.depth g e.1

theorem evalsTo_leavesV :
    ∀ cs : List (ℕ × Check lam L),
      EvalsTo f (leavesV (K := K) cs) (cs.map fun e => leafFB f e.2.inp)
  | [] => (evaluates_eager f).pure _
  | e :: es =>
    (evaluates_eager f).bind (evalsTo_ask f OracleName.leaf e.2.inp)
      ((evaluates_eager f).bind (evalsTo_leavesV es) ((evaluates_eager f).pure _))

omit f in
theorem of_mem_zip_map {α β : Type} (φ : α → β) :
    ∀ (l : List α) (m : α × β), m ∈ l.zip (l.map φ) → m.1 ∈ l ∧ m.2 = φ m.1
  | [], m, h => by simp at h
  | a :: l, m, h => by
      rw [List.map_cons, List.zip_cons_cons] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨List.mem_cons_self, rfl⟩
      · exact ⟨List.mem_cons_of_mem _ (of_mem_zip_map φ l m h).1, (of_mem_zip_map φ l m h).2⟩

variable {f} in
/-- The verification of an honest forest, with its pruned Merkle paths (`F.reads`), accepts. -/
theorem evalsTo_runForest {F : Forest lam L} (h : HonestForest f F) :
    EvalsTo f (runForest (K := K) F F.reads) true := by
  obtain ⟨g, hg⟩ := h
  have h1 : (F.cs.map fun e => leafFB f e.2.inp) = F.idx.map g := by
    unfold Forest.idx
    rw [List.map_map]
    exact List.map_congr_left fun e he => (hg e he).2.1
  have h2 : F.reads = reads F.depth (F.idx.map fun j => (j, hpath (nodeFB f) F.depth g j)) := by
    unfold Forest.reads Forest.idx
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun e he => by rw [(hg e he).2.2.1]; rfl
  have h3 := Octopus.complete (Dig lam) (nodeFB f) F.depth g F.idx
  have hall : (((upN F.depth F.idx).zip
          (octF (nodeFB f) F.depth F.idx (F.cs.map fun e => leafFB f e.2.inp) F.reads)).all
        fun m => decide (m.2 = F.treeRoot m.1)) = true := by
    rw [h1, h2, h3]
    refine List.all_eq_true.2 fun m hm => decide_eq_true ?_
    obtain ⟨m1, m2⟩ := of_mem_zip_map _ _ m hm
    obtain ⟨k, hk, hk2⟩ := mem_upN F.depth F.idx m.1 m1
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
    have e1 : m.1 = e.1 := by
      rw [hk2, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt (hg e he).1, Nat.zero_add]
    rw [m2, e1, (hg e he).2.2.2]
  refine (evaluates_eager f).bind (evalsTo_leavesV f F.cs)
    ((evaluates_eager f).bind
      ((evaluates_eager f).octC (qN := hashTreeNode (L := L) (K := K)) (hN := nodeFB f)
        (fun a b => evalsTo_ask f OracleName.node (List.ofFn a, List.ofFn b)) F.depth F.idx _ _) ?_)
  rw [hall]
  exact (evaluates_eager f).pure true

variable {f} in
theorem evalsTo_runForests :
    ∀ Fs : List (Forest lam L),
      (∀ F ∈ Fs, HonestForest f F) → EvalsTo f (runForests (K := K) Fs (readsF Fs)) true
  | [], _ => (evaluates_eager f).pure _
  | F :: Fs, h => by
      have e : readsF (F :: Fs) = F.reads ++ readsF Fs := by simp [readsF]
      unfold runForests
      rw [e, List.take_left' (Forest.length_reads F), List.drop_left' (Forest.length_reads F)]
      exact (evaluates_eager f).bind (evalsTo_runForest (h F List.mem_cons_self))
        ((evaluates_eager f).bind
          (evalsTo_runForests Fs fun G hG => h G (List.mem_cons_of_mem _ hG))
          ((evaluates_eager f).pure _))

/-! ## Part 2. The forests of the honest proof string are honest

(each under the hypotheses of its statement) -/

variable {f} in
/-- the parts of an honest forest are honest -/
theorem HonestForest.split {F : Forest lam L} (h : HonestForest f F) (pr : Bool) :
    ∀ G ∈ F.split pr, HonestForest f G := by
  intro G hG
  unfold Forest.split at hG
  cases pr with
  | true =>
    obtain rfl := List.mem_singleton.1 hG
    exact h
  | false =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hG
    obtain ⟨g, hg⟩ := h
    refine ⟨g, fun e' he' => ?_⟩
    obtain rfl := List.mem_singleton.1 he'
    exact hg e' he

theorem honest_of_checksOpt {sMT : ℕ} {r : Round} (posAt : ℕ → Option r.Pos) (place : r.Pos → ℕ)
    (hpl : ∀ j p, posAt j = some p → place p = j) (depth : ℕ) (emb : (p : r.Pos) → r.Sym p → Body L)
    (o : r.Orc) (tr : Option TTree) (rt : Option (Dig lam)) (vs : List Bits)
    (htr : CompOK f sMT vs tr rt depth (bodyAt posAt emb o)) (isRead : r.Pos → Bool)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (hg : ∀ t,
      tr = some t → ∀ j p, posAt j = some p → isRead p = true → g p = some (opT place vs t o p))
    (cs : List (Check lam L)) (h : checksOpt posAt depth emb rt isRead g = some cs) :
    HonestForest f (⟨depth, fun _ => rt.getD default, cs.map fun c => (0, c)⟩ : Forest lam L) := by
  match tr, rt, htr with
  | none, none, _ =>
    obtain rfl : [] = cs := Option.some.inj h
    exact ⟨fun _ => default, fun e he => by cases he⟩
  | some t, some c, htr =>
    obtain ⟨⟨-, -, -, h4⟩, hc⟩ := htr
    set digs : List (Dig lam) :=
      (List.range (2 ^ depth)).map fun j =>
        leafFB f ⟨bodyAt posAt emb o j, vs.getD (t.salts.getD j 0) []⟩ with hdigs
    have hlen : digs.length = 2 ^ depth := by simp [hdigs]
    have hblock : ∀ i < 2 ^ depth,
        (fun i => digs.getD i default) (0 * 2 ^ depth + i) = digs.getD i default :=
      fun i _ => by simp
    refine ⟨fun i => digs.getD i default, fun e he => ?_⟩
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 he
    obtain ⟨p, op, hj, hpos, hr, hop, hform⟩ :=
      inv_checksComp posAt depth emb c isRead g _ cs h c' hc'
    have hjl : c'.j < 2 ^ depth := List.mem_range.1 hj
    rw [hg t rfl c'.j p hpos hr] at hop
    obtain rfl := Option.some.inj hop
    have hp : place p = c'.j := hpl _ p hpos
    refine ⟨hjl, ?_, ?_, ?_⟩
    · show leafFB f c'.inp = digs.getD (0 * 2 ^ depth + c'.j) default
      rw [hform]
      simp only [opT, hp, Nat.zero_mul, Nat.zero_add, hdigs, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range hjl, Option.map_some, Option.getD_some, bodyAt, hpos]
    · show c'.path = _
      rw [← pathOf_eq_hpath (nodeFB f) depth 0 digs _ c'.j hlen hblock hjl,
        ← pathOf_map (dv lam vs) (nodeFB f) depth t.levels digs c'.j hlen hjl h4, hform]
      simp only [opT, hp]
    · show c = _
      rw [← rootOf_eq_topG (nodeFB f) depth 0 digs _ hlen hblock, hc]
      exact rootOf_map (dv lam vs) (nodeFB f) depth t.levels digs hlen h4

/-- One tree that the prover keeps correctly, against its own root, under the hypotheses below: the
forest of its checks is honest. -/
theorem honest_of_checksComp {sMT : ℕ} {r : Round} (posAt : ℕ → Option r.Pos) (place : r.Pos → ℕ)
    (hpl : ∀ j p, posAt j = some p → place p = j) (depth : ℕ) (emb : (p : r.Pos) → r.Sym p → Body L)
    (o : r.Orc) (t : TTree) (vs : List Bits)
    (htr : TTreeOK f sMT vs t depth (bodyAt posAt emb o)) (isRead : r.Pos → Bool)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (hg : ∀ j p, posAt j = some p → isRead p = true → g p = some (opT place vs t o p))
    (cs : List (Check lam L))
    (h : checksComp posAt depth emb (dv lam vs t.root) isRead g (List.range (2 ^ depth)) =
      some cs) :
    HonestForest f
      (⟨depth, fun _ => dv lam vs t.root, cs.map fun c => (0, c)⟩ : Forest lam L) := by
  obtain ⟨-, -, -, h4⟩ := htr
  set digs : List (Dig lam) :=
    (List.range (2 ^ depth)).map fun j =>
      leafFB f ⟨bodyAt posAt emb o j, vs.getD (t.salts.getD j 0) []⟩ with hdigs
  have hlen : digs.length = 2 ^ depth := by simp [hdigs]
  have hblock : ∀ i < 2 ^ depth,
      (fun i => digs.getD i default) (0 * 2 ^ depth + i) = digs.getD i default :=
    fun i _ => by simp
  refine ⟨fun i => digs.getD i default, fun e he => ?_⟩
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 he
  obtain ⟨p, op, hj, hpos, hr, hop, hform⟩ :=
    inv_checksComp posAt depth emb (dv lam vs t.root) isRead g _ cs h c' hc'
  have hjl : c'.j < 2 ^ depth := List.mem_range.1 hj
  rw [hg c'.j p hpos hr] at hop
  obtain rfl := Option.some.inj hop
  have hp : place p = c'.j := hpl _ p hpos
  refine ⟨hjl, ?_, ?_, ?_⟩
  · show leafFB f c'.inp = digs.getD (0 * 2 ^ depth + c'.j) default
    rw [hform]
    simp only [opT, hp, Nat.zero_mul, Nat.zero_add, hdigs, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range hjl, Option.map_some, Option.getD_some, bodyAt, hpos]
  · show c'.path = _
    rw [← pathOf_eq_hpath (nodeFB f) depth 0 digs _ c'.j hlen hblock hjl,
      ← pathOf_map (dv lam vs) (nodeFB f) depth t.levels digs c'.j hlen hjl h4, hform]
    simp only [opT, hp]
  · show dv lam vs t.root = _
    rw [← rootOf_eq_topG (nodeFB f) depth 0 digs _ hlen hblock]
    exact rootOf_map (dv lam vs) (nodeFB f) depth t.levels digs hlen h4

/-- The trees of one component from number k on (`posAt n j`: the position at leaf j of tree number
n; `leaf n`: the leaves of tree number k + n), each kept correctly, against their own roots, under
the hypotheses below: for each tree the forest of its checks is honest. -/
theorem honest_of_checksTrees {sMT : ℕ} {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (place : r.Pos → ℕ) (hpl : ∀ n j p, posAt n j = some p → place p = j)
    (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) (vs : List Bits) (isRead : r.Pos → Bool)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree) (leaf : ℕ → ℕ → Body L),
      (∀ n, leaf n = bodyAt (posAt (k + n)) emb o) →
      OTreesOK f sMT vs ds trs leaf →
      (∀ n t, trs[n]? = some t →
        ∀ j p, posAt (k + n) j = some p → isRead p = true → g p = some (opT place vs t o p)) →
      ∀ l, checksTrees posAt emb isRead g k ds (rootsV lam vs trs) = some l →
        ∀ z ∈ l,
          HonestForest f (⟨z.1, fun _ => z.2.1, z.2.2.map fun c => (0, c)⟩ : Forest lam L)
  | _, [], [], _, _, _, _, l, h, z, hz => by
      simp only [checksTrees] at h
      cases h
      cases hz
  | _, [], _ :: _, _, _, hOK, _, _, _, _, _ => False.elim hOK
  | _, _ :: _, [], _, _, hOK, _, _, _, _, _ => False.elim hOK
  | k, d :: ds, tr :: trs, leaf, hleaf, hOK, hg, l, h, z, hz => by
      obtain ⟨h0, hrest⟩ := hOK
      rw [hleaf 0] at h0
      have h : checksTrees posAt emb isRead g k (d :: ds)
          (dv lam vs tr.root :: rootsV lam vs trs) = some l := h
      simp only [checksTrees] at h
      split at h
      · rename_i a b ha hb
        obtain rfl := Option.some.inj h
        rcases List.mem_cons.1 hz with rfl | hz
        · exact honest_of_checksComp f (posAt k) place (hpl k) d emb o tr vs h0 isRead g
            (hg 0 tr List.getElem?_cons_zero) a ha
        · exact honest_of_checksTrees posAt place hpl emb o vs isRead g (k + 1) ds trs
            (fun n => leaf (n + 1))
            (fun n => (hleaf (n + 1)).trans (by rw [show k + (n + 1) = k + 1 + n by omega])) hrest
            (fun n t ht j p hp hr =>
              hg (n + 1) t (by rw [List.getElem?_cons_succ]; exact ht) j p
                (by rw [show k + (n + 1) = k + 1 + n by omega]; exact hp) hr)
            b hb z hz
      · cases h

/-- One component with a list of trees, under the hypotheses below: its forests, each tree whole or
split, are honest. A component without a root has no forest. -/
theorem honest_forestsOfTrees {sMT : ℕ} {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (place : r.Pos → ℕ) (hpl : ∀ n j p, posAt n j = some p → place p = j) (ds : List ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) (trs : List TTree) (rts : List (Dig lam))
    (vs : List Bits) (htr : CompsOK f sMT vs trs rts ds fun n => bodyAt (posAt n) emb o)
    (isRead : r.Pos → Bool) (g : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (hg : ∀ n t, trs[n]? = some t →
      ∀ j p, posAt n j = some p → isRead p = true → g p = some (opT place vs t o p))
    (pr : Bool) (l : List (ℕ × Dig lam × List (Check lam L)))
    (h : checksTrees posAt emb isRead g 0 ds rts = some l) :
    ∀ F ∈ forestsOfTrees pr l, HonestForest f F := by
  intro F hF
  obtain ⟨z, hz, hF⟩ := List.mem_flatMap.1 hF
  rcases htr with ⟨-, rfl⟩ | ⟨htr, rfl⟩
  · have e : l = [] := by
      cases ds <;> simp only [checksTrees] at h <;> exact (Option.some.inj h).symm
    rw [e] at hz
    cases hz
  · exact (honest_of_checksTrees f posAt place hpl emb o vs isRead g 0 ds trs _
      (fun n => by rw [Nat.zero_add]) htr
      (fun n t ht j p hp hr => hg n t ht j p (by rw [Nat.zero_add] at hp; exact hp) hr)
      l h z hz).split pr F hF

theorem honest_forestsB {sMT : ℕ} (vs : List Bits) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (embS : (p : OPos s) → OSym s p → Body L)
          (τ : Tr s) (tjs t0s : List (Option TTree)) (rts : RootsOfChain lam s),
        RoundsOK f sMT vs s A W embS τ tjs t0s rts →
        ∀ (isRead : OPos s → Bool) (g : (p : OPos s) → Option (Opening lam (OSym s p))),
          OpensOK vs s A W τ tjs t0s isRead g →
          ∀ Fs, forestsB s A W embS rts isRead g = some Fs → ∀ F ∈ Fs, HonestForest f F
  | [], _, _, _, _, _, _, _, _, _, _, _, _, Fs, h, F, hF => by
      obtain rfl : [] = Fs := Option.some.inj h
      cases hF
  | r :: s, (a, A), (w, W), hW, embS, (m, _, τ), tjs, t0s, (rt, rts), htr, isRead, g, hg, Fs, h, F, hF => by
      obtain ⟨tj, t0, tjs', t0s', rfl, rfl, h0, hj, -, -, -, -, hrest⟩ := htr
      simp only [forestsB] at h
      split at h
      · rename_i c0 cJ c2 e0 eJ e2
        obtain rfl := Option.some.inj h
        rcases List.mem_append.1 hF with hF | hF
        · exact (honest_of_checksOpt f w.posAt0 w.place
              (fun j p h => (hW.1.place_posAt0 j p h).2) w.depth0 (fun p => embS (.inl p))
              m.1 t0 rt.1.join vs h0 (fun p => isRead (.inl p)) (fun p => g (.inl p))
              (fun t ht j p hpos hp =>
                hg.1 t (by rw [List.headD_cons]; exact ht) p (hW.1.place_posAt0 j p hpos).1 hp)
              c0 e0).split
            _ F hF
        · rcases List.mem_append.1 hF with hF | hF
          · exact (honest_of_checksOpt f w.posAtJ w.place
                (fun j p h => (hW.1.place_posAtJ j p h).2) w.depthJ (fun p => embS (.inl p))
                m.1 tj rt.2.join vs hj (fun p => isRead (.inl p)) (fun p => g (.inl p))
                (fun t ht j p hpos hp =>
                  hg.2.1 t (by rw [List.headD_cons]; exact ht) p (hW.1.place_posAtJ j p hpos).1 hp)
                cJ eJ).split
              _ F hF
          · exact honest_forestsB vs s A W hW.2 (fun p => embS (.inr p)) τ tjs' t0s' rts hrest
              (fun p => isRead (.inr p)) (fun p => g (.inr p)) hg.2.2 c2 e2 F hF
      · cases h

theorem honest_forestExt {sMT : ℕ} {E : ExtSpec} (we : WireE E) (embE : E.Sym → Body L)
    (vs : List Bits) (trees : List (TreeH lam)) (y : E.Str) (hext : ExtOK f sMT we embE vs trees y)
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym))
    (hg : ∀ p, isRead p = true → g p = some (honestExt we vs trees y p)) (Fs : List (Forest lam L))
    (h : forestExt we embE (trees.map TreeH.root) isRead g = some Fs) :
    ∀ F ∈ Fs, HonestForest f F := by
  unfold forestExt at h
  obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 h
  refine HonestForest.split
    (F := ⟨we.depth, fun t => (trees.map TreeH.root).getD t default, cs⟩) ?_ _
  refine ⟨fun i =>
      ((trees.getD (i / 2 ^ we.depth) ⟨[], []⟩).levels.headD []).getD (i % 2 ^ we.depth) default,
    fun e he => ?_⟩
  obtain ⟨p, op, -, hr, hop, rfl⟩ := inv_checksExtW we embE _ isRead g _ cs hcs e he
  rw [hg p hr] at hop
  obtain rfl := Option.some.inj hop
  obtain ⟨e1, e2, leaf, ⟨-, -, -, h4⟩, e4⟩ := hext p
  set T := trees.getD (we.which p) ⟨[], []⟩ with hT
  set digs : List (Dig lam) :=
    (List.range (2 ^ we.depth)).map fun j =>
      leafFB f ⟨(leaf j).1, saltVal vs (T.salts.getD j none)⟩ with hdigs
  have hlen : digs.length = 2 ^ we.depth := by simp [hdigs]
  have hhead : T.levels.headD [] = digs := by
    obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons (nodeFB f) we.depth digs
    rw [h4, hls]; rfl
  have hblock : ∀ i < 2 ^ we.depth,
      (fun i =>
            ((trees.getD (i / 2 ^ we.depth) ⟨[], []⟩).levels.headD []).getD
              (i % 2 ^ we.depth) default)
          (we.which p * 2 ^ we.depth + i) =
        digs.getD i default := by
    intro i hi
    have d1 : (we.which p * 2 ^ we.depth + i) / 2 ^ we.depth = we.which p := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt hi, Nat.zero_add]
    have d2 : (we.which p * 2 ^ we.depth + i) % 2 ^ we.depth = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    show ((trees.getD ((we.which p * 2 ^ we.depth + i) / 2 ^ we.depth)
          ⟨[], []⟩).levels.headD []).getD
        ((we.which p * 2 ^ we.depth + i) % 2 ^ we.depth) default = _
    rw [d1, d2, ← hT, hhead]
  refine ⟨e2, ?_, ?_, ?_⟩
  · show leafFB f ⟨embE (honestExt we vs trees y p).sym, (honestExt we vs trees y p).salt⟩ = _
    rw [hblock _ e2]
    simp only [honestExt, hdigs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range e2, Option.map_some, Option.getD_some, e4]
    rw [hT, List.getD_eq_getElem?_getD]
  · show (honestExt we vs trees y p).path = _
    rw [← pathOf_eq_hpath (nodeFB f) we.depth (we.which p) digs _ (we.leaf p) hlen hblock e2, ← h4]
    rfl
  · show (trees.map TreeH.root).getD (we.which p) default = _
    rw [← rootOf_eq_topG (nodeFB f) we.depth (we.which p) digs _ hlen hblock, ← h4]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem e1, hT, TreeH.root]

/-! ## Part 3. After the chain -/

/-- What the strict verifier does (`checkPrunedOpenings`) after it has recomputed the chain and made the
strict-format check (`proofHasStrictFormat`), on the honest proof string: it accepts. The hypotheses are those
of `evalsTo_afterChain` (Compile/Batch/CompleteOpen.lean), for the fields of the string π, and hpl;
hreq: the check in the request tree accepts, if the chain has joined. (By their names below: hwq:
`wq.OKG`; hloc: `IsLocal`; hC: `Coherent`; hDe; hext: `ExtOK`; hτ: `Q.loc.accept x y τ = true`; htr:
`RoundsOK`; hpl: `π.plains = τ.plains`; hR1, hg1: `OpensOK` at the positions that are read; hR2,
hg2: `honestExt` at the external positions that are read.) -/
theorem evalsTo_afterBO {sMT : ℕ} {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (hwq : wq.OKG) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (trees : List (TreeH lam)) (y : E.Str) (x : Y) (hDe : wq.ext.depth ≤ wq.maxDepth)
    (vs : List Bits) (hext : ExtOK f sMT wq.ext embE vs trees y) (τ : Tr Q.loc.shape)
    (hτ : Q.loc.accept x y τ = true) (tjs t0s : List (Option TTree)) (rts : RootsOfChain lam Q.loc.shape)
    (htr : RoundsOK f sMT vs Q.loc.shape Q.ann wq.sh embS τ tjs t0s rts) (π : OneProtocolProof lam Q)
    (hpl : π.plains = τ.plains) (isR1 : OPos Q.loc.shape → Bool)
    (hR1 : ∀ p, isR1 p = true ↔ p ∈ Q.loc.reads x τ.rho τ.plains)
    (hg1 : OpensOK vs Q.loc.shape Q.ann wq.sh τ tjs t0s isR1 π.opens) (isR2 : E.Pos → Bool)
    (hR2 : ∀ p, isR2 p = true ↔ p ∈ Q.loc.extReads x τ.rho)
    (hg2 : ∀ p, isR2 p = true → π.ext p = some (honestExt wq.ext vs trees y p)) (ph : Phase lam)
    (hreq : EvalsTo f (reqPart (K := K) (L := L) depthReq π ph) true) :
    EvalsTo f (checkPrunedOpenings Q wq embS embE depthReq (trees.map TreeH.root) x π τ.rho rts ph) true := by
  obtain ⟨a, a1, a2, a3⟩ := checksB_ok f vs wq.maxDepth Q.loc.shape Q.ann wq.sh hwq.sh hwq.depth
    embS τ tjs t0s rts htr isR1 π.opens hg1 (Q.loc.reads x τ.rho τ.plains) fun p hp => (hR1 p).1 hp
  obtain ⟨b, b1, b2, b3⟩ := checksExt_ok f wq.ext embE vs trees y hext isR2 π.ext wq.maxDepth hDe
    wq.ext.all fun p _ hp => hg2 p hp
  have hb : b.length ≤ (Q.loc.extReads x τ.rho).card := by
    rw [b3]; exact length_filter_le_card _ hwq.ext.nodup isR2 _ fun p hp => (hR2 p).1 hp
  have hgood : ∀ c ∈ a ++ b, GoodCheck f wq.maxDepth c := fun c hc => by
    rcases List.mem_append.1 hc with h | h
    · exact a2 c h
    · exact b2 c h
  have hcond : (a ++ b).length ≤ wq.nOpen ∧
      (a ++ b).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) = true := by
    refine ⟨?_, List.all_eq_true.2 fun c hc => ?_⟩
    · rw [List.length_append]
      exact le_trans (Nat.add_le_add a3 hb) (hwq.opens x τ.rho τ.plains)
    · simp [(hgood c hc).1, (hgood c hc).2.1]
  have hacc : Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
        (mkTr Q.loc.shape Q.ann wq.sh rts τ.plains τ.rho π.opens) = true := by
    rw [← hτ]
    refine (hloc x y _ τ _ (rho_mkTr _ _ _ _ _ _ _).symm
      ((plains_mkTr _ _ _ _ _ _ _).trans (effPlains_eq f _ _ _ embS τ tjs t0s rts hC htr)).symm
      (fun p hp => ?_) fun p hp => ?_).symm
    · refine (hwq.ext.build_rd _ p _ ?_).symm
      rw [hg2 p ((hR2 p).2 hp)]; rfl
    · exact (read_mkTr f _ _ _ embS τ tjs t0s rts htr isR1 π.opens hg1 _ _ p ((hR1 p).2 hp)).symm
  obtain ⟨A, hA, hfa⟩ : ∃ A,
      forestsB Q.loc.shape Q.ann wq.sh embS rts isR1 π.opens = some A ∧ flatF A = a := by
    have := map_flatF_forestsB Q.loc.shape Q.ann wq.sh embS rts isR1 π.opens
    rw [a1] at this
    exact Option.map_eq_some_iff.1 this
  obtain ⟨cs, hcs, hfb⟩ : ∃ cs,
      checksExtW wq.ext embE (trees.map TreeH.root) isR2 π.ext wq.ext.all = some cs ∧
      cs.map Prod.snd = b := by
    have := map_snd_checksExtW wq.ext embE (trees.map TreeH.root) isR2 π.ext wq.ext.all
    rw [b1] at this
    exact Option.map_eq_some_iff.1 this
  have hB : forestExt wq.ext embE (trees.map TreeH.root) isR2 π.ext =
      some (Forest.split wq.ext.pr
          ⟨wq.ext.depth, fun t => (trees.map TreeH.root).getD t default, cs⟩) := by
    unfold forestExt; rw [hcs]; rfl
  have e1 : (fun p =>
        @decide (p ∈ Q.loc.reads x τ.rho τ.plains) (@Finset.decidableMem _ wq.decO _ _)) = isR1 :=
    funext fun p => by rw [Bool.eq_iff_iff, hR1]; simp
  have e2 : (fun p =>
        @decide (p ∈ Q.loc.extReads x τ.rho) (@Finset.decidableMem _ wq.ext.dec _ _)) = isR2 :=
    funext fun p => by rw [Bool.eq_iff_iff, hR2]; simp
  have hflat : flatF
        (A ++ Forest.split wq.ext.pr
            (⟨wq.ext.depth, fun t => (trees.map TreeH.root).getD t default, cs⟩ : Forest lam L)) =
      a ++ b := by
    rw [flatF_append, flatF_split, hfa, hfb]
  have hFs : forestsOf Q wq embS embE (trees.map TreeH.root) x π τ.rho rts =
      some (A ++ Forest.split wq.ext.pr
            ⟨wq.ext.depth, fun t => (trees.map TreeH.root).getD t default, cs⟩) := by
    unfold forestsOf
    rw [hpl, effPlains_eq f _ _ _ embS τ tjs t0s rts hC htr, e1, e2, hA, hB]
  unfold checkPrunedOpenings
  rw [hFs]
  dsimp only
  rw [hflat, if_pos hcond]
  unfold afterF
  rw [hpl, hacc]
  refine (evaluates_eager f).bind (evalsTo_runForests _ fun F hF => ?_)
    ((evaluates_eager f).bind hreq ((evaluates_eager f).pure _))
  rcases List.mem_append.1 hF with hF | hF
  · exact honest_forestsB f vs Q.loc.shape Q.ann wq.sh hwq.sh embS τ tjs t0s rts htr
      isR1 π.opens hg1 A hA F hF
  · exact honest_forestExt f wq.ext embE vs trees y hext isR2 π.ext hg2 _ hB F hF

end Compile.Batch.Cmpl
