-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Walks.lean: under fixed oracle functions g the verifier's walks of the forests say
yes on the openings that the compiled prover lays (OnBytes/Prover/Defs.lean), if what is kept of the
rounds meets the invariant (OnBytes/Prover/Inv.lean) and the outer trees are kept rightly.

The verifier checks the opened leaves of a tree together (`walkP`,
OnBytes/TypedOracleCompiler/Joined/WalkAt.lean): where two opened leaves share a node it follows one path. That each
path climbs to the root is therefore not enough. Here all checks of a forest are read off trees that
are kept rightly, and honest trees pass (`Octopus.complete`, Hash/OctopusFacts.lean).

Main names:
  `TreeK.digs`, `leafAt`   the digests of a kept tree's leaves; those of the trees xt 0, xt 1, ..
                      in a row
  `FromKept g xt F`   the checks of the forest F are read off the trees xt, each kept rightly: leaf
                      number, leaf input, path, root
  `FromKept.split`, `FromKept.walk`   so are the parts of F; the walk of F says yes
  `fromKept_checksTrees`, `walks_comp`   the trees of one component of one round
  `walks_at`    the forests at the rounds
  `walksE_at`   the forests over the external strings

Limits: one direction; nothing on soundness, nothing on probability. Nothing says that a prover's
run meets the invariant: that is OnBytes/Prover/Chain.lean.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Opened
import Compile.OctopusList

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The leaves' digests -/

/-- the digests of the leaves of a kept tree of depth d -/
def TreeK.digs (g : Fam (typedOracleFamily lam K L)) (d : ℕ) (T : TreeK lam L) : List (Dig lam) :=
  (List.range (2 ^ d)).map fun j => (g OracleName.leaf (T.inp j) : Dig lam)

theorem TreeK.length_digs (g : Fam (typedOracleFamily lam K L)) (d : ℕ) (T : TreeK lam L) :
    (T.digs g d).length = 2 ^ d := by
  unfold TreeK.digs
  rw [List.length_map, List.length_range]

theorem TreeK.getD_digs (g : Fam (typedOracleFamily lam K L)) {d j : ℕ} (T : TreeK lam L) (hj : j < 2 ^ d) :
    (T.digs g d).getD j default = (g OracleName.leaf (T.inp j) : Dig lam) := by
  unfold TreeK.digs
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- the leaves' digests of the trees xt 0, xt 1, .., each of depth d, in a row -/
def leafAt (g : Fam (typedOracleFamily lam K L)) (xt : ℕ → TreeK lam L) (d i : ℕ) : Dig lam :=
  ((xt (i / 2 ^ d)).digs g d).getD (i % 2 ^ d) default

theorem leafAt_block (g : Fam (typedOracleFamily lam K L)) (xt : ℕ → TreeK lam L) (d t : ℕ) :
    ∀ i < 2 ^ d, leafAt g xt d (t * 2 ^ d + i) = ((xt t).digs g d).getD i default := by
  intro i hi
  have d1 : (t * 2 ^ d + i) / 2 ^ d = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hi,
      Nat.zero_add]
  have d2 : (t * 2 ^ d + i) % 2 ^ d = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  unfold leafAt
  rw [d1, d2]

/-! ## A forest that is read off kept trees -/

/-- a list zipped with its own image (as `of_mem_zip_map`, Compile/Batch/CompleteForest.lean, which
is not imported here: it lies over the compiler's first form) -/
private theorem mem_zip_image {α β : Type} (φ : α → β) :
    ∀ (l : List α) (m : α × β), m ∈ l.zip (l.map φ) → m.1 ∈ l ∧ m.2 = φ m.1
  | [], m, h => by simp at h
  | a :: l, m, h => by
    rw [List.map_cons, List.zip_cons_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨List.mem_cons_self, rfl⟩
    · exact ⟨List.mem_cons_of_mem _ (mem_zip_image φ l m h).1, (mem_zip_image φ l m h).2⟩

/-- The checks of the forest F are read off the trees xt: the tree of each check is kept rightly at
the forest's depth; the check has the number of one of its leaves, that leaf's input, that leaf's
path, and the forest has that tree's root. -/
def FromKept (g : Fam (typedOracleFamily lam K L)) (xt : ℕ → TreeK lam L) (F : Forest lam L) : Prop :=
  ∀ e ∈ F.cs, (xt e.1).At g F.depth ∧ e.2.j < 2 ^ F.depth ∧ e.2.inp = (xt e.1).inp e.2.j ∧
    e.2.path = pathOf (xt e.1).lv e.2.j ∧ F.treeRoot e.1 = (xt e.1).root

/-- the parts of such a forest are such forests -/
theorem FromKept.split {g : Fam (typedOracleFamily lam K L)} {xt : ℕ → TreeK lam L} {F : Forest lam L}
    (h : FromKept g xt F) (pr : Bool) : ∀ G ∈ F.split pr, FromKept g xt G := by
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

/-- **The walk of a forest that is read off kept trees, with the sibling digests read off its own
paths, says yes under g.** -/
theorem FromKept.walk {g : Fam (typedOracleFamily lam K L)} {xt : ℕ → TreeK lam L} {F : Forest lam L}
    (h : FromKept g xt F) : walkP g F F.reads = true := by
  have h1 : TypedOracleCompiler.Joined.leavesP g F.cs = F.idx.map (leafAt g xt F.depth) := by
    unfold TypedOracleCompiler.Joined.leavesP Forest.idx
    rw [List.map_map]
    refine List.map_congr_left fun e he => ?_
    obtain ⟨-, hj, hi, -, -⟩ := h e he
    show (g OracleName.leaf e.2.inp : Dig lam) = leafAt g xt F.depth (e.1 * 2 ^ F.depth + e.2.j)
    rw [leafAt_block g xt F.depth e.1 e.2.j hj, TreeK.getD_digs g _ hj, hi]
  have h2 : F.reads = Octopus.reads F.depth (F.idx.map fun j =>
      (j, Octopus.hpath (nodeAt g) F.depth (leafAt g xt F.depth) j)) := by
    unfold Forest.reads Forest.idx
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun e he => ?_
    obtain ⟨hA, hj, -, hp, -⟩ := h e he
    have hA' : (xt e.1).lv = levelsF (nodeAt g) F.depth ((xt e.1).digs g F.depth) := hA
    show (e.1 * 2 ^ F.depth + e.2.j, e.2.path) = (e.1 * 2 ^ F.depth + e.2.j,
      Octopus.hpath (nodeAt g) F.depth (leafAt g xt F.depth) (e.1 * 2 ^ F.depth + e.2.j))
    rw [hp, hA', pathOf_eq_hpath (nodeAt g) F.depth e.1 _ _ e.2.j (TreeK.length_digs g _ _)
      (leafAt_block g xt F.depth e.1) hj]
  have h3 := Octopus.complete (Dig lam) (nodeAt g) F.depth (leafAt g xt F.depth) F.idx
  unfold walkP
  rw [h1, h2, h3]
  refine List.all_eq_true.2 fun m hm => decide_eq_true ?_
  obtain ⟨m1, m2⟩ := mem_zip_image _ _ m hm
  obtain ⟨k, hk, hk2⟩ := mem_upN F.depth F.idx m.1 m1
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
  obtain ⟨hA, hj, -, -, hr⟩ := h e he
  have hA' : (xt e.1).lv = levelsF (nodeAt g) F.depth ((xt e.1).digs g F.depth) := hA
  have e1 : m.1 = e.1 := by
    rw [hk2, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hj,
      Nat.zero_add]
  rw [m2, e1, hr]
  unfold TreeK.root
  rw [hA']
  exact (rootOf_eq_topG (nodeAt g) F.depth e.1 _ _ (TreeK.length_digs g _ _)
    (leafAt_block g xt F.depth e.1)).symm

/-! ## The trees of one component of one round -/

/-- The trees of a component from number k on, against their own roots: for each tree the forest of
its checks is read off that tree, if each opening that is read is that of its leaf. -/
theorem fromKept_checksTrees {g : Fam (typedOracleFamily lam K L)} {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (Ts : List (TreeK lam L))
      (l : List (ℕ × Dig lam × List (Check lam L))),
      checksTrees posAt emb isRead f k ds (Ts.map TreeK.root) = some l →
      (∀ i d T, ds[i]? = some d → Ts[i]? = some T → T.At g d ∧
        ∀ j p op, posAt (k + i) j = some p → isRead p = true → f p = some op →
          (⟨emb p op.sym, op.salt⟩ : LeafIn L) = T.inp j ∧ op.path = pathOf T.lv j) →
      ∀ z ∈ l, ∃ T : TreeK lam L,
        FromKept g (fun _ => T) ⟨z.1, fun _ => z.2.1, z.2.2.map fun c => (0, c)⟩
  | k, d0 :: ds, T0 :: Ts, l, h, H, z, hz => by
    rw [List.map_cons] at h
    simp only [checksTrees] at h
    cases h1 : checksComp (posAt k) d0 emb T0.root isRead f (List.range (2 ^ d0)) with
    | none => rw [h1] at h; cases h
    | some a =>
      cases h2 : checksTrees posAt emb isRead f (k + 1) ds (Ts.map TreeK.root) with
      | none => rw [h1, h2] at h; cases h
      | some b =>
        rw [h1, h2] at h
        cases h
        rcases List.mem_cons.1 hz with rfl | hz'
        · obtain ⟨hA, hl⟩ := H 0 d0 T0 rfl rfl
          refine ⟨T0, fun e he => ?_⟩
          obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
          obtain ⟨q1, q2, q3⟩ := forall_checksComp
            (P := fun c => c.j < 2 ^ d0 ∧ c.inp = T0.inp c.j ∧ c.path = pathOf T0.lv c.j)
            (posAt k) d0 emb T0.root isRead f _ a h1
            (fun j hj p op hp hr hf =>
              ⟨List.mem_range.1 hj, hl j p op (by rwa [Nat.add_zero]) hr hf⟩) c hc
          exact ⟨hA, q1, q2, q3, rfl⟩
        · exact fromKept_checksTrees posAt emb isRead f (k + 1) ds Ts b h2
            (fun i d T hd hT =>
              ⟨(H (i + 1) d T (by simpa using hd) (by simpa using hT)).1,
                fun j p op hp =>
                  (H (i + 1) d T (by simpa using hd) (by simpa using hT)).2 j p op
                    (by rwa [show k + (i + 1) = k + 1 + i by omega])⟩) z hz'
  | _, [], _, l, h, _, z, hz => by
    simp only [checksTrees] at h
    cases h
    cases hz
  | _, _ :: _, [], l, h, _, z, hz => by
    simp only [List.map_nil, checksTrees] at h
    cases h
    cases hz

/-- One component: it has no tree, or its trees are kept rightly; at each read position stands the
opening of that position's leaf. Then the walk of each of its forests, whole or cut, says yes. -/
theorem walks_comp {g : Fam (typedOracleFamily lam K L)} {sMT : ℕ} {r : Round} {posAt : ℕ → ℕ → Option r.Pos}
    {emb : (p : r.Pos) → r.Sym p → Body L} {o : r.Orc} {ds : List ℕ} {Ts : List (TreeK lam L)}
    {isRead : r.Pos → Bool} {f : (p : r.Pos) → Option (Opening lam (r.Sym p))}
    (hc : Ts = [] ∨ CompAt g sMT posAt emb o ds Ts)
    (hf : ∀ k j p T, posAt k j = some p → isRead p = true → Ts[k]? = some T →
      f p = some (T.opening j (r.rd o p)))
    {l : List (ℕ × Dig lam × List (Check lam L))}
    (h : checksTrees posAt emb isRead f 0 ds (Ts.map TreeK.root) = some l) (pr : Bool) :
    ∀ F ∈ forestsT pr l, walkP g F F.reads = true := by
  intro F hF
  obtain ⟨z, hz, hF⟩ := List.mem_flatMap.1 hF
  obtain ⟨T, hT⟩ := fromKept_checksTrees (g := g) posAt emb isRead f 0 ds Ts l h
    (fun i d T hd hT => by
      rcases hc with rfl | hc
      · simp at hT
      · obtain ⟨hA, hl⟩ := hc.2 i d T hd hT
        refine ⟨hA, fun j p op hp hr hop => ?_⟩
        rw [Nat.zero_add] at hp
        rw [hf i j p T hp hr hT] at hop
        obtain rfl := Option.some.inj hop
        exact ⟨congrArg (fun b => (⟨b, (T.inp j).salt⟩ : LeafIn L)) (hl j p hp).1.symm, rfl⟩)
    z hz
  exact (hT.split pr F hF).walk

/-! ## The forests of a proof string -/

/-- **The forests at the rounds.** -/
theorem walks_at : ∀ (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) (s : Shape) (A : RoundSplits s)
    (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L) (kp : Kept lam L s)
    (R : RootsOfChain lam s) (rd : OPos s → Bool),
  RoundsAt g sMT s A W embS kp R → RoundsQueryLayout.OKG s A W →
  ∀ Fs, forestsB s A W embS R rd (opensK s A W kp rd) = some Fs →
    ∀ T ∈ Fs, walkP g T T.reads = true
  | _, _, [], _, _, _, _, _, _, _, _, Fs, h, T, hT => by
    obtain rfl : [] = Fs := Option.some.inj h
    cases hT
  | g, sMT, r :: s, (a, A), (w, W), embS, (kp, ks), (rt, R), rd, hR, hW, Fs, h, T, hT => by
    obtain ⟨h0, hJ, hrest⟩ := hR
    have r0 : rt.1.getD [] = kp.2.1.map TreeK.root := by
      rcases h0 with ⟨e1, e2, -⟩ | ⟨e1, -⟩
      · rw [e1, e2]
        rfl
      · rw [e1]
        rfl
    have rJ : rt.2.getD [] = kp.2.2.map TreeK.root := by
      rcases hJ with ⟨e1, e2, -⟩ | ⟨e1, -⟩
      · rw [e1, e2]
        rfl
      · rw [e1]
        rfl
    simp only [forestsB] at h
    rw [r0, rJ] at h
    split at h
    · rename_i c0 cJ c2 e0 eJ e2
      obtain rfl := Option.some.inj h
      rcases List.mem_append.1 hT with hT | hT
      · refine walks_comp (g := g) (sMT := sMT) (o := kp.1.1)
          (h0.imp (fun x => x.2.1) fun x => x.2) (fun k j p T' hp hr hT' => ?_) e0 w.pr0 T hT
        obtain ⟨ho, rfl, rfl⟩ := hW.1.place_posAt0 k j p hp
        have hr' : rd (.inl p) = true := hr
        show opensK (r :: s) (a, A) (w, W) (kp, ks) rd (.inl p) = _
        simp only [opensK, hr', if_true, ho, Bool.false_eq_true, if_false, hT', Option.map_some]
        rfl
      · rcases List.mem_append.1 hT with hT | hT
        · refine walks_comp (g := g) (sMT := sMT) (o := kp.1.1)
            (hJ.imp (fun x => x.2.1) fun x => x.2) (fun k j p T' hp hr hT' => ?_) eJ w.prJ T hT
          obtain ⟨ho, rfl, rfl⟩ := hW.1.place_posAtJ k j p hp
          have hr' : rd (.inl p) = true := hr
          show opensK (r :: s) (a, A) (w, W) (kp, ks) rd (.inl p) = _
          simp only [opensK, hr', if_true, ho, hT', Option.map_some]
          rfl
        · exact walks_at g sMT s A W (fun p => embS (.inr p)) ks R (fun p => rd (.inr p)) hrest
            hW.2 c2 e2 T hT
    · cases h

/-- **The forests over the external strings.** -/
theorem walksE_at : ∀ (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) (E : ExtSpec) (we : WireE E)
    (embE : E.Sym → Body L) (cms : List (Dig lam)) (y : E.Str) (xt : ℕ → TreeK lam L)
    (rd : E.Pos → Bool),
  ExtAt g sMT we embE cms y xt →
  ∀ Fe, forestExt we embE cms rd (extK we y xt rd) = some Fe →
    ∀ T ∈ Fe, walkP g T T.reads = true := by
  intro g sMT E we embE cms y xt rd hx Fe h T hT
  unfold forestExt at h
  obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 h
  refine (FromKept.split (g := g) (xt := xt)
    (F := ⟨we.depth, fun t => cms.getD t default, cs⟩) (fun e he => ?_) we.pr T hT).walk
  obtain ⟨p, op, -, hr, hop, rfl⟩ := inv_checksExtW we embE cms rd (extK we y xt rd) _ cs hcs e he
  rw [extK_read we y xt rd hr] at hop
  obtain rfl := Option.some.inj hop
  exact ⟨hx.tree p, hx.leaf p,
    congrArg (fun b => (⟨b, ((xt (we.which p)).inp (we.leaf p)).salt⟩ : LeafIn L))
      (hx.body p).symm, rfl, (hx.root p).symm⟩

end OnBytes.Prover
