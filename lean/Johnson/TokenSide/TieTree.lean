-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/TieTree.lean: THE TREES OF THE TOKEN SIDE AGAINST THE COMPILED PROVER's BUILDERS:
leavesT, treeT, treesT (Johnson/TokenSide/Tree.lean), as ordinary algorithms (plainOf,
Johnson/TokenSide/Erased.lean), do what leavesO, treeO, treesO (OnBytes/Prover/Defs.lean) do at
salts that are handed over at the start (Tie, Johnson/TokenSide/Tie.lean). Definitions, and theorems
with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

THE COINS are a letter Ω with a law μ. What is used of them is a LeafLens: how the free bits of the
salt of a leaf are read (get ω i b k j: round, own component?, tree, leaf) and written (upd), and
that within a set Z of coordinates each is ℓ uniform bits, independent of all the rest (Resamples,
Rom/Handle/Coins.lean).

After a tree is built, the family on the right is read at coins into which the drawn bits are laid.
patchL, patchT, patchTs are these coins, written out of the tokens and the store.

Main names (namespace OnBytes.TokenSide).
  LeafLens   the coins as far as leaves' salts go.
  patchL, patchT, patchTs   the coins with the drawn bits laid in.
  mkK, mkKs  a tree, a list of trees, as the compiled prover keeps them, at given coins.
  TreeOK, TreesOK   a tree, the trees of a component, are in order at a store.
  get_patchL_in, get_patchT_in, get_patchL_ne   what these coins hold.
  plainOf_levels   the inner nodes: one algorithm on both sides.
  tie_leaves, tie_tree, tie_trees   THE TIES.

Limits. All is said of the ERASED program (plainOf, Johnson/TokenSide/Erased.lean): tokens are
strings in a store, and the names fbw t k are written back to fb t. Nothing here speaks of these
names, or of the two modes of deferred programming (Rom/Defer.lean): they are the matter of
Johnson/HopSide/, Johnson/GhostSide/ and Compile/DeferRun/.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Erased
import Johnson.TokenSide.Tree

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- **The coins as far as leaves' salts go.** -/
structure LeafLens (Ω : Type) (μ : PMF Ω) (ℓ : ℕ) (Z : ℕ → Bool → ℕ → ℕ → Prop) where
  /-- the free bits of the salt of a leaf: round, own component?, tree, leaf -/
  get : Ω → ℕ → Bool → ℕ → ℕ → Bits
  upd : ℕ → Bool → ℕ → ℕ → (Fin ℓ → Bool) → Ω → Ω
  get_same : ∀ i b k j u ω, Z i b k j → get (upd i b k j u ω) i b k j = List.ofFn u
  get_ne : ∀ i b k j u ω i' b' k' j', ¬(i' = i ∧ b' = b ∧ k' = k ∧ j' = j) →
    get (upd i b k j u ω) i' b' k' j' = get ω i' b' k' j'
  law : ∀ i b k j, Z i b k j → Resamples μ (unif (Fin ℓ → Bool)) (upd i b k j)

variable {Ω : Type} {μ : PMF Ω} {ℓ : ℕ} {Z : ℕ → Bool → ℕ → ℕ → Prop}

/-- the coins with the values of the tokens as laid in at the leaves js of tree (i, b, k) -/
def patchL (ll : LeafLens Ω μ ℓ Z) (i : ℕ) (b : Bool) (k : ℕ) :
    List ℕ → List (Tok × Tok) → List Bits → Ω → Ω
  | j :: js, a :: as, vs, ω => ll.upd i b k j (digOf ℓ (vs.getD a.1 [])) (patchL ll i b k js as vs
      ω)
  | _, _, _, ω => ω

/-- A tree with tokens is in order at a store: it has 2 ^ d leaves; the token of each leaf's free
bits is in the store, and its value has ℓ bits; its first level has 2 ^ d digests. -/
def TreeOK (ℓ d : ℕ) (vs : List Bits) (T : TreeT lam L) : Prop :=
  T.tok.length = 2 ^ d ∧
    (∀ a ∈ T.tok, a.1 < vs.length ∧ ∃ u : Fin ℓ → Bool, vs.getD a.1 [] = List.ofFn u) ∧
    (T.lv.headD []).length = 2 ^ d

theorem TreeOK.mono {ℓ d : ℕ} {vs ws : List Bits} {T : TreeT lam L} (h : TreeOK ℓ d vs T)
    (hp : vs <+: ws) : TreeOK ℓ d ws T :=
  ⟨h.1, fun a ha => ⟨Nat.lt_of_lt_of_le (h.2.1 a ha).1 hp.length_le,
    (h.2.1 a ha).2.imp fun _ e => by rw [getD_of_prefix hp (h.2.1 a ha).1]; exact e⟩, h.2.2⟩

/-- the trees of a component are in order: one for each depth of the list -/
def TreesOK (ℓ : ℕ) (ds : List ℕ) (vs : List Bits) (Ts : List (TreeT lam L)) : Prop :=
  List.Forall₂ (fun d T => TreeOK ℓ d vs T) ds Ts

theorem TreesOK.mono {ℓ : ℕ} {ds : List ℕ} {vs ws : List Bits} {Ts : List (TreeT lam L)}
    (h : TreesOK ℓ ds vs Ts) (hp : vs <+: ws) : TreesOK ℓ ds ws Ts :=
  List.Forall₂.imp (fun _ _ h1 => h1.mono hp) h

theorem TreesOK.lt {ℓ : ℕ} {ds : List ℕ} {vs : List Bits} {Ts : List (TreeT lam L)}
    (h : TreesOK ℓ ds vs Ts) : ∀ T ∈ Ts, ∀ a ∈ T.tok, a.1 < vs.length := by
  induction h with
  | nil => exact fun T hT => absurd hT (List.not_mem_nil)
  | cons h1 _ ih =>
    intro T hT a ha
    rcases List.mem_cons.mp hT with rfl | hT
    · exact (h1.2.1 a ha).1
    · exact ih T hT a ha

/-- What the leaf's program is as an ordinary algorithm. -/
theorem plainOf_leafT_bind {β : Type} (us : List Tok) (pre : List Bits → Bits) (bd : Body L)
    (g : Dig lam × Tok × Tok → StT lam K L β) (vs : List Bits) :
    plainOf ((leafT (K := K) ℓ us pre bd).bind g) vs =
      .sample (2 ^ ℓ - 1) fun r =>
        .query (S := typedOracleFamily lam K L) OracleName.leaf
          (⟨bd, pre (us.map fun u => (vs ++ [List.ofFn (Life2.bitsE ℓ r)]).getD u []) ++
            (vs ++ [List.ofFn (Life2.bitsE ℓ r)]).getD vs.length []⟩ : LeafIn L) fun d =>
          plainOf (g ((d : Dig lam), vs.length, (vs ++ [List.ofFn (Life2.bitsE ℓ r)]).length))
            (vs ++ [List.ofFn (Life2.bitsE ℓ r)] ++
              [List.ofFn ((splitT lam K L).split OracleName.leaf d).2]) := rfl

/-- **The leaves.** -/
theorem tie_leaves (ll : LeafLens Ω μ ℓ Z) (us : List Tok) (pre : List Bits → Bits) (st : Bits)
    (i : ℕ) (b : Bool) (k : ℕ) (body : ℕ → Body L) :
    ∀ (js : List ℕ) (vs : List Bits), js.Nodup → (∀ j ∈ js, Z i b k j) →
      (∀ u ∈ us, u < vs.length) → pre (us.map fun u => vs.getD u []) = st →
      Tie μ
        (fun (p : (List (Dig lam) × List (Tok × Tok)) × List Bits) ω =>
          (p.1.1, patchL ll i b k js p.1.2 p.2 ω))
        (fun p => (p.1.1.length = js.length ∧ p.1.2.length = js.length) ∧ vs <+: p.2 ∧
          ∀ a ∈ p.1.2, a.1 < p.2.length ∧ ∃ u : Fin ℓ → Bool, p.2.getD a.1 [] = List.ofFn u)
        (plainOf (leavesT (K := K) ℓ us pre (js.map body)) vs)
        (fun ω => (leavesO (K := K) (js.map fun j =>
          (⟨body j, st ++ ll.get ω i b k j⟩ : LeafIn L))).bind fun ds => .pure (ds, ω)) := by
  intro js
  induction js with
  | nil =>
    intro vs _ _ _ _
    exact .done ⟨⟨rfl, rfl⟩, List.prefix_rfl, fun a h => absurd h (List.not_mem_nil)⟩ fun _ => rfl
  | cons j js ih =>
    intro vs hn hz hu hst
    have hj : Z i b k j := hz j (List.mem_cons_self ..)
    have hnj : j ∉ js := (List.nodup_cons.mp hn).1
    show Tie μ _ _ (plainOf ((leafT (K := K) ℓ us pre (body j)).bind fun u =>
      (leavesT ℓ us pre (js.map body)).bind fun r => Step.pure (u.1 :: r.1, u.2 :: r.2)) vs) _
    rw [plainOf_leafT_bind]
    refine Tie.fresh ℓ (ll.upd i b k j) (ll.law i b k j hj) fun r => ?_
    generalize Life2.bitsE ℓ r = x
    have hus : (us.map fun u => (vs ++ [List.ofFn x]).getD u []) = us.map fun u => vs.getD u [] :=
      List.map_congr_left fun u hu' => getD_of_prefix (List.prefix_append _ _) (hu u hu')
    rw [hus, hst, getD_length_append]
    refine Tie.query (fun ω d => ((leavesO (K := K) (js.map fun j' =>
        (⟨body j', st ++ ll.get ω i b k j'⟩ : LeafIn L))).bind fun ds => .pure (d :: ds)).bind
        fun ds => .pure (ds, ll.upd i b k j x ω)) (fun ω => ?_) fun d => ?_
    · have e2 : (js.map fun j' =>
          (⟨body j', st ++ ll.get (ll.upd i b k j x ω) i b k j'⟩ : LeafIn L)) =
          js.map fun j' => (⟨body j', st ++ ll.get ω i b k j'⟩ : LeafIn L) :=
        List.map_congr_left fun j' hj' => by
          rw [ll.get_ne i b k j x ω i b k j' fun h => hnj (h.2.2.2 ▸ hj')]
      show (leavesO (K := K) ((⟨body j, st ++ ll.get (ll.upd i b k j x ω) i b k j⟩ : LeafIn L) ::
        js.map fun j' => (⟨body j', st ++ ll.get (ll.upd i b k j x ω) i b k j'⟩ : LeafIn L))).bind
        _ = _
      rw [e2, ll.get_same i b k j x ω hj]
      rfl
    · rw [plainOf_bind]
      have hp0 : vs <+: vs ++ [List.ofFn x] ++
          [List.ofFn ((splitT lam K L).split OracleName.leaf d).2] := by
        rw [List.append_assoc]
        exact List.prefix_append _ _
      have hlen : ∀ u ∈ us, u < (vs ++ [List.ofFn x] ++
          [List.ofFn ((splitT lam K L).split OracleName.leaf d).2]).length :=
        fun u hu' => Nat.lt_of_lt_of_le (hu u hu') hp0.length_le
      have hst' : pre (us.map fun u => (vs ++ [List.ofFn x] ++
          [List.ofFn ((splitT lam K L).split OracleName.leaf d).2]).getD u []) = st := by
        rw [← hst]
        refine congrArg pre (List.map_congr_left fun u hu' => ?_)
        rw [List.append_assoc]
        exact getD_of_prefix (List.prefix_append _ _) (hu u hu')
      refine ((ih _ (List.nodup_cons.mp hn).2 (fun j' hj' => hz j' (List.mem_cons_of_mem _ hj'))
        hlen hst').bind (f' := fun y => .pure ((d : Dig lam) :: y.1, ll.upd i b k j x y.2))
        fun p hp => ?_).congr fun ω => ?_
      · have hpre : vs ++ List.ofFn x :: [List.ofFn ((splitT lam K L).split OracleName.leaf d).2] <+:
            p.2 := by
          have := hp.2.1
          rwa [List.append_assoc] at this
        have hv : p.2.getD vs.length [] = List.ofFn x := by
          rw [getD_of_prefix hpre (by simp), getD_length_append]
        refine .done ⟨?_, ?_, ?_⟩ fun ω => ?_
        · refine ⟨?_, ?_⟩
          · show (p.1.1.length + 1) = js.length + 1
            rw [hp.1.1]
          · show (p.1.2.length + 1) = js.length + 1
            rw [hp.1.2]
        · exact (List.prefix_append _ _).trans hpre
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · refine ⟨?_, x, hv⟩
            have := hpre.length_le
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            show vs.length < p.2.length
            omega
          · exact hp.2.2 a ha
        · show OComp.pure _ = OComp.pure ((d : Dig lam) :: p.1.1,
            ll.upd i b k j (digOf ℓ (p.2.getD vs.length [])) (patchL ll i b k js p.1.2 p.2 ω))
          rw [hv, digOf_ofFn]
      · beta_reduce
        rw [Tie.obind_assoc, Tie.obind_assoc]
        rfl

/-! ## The inner nodes: one algorithm on both sides -/

theorem plainOf_pairUp : ∀ (l : List (Dig lam)) (vs : List Bits),
    plainOf (pairUp (nodeT (K := K) (L := L)) l) vs =
      (pairUp (hashTreeNode (K := K) (L := L)) l).bind fun u => .pure (u, vs)
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, vs => by
    show OComp.query (S := typedOracleFamily lam K L) OracleName.node ((List.ofFn a, List.ofFn b) : Bits × Bits)
        (fun c => plainOf ((pairUp (nodeT (K := K) (L := L)) t).bind fun r =>
          Step.pure ((c : Dig lam) :: r)) vs) =
      OComp.query (S := typedOracleFamily lam K L) OracleName.node ((List.ofFn a, List.ofFn b) : Bits × Bits)
        fun c => ((pairUp (hashTreeNode (K := K) (L := L)) t).bind fun r =>
          OComp.pure ((c : Dig lam) :: r)).bind fun u => .pure (u, vs)
    refine congrArg _ (funext fun c => ?_)
    rw [plainOf_bind, plainOf_pairUp t vs, Tie.obind_assoc, Tie.obind_assoc]
    rfl

theorem plainOf_levels : ∀ (d : ℕ) (l : List (Dig lam)) (vs : List Bits),
    plainOf (levelsM (nodeT (K := K) (L := L)) d l) vs =
      (levelsM (hashTreeNode (K := K) (L := L)) d l).bind fun lv => .pure (lv, vs)
  | 0, _, _ => rfl
  | d + 1, l, vs => by
    show plainOf ((pairUp (nodeT (K := K) (L := L)) l).bind fun u =>
        (levelsM (nodeT (K := K) (L := L)) d u).bind fun r => Step.pure (l :: r)) vs =
      ((pairUp (hashTreeNode (K := K) (L := L)) l).bind fun u =>
        (levelsM (hashTreeNode (K := K) (L := L)) d u).bind fun r => OComp.pure (l :: r)).bind
        fun lv => .pure (lv, vs)
    rw [plainOf_bind, plainOf_pairUp, Tie.obind_assoc, Tie.obind_assoc]
    refine congrArg _ (funext fun u => ?_)
    show plainOf ((levelsM (nodeT (K := K) (L := L)) d u).bind fun r => Step.pure (l :: r)) vs = _
    rw [plainOf_bind, plainOf_levels d u vs, Tie.obind_assoc, Tie.obind_assoc]
    rfl

/-- the first of the levels is the list of the leaves' digests -/
theorem post_levels (d : ℕ) (l : List (Dig lam)) :
    Post (fun lv : List (List (Dig lam)) => lv.headD [] = l)
      (levelsM (hashTreeNode (K := K) (L := L)) d l) := by
  cases d with
  | zero => rfl
  | succ d =>
    show Post _ ((pairUp (hashTreeNode (K := K) (L := L)) l).bind fun u =>
      (levelsM (hashTreeNode (K := K) (L := L)) d u).bind fun r => OComp.pure (l :: r))
    exact Post.bind (Post.of_forall (P := fun _ => True) (fun _ => trivial) _) fun u _ =>
      Post.bind (Post.of_forall (P := fun _ => True) (fun _ => trivial) _) fun r _ => rfl

/-! ## One tree -/

/-- the coins with the values of a tree's tokens laid in -/
def patchT (ll : LeafLens Ω μ ℓ Z) (i : ℕ) (b : Bool) (k : ℕ) (T : TreeT lam L) (vs : List Bits)
    (ω : Ω) : Ω :=
  patchL ll i b k (List.range T.tok.length) T.tok vs ω

/-- a tree as the compiled prover keeps it, its salts read at the coins ωa -/
def mkK (ll : LeafLens Ω μ ℓ Z) (st : Bits) (i : ℕ) (b : Bool) (k : ℕ) (ωa : Ω) (T : TreeT lam L) :
    TreeK lam L :=
  ⟨fun j => ⟨T.body j, st ++ ll.get ωa i b k j⟩, T.lv⟩

/-- **One tree.** -/
theorem tie_tree (ll : LeafLens Ω μ ℓ Z) (us : List Tok) (pre : List Bits → Bits) (st : Bits)
    (i : ℕ) (b : Bool) (k d : ℕ) (body : ℕ → Body L) (vs : List Bits)
    (hz : ∀ j, j < 2 ^ d → Z i b k j) (hu : ∀ u ∈ us, u < vs.length)
    (hst : pre (us.map fun u => vs.getD u []) = st) :
    Tie μ
      (fun (p : TreeT lam L × List Bits) ω =>
        (mkK ll st i b k (patchT ll i b k p.1 p.2 ω) p.1, patchT ll i b k p.1 p.2 ω))
      (fun p => vs <+: p.2 ∧ TreeOK ℓ d p.2 p.1)
      (plainOf (treeT (K := K) ℓ us pre d body) vs)
      (fun ω => (treeO (K := K) d fun j => (⟨body j, st ++ ll.get ω i b k j⟩ : LeafIn L)).bind
        fun T => .pure (T, ω)) := by
  show Tie μ _ _ (plainOf ((leavesT (K := K) ℓ us pre ((List.range (2 ^ d)).map body)).bind fun l =>
    (levelsM (nodeT (K := K) (L := L)) d l.1).bind fun lv =>
      Step.pure (⟨body, l.2, lv⟩ : TreeT lam L)) vs) _
  rw [plainOf_bind]
  refine (Tie.bindW (tie_leaves ll us pre st i b k body (List.range (2 ^ d)) vs List.nodup_range
    (fun j hj => hz j (List.mem_range.mp hj)) hu hst)
    (f' := fun ω l => (levelsM (hashTreeNode (K := K) (L := L)) d l).bind fun lv =>
      .pure ((⟨fun j => ⟨body j, st ++ ll.get ω i b k j⟩, lv⟩ : TreeK lam L), ω))
    fun p hp => ?_).congr fun ω => ?_
  · rw [plainOf_bind, plainOf_levels, Tie.obind_assoc]
    have hl : p.1.2.length = 2 ^ d := by rw [hp.1.2, List.length_range]
    have hl1 : p.1.1.length = 2 ^ d := by rw [hp.1.1, List.length_range]
    refine Tie.leftP (post_levels d p.1.1)
      (f' := fun ω lv => .pure ((⟨fun j => ⟨body j, st ++ ll.get
        (patchL ll i b k (List.range (2 ^ d)) p.1.2 p.2 ω) i b k j⟩, lv⟩ : TreeK lam L),
        patchL ll i b k (List.range (2 ^ d)) p.1.2 p.2 ω)) fun lv hlv => ?_
    refine .done ⟨hp.2.1, hl, hp.2.2, by
      show (lv.headD []).length = 2 ^ d
      rw [hlv, hl1]⟩ fun ω => ?_
    show OComp.pure _ = OComp.pure (mkK ll st i b k
      (patchL ll i b k (List.range p.1.2.length) p.1.2 p.2 ω) ⟨body, p.1.2, lv⟩,
      patchL ll i b k (List.range p.1.2.length) p.1.2 p.2 ω)
    rw [hl]
    rfl
  · show ((leavesO (K := K) ((List.range (2 ^ d)).map fun j =>
        (⟨body j, st ++ ll.get ω i b k j⟩ : LeafIn L))).bind fun l =>
      (levelsM (hashTreeNode (K := K) (L := L)) d l).bind fun lv =>
        OComp.pure (⟨fun j => ⟨body j, st ++ ll.get ω i b k j⟩, lv⟩ : TreeK lam L)).bind
      (fun T => OComp.pure (T, ω)) = _
    rw [Tie.obind_assoc]
    refine congrArg _ (funext fun l => ?_)
    rw [Tie.obind_assoc]
    rfl

/-! ## The trees of a component -/

theorem get_patchL_ne (ll : LeafLens Ω μ ℓ Z) (i : ℕ) (b : Bool) (k : ℕ) (vs : List Bits) (ω : Ω)
    (i' : ℕ) (b' : Bool) (k' j' : ℕ) (h : ¬(i' = i ∧ b' = b ∧ k' = k)) :
    ∀ (js : List ℕ) (as : List (Tok × Tok)),
      ll.get (patchL ll i b k js as vs ω) i' b' k' j' = ll.get ω i' b' k' j'
  | [], _ => rfl
  | _ :: _, [] => rfl
  | j :: js, a :: as => by
    show ll.get (ll.upd i b k j _ (patchL ll i b k js as vs ω)) i' b' k' j' = _
    rw [ll.get_ne _ _ _ _ _ _ _ _ _ _ fun e => h ⟨e.1, e.2.1, e.2.2.1⟩]
    exact get_patchL_ne ll i b k vs ω i' b' k' j' h js as

/-- At a leaf whose bits were drawn the coins hold the value of the leaf's token. -/
theorem get_patchL_in (ll : LeafLens Ω μ ℓ Z) (i : ℕ) (b : Bool) (k : ℕ) (vs : List Bits) (ω : Ω) :
    ∀ (js : List ℕ) (as : List (Tok × Tok)) (n j : ℕ) (a : Tok × Tok), js.Nodup →
      (∀ j ∈ js, Z i b k j) → js[n]? = some j → as[n]? = some a →
      ll.get (patchL ll i b k js as vs ω) i b k j = List.ofFn (digOf ℓ (vs.getD a.1 []))
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | j0 :: js, a0 :: as, 0, j, a, _, hz, h1, h2 => by
    obtain rfl : j0 = j := by simpa using h1
    obtain rfl : a0 = a := by simpa using h2
    exact ll.get_same i b k j0 _ _ (hz j0 (List.mem_cons_self ..))
  | j0 :: js, a0 :: as, n + 1, j, a, hn, hz, h1, h2 => by
    have h1' : js[n]? = some j := by simpa using h1
    have h2' : as[n]? = some a := by simpa using h2
    have hj : j ∈ js := List.mem_of_getElem? h1'
    show ll.get (ll.upd i b k j0 _ (patchL ll i b k js as vs ω)) i b k j = _
    rw [ll.get_ne i b k j0 _ _ i b k j fun e => (List.nodup_cons.mp hn).1 (by rw [← e.2.2.2]; exact
        hj)]
    exact get_patchL_in ll i b k vs ω js as n j a (List.nodup_cons.mp hn).2
      (fun j' hj' => hz j' (List.mem_cons_of_mem _ hj')) h1' h2'

/-- The same for a tree that is in order: the coins hold the token's value itself. -/
theorem get_patchT_in (ll : LeafLens Ω μ ℓ Z) (i : ℕ) (b : Bool) (k d : ℕ) (vs : List Bits) (ω : Ω)
    (T : TreeT lam L) (hT : TreeOK ℓ d vs T) (hz : ∀ j, j < 2 ^ d → Z i b k j) (j : ℕ)
    (a : Tok × Tok) (h : T.tok[j]? = some a) :
    ll.get (patchT ll i b k T vs ω) i b k j = vs.getD a.1 [] := by
  have hj : j < T.tok.length := (List.getElem?_eq_some_iff.mp h).1
  obtain ⟨u, hu⟩ := (hT.2.1 a (List.mem_of_getElem? h)).2
  unfold patchT
  rw [get_patchL_in ll i b k vs ω (List.range T.tok.length) T.tok j j a List.nodup_range
    (fun j' hj' => hz j' (by rw [← hT.1]; exact List.mem_range.mp hj'))
    (by rw [List.getElem?_range hj]) h, hu, digOf_ofFn]

/-- the values of tokens that are in a store do not change when the store grows -/
theorem patchL_store (ll : LeafLens Ω μ ℓ Z) (i : ℕ) (b : Bool) (k : ℕ) {vs ws : List Bits}
    (hp : vs <+: ws) (ω : Ω) : ∀ (js : List ℕ) (as : List (Tok × Tok)),
      (∀ a ∈ as, a.1 < vs.length) → patchL ll i b k js as ws ω = patchL ll i b k js as vs ω
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | j :: js, a :: as, h => by
    show ll.upd i b k j _ (patchL ll i b k js as ws ω) = ll.upd i b k j _ (patchL ll i b k js as vs
        ω)
    rw [getD_of_prefix hp (h a (List.mem_cons_self ..)),
      patchL_store ll i b k hp ω js as fun a' ha' => h a' (List.mem_cons_of_mem _ ha')]

/-- the coins with the values of the tokens of the trees k, k + 1, .. of a component laid in -/
def patchTs (ll : LeafLens Ω μ ℓ Z) (i : ℕ) (b : Bool) :
    ℕ → List (TreeT lam L) → List Bits → Ω → Ω
  | k, T :: Ts, vs, ω => patchT ll i b k T vs (patchTs ll i b (k + 1) Ts vs ω)
  | _, [], _, ω => ω

/-- the trees k, k + 1, .. of a component as the compiled prover keeps them, at the coins ωa -/
def mkKs (ll : LeafLens Ω μ ℓ Z) (st : Bits) (i : ℕ) (b : Bool) (ωa : Ω) :
    ℕ → List (TreeT lam L) → List (TreeK lam L)
  | k, T :: Ts => mkK ll st i b k ωa T :: mkKs ll st i b ωa (k + 1) Ts
  | _, [] => []

theorem mkKs_congr (ll : LeafLens Ω μ ℓ Z) (st : Bits) (i : ℕ) (b : Bool) (ωa ωb : Ω) :
    ∀ (Ts : List (TreeT lam L)) (k : ℕ),
      (∀ k' j, k ≤ k' → ll.get ωa i b k' j = ll.get ωb i b k' j) →
      mkKs ll st i b ωa k Ts = mkKs ll st i b ωb k Ts
  | [], _, _ => rfl
  | T :: Ts, k, h => by
    show mkK ll st i b k ωa T :: mkKs ll st i b ωa (k + 1) Ts =
      mkK ll st i b k ωb T :: mkKs ll st i b ωb (k + 1) Ts
    rw [mkKs_congr ll st i b ωa ωb Ts (k + 1) fun k' j hk => h k' j (Nat.le_of_succ_le hk)]
    refine congrArg (· :: _) ?_
    unfold mkK
    exact congrArg (fun f => (⟨f, T.lv⟩ : TreeK lam L))
      (funext fun j => by rw [h k j (Nat.le_refl k)])

/-- The builder reads the salts of the trees from number k on alone. -/
theorem treesO_congr {r : Round} (pad : Body L) (sl sl' : ℕ → ℕ → Bits)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ∀ (ds : List ℕ) (k : ℕ), (∀ k' j, k ≤ k' → sl k' j = sl' k' j) →
      treesO (lam := lam) (K := K) pad sl posAt emb o k ds = treesO pad sl' posAt emb o k ds
  | [], _, _ => rfl
  | d :: ds, k, h => by
    have e : sl k = sl' k := funext fun j => h k j (Nat.le_refl k)
    simp only [treesO, e,
      treesO_congr pad sl sl' posAt emb o ds (k + 1) fun k' j hk => h k' j (Nat.le_of_succ_le hk)]

/-- **The trees of a component.** -/
theorem tie_trees {r : Round} (ll : LeafLens Ω μ ℓ Z) (us : List Tok) (pre : List Bits → Bits)
    (st : Bits) (i : ℕ) (b : Bool) (pad : Body L) (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ∀ (ds : List ℕ) (k : ℕ) (vs : List Bits),
      (∀ n d, ds[n]? = some d → ∀ j, j < 2 ^ d → Z i b (k + n) j) →
      (∀ u ∈ us, u < vs.length) → pre (us.map fun u => vs.getD u []) = st →
      Tie μ
        (fun (p : List (TreeT lam L) × List Bits) ω =>
          (mkKs ll st i b (patchTs ll i b k p.1 p.2 ω) k p.1, patchTs ll i b k p.1 p.2 ω))
        (fun p => vs <+: p.2 ∧ TreesOK ℓ ds p.2 p.1)
        (plainOf (treesT (K := K) ℓ us pre pad posAt emb o k ds) vs)
        (fun ω => (treesO (K := K) pad (fun k j => st ++ ll.get ω i b k j) posAt emb o k ds).bind
          fun Ts => .pure (Ts, ω)) := by
  intro ds
  induction ds with
  | nil =>
    intro k vs _ _ _
    exact .done ⟨List.prefix_rfl, List.Forall₂.nil⟩ fun _ => rfl
  | cons d ds ih =>
    intro k vs hz hu hst
    show Tie μ _ _ (plainOf ((treeT (K := K) ℓ us pre d fun j => match posAt k j with
        | some p => emb p (r.rd o p)
        | none => pad).bind fun T =>
      (treesT ℓ us pre pad posAt emb o (k + 1) ds).bind fun Ts => Step.pure (T :: Ts)) vs) _
    rw [plainOf_bind]
    refine (Tie.bindW (tie_tree ll us pre st i b k d _ vs (fun j hj => hz 0 d rfl j hj) hu hst)
      (f' := fun ω T => (treesO (K := K) pad (fun k j => st ++ ll.get ω i b k j) posAt emb o
        (k + 1) ds).bind fun Ts => .pure (T :: Ts, ω)) fun p hp => ?_).congr fun ω => ?_
    · have e : ∀ ω, treesO (lam := lam) (K := K) pad
          (fun k' j => st ++ ll.get (patchT ll i b k p.1 p.2 ω) i b k' j) posAt emb o (k + 1) ds =
          treesO pad (fun k' j => st ++ ll.get ω i b k' j) posAt emb o (k + 1) ds := fun ω =>
        treesO_congr pad _ _ posAt emb o ds (k + 1) fun k' j hk => by
          show st ++ ll.get (patchL ll i b k _ _ _ ω) i b k' j = _
          rw [get_patchL_ne ll i b k p.2 ω i b k' j fun h => by omega]
      rw [plainOf_bind]
      refine ((ih (k + 1) p.2 (fun n d' hn j hj => by
          have := hz (n + 1) d' hn j hj
          rwa [show k + (n + 1) = k + 1 + n by omega] at this)
        (fun u hu' => Nat.lt_of_lt_of_le (hu u hu') hp.1.length_le) (by
          rw [← hst]
          exact congrArg pre (List.map_congr_left fun u hu' => getD_of_prefix hp.1 (hu u
              hu')))).bind
        (f' := fun y => .pure (mkK ll st i b k (patchT ll i b k p.1 p.2 y.2) p.1 :: y.1,
          patchT ll i b k p.1 p.2 y.2)) fun q hq => ?_).congr fun ω => ?_
      · have es : ∀ ω', patchT ll i b k p.1 q.2 ω' = patchT ll i b k p.1 p.2 ω' := fun ω' =>
          patchL_store ll i b k hq.1 ω' _ _ fun a ha => (hp.2.2.1 a ha).1
        refine .done ⟨hp.1.trans hq.1, List.Forall₂.cons (hp.2.mono hq.1) hq.2⟩ fun ω => ?_
        · show OComp.pure _ = OComp.pure
            (mkK ll st i b k (patchT ll i b k p.1 q.2 (patchTs ll i b (k + 1) q.1 q.2 ω)) p.1 ::
              mkKs ll st i b (patchT ll i b k p.1 q.2 (patchTs ll i b (k + 1) q.1 q.2 ω)) (k + 1)
                q.1,
             patchT ll i b k p.1 q.2 (patchTs ll i b (k + 1) q.1 q.2 ω))
          rw [es, mkKs_congr ll st i b (patchT ll i b k p.1 p.2 (patchTs ll i b (k + 1) q.1 q.2 ω))
            (patchTs ll i b (k + 1) q.1 q.2 ω) q.1 (k + 1) fun k' j hk =>
              get_patchL_ne ll i b k p.2 _ i b k' j (fun h => by omega) _ _]
      · beta_reduce
        rw [e, Tie.obind_assoc]
        rfl
    · show ((treeO (K := K) d fun j => (⟨match posAt k j with
          | some p => emb p (r.rd o p)
          | none => pad, st ++ ll.get ω i b k j⟩ : LeafIn L)).bind fun T =>
        (treesO (K := K) pad (fun k j => st ++ ll.get ω i b k j) posAt emb o (k + 1) ds).bind
          fun Ts => OComp.pure (T :: Ts)).bind (fun Ts => OComp.pure (Ts, ω)) = _
      rw [Tie.obind_assoc]
      refine congrArg _ (funext fun T => ?_)
      rw [Tie.obind_assoc]
      rfl

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.tie_leaves
#print axioms OnBytes.TokenSide.tie_tree
#print axioms OnBytes.TokenSide.tie_trees
