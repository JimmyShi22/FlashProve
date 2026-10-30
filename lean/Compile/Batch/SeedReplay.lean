-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedReplay.lean: the prover with the seed replays the key, for every scheme `argBk` of
Compile/Batch/SeedStar.lean, under two hypotheses. (Words of this library: lean/GLOSSARY.md.)

After the derived run of the committer (C with its samples made from small ones: `Cb` of
Compile/Batch/SeedStar.lean), on every table that contains what that run has written, the prover
`PS`, which derives only the `Node` of the sampled copy again, on an empty store, behaves as the
prover of the scheme with the whole key. This is the property `Rom.Replays` of Rom/DeriveWith.lean.

  Part 1  `node_small`: the `Node` of a copy made on the empty store is the `Node` made on the store
          that C has at that moment, followed by a renumbering of tokens; `batch_eq`: a batch does
          not depend on the store around the `Node` (from `Face.TokFree`, under the conditions of
          its statement)
  Part 2  `key_facts`: what the run of C fixes: the `Node` of each copy, at its offset
  Part 3  `replays`: the theorem, if σ.o = `OracleName.other` and F has `TokFree`; `argAvoids`,
          `argAvoidsBk`: under `F.NoOther` no algorithm of `argOf`, `argBk` queries the auxiliary
          oracle

Limits: nothing about a particular prover: that the program of a batch does not look at the numbers
of its tokens, and that it and V never query the auxiliary oracle, are hypotheses here
(`Face.TokFree`, `Face.NoOther`).
-/
import Compile.Batch.SeedShape
import Compile.Batch.SeedParNode
import Compile.Batch.RealQTree
import Compile.SeedReplay

noncomputable section

open Rom Iop ZKCP

namespace Compile.Batch
namespace Seed

open Compile.Life2 (up down viewVals)
open Compile.Seed
  (Par ORel Out All Fixes SaltsLt Wt Tosses upTree downTree downTree_up upTree_of_lt viewVals_prefix
    fixes_of_mem mem_runRec_bind runRec_map all_prefix)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-! ## Part 1 -/

/-- the tokens of a `Node`, shown back (`downTree`) -/
def downNode (N₀ δ : ℕ) (nd : Node lam L) : Node lam L := ⟨nd.r, downTree N₀ δ nd.tree⟩

theorem downNode_up (N₀ δ : ℕ) (nd : Node lam L) : downNode N₀ δ (upNode N₀ δ nd) = nd := by
  unfold downNode upNode
  simp only [downTree_up]

theorem upNode_of_lt {N₀ δ : ℕ} {nd : Node lam L} (h : SaltsLt N₀ nd.tree.salts) :
    upNode N₀ δ nd = nd := by
  unfold upNode
  rw [upTree_of_lt h]

theorem viewVals_all (Sk : List Bits) : viewVals 0 Sk.length Sk = [] := by
  simp [viewVals]

/-- the relation between the `Node` of a copy on the store Sk of C and on the empty store -/
theorem orel_node (i : I) (Sk : List Bits) :
    ORel (Out 0 Sk.length fun a a' => a = upNode 0 Sk.length a')
      (erase (nodeP' W WP p i) Sk) (erase (nodeP' W WP p i) []) := by
  have h := par_nodeP' (N₀ := 0) (δ := Sk.length) W WP p i Sk (by omega)
  rwa [viewVals_all] at h

/-- The `Node` of a copy on the empty store is the `Node` on the store that C has at that moment,
followed by a renumbering of tokens. -/
theorem node_small (i : I) (Sk : List Bits) :
    erase (nodeP' W WP p i) [] =
      (erase (nodeP' W WP p i) Sk).bind fun o =>
        .pure (downNode 0 Sk.length o.1, viewVals 0 Sk.length o.2) :=
  (orel_node W WP p i Sk).eq_map _ fun a b hab => by
    obtain ⟨h1, h2, -⟩ := hab
    refine Prod.ext ?_ h2
    show b.1 = downNode _ _ a.1
    rw [h1, downNode_up]

variable {W} {IVK' Pf' : Type} (F : Face W IVK' Pf')

/-- Under `F.TokFree` and the conditions below, a batch does not depend on the store around the
`Node`. nd is the `Node` as C has it, S1 the store of C right after the `Node`, vs the whole store.
-/
theorem batch_eq0 {γ : Type} (hF : F.TokFree) (i : I) (j : ℕ) (b : List (X × Unit))
    {nd : Node lam L} {S1 vs : List Bits} {N₀ δ : ℕ} (hlt : SaltsLt S1.length nd.tree.salts)
    (hpre : S1 <+: vs) (hN : N₀ + δ ≤ S1.length) (hup : upNode N₀ δ (downNode N₀ δ nd) = nd)
    (g : Gen.Slots Pf' b → TypedOracleComputation lam W.K L γ) :
    (erase (F.bat i j (some (downNode N₀ δ nd)) b) (viewVals N₀ δ S1)).bind (fun c => g c.1) =
      (erase (F.bat i j (some nd) b) vs).bind fun c => g c.1 := by
  have h1 := hF S1.length (vs.length - S1.length) i j nd b vs (by have := hpre.length_le; omega)
  rw [upNode_of_lt hlt, viewVals_prefix hpre] at h1
  have h2 := hF N₀ δ i j (downNode N₀ δ nd) b S1 hN
  rw [hup] at h2
  rw [h1.bind_eq (g := fun c => g c.1) (g' := fun c => g c.1) fun a b hab => congrArg g hab.1]
  exact (h2.bind_eq (g := fun c => g c.1) (g' := fun c => g c.1) fun a b hab =>
    congrArg g hab.1).symm

/-- `batch_eq0` for what the scheme runs: `eraseR` in the place of `erase` (the ghost names written
back) -/
theorem batch_eq {γ : Type} (hF : F.TokFree) (i : I) (j : ℕ) (b : List (X × Unit)) {nd : Node lam L}
    {S1 vs : List Bits} {N₀ δ : ℕ} (hlt : SaltsLt S1.length nd.tree.salts) (hpre : S1 <+: vs)
    (hN : N₀ + δ ≤ S1.length) (hup : upNode N₀ δ (downNode N₀ δ nd) = nd)
    (g : Gen.Slots Pf' b → TypedOracleComputation lam W.K L γ) :
    (eraseR (F.bat i j (some (downNode N₀ δ nd)) b) (viewVals N₀ δ S1)).bind (fun c => g c.1) =
      (eraseR (F.bat i j (some nd) b) vs).bind fun c => g c.1 := by
  have e : ∀ (c : St lam W.K L (Gen.Slots Pf' b)) (ws : List Bits),
      (eraseR c ws).bind (fun o => g o.1) =
        (realQ ((erase c ws).bind fun o => OComp.pure o.1)).bind g := by
    intro c ws
    rw [realQ_bind, OComp.bind_assoc]
    rfl
  rw [e, e, batch_eq0 F hF i j b hlt hpre hN hup fun o => OComp.pure o]

/-- what holds of every result still holds when the ghost names are written back (`realQ`) -/
theorem all_realQ {K : ℕ} {α : Type} {Q : α → Prop} :
    ∀ c : OComp (spec lam K L) α, All Q c → All Q (realQ c) := by
  intro c
  induction c with
  | pure a => exact fun h => h
  | sample m k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    intro h
    cases o with
    | fbw t j => exact fun r => ih r (h r)
    | _ => exact fun r => ih r (h r)

/-- the weighted number of samples on every path, stated for `eraseR` (so that a rewriting finds its
pattern) -/
theorem wt_eraseR {K : ℕ} {α : Type} {μ : ℕ → ℕ} {n : ℕ} {c : St lam K L α}
    {vs : List Bits} (h : Wt μ n (erase c vs)) : Wt μ n (eraseR c vs) := wt_realQ h

/-! ## Part 2. What the run of C fixes -/

variable (W) (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))

/-- What the run of C fixes of the `Node` of one copy: nd is the `Node`, j the number of its first
small sample, vsE the whole store. Sk and Sk1 are the stores of C before and after the `Node`. -/
def NodeFacts (i : I) (vsE : List Bits) (T : Table (spec lam W.K L)) (R : Derive.Rec σ)
    (j : ℕ) (nd : Node lam L) : Prop :=
  ∃ Sk Sk1 : List Bits,
    Sk <+: Sk1 ∧ Sk1 <+: vsE ∧
    Fixes σ ((erase (nodeP' W WP p i) Sk).blocks bk) j T R (nd, Sk1) ∧
    SaltsLt Sk1.length nd.tree.salts ∧
    upNode 0 Sk.length (downNode 0 Sk.length nd) = nd

/-- the copies of C, as an oracle algorithm: a `Node`, its run of Link, then the other copies -/
theorem erase_leavesC_succ (i : I) (root : Node lam L) (n : ℕ) (vs : List Bits) :
    eraseR (leavesC W WP p i root (n + 1)) vs =
      (erase (nodeP' W WP p i) vs).bind fun a =>
        (eraseR (proveLk W WP p root.tree a.1.tree i root.r a.1.r) a.2).bind fun c =>
      (eraseR (leavesC W WP p i root n) c.2).bind fun r =>
          .pure ((⟨a.1, c.1⟩ : LeafRec lam L) :: r.1, r.2) := by
  simp only [leavesC, eraseR_bind, eraseR_nodeP']
  rfl

/-- The copies of C, by induction: the list has an entry at each k < n, and the `Node` of copy k is
fixed at its offset. -/
theorem leaves_facts (i : I) (root : Node lam L) :
    ∀ (n : ℕ) (S : List Bits) (j0 : ℕ) (T₀ : Table (spec lam W.K L)) (R₀ : Derive.Rec σ),
      ∀ x ∈ (Derive.runRec σ ((eraseR (leavesC W WP p i root n) S).blocks bk) j0 T₀ R₀).support,
        S <+: x.1.2 ∧
        ∀ k < n, ∃ lf,
          x.1.1[k]? = some lf ∧
          NodeFacts W WP p bk σ i x.1.2 x.2.1 x.2.2 (j0 + k * cLeaf W WP p bk.m) lf.node
  | 0, S, j0, T₀, R₀, x, hx => by
      have hx' : x ∈ (PMF.pure ((([] : List (LeafRec lam L)), S), T₀, R₀)).support := hx
      rw [PMF.support_pure, Set.mem_singleton_iff] at hx'
      subst hx'
      exact ⟨List.prefix_refl S, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | n + 1, S, j0, T₀, R₀, x, hx => by
      rw [erase_leavesC_succ, OComp.blocks_bind] at hx
      obtain ⟨a, ha, hx⟩ := mem_runRec_bind ((wt_nodeP' W WP p bk.m i S).tosses_blocks bk) hx
      rw [OComp.blocks_bind] at hx
      obtain ⟨c, hc, hx⟩ := mem_runRec_bind
        ((wt_realQ
          (wt_proveLk W WP p bk.m root.tree a.1.1.tree i root.r a.1.1.r a.1.2)).tosses_blocks bk) hx
      rw [OComp.blocks_bind] at hx
      have hx' : x ∈
          (Derive.runRec σ
            (((eraseR (leavesC W WP p i root n) c.1.2).blocks bk).bind fun r =>
              .pure ((⟨a.1.1, c.1.1⟩ : LeafRec lam L) :: r.1, r.2))
            (j0 + cNode W WP p bk.m + cProveB bk.m p.sMT p.sFS W.Lk WP.Lk 1) c.2.1 c.2.2).support :=
        hx
      rw [runRec_map ((eraseR (leavesC W WP p i root n) c.1.2).blocks bk) fun r =>
          ((⟨a.1.1, c.1.1⟩ : LeafRec lam L) :: r.1, r.2)] at hx'
      obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx'
      have hSa : S <+: a.1.2 :=
        All.of_runRec σ ((all_prefix (nodeP' W WP p i) S).blocks bk) _ _ _ a ha
      have hac : a.1.2 <+: c.1.2 :=
        All.of_runRec σ ((all_realQ _ (all_prefix _ a.1.2)).blocks bk) _ _ _ c hc
      obtain ⟨hcz, ih⟩ := leaves_facts i root n c.1.2 _ c.2.1 c.2.2 z hz
      obtain ⟨hT1, hR1⟩ := Derive.runRec_sub σ _ _ _ _ c hc
      obtain ⟨hT2, hR2⟩ := Derive.runRec_sub σ _ _ _ _ z hz
      refine ⟨(hSa.trans hac).trans hcz, fun k hk => ?_⟩
      cases k with
      | zero =>
        refine ⟨⟨a.1.1, c.1.1⟩, rfl, S, a.1.2, hSa, hac.trans hcz, ?_,
          All.of_runRec σ ((all_nodeP' W WP p i S).blocks bk) _ _ _ a ha, ?_⟩
        · rw [Nat.zero_mul, Nat.add_zero]
          exact (fixes_of_mem ha).mono (hT1.trans hT2) (hR1.trans hR2)
        · obtain ⟨b, hb, -⟩ :=
            All.of_runRec σ ((orel_node W WP p i S).all_left.blocks bk) _ _ _ a ha
          show upNode 0 S.length (downNode 0 S.length a.1.1) = a.1.1
          rw [hb, downNode_up]
      | succ k =>
        obtain ⟨lf, h1, h2⟩ := ih k (by omega)
        refine ⟨lf, h1, ?_⟩
        have e : j0 + cNode W WP p bk.m +
              cProveB bk.m p.sMT p.sFS W.Lk WP.Lk 1 + k * cLeaf W WP p bk.m =
            j0 + (k + 1) * cLeaf W WP p bk.m := by
          rw [Nat.succ_mul]
          unfold cLeaf
          omega
        rw [← e]
        exact h2

variable {W}

/-- the committer of `argOf`, step by step -/
theorem argOf_C (i : I) :
    (argOf WP p F).C i =
      ((erase (nodeP' W WP p i) []).bind fun a =>
        (eraseR (proveT W WP p a.1.tree i a.1.r) a.2).bind fun b =>
            (eraseR (leavesC W WP p i a.1 (p.M + 1)) b.2).bind fun c =>
                .pure (F.key ⟨a.1.tree.root, b.1⟩ ⟨i, a.1, c.1⟩,
                      ((⟨i, a.1, c.1⟩ : IskH lam L), c.2))) := by
  have e : C W WP p i = (eraseR (Cp W WP p i) []).bind fun o => .pure (o.1.1, (o.1.2, o.2)) :=
    realQ_bind _ _
  unfold argOf
  show (C W WP p i).bind _ = _
  rw [e]
  unfold Cp
  simp only [eraseR_bind, eraseR_nodeP', OComp.bind_assoc]
  rfl

/-- What the run of C fixes: the index, and the `Node` of every copy at its offset. -/
theorem key_facts (i : I) (x : (IVK' × ISK lam L) × Table (spec lam W.K L) × Derive.Rec σ)
    (hx : x ∈ (Derive.runRec σ (Cb WP p F bk i) 0 (Table.empty _) fun _ => none).support) :
    x.1.2.1.i = i ∧
    ∀ k < p.M + 1, ∃ lf,
      x.1.2.1.leaves[k]? = some lf ∧
      NodeFacts W WP p bk σ i x.1.2.2 x.2.1 x.2.2 (off W WP p bk.m k) lf.node := by
  unfold Cb at hx
  rw [argOf_C, OComp.blocks_bind] at hx
  obtain ⟨a, ha, hx⟩ := mem_runRec_bind ((wt_nodeP' W WP p bk.m i []).tosses_blocks bk) hx
  rw [OComp.blocks_bind] at hx
  obtain ⟨b, hb, hx⟩ := mem_runRec_bind
    ((wt_realQ (wt_proveT W WP p bk.m a.1.1.tree i a.1.1.r a.1.2)).tosses_blocks bk) hx
  rw [OComp.blocks_bind] at hx
  have hx' : x ∈ (Derive.runRec σ (((eraseR (leavesC W WP p i a.1.1 (p.M + 1)) b.1.2).blocks bk).bind fun c =>
      .pure (F.key ⟨a.1.1.tree.root, b.1.1⟩ ⟨i, a.1.1, c.1⟩, ((⟨i, a.1.1, c.1⟩ : IskH lam L), c.2)))
      (0 + cNode W WP p bk.m + cProveB bk.m p.sMT p.sFS W.T WP.T 1) b.2.1 b.2.2).support := hx
  rw [runRec_map ((eraseR (leavesC W WP p i a.1.1 (p.M + 1)) b.1.2).blocks bk) fun c =>
      (F.key ⟨a.1.1.tree.root, b.1.1⟩ ⟨i, a.1.1, c.1⟩,
        ((⟨i, a.1.1, c.1⟩ : IskH lam L), c.2))] at hx'
  obtain ⟨c, hc, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx'
  obtain ⟨-, hl⟩ := leaves_facts W WP p bk σ i a.1.1 (p.M + 1) b.1.2 _ b.2.1 b.2.2 c hc
  refine ⟨rfl, fun k hk => ?_⟩
  obtain ⟨lf, h1, h2⟩ := hl k hk
  refine ⟨lf, h1, ?_⟩
  have e : 0 + cNode W WP p bk.m + cProveB bk.m p.sMT p.sFS W.T WP.T 1 + k * cLeaf W WP p bk.m =
      off W WP p bk.m k := by
    unfold off; omega
  rw [← e]
  exact h2

/-! ## Part 3. The theorem -/

variable {σ}

/-- Under hσ, hF: the prover with the seed replays the key. -/
theorem replays (hσ : σ.o = OracleName.other) (hF : F.TokFree) :
    Replays (argBk WP p F bk) σ (PS WP p F bk σ) := by
  intro i s x hx T hT b
  obtain ⟨hi, hl⟩ := key_facts WP p F bk σ i x hx
  show (PMF.uniformOfFintype (Fin (p.M + 1))).bind _ = (PMF.uniformOfFintype (Fin (p.M + 1))).bind _
  refine congrArg _ (funext fun j => ?_)
  obtain ⟨lf, hlf, Sk, Sk1, h1, h2, hfix, hlt, hup⟩ := hl j.val j.2
  show ((((erase (nodeP' W WP p i) []).blocks bk).derive σ s (off W WP p bk.m j.val)).bind
      fun a => (eraseR (F.bat i j.val (some a.1) b) a.2).bind fun o => OComp.pure o.1).runLazy _ =
    ((eraseR (F.bat x.1.2.1.i j.val (x.1.2.1.leaves[j.val]?.map LeafRec.node) b) x.1.2.2).bind
      fun o => OComp.pure o.1).runLazy _
  have hfix' :=
    hfix.map fun o : Node lam L × List Bits => (downNode 0 Sk.length o.1, viewVals 0 Sk.length o.2)
  have esm : (erase (nodeP' W WP p i) []).blocks bk =
      ((erase (nodeP' W WP p i) Sk).blocks bk).bind fun o =>
        .pure (downNode 0 Sk.length o.1, viewVals 0 Sk.length o.2) :=
    (congrArg (fun c => OComp.blocks bk c) (node_small W WP p i Sk)).trans
      (OComp.blocks_bind bk _ _)
  rw [← esm] at hfix'
  rw [OComp.runLazy_bind, hfix'.runLazy (hσ ▸ (avoids_nodeP' W WP p i []).blocks bk) s hT,
    PMF.pure_bind, hlf, hi]
  exact congrArg (fun c => OComp.runLazy c (Derive.glue σ s T x.2.2))
    (batch_eq F hF i j.val b (nd := lf.node) (S1 := Sk1) (vs := x.1.2.2) (N₀ := 0) (δ := Sk.length)
      hlt h2 (by have := h1.length_le; omega) hup fun o => OComp.pure o)

/-- None of the three algorithms of `argOf` queries OracleName.other, if its program of a batch and its
verifier do not. -/
theorem argAvoids (hF : F.NoOther) : ArgAvoids (argOf WP p F) OracleName.other where
  C := fun i => Derive.Avoids.bind (avoids_C W WP p i) fun _ => trivial
  P := fun _ _ _ => Derive.Avoids.bind (hF.bat _ _ _ _ _) fun _ => trivial
  V := hF.V

/-- the same for `argBk`, whose committer makes its samples from small ones -/
theorem argAvoidsBk (hF : F.NoOther) : ArgAvoids (argBk WP p F bk) OracleName.other where
  C := fun i => ((argAvoids WP p F hF).C i).blocks bk
  P := (argAvoids WP p F hF).P
  V := (argAvoids WP p F hF).V

end Seed
end Compile.Batch
