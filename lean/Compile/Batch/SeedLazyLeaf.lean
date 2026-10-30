-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedLazyLeaf.lean: a block of leaves of a derived `Node`, recomputed alone, is the
block of the `Node`. (not all hypotheses are named here: see `sumry_block`) (Words of this library:
lean/GLOSSARY.md.)

The committer derives the `Node` (Compile/Batch/Star.lean) of copy j under the seed: the randomness
r of the encoding, then, leaf by leaf, a digest for each of the 2 ^ depth leaves of its tree and a
salt for each leaf that holds a symbol. The lazy prover of Compile/Batch/SeedLazyDefs.lean derives r
and, for a position that is shown, only the block of 2 ^ ℓ leaves that holds it, on an empty store,
at the counter at which the committer derived that block. Here: for ℓ ≤ W.depth and a block, or
leaf, within the tree, under fixed oracle functions it gets the same digests and the same salts, and
with the stored level the same path.

  Part 1  `ORel.derive`, `ORel.det`: two algorithms of the same shape stay so when their coins are
          derived, and have related values under fixed oracle functions
  Part 2  `leavesD`: a derived run of `leavesE`; `sumry`: its digests and the strings of its salts.
          `sumry_store`: the summary does not depend on the store on which the leaves are made;
          `sumry_append`: it is additive over l₁ ++ l₂, the counter moved by the samples of l₁
  Part 3  `sumry_block`: the summary of block u is the stretch of the `Node`'s summary
  Part 4  `det_opL`: the opening of leaf q that the lazy prover makes is the opening from the whole
          `Node`: the same salt, the same path, and the comparison with the stored level succeeds

Notation: `bk`: a `CoinPlan`: how a uniform sample is made from small ones (Rom/Blocks.lean); `σ`: a
`SeedOracle`: an auxiliary oracle, used as a source of coins; `pt s j` is the query for the seed s
and the counter j (Rom/SpecDerive.lean); `s`: an element of `Fin (σ.sd + 1)`, a seed; `k`: an
element of `I × Fin (σ.sd + 1)`: (i, seed); `g`: a `Fam`: a whole family of functions
(Rom/OSpec.lean); `j`: a natural number: in Parts 3 and 4 the number of a copy; `sMT`: a natural
number: the length of the salt of a leaf (Compile/Batch/Verifier.lean); `c.derive σ s j`: the
algorithm with its coins derived under the seed s; j is the number of samples so far
(Rom/SpecDerive.lean); `c.det g`: the result of the run under the oracle functions g in which every
sample is 0 (Rom/Cache.lean); `frontD k j`: the first part of `nodeD`, the `Node` of copy j, derived
under the seed on an empty store (Compile/Batch/SeedCache.lean); of its value `.1.1` is the
randomness of the encoding, `.1.2.1` the digests of the leaves, `.1.2.2` the tokens of their salts
(`Front`), `.2` the store; `hNode g`: the node function of the trees over encoded indices under
fixed oracle functions; `lowF h ℓ l`: the levels below level ℓ, and level ℓ as it is hashed from the
level below it (level 0: the leaves themselves) (both: Compile/Batch/SeedCache.lean); `blockD`:
block u of 2^ℓ leaves of the tree of copy j, derived under the seed on an empty store; `strOf`,
`leafFn`, `opL`: see their doc comments (these four: Compile/Batch/SeedLazyDefs.lean); store: the
head of Compile/Batch/SeedParTree.lean.

Limits: nothing about a stored level that is not the `Node`'s own. No cost.
-/
import Compile.Batch.SeedLazyDefs
import Compile.Batch.SeedLazyTree
import Compile.Batch.SeedReplay
import Compile.SeedSize

noncomputable section

open Rom Iop ZKCP

namespace Compile.Batch
namespace Seed

open Compile.Life2 (up viewVals getD_viewVals)
open Compile.Seed (ORel Out All SaltsLt Tosses derive_bind all_prefix upS cLeaves length_filter_lt)

/-! ## Part 1 -/

section Gen
variable {S : OSpec} {α β : Type}

theorem ORel.derive {r : α → β → Prop} {c : OComp S α} {c' : OComp S β} (h : ORel r c c')
    (σ : SeedOracle S) (s : Fin (σ.sd + 1)) :
    ∀ j, ORel r (c.derive σ s j) (c'.derive σ s j) := by
  induction h with
  | pure h => exact fun _ => .pure h
  | query o q _ ih => exact fun j => .query o q fun x => ih x j
  | sample n _ ih => exact fun j => .query σ.o (σ.pt s j) fun d => ih _ (j + 1)

theorem ORel.det {r : α → β → Prop} {c : OComp S α} {c' : OComp S β} (h : ORel r c c') (g : Fam S) :
    r (c.det g) (c'.det g) := by
  induction h with
  | pure h => exact h
  | query o q _ ih => exact ih _
  | sample n _ ih => exact ih _

theorem bind_pure_id (c : OComp S α) : (c.bind fun a => .pure a) = c := by
  induction c with
  | pure a => rfl
  | query o q k ih => exact congrArg _ (funext ih)
  | sample n k ih => exact congrArg _ (funext ih)

end Gen

/-! ## Part 2. Derived leaves -/

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

section Leaves
variable {K : ℕ} (sMT : ℕ) (bk : CoinPlan) (σ : SeedOracle (spec lam K L))
  (s : Fin (σ.sd + 1)) (g : Fam (spec lam K L))

/-- what a run of leavesE returns: digests, tokens of salts; and the store -/
abbrev LOut (lam : ℕ) : Type := (List (Dig lam) × List (Option (Tok × Tok))) × List Bits

/-- a derived run of leavesE, from the counter c, on the store vs -/
def leavesD (c : ℕ) (l : List (Body L × Bool)) (vs : List Bits) : TypedOracleComputation lam K L (LOut lam) :=
  ((erase (leavesE sMT l) vs).blocks bk).derive σ s c

/-- the digests, and the strings of the salts -/
def sumry (o : LOut lam) : List (Dig lam) × List Bits := (o.1.1, o.1.2.map (strOf o.2))

theorem leavesE_cons (b : Body L) (bl : Bool) (t : List (Body L × Bool)) :
    leavesE (lam := lam) (K := K) sMT ((b, bl) :: t) =
      (leafE sMT b bl).bind fun x =>
        (leavesE sMT t).bind fun r => Step.pure (x.1 :: r.1, x.2 :: r.2) := rfl

theorem erase_leavesE_append :
    ∀ (l₁ l₂ : List (Body L × Bool)) (vs : List Bits),
      erase (leavesE (lam := lam) (K := K) sMT (l₁ ++ l₂)) vs =
        (erase (leavesE sMT l₁) vs).bind fun a =>
          (erase (leavesE sMT l₂) a.2).bind fun b => .pure ((a.1.1 ++ b.1.1, a.1.2 ++ b.1.2), b.2)
  | [], l₂, vs => (bind_pure_id _).symm
  | (b, bl) :: t, l₂, vs => by
      rw [List.cons_append, leavesE_cons, leavesE_cons]
      simp only [erase_bind, OComp.bind_assoc, erase_leavesE_append t l₂]
      rfl

theorem tosses_leavesE (l : List (Body L × Bool)) (vs : List Bits) :
    Tosses (cLeaves l * bk.m (2 ^ sMT - 1))
      ((erase (leavesE (lam := lam) (K := K) sMT l) vs).blocks bk) :=
  ((sh_leavesE bk.m sMT l).wt vs).tosses_blocks bk

theorem leavesD_append (c : ℕ) (l₁ l₂ : List (Body L × Bool)) (vs : List Bits) :
    leavesD sMT bk σ s c (l₁ ++ l₂) vs =
      (leavesD sMT bk σ s c l₁ vs).bind fun a =>
        (leavesD sMT bk σ s (c + cLeaves l₁ * bk.m (2 ^ sMT - 1)) l₂ a.2).bind fun b =>
      .pure ((a.1.1 ++ b.1.1, a.1.2 ++ b.1.2), b.2) := by
  unfold leavesD
  rw [erase_leavesE_append, OComp.blocks_bind, derive_bind σ s (tosses_leavesE sMT bk l₁ vs)]
  refine congrArg _ (funext fun a => ?_)
  rw [OComp.blocks_bind, derive_bind σ s (tosses_leavesE sMT bk l₂ a.2)]
  rfl

theorem strOf_up {A : List Bits} {δ : ℕ} (h : 0 + δ ≤ A.length) (x : Option (Tok × Tok)) :
    strOf A (upS 0 δ x) = strOf (viewVals 0 δ A) x := by
  cases x with
  | none => rfl
  | some y => exact (getD_viewVals h y.1).symm

/-- The summary does not depend on the store on which the leaves are made. -/
theorem sumry_store (c : ℕ) (l : List (Body L × Bool)) (vs : List Bits) :
    sumry ((leavesD sMT bk σ s c l vs).det g) = sumry ((leavesD sMT bk σ s c l []).det g) := by
  have h :=
    par_leavesE (lam := lam) (K := K) (L := L) (N₀ := 0) (δ := vs.length) sMT l vs (by omega)
  rw [viewVals_all] at h
  obtain ⟨h1, h2, h3⟩ := ORel.det (ORel.derive (h.blocks bk) σ s c) g
  unfold sumry
  show (((leavesD sMT bk σ s c l vs).det g).1.1, _) = (((leavesD sMT bk σ s c l []).det g).1.1, _)
  have e1 : ((leavesD sMT bk σ s c l vs).det g).1 =
      (((leavesD sMT bk σ s c l []).det g).1.1,
        ((leavesD sMT bk σ s c l []).det g).1.2.map (upS 0 vs.length)) := h1
  have e2 : ((leavesD sMT bk σ s c l []).det g).2 =
      viewVals 0 vs.length ((leavesD sMT bk σ s c l vs).det g).2 := h2
  rw [e1, e2, List.map_map]
  exact congrArg _ (List.map_congr_left fun x _ => strOf_up h3 x)

theorem strOf_prefix {A B : List Bits} (h : A <+: B)
    {l : List (Option (Tok × Tok))} (hl : SaltsLt A.length l) :
    l.map (strOf B) = l.map (strOf A) := by
  obtain ⟨C, rfl⟩ := h
  refine List.map_congr_left fun x hx => ?_
  cases x with
  | none => rfl
  | some y =>
    show (A ++ C).getD y.1 [] = A.getD y.1 []
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (hl y hx).1]

theorem prefix_leavesD (c : ℕ) (l : List (Body L × Bool)) (vs : List Bits) :
    vs <+: ((leavesD sMT bk σ s c l vs).det g).2 :=
  all_det (Q := fun o : LOut lam => vs <+: o.2)
    g (all_derive σ s ((all_prefix (leavesE sMT l) vs).blocks bk) c)

theorem saltsLt_leavesD (c : ℕ) (l : List (Body L × Bool)) (vs : List Bits) :
    SaltsLt ((leavesD sMT bk σ s c l vs).det g).2.length ((leavesD sMT bk σ s c l vs).det g).1.2 :=
  all_det (Q := fun o : LOut lam => SaltsLt o.2.length o.1.2)
    g (all_derive σ s ((all_leavesE_lt sMT l vs).blocks bk) c)

/-- The summary is additive. -/
theorem sumry_append (c : ℕ) (l₁ l₂ : List (Body L × Bool)) :
    sumry ((leavesD sMT bk σ s c (l₁ ++ l₂) []).det g) =
      ((sumry ((leavesD sMT bk σ s c l₁ []).det g)).1 ++
          (sumry ((leavesD sMT bk σ s (c + cLeaves l₁ * bk.m (2 ^ sMT - 1)) l₂ []).det g)).1,
        (sumry ((leavesD sMT bk σ s c l₁ []).det g)).2 ++
          (sumry ((leavesD sMT bk σ s (c + cLeaves l₁ * bk.m (2 ^ sMT - 1)) l₂ []).det g)).2) := by
  rw [leavesD_append, OComp.det_bind, OComp.det_bind,
    ← sumry_store sMT bk σ s g (c + cLeaves l₁ * bk.m (2 ^ sMT - 1))
      l₂ ((leavesD sMT bk σ s c l₁ []).det g).2]
  have hp := strOf_prefix
    (prefix_leavesD sMT bk σ s g (c + cLeaves l₁ * bk.m (2 ^ sMT - 1))
      l₂ ((leavesD sMT bk σ s c l₁ []).det g).2)
    (saltsLt_leavesD sMT bk σ s g c l₁ [])
  generalize (leavesD sMT bk σ s c l₁ []).det g = A at hp ⊢
  generalize (leavesD sMT bk σ s (c + cLeaves l₁ * bk.m (2 ^ sMT - 1)) l₂ A.2).det g = B at hp ⊢
  show (A.1.1 ++ B.1.1, List.map (strOf B.2) (A.1.2 ++ B.1.2)) = _
  rw [List.map_append, hp]
  rfl

theorem all_leavesE_len2 :
    ∀ (l : List (Body L × Bool)) (vs : List Bits),
      All (fun o => o.1.2.length = l.length) (erase (leavesE (lam := lam) (K := K) sMT l) vs)
  | [], _ => rfl
  | (b, bl) :: t, vs => by
      rw [leavesE_cons, erase_bind]
      refine All.bind (all_true _) fun a _ => ?_
      rw [erase_bind]
      exact All.bind (all_leavesE_len2 t a.2) fun r hr => by
        show (a.1.2 :: r.1.2).length = _
        rw [List.length_cons, List.length_cons, hr]

theorem length_sumry1 (c : ℕ) (l : List (Body L × Bool)) (vs : List Bits) :
    (sumry ((leavesD sMT bk σ s c l vs).det g)).1.length = l.length :=
  all_det (Q := fun o : LOut lam => o.1.1.length = l.length)
    g (all_derive σ s ((all_leavesE sMT l vs).blocks bk) c)

theorem length_sumry2 (c : ℕ) (l : List (Body L × Bool)) (vs : List Bits) :
    (sumry ((leavesD sMT bk σ s c l vs).det g)).2.length = l.length := by
  unfold sumry
  rw [List.length_map]
  exact all_det (Q := fun o : LOut lam => o.1.2.length = l.length) g
    (all_derive σ s ((all_leavesE_len2 sMT l vs).blocks bk) c)

end Leaves

/-! ## Part 3. The first part of a derived `Node` -/

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
  (σ : SeedOracle (spec lam W.K L)) (g : Fam (spec lam W.K L)) (k : I × Fin (σ.sd + 1)) (j : ℕ)

/-- the first part of a derived `Node`: r, then the derived leaves -/
theorem frontD_eq : frontD W WP p bk σ k j = (rD W WP p bk σ k j).bind fun ra =>
    (leavesD p.sMT bk σ k.2 (off W WP p bk.m j + bk.m WP.ri.n)
          ((List.range (2 ^ W.depth)).map (leafFn k.1 ra.1)) ra.2).bind
        fun x => .pure ((ra.1, x.1), x.2) := by
  unfold frontD frontP rD leavesD
  rw [erase_bind, OComp.blocks_bind,
    derive_bind σ k.2 (((sh_drawT bk.m WP.ri).wt []).tosses_blocks bk)]
  refine congrArg _ (funext fun ra => ?_)
  rw [erase_bind, OComp.blocks_bind, derive_bind σ k.2 (tosses_leavesE p.sMT bk _ ra.2)]
  rfl

/-- The lazy prover's r is the `Node`'s. -/
theorem det_rD : ((rD W WP p bk σ k j).det g).1 = ((frontD W WP p bk σ k j).det g).1.1 := by
  rw [frontD_eq, OComp.det_bind, OComp.det_bind]
  rfl

/-- the summary of the `Node`'s leaves -/
theorem sumry_frontD :
    (((frontD W WP p bk σ k j).det g).1.2.1,
        ((frontD W WP p bk σ k j).det g).1.2.2.map (strOf ((frontD W WP p bk σ k j).det g).2)) =
      sumry ((leavesD p.sMT bk σ k.2 (off W WP p bk.m j + bk.m WP.ri.n)
          ((List.range (2 ^ W.depth)).map (leafFn k.1 ((frontD W WP p bk σ k j).det g).1.1))
          []).det g) := by
  rw [← det_rD, ← sumry_store p.sMT bk σ k.2 g _ _ ((rD W WP p bk σ k j).det g).2, frontD_eq,
    OComp.det_bind, OComp.det_bind]
  rfl

theorem cLeaves_range (i : I) (r : L.EncodingRandomness) (a : ℕ) :
    cLeaves ((List.range a).map (leafFn i r)) = min a L.wordLength := by
  unfold cLeaves
  rw [List.countP_map, List.countP_eq_length_filter, Nat.min_comm, ← length_filter_lt a L.wordLength]
  congr 1
  refine List.filter_congr fun t _ => ?_
  show (leafFn i r t).2 = _
  unfold leafFn
  by_cases h : t < L.wordLength
  · rw [dif_pos h, decide_eq_true h]
  · rw [dif_neg h, decide_eq_false h]

/-- the leaves of a `Node` (block u within the tree): those before block u, block u, those after it
-/
theorem range_blocks (i : I) (r : L.EncodingRandomness) {ℓ u : ℕ} (hu : (u + 1) * 2 ^ ℓ ≤ 2 ^ W.depth) :
    (List.range (2 ^ W.depth)).map (leafFn i r) =
      (List.range (u * 2 ^ ℓ)).map (leafFn i r) ++
        (((List.range (2 ^ ℓ)).map fun t => leafFn i r (u * 2 ^ ℓ + t)) ++
          (List.range (2 ^ W.depth - (u + 1) * 2 ^ ℓ)).map fun t =>
            leafFn i r ((u + 1) * 2 ^ ℓ + t)) := by
  have e : 2 ^ W.depth = u * 2 ^ ℓ + (2 ^ ℓ + (2 ^ W.depth - (u + 1) * 2 ^ ℓ)) := by
    rw [Nat.succ_mul] at hu ⊢
    omega
  conv_lhs => rw [e]
  rw [List.range_add, List.range_add, List.map_append, List.map_map, List.map_append, List.map_map]
  refine congrArg _ (congrArg₂ _ rfl ?_)
  refine List.map_congr_left fun t _ => ?_
  show leafFn i r (u * 2 ^ ℓ + (2 ^ ℓ + t)) = leafFn i r ((u + 1) * 2 ^ ℓ + t)
  rw [Nat.succ_mul, Nat.add_assoc]

/-- If block u is within the tree, its summary (`sumry`), derived by itself (`blockD`), is the
stretch of the `Node`'s summary that begins at entry u * 2 ^ ℓ: d1, s1, each of the length
u * 2 ^ ℓ, are what is before the block, d3, s3 what is after it. -/
theorem sumry_block {ℓ u : ℕ} (hu : (u + 1) * 2 ^ ℓ ≤ 2 ^ W.depth) :
    ∃ (d1 d3 : List (Dig lam)) (s1 s3 : List Bits),
      d1.length = u * 2 ^ ℓ ∧
      s1.length = u * 2 ^ ℓ ∧
      ((frontD W WP p bk σ k j).det g).1.2.1 =
        d1 ++ ((sumry
              ((blockD W WP p bk σ ℓ k j ((frontD W WP p bk σ k j).det g).1.1 u).det g)).1 ++ d3) ∧
      ((frontD W WP p bk σ k j).det g).1.2.2.map (strOf ((frontD W WP p bk σ k j).det g).2) =
        s1 ++ ((sumry
              ((blockD W WP p bk σ ℓ k j ((frontD W WP p bk σ k j).det g).1.1 u).det g)).2 ++
            s3) := by
  have h := sumry_frontD W WP p bk σ g k j
  rw [range_blocks W k.1 _ hu, sumry_append, sumry_append, cLeaves_range] at h
  refine ⟨_, _, _, _, ?_, ?_, congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rw [length_sumry1, List.length_map, List.length_range]
  · rw [length_sumry2, List.length_map, List.length_range]

/-! ## Part 4. The opening -/

theorem getD_map' {β γ : Type} (f : β → γ) (l : List β) (n : ℕ) (d : β) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> rfl

theorem getD_mid {β : Type} (d : β) {a b c : List β} {n t : ℕ}
    (ha : a.length = n) (ht : t < b.length) :
    (a ++ (b ++ c)).getD (n + t) d = b.getD t d := by
  subst ha
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left ht]

theorem block_mid {β : Type} {a b c : List β} {ℓ u : ℕ}
    (ha : a.length = u * 2 ^ ℓ) (hb : b.length = 2 ^ ℓ) :
    block ℓ u (a ++ (b ++ c)) = b := by
  unfold block
  rw [← ha, List.drop_left, ← hb, List.take_left]

/-- If ℓ ≤ W.depth and q < 2 ^ W.depth, and if r, the stored level and the levels above it are the
`Node`'s own, then the opening of leaf q that the lazy prover makes is the opening from the whole
`Node`. -/
theorem det_opL {ℓ q : ℕ} (hℓ : ℓ ≤ W.depth) (hq : q < 2 ^ W.depth) :
    (opL W WP p bk σ ℓ k j ((frontD W WP p bk σ k j).det g).1.1
        (lowF (hNode g) ℓ ((frontD W WP p bk σ k j).det g).1.2.1).2
        (levelsF (hNode g) (W.depth - ℓ)
          (lowF (hNode g) ℓ ((frontD W WP p bk σ k j).det g).1.2.1).2) q).det g =
      some (strOf ((frontD W WP p bk σ k j).det g).2
            (((frontD W WP p bk σ k j).det g).1.2.2.getD q none),
          pathOf (levelsF (hNode g) W.depth ((frontD W WP p bk σ k j).det g).1.2.1) q) := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hℓ
  have hpos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  have hpow : 2 ^ W.depth = 2 ^ e * 2 ^ ℓ := by rw [he, pow_add, Nat.mul_comm]
  have hu : q / 2 ^ ℓ < 2 ^ e := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hpow]; exact hq)
  have hu' : (q / 2 ^ ℓ + 1) * 2 ^ ℓ ≤ 2 ^ W.depth := by rw [hpow]; exact Nat.mul_le_mul_right _ hu
  have ht : q % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt _ hpos
  have hqq : q / 2 ^ ℓ * 2 ^ ℓ + q % 2 ^ ℓ = q := Nat.div_add_mod' q _
  obtain ⟨d1, d3, s1, s3, hd1, hs1, hD, hS⟩ := sumry_block W WP p bk σ g k j hu'
  generalize hy : (frontD W WP p bk σ k j).det g = y at hD hS ⊢
  generalize ha : (blockD W WP p bk σ ℓ k j y.1.1 (q / 2 ^ ℓ)).det g = a at hD hS
  have hlenY : y.1.2.1.length = 2 ^ W.depth := hy ▸ length_frontD W WP p bk σ g k j
  have hla1 : a.1.1.length = 2 ^ ℓ := by
    have := length_sumry1 p.sMT bk σ k.2 g
      (off W WP p bk.m j + bk.m WP.ri.n + min (q / 2 ^ ℓ * 2 ^ ℓ) L.wordLength * bk.m (2 ^ p.sMT - 1))
      ((List.range (2 ^ ℓ)).map fun t => leafFn k.1 y.1.1 (q / 2 ^ ℓ * 2 ^ ℓ + t)) []
    rw [List.length_map, List.length_range] at this
    rw [← ha]
    exact this
  have hla2 : (sumry a).2.length = 2 ^ ℓ := by
    have := length_sumry2 p.sMT bk σ k.2 g
      (off W WP p bk.m j + bk.m WP.ri.n + min (q / 2 ^ ℓ * 2 ^ ℓ) L.wordLength * bk.m (2 ^ p.sMT - 1))
      ((List.range (2 ^ ℓ)).map fun t => leafFn k.1 y.1.1 (q / 2 ^ ℓ * 2 ^ ℓ + t)) []
    rw [List.length_map, List.length_range] at this
    rw [← ha]
    exact this
  have hblock : block ℓ (q / 2 ^ ℓ) y.1.2.1 = a.1.1 := by rw [hD]; exact block_mid hd1 hla1
  have hlv : (lowF (hNode g) ℓ y.1.2.1).2 = lvl (hNode g) ℓ y.1.2.1 := by
    rw [← getD_levelsF (hNode g) hℓ, he, getD_levelsF_lvl]
  have hlen : (lvl (hNode g) ℓ y.1.2.1).length = 2 ^ e := by
    rw [← hlv, ← getD_levelsF (hNode g) hℓ, length_getD_levelsF' (hNode g) hℓ _ hlenY,
      he, Nat.add_sub_cancel_left]
  have hsalt : strOf a.2 (a.1.2.getD (q % 2 ^ ℓ) none) = strOf y.2 (y.1.2.2.getD q none) := by
    have e1 : strOf y.2 (y.1.2.2.getD q none) = (y.1.2.2.map (strOf y.2)).getD q [] :=
      (getD_map' (strOf y.2) y.1.2.2 q none).symm
    have e2 : strOf a.2 (a.1.2.getD (q % 2 ^ ℓ) none) = (sumry a).2.getD (q % 2 ^ ℓ) [] :=
      (getD_map' (strOf a.2) a.1.2 (q % 2 ^ ℓ) none).symm
    rw [e1, e2, hS]
    conv_rhs => rw [← hqq]
    exact (getD_mid [] hs1 (by rw [hla2]; exact ht)).symm
  unfold opL
  rw [OComp.det_bind, ha, OComp.det_bind, det_levelsV]
  show (if (lowF (hNode g) ℓ y.1.2.1).2[q / 2 ^ ℓ]? = some (rootOf (levelsF (hNode g) ℓ a.1.1)) then
        _
      else none) = _
  rw [if_pos (by
    rw [← hblock, rootOf_block, hlv, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hlen]; exact hu)]
    rfl), hsalt, ← hblock, hlv]
  congr 2
  have hp := pathOf_block (hNode g) ℓ e y.1.2.1 q
  rw [← he] at hp
  rw [hp, he, Nat.add_sub_cancel_left]

end Seed
end Compile.Batch
