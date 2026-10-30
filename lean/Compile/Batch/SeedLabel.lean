-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedLabel.lean: the label of a derived sample, read as (purpose, counter); the
purposes `leaf k` and `link k` name a copy. (Words of this library: lean/GLOSSARY.md.)

In Rom/SpecDerive.lean the coins of the committer C are derived from the seed under one running
counter. The implementation derives one key for each purpose (the anchor's masks; the one-time
files' coins; leaf k's masks; link k's coins) and counts under each key from 0. This file removes
that difference as far as the labels go. Nothing new is proved about the scheme: a way to write
labels is a choice of the queries `pt` of a `Rom.SeedOracle`, which Compile/Batch/SeedMain.lean
leaves free.

  `Purpose`   `anchor` (the first encoding), `test`, `leaf k` (copy k), `link k`
  `LabelOracle`   an oracle used as a source of coins under labels (purpose, counter): different
                  triples (seed, purpose, counter) have different queries
  `labelOf`, `labelOf_inj`   the running counter of C, read as a label: its purpose, and its number
                             among the samples of that purpose. Distinct counters have distinct
                             labels
  `derive_flat`   under the hypotheses of its statement, a stretch of C's run that serves one
                  purpose, derived under the running counter, is that stretch derived under its
                  purpose with a counter from 0
  `PSL`, `PS_flat`   the prover with the seed, written with labels: for copy j it queries the oracle
                     at (seed, leaf j, 0), (seed, leaf j, 1), .. and (if neither the program of a
                     `Node` nor that of a batch queries that oracle) nowhere else. It is the prover
                     `PS` of Compile/Batch/SeedStar.lean at the seed oracle `flatOf`
  `leavesL`, `CL`, `C_flat`   the committer, written with labels: the `Node` of the first encoding
                              under (anchor), Test under (test), for each k the `Node` of copy k
                              under (leaf k) and Link under (link k).
                              So no sample of one copy moves the label of another: the strings of
                              the `Node` of copy k (the randomness of its encoding, its salts, its
                              tree) are fixed by (i, seed, k) and the oracles.
                              (The numbers of its tokens are not: they count from the length of the
                              store on which the `Node` is made; `node_small` of
                              Compile/Batch/SeedReplay.lean says that nothing else depends on that
                              store.)
                              (`Node`: Compile/Batch/Star.lean; token, store: the head of
                              Compile/Batch/SeedParTree.lean.)

Limits. The implementation derives in two steps (a key for the purpose from the seed, coins from
that key) with a stream cipher; here it is one step through the random oracle. Inside a purpose the
order of the samples is Lean's. In C the token programs still run on one growing store, which fixes
only the numbers of the tokens in the record that `F.key` reads (`IskH`, Compile/Batch/Star.lean);
it fixes no string.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.SeedReplay

noncomputable section

open Rom Iop ZKCP

namespace Compile.Batch
namespace Seed

open Compile.Seed (Tosses Wt derive_bind)

/-- The purposes for which the committer uses coins. -/
inductive Purpose
  /-- the `Node` of the first encoding -/
  | anchor
  /-- the compiled Test on the first encoding -/
  | test
  /-- the `Node` of copy k -/
  | leaf (k : ℕ)
  /-- the compiled Link between the first encoding and copy k -/
  | link (k : ℕ)
  deriving DecidableEq

/-- An auxiliary oracle, used as a source of coins under labels: pt s q j is the query for the seed
s, the purpose q and the counter j. -/
structure LabelOracle (S : OSpec) where
  o : S.ι
  sd : ℕ
  pt : Fin (sd + 1) → Purpose → ℕ → S.Dom o
  inj : ∀ s q j s' q' j', pt s q j = pt s' q' j' → s = s' ∧ q = q' ∧ j = j'
  ψ : (n : ℕ) → S.Rng o → Fin (n + 1)

/-- the source of coins of one purpose -/
def LabelOracle.at {S : OSpec} (τ : LabelOracle S) (q : Purpose) : SeedOracle S where
  o := τ.o
  sd := τ.sd
  pt := fun s j => τ.pt s q j
  inj := fun _ _ _ _ h => ⟨(τ.inj _ _ _ _ _ _ h).1, (τ.inj _ _ _ _ _ _ h).2.2⟩
  ψ := τ.ψ

/-- The running counter of C, read as a label. cN, cT, cL: the numbers of samples of a `Node`, of
Test, of a run of Link. -/
def labelOf (cN cT cL n : ℕ) : Purpose × ℕ :=
  if n < cN then (.anchor, n)
  else if n < cN + cT then (.test, n - cN)
  else if (n - (cN + cT)) % (cN + cL) < cN then
    (.leaf ((n - (cN + cT)) / (cN + cL)), (n - (cN + cT)) % (cN + cL))
  else (.link ((n - (cN + cT)) / (cN + cL)), (n - (cN + cT)) % (cN + cL) - cN)

theorem labelOf_inj (cN cT cL : ℕ) : Function.Injective (labelOf cN cT cL) := by
  intro n n' h
  unfold labelOf at h
  have key : ∀ m m' : ℕ, m / (cN + cL) = m' / (cN + cL) →
      m % (cN + cL) = m' % (cN + cL) → m = m' := fun m m' h1 h2 => by
    rw [← Nat.div_add_mod m (cN + cL), ← Nat.div_add_mod m' (cN + cL), h1, h2]
  split_ifs at h with a1 a2 a3 b1 b2 b3 b1 b2 b3 b1 b2 b3 b1 b2 b3
    <;> simp only [Prod.mk.injEq, Purpose.leaf.injEq, Purpose.link.injEq, reduceCtorEq,
      false_and, true_and] at h
  · exact h
  · omega
  · have := key _ _ h.1 h.2
    omega
  · have := key _ _ h.1 (by omega)
    omega

theorem labelOf_anchor {cN cT cL t : ℕ} (h : t < cN) : labelOf cN cT cL (0 + t) = (.anchor, t) := by
  unfold labelOf
  rw [Nat.zero_add, if_pos h]

theorem labelOf_test {cN cT cL t : ℕ} (h : t < cT) : labelOf cN cT cL (cN + t) = (.test, t) := by
  unfold labelOf
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem labelOf_leaf {cN cT cL t : ℕ} (k : ℕ) (h : t < cN) :
    labelOf cN cT cL (cN + cT + k * (cN + cL) + t) = (.leaf k, t) := by
  have e : cN + cT + k * (cN + cL) + t - (cN + cT) = t + (cN + cL) * k := by
    rw [Nat.mul_comm]; omega
  have hm : (t + (cN + cL) * k) % (cN + cL) = t := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hd : (t + (cN + cL) * k) / (cN + cL) = k := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  unfold labelOf
  rw [if_neg (by omega), if_neg (by omega), e, hm, hd, if_pos h]

theorem labelOf_link {cN cT cL t : ℕ} (k : ℕ) (h : t < cL) :
    labelOf cN cT cL (cN + cT + k * (cN + cL) + cN + t) = (.link k, t) := by
  have e : cN + cT + k * (cN + cL) + cN + t - (cN + cT) = (cN + t) + (cN + cL) * k := by
    rw [Nat.mul_comm]; omega
  have hm : ((cN + t) + (cN + cL) * k) % (cN + cL) = cN + t := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hd : ((cN + t) + (cN + cL) * k) / (cN + cL) = k := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  unfold labelOf
  rw [if_neg (by omega), if_neg (by omega), e, hm, hd, if_neg (by omega)]
  congr 1
  omega

/-- The source of coins under the running counter of C: the query of the counter n is the query of
its label. -/
def LabelOracle.flat {S : OSpec} (τ : LabelOracle S) (cN cT cL : ℕ) : SeedOracle S where
  o := τ.o
  sd := τ.sd
  pt := fun s n => τ.pt s (labelOf cN cT cL n).1 (labelOf cN cT cL n).2
  inj := fun _ _ _ _ h =>
    ⟨(τ.inj _ _ _ _ _ _ h).1,
      labelOf_inj cN cT cL (Prod.ext (τ.inj _ _ _ _ _ _ h).2.1 (τ.inj _ _ _ _ _ _ h).2.2)⟩
  ψ := τ.ψ

/-- A stretch of the run that serves one purpose. If the counters base, .., base + width - 1 have
the labels (q, 0), .., (q, width - 1), an algorithm with exactly n samples on every path
(`Tosses n c`), t + n ≤ width, is derived alike under `τ.flat` from the counter base + t and under
`τ.at q` from t. -/
theorem derive_flat {S : OSpec} {α : Type} (τ : LabelOracle S) (cN cT cL : ℕ) (s : Fin (τ.sd + 1))
    (q : Purpose) (base width : ℕ) (hq : ∀ t < width, labelOf cN cT cL (base + t) = (q, t)) {n : ℕ}
    {c : OComp S α} (hc : Tosses n c) :
    ∀ t, t + n ≤ width → c.derive (τ.flat cN cT cL) s (base + t) = c.derive (τ.at q) s t := by
  induction hc with
  | pure a => intro t _; rfl
  | query o x _ ih =>
    intro t ht
    simp only [OComp.derive]
    exact congrArg _ (funext fun r => ih r t ht)
  | @sample n m k _ ih =>
    intro t ht
    simp only [OComp.derive]
    have e : (τ.flat cN cT cL).pt s (base + t) = (τ.at q).pt s t := by
      show τ.pt s (labelOf cN cT cL (base + t)).1 (labelOf cN cT cL (base + t)).2 = τ.pt s q t
      rw [hq t (by omega)]
    show OComp.query τ.o ((τ.flat cN cT cL).pt s (base + t)) _ = OComp.query τ.o ((τ.at q).pt s t) _
    rw [e]
    exact congrArg _ (funext fun d => ih _ (t + 1) (by omega))

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L} (WP : WireBP L) (p : Params)
  {IVK' Pf' : Type} (F : Face W IVK' Pf') (bk : CoinPlan) (τ : LabelOracle (spec lam W.K L))

/-- the source of coins under the running counter of the committer of Compile/Batch/Star.lean, its
samples made from small ones -/
def flatOf : SeedOracle (spec lam W.K L) :=
  τ.flat (cNode W WP p bk.m) (cProveB bk.m p.sMT p.sFS W.T WP.T 1)
    (cProveB bk.m p.sMT p.sFS W.Lk WP.Lk 1)

/-- The prover with the seed, written with labels: the `Node` of copy j is derived under the purpose
(leaf j), with a counter from 0. -/
def PSL (k : I × Fin (τ.sd + 1)) (b : List (X × Unit)) : TypedOracleComputation lam W.K L (Gen.Slots Pf' b) :=
  .sample p.M fun j =>
  (((erase (nodeP' W WP p k.1) []).blocks bk).derive (τ.at (.leaf j.val)) k.2 0).bind fun a =>
  (eraseR (F.bat k.1 j.val (some a.1) b) a.2).bind fun o => .pure o.1

/-- the `Node` of copy j, on any store: the two derivations agree -/
theorem derive_node (i : I) (s : Fin (τ.sd + 1)) (j : ℕ) (vs : List Bits) :
    ((erase (nodeP' W WP p i) vs).blocks bk).derive (flatOf WP p bk τ) s (off W WP p bk.m j) =
      ((erase (nodeP' W WP p i) vs).blocks bk).derive (τ.at (.leaf j)) s 0 :=
  derive_flat τ _ _ _ s (.leaf j) (off W WP p bk.m j) (cNode W WP p bk.m)
    (fun _ ht => labelOf_leaf j ht) ((wt_nodeP' W WP p bk.m i vs).tosses_blocks bk) 0 (by omega)

/-- `PSL` is the prover `PS` of Compile/Batch/SeedStar.lean at the seed oracle `flatOf`. -/
theorem PS_flat : PS WP p F bk (flatOf WP p bk τ) = PSL WP p F bk τ := by
  funext k b
  unfold PS PSL
  refine congrArg _ (funext fun j => ?_)
  rw [derive_node]

/-! ## The committer, written with labels -/

theorem derive_anchor (i : I) (s : Fin (τ.sd + 1)) (vs : List Bits) :
    ((erase (nodeP' W WP p i) vs).blocks bk).derive (flatOf WP p bk τ) s 0 =
      ((erase (nodeP' W WP p i) vs).blocks bk).derive (τ.at .anchor) s 0 :=
  derive_flat τ _ _ _ s .anchor 0 (cNode W WP p bk.m) (fun _ ht => labelOf_anchor ht)
    ((wt_nodeP' W WP p bk.m i vs).tosses_blocks bk) 0 (by omega)

theorem derive_test (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) (s : Fin (τ.sd + 1)) (vs : List Bits) :
    ((eraseR (proveT W WP p tree i r) vs).blocks bk).derive
        (flatOf WP p bk τ) s (0 + cNode W WP p bk.m) =
      ((eraseR (proveT W WP p tree i r) vs).blocks bk).derive (τ.at .test) s 0 := by
  rw [Nat.zero_add]
  exact derive_flat τ _ _ _ s .test (cNode W WP p bk.m) (cProveB bk.m p.sMT p.sFS W.T WP.T 1)
    (fun _ ht => labelOf_test ht)
    ((wt_eraseR (wt_proveT W WP p bk.m tree i r vs)).tosses_blocks bk) 0 (by omega)

theorem derive_link (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) (s : Fin (τ.sd + 1))
    (k : ℕ) (vs : List Bits) :
    ((eraseR (proveLk W WP p root tree i r₀ r) vs).blocks bk).derive
        (flatOf WP p bk τ) s (off W WP p bk.m k + cNode W WP p bk.m) =
      ((eraseR (proveLk W WP p root tree i r₀ r) vs).blocks bk).derive (τ.at (.link k)) s 0 :=
  derive_flat τ _ _ _ s (.link k) (off W WP p bk.m k + cNode W WP p bk.m)
    (cProveB bk.m p.sMT p.sFS W.Lk WP.Lk 1) (fun _ ht => labelOf_link k ht)
    ((wt_eraseR (wt_proveLk W WP p bk.m root tree i r₀ r vs)).tosses_blocks bk) 0 (by omega)

/-- the copies k, .., k + n - 1 of the committer: the `Node` of each under its own purpose, and
likewise its run of Link; vs is the store -/
def leavesL (i : I) (s : Fin (τ.sd + 1)) (root : Node lam L) :
    ℕ → ℕ → List Bits → TypedOracleComputation lam W.K L (List (LeafRec lam L) × List Bits)
  | 0, _, vs => .pure ([], vs)
  | n + 1, k, vs =>
      (((erase (nodeP' W WP p i) vs).blocks bk).derive (τ.at (.leaf k)) s 0).bind fun a =>
      (((eraseR (proveLk W WP p root.tree a.1.tree i root.r a.1.r) a.2).blocks bk).derive
          (τ.at (.link k)) s 0).bind fun c =>
      (leavesL i s root n (k + 1) c.2).bind fun r =>
        .pure ((⟨a.1, c.1⟩ : LeafRec lam L) :: r.1, r.2)

theorem derive_leavesC (i : I) (s : Fin (τ.sd + 1)) (root : Node lam L) :
    ∀ (n k : ℕ) (vs : List Bits),
      ((eraseR (leavesC W WP p i root n) vs).blocks bk).derive
          (flatOf WP p bk τ) s (off W WP p bk.m k) =
        leavesL WP p bk τ i s root n k vs
  | 0, _, _ => rfl
  | n + 1, k, vs => by
      rw [erase_leavesC_succ, OComp.blocks_bind,
        derive_bind (flatOf WP p bk τ) s ((wt_nodeP' W WP p bk.m i vs).tosses_blocks bk),
        derive_node]
      refine congrArg _ (funext fun a => ?_)
      rw [OComp.blocks_bind,
        derive_bind (flatOf WP p bk τ) s
          ((wt_eraseR
            (wt_proveLk W WP p bk.m root.tree a.1.tree i root.r a.1.r a.2)).tosses_blocks bk),
        derive_link]
      refine congrArg _ (funext fun c => ?_)
      have e : off W WP p bk.m k + cNode W WP p bk.m + cProveB bk.m p.sMT p.sFS W.Lk WP.Lk 1 =
          off W WP p bk.m (k + 1) := by
        unfold off cLeaf
        rw [Nat.succ_mul]
        omega
      rw [OComp.blocks_bind,
        derive_bind (flatOf WP p bk τ) s
          ((wt_eraseR (wt_leavesC W WP p bk.m i root n c.2)).tosses_blocks bk),
        e, derive_leavesC i s root n (k + 1) c.2]
      rfl

/-- The committer with the seed, written with labels. -/
def CL (i : I) : TypedOracleComputation lam W.K L (IVK' × (I × Fin (τ.sd + 1))) :=
  .sample τ.sd fun s =>
  (((erase (nodeP' W WP p i) []).blocks bk).derive (τ.at .anchor) s 0).bind fun a =>
  (((eraseR (proveT W WP p a.1.tree i a.1.r) a.2).blocks bk).derive (τ.at .test) s 0).bind fun b =>
  (leavesL WP p bk τ i s a.1 (p.M + 1) 0 b.2).bind fun c =>
    .pure (F.key ⟨a.1.tree.root, b.1⟩ ⟨i, a.1, c.1⟩, (i, s))

/-- `CL` is the committer of `argSeed` (Compile/Batch/SeedStar.lean) at the seed oracle `flatOf`. -/
theorem C_flat : (argSeed WP p F bk (flatOf WP p bk τ)).C = CL WP p F bk τ := by
  funext i
  show OComp.sample τ.sd (fun s =>
      ((Cb WP p F bk i).derive (flatOf WP p bk τ) s 0).bind fun out => OComp.pure (out.1, (i, s))) =
    _
  unfold CL
  refine congrArg _ (funext fun s => ?_)
  unfold Cb
  rw [argOf_C, OComp.blocks_bind,
    derive_bind (flatOf WP p bk τ) s ((wt_nodeP' W WP p bk.m i []).tosses_blocks bk),
    derive_anchor, OComp.bind_assoc]
  refine congrArg _ (funext fun a => ?_)
  rw [OComp.blocks_bind,
    derive_bind (flatOf WP p bk τ) s
      ((wt_eraseR (wt_proveT W WP p bk.m a.1.tree i a.1.r a.2)).tosses_blocks bk),
    derive_test, OComp.bind_assoc]
  refine congrArg _ (funext fun b => ?_)
  have e : 0 + cNode W WP p bk.m + cProveB bk.m p.sMT p.sFS W.T WP.T 1 = off W WP p bk.m 0 := by
    unfold off
    omega
  rw [OComp.blocks_bind,
    derive_bind (flatOf WP p bk τ) s
      ((wt_eraseR (wt_leavesC W WP p bk.m i a.1 (p.M + 1) b.2)).tosses_blocks bk),
    e, derive_leavesC, OComp.bind_assoc]
  rfl

end Seed
end Compile.Batch
