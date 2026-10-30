-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/CommitValueOneHashByFirstBlockTest.lean: the value of the committer's (root, out-of-domain sample)
where the step to one hash function is the third exit (OComp.overOneF, Rom/OverOneF.lean): of each
answer the first hash block is asked, and the others only if a test on the first block says so.

 1. Of the whole key that the committer commitW makes at a number n, by the third exit, at every
    hash function: (root, out-of-domain sample) is that of the first table alone (committerAtFixedCoins) at the
    first two digits of n, read at the typed oracles that the hash function spells.
 2. One premise: the program of ONE TABLE (tabO: its tree, its seed's two queries), at every encoding
    randomness and all salts, reads each answer only as far as the third exit asks it
    (FactorsBy (AgreeF m more)).
 3. Of the offline run, the link runs and their searches for a nonce nothing is asked: whatever they
    do, the first table's root and sample stand in the key.
 4. At a test that is made of a letter pass (moreP pass), the premise holds where the seed's two
    queries are asked whole (PassFits.seed0, seed1) and the coding's first block of a Fiat-Shamir
    answer is the answer's block 0 (FirstIs). Both hold at the description's own family, at the test
    made of the wires' own work bits: so evaluate_commit_frontArgKF_atFiles (CommitValueF.lean of this
    folder) has no premise.
 5. A remark, no theorem: where the premise fails, blocks that were not asked stand as zeros in the
    seed, and the equation need not hold.
An equation between values. Nothing on the committer's queries, on binding or on hiding.
The scheme that takes its committer by the third exit is committerAndProverOverOneHash (Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTestFront.lean),
which compile calls: CommitValueF.lean brings this lemma to it.
-/
import Johnson.Face.CommitValue
import Johnson.Prover.All.CountF
import Johnson.Prover.Law.FirstBlockLaws
import Run.OverOneFRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Face
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop (HolographicProtocol RoundSplits Dig)

/-! ## 1. Whatever the answers and the coins -/

section Always
variable {S : OSpec} {lam : ℕ} {α β : Type}

/-- Whatever the oracles answer and whatever is sampled, the result meets P. -/
def Always (P : α → Prop) : Rom.OComp S α → Prop
  | .pure a => P a
  | .query _ _ k => ∀ r, Always P (k r)
  | .sample _ k => ∀ r, Always P (k r)

theorem always_true : ∀ c : Rom.OComp S α, Always (fun _ => True) c
  | .pure _ => trivial
  | .query _ _ k => fun r => always_true (k r)
  | .sample _ k => fun r => always_true (k r)

theorem Always.bind {Q : α → Prop} {P : β → Prop} {k : α → Rom.OComp S β} :
    ∀ c : Rom.OComp S α, Always Q c → (∀ a, Q a → Always P (k a)) → Always P (c.bind k)
  | .pure a, h, hk => hk a h
  | .query _ _ f, h, hk => fun r => Always.bind (f r) (h r) hk
  | .sample _ f, h, hk => fun r => Always.bind (f r) (h r) hk

theorem Always.ever {P : α → Prop} (g : Fam S) : ∀ c : Rom.OComp S α, Always P c → Ever g P c
  | .pure _, h => h
  | .query o q k, h => Always.ever g (k (g o q)) (h _)
  | .sample _ k, h => fun r => Always.ever g (k r) (h r)

theorem Always.det {P : α → Prop} (g : Fam S) : ∀ c : Rom.OComp S α, Always P c → P (c.det g)
  | .pure _, h => h
  | .query o q k, h => Always.det g (k (g o q)) (h _)
  | .sample _ k, h => Always.det g (k 0) (h 0)

/-- The third exit keeps it. -/
theorem Always.overOneF {P : α → Prop} (m : OracleCoding S lam) (more : More S lam) :
    ∀ c : Rom.OComp S α, Always P c → Always P (c.overOneF m more)
  | .pure _, h => h
  | .sample _ k, h => fun r => Always.overOneF m more (k r) (h r)
  | .query o q k, h =>
    Always.bind (Q := fun _ => True) (askFirst lam (m.blocks o) (more o q) (m.code o q))
      (always_true _) fun bs _ => Always.overOneF m more (k ((m.rng o).symm bs)) (h _)

end Always

/-! ## 2. The committer by the third exit -/

section Typed
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL)
  (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
  (more : More (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (g : Fam (rom lam))

/-- What the committer does behind its first table. -/
def behindFirstTable (i : I) (d : DrawC lam L Bd aT aL h.KT h.KL) (t₁ : TabK lam L Bd aT aL) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (FullKey lam L aT aL × Isk lam L Bd aT aL) :=
  (tabsO W S h i d.copies).bind fun ts =>
    (proveTA W cA (fun _ => t₁.tree) (h.dressT (h.rvT d.κ) d.co) h.capT
      t₁.tree.root (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
      (h.st.T i t₁.r t₁.seed d.κ)).bind fun a =>
    (linksO W cA h i t₁ (d.copies.zip ts)).bind fun ls =>
    .pure (⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, shown (h.st.stopT i t₁.r t₁.seed) a, ls⟩,
      ⟨i, ts⟩)

theorem commitAt_eq (i : I) (d : DrawC lam L Bd aT aL h.KT h.KL) :
    commitAt W S cA h i d =
      (tabO W S h.b₀ i d.r (cutS (2 ^ W.depth) d.s)).bind (behindFirstTable W S cA h i d) := rfl

/-- Whatever is answered behind the first table, its root and sample stand in the key. -/
theorem always_behindFirstTable (i : I) (d : DrawC lam L Bd aT aL h.KT h.KL)
    (t₁ : TabK lam L Bd aT aL) :
    Always (fun o : FullKey lam L aT aL × Isk lam L Bd aT aL =>
      lowKey o.1 = ⟨t₁.tree.root, L.recOf i t₁.r t₁.seed⟩) (behindFirstTable W S cA h i d t₁) :=
  Always.bind (Q := fun _ => True) _ (always_true _) fun _ _ =>
    Always.bind (Q := fun _ => True) _ (always_true _) fun _ _ =>
      Always.bind (Q := fun _ => True) _ (always_true _) fun _ _ => rfl

/-- **THE JOINT AT THE THIRD EXIT**, behind the coins. -/
theorem lowKey_commitAt_thirdExit (i : I) (d : DrawC lam L Bd aT aL h.KT h.KL)
    (factors : (tabO W S h.b₀ i d.r (cutS (2 ^ W.depth) d.s)).FactorsBy (AgreeF m more)) :
    lowKey (((commitAt W S cA h i d).overOneF m more).det g).1 =
      ((committerAtFixedCoins W S h.b₀ i d.r (cutS (2 ^ W.depth) d.s)).det (readBlocks m g)).1 := by
  rw [commitAt_eq, overOneF_bind, OComp.det_bind, det_overOneF m more g _ factors,
    Always.det g _ (Always.overOneF m more _ (always_behindFirstTable W S cA h i d _)),
    det_tabO, det_committerAtFixedCoins]
  rfl

theorem always_laterCoins (a : Fin (h.ri.n + 1)) (b : Fin (h.sl.n + 1)) :
    Always (fun d => d.r = h.ri.e a ∧ d.s = h.sl.e b) (laterCoins W h a b) :=
  fun _ _ => Always.bind (Q := fun _ => True) (coinsCopies W h (h.M + 1)) (always_true _)
    fun _ _ => ⟨rfl, rfl⟩

theorem commitW_thirdExit_withCoins (i : I) (n : ℕ) :
    ((commitW W S cA h i).overOneF m more).withCoins n =
      (((laterCoins W h ⟨n % (h.ri.n + 1), Nat.mod_lt _ h.ri.n.succ_pos⟩
        ⟨n / (h.ri.n + 1) % (h.sl.n + 1), Nat.mod_lt _ h.sl.n.succ_pos⟩).bind
          (commitAt W S cA h i)).overOneF m more).withCoins (n / (h.ri.n + 1) / (h.sl.n + 1)) :=
  rfl

/-- **The committer by the third exit, at a number**: (root, out-of-domain sample) is the first
table's at the first two digits. -/
theorem lowKey_commitW_thirdExit (i : I) (n : ℕ)
    (factors : ∀ r s, (tabO W S h.b₀ i r (cutS (2 ^ W.depth) s)).FactorsBy (AgreeF m more)) :
    lowKey ((((commitW W S cA h i).overOneF m more).withCoins n).det g).1 =
      ((committerAtFixedCoins W S h.b₀ i (h.ri.e ⟨n % (h.ri.n + 1), Nat.mod_lt _ h.ri.n.succ_pos⟩)
        (cutS (2 ^ W.depth)
          (h.sl.e ⟨n / (h.ri.n + 1) % (h.sl.n + 1), Nat.mod_lt _ h.sl.n.succ_pos⟩))).det
            (readBlocks m g)).1 := by
  rw [commitW_thirdExit_withCoins, overOneF_bind]
  refine Ever.withCoins (g := g)
    (P := fun o : FullKey lam L aT aL × Isk lam L Bd aT aL => lowKey o.1 =
      ((committerAtFixedCoins W S h.b₀ i (h.ri.e ⟨n % (h.ri.n + 1), Nat.mod_lt _ h.ri.n.succ_pos⟩)
        (cutS (2 ^ W.depth)
          (h.sl.e ⟨n / (h.ri.n + 1) % (h.sl.n + 1), Nat.mod_lt _ h.sl.n.succ_pos⟩))).det
            (readBlocks m g)).1)
    _ _ ?_
  refine Ever.bind _ (Always.ever g _ (Always.overOneF m more _ (always_laterCoins W h _ _)))
    fun d hd => ?_
  refine ever_of_noCoin _ (noCoin_overOneF m more _ (noCoin_commitAt W S cA h i d)) ?_
  show lowKey (((commitAt W S cA h i d).overOneF m more).det g).1 = _
  rw [lowKey_commitAt_thirdExit W S cA h m more g i d (factors d.r d.s), hd.1, hd.2]

/-- One table's program factors, at a test made of a letter pass under which the seed's two queries
are asked whole. -/
theorem factors_tabO {hK : 0 < W.K} {pass : Pass lam (typedOracleCarrier L Bd aT aL)}
    (fits : PassFits W S hK pass) (first : FirstIs hK m) (b₀ : Bd) (i : I) (r : L.EncodingRandomness)
    (s : ℕ → Bits) : (tabO W S b₀ i r s).FactorsBy (AgreeF m (moreP pass)) :=
  factorsF_of hK pass m first
    (OComp.FactorsBy.bind (factors_committerTreeKeptByProver b₀ hK pass _ _) fun _ =>
      OComp.FactorsBy.bind (factors_seedsO fits _) fun _ => trivial)

/-- The same at such a test. -/
theorem lowKey_commitW_thirdExit_pass {hK : 0 < W.K} {pass : Pass lam (typedOracleCarrier L Bd aT aL)}
    (fits : PassFits W S hK pass) (first : FirstIs hK m) (i : I) (n : ℕ) :
    lowKey ((((commitW W S cA h i).overOneF m (moreP pass)).withCoins n).det g).1 =
      ((committerAtFixedCoins W S h.b₀ i (h.ri.e ⟨n % (h.ri.n + 1), Nat.mod_lt _ h.ri.n.succ_pos⟩)
        (cutS (2 ^ W.depth)
          (h.sl.e ⟨n / (h.ri.n + 1) % (h.sl.n + 1), Nat.mod_lt _ h.sl.n.succ_pos⟩))).det
            (readBlocks m g)).1 :=
  lowKey_commitW_thirdExit W S cA h m (moreP pass) g i n fun r _ =>
    factors_tabO W S m fits first h.b₀ i r _

end Typed

end Johnson.Face

#print axioms Johnson.Face.lowKey_commitAt_thirdExit
#print axioms Johnson.Face.lowKey_commitW_thirdExit
#print axioms Johnson.Face.factors_tabO
#print axioms Johnson.Face.lowKey_commitW_thirdExit_pass
