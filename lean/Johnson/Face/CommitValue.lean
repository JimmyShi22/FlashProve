-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/CommitValue.lean: the value of the compiled committer's commitment.

 1. The scheme frontArgK (Johnson/FrontRoad/FrontK.lean), where what is published is the commitment
    alone, is run at a number n in the place of its coins.
 2. At every hash function its commitment is that of the committer of the first table alone
    (LayoutsByPublicReading.commitAtCoins, Johnson/Top/ToldCommitPlain.lean), at the encoding randomness and the
    salts that the first two digits of n name in the honest side's two enumerations.
 3. The honest side is read at the value that the public reading has at that hash function.
 4. So the commitment hangs on no prover, no search for a nonce, no copy and no further coin.
 5. An equation between values. Nothing on the committer's queries, on binding or on hiding.
General in the input, the family, the honest sides and the map from weights to indices.
-/
import Johnson.FrontRoad.FrontK
import Johnson.FrontRoad.CoinsEnough
import Johnson.WholeKey.Complete
import Johnson.Top.ToldCommitPlain
import Johnson.Top.ParsedReader
import Rom.WithCoins
import ZKCP.WithCoinsBind
import Run.DetOverOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Face
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt OnBytes.FrontRoad VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop (HolographicProtocol RoundSplits Dig)

/-! ## 1. Whatever the coins -/

section Ever
variable {S : OSpec} {α β : Type}

/-- Under the oracle functions g, whatever is sampled, the result meets P. -/
def Ever (g : Fam S) (P : α → Prop) : Rom.OComp S α → Prop
  | .pure a => P a
  | .query o q k => Ever g P (k (g o q))
  | .sample _ k => ∀ r, Ever g P (k r)

/-- So it does at every number in the place of the coins. -/
theorem Ever.withCoins {g : Fam S} {P : α → Prop} :
    ∀ (c : Rom.OComp S α) (n : ℕ), Ever g P c → P ((c.withCoins n).det g)
  | .pure _, _, h => h
  | .query o q k, n, h => Ever.withCoins (k (g o q)) n h
  | .sample _ k, _, h => Ever.withCoins (k _) _ (h _)

/-- An algorithm that samples nothing has one result. -/
theorem ever_of_noCoin {g : Fam S} {P : α → Prop} :
    ∀ c : Rom.OComp S α, c.NoCoin → P (c.det g) → Ever g P c
  | .pure _, _, h => h
  | .query o q k, hc, h => ever_of_noCoin (k (g o q)) (hc _) h
  | .sample _ _, hc, _ => hc.elim

theorem Ever.bind {g : Fam S} {Q : α → Prop} {P : β → Prop} {k : α → Rom.OComp S β} :
    ∀ c : Rom.OComp S α, Ever g Q c → (∀ a, Q a → Ever g P (k a)) → Ever g P (c.bind k)
  | .pure a, h, hk => hk a h
  | .query o q f, h, hk => Ever.bind (f (g o q)) h hk
  | .sample _ f, h, hk => fun r => Ever.bind (f r) (h r) hk

theorem ever_true {g : Fam S} : ∀ c : Rom.OComp S α, Ever g (fun _ => True) c
  | .pure _ => trivial
  | .query o q k => ever_true (k (g o q))
  | .sample _ k => fun r => ever_true (k r)

end Ever

/-! ## 2. Over the typed oracles -/

section Typed
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL)
  (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- **THE ONE JOINT: of the whole key, (root, out-of-domain sample) is the first table's.** -/
theorem lowKey_commitAt (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL) :
    lowKey ((commitAt W S cA h i c).det g).1 =
      ((committerAtFixedCoins W S h.b₀ i c.r (cutS (2 ^ W.depth) c.s)).det g).1 := by
  rw [det_commitAt, det_committerAtFixedCoins]
  rfl

/-- The committer's coins behind the first two. -/
def laterCoins (a : Fin (h.ri.n + 1)) (b : Fin (h.sl.n + 1)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (DrawC lam L Bd aT aL h.KT h.KL) :=
  .sample h.kT.n fun c => .sample h.coT.n fun e =>
    (coinsCopies W h (h.M + 1)).bind fun ds =>
      .pure ⟨h.ri.e a, h.sl.e b, h.kT.e c, h.coT.e e, ds⟩

theorem commitW_withCoins (i : I) (n : ℕ) :
    (commitW W S cA h i).withCoins n =
      ((laterCoins W h ⟨n % (h.ri.n + 1), Nat.mod_lt _ h.ri.n.succ_pos⟩
        ⟨n / (h.ri.n + 1) % (h.sl.n + 1), Nat.mod_lt _ h.sl.n.succ_pos⟩).bind
          (commitAt W S cA h i)).withCoins (n / (h.ri.n + 1) / (h.sl.n + 1)) := rfl

theorem ever_laterCoins (a : Fin (h.ri.n + 1)) (b : Fin (h.sl.n + 1)) :
    Ever g (fun d => d.r = h.ri.e a ∧ d.s = h.sl.e b) (laterCoins W h a b) :=
  fun _ _ => Ever.bind (Q := fun _ => True) (coinsCopies W h (h.M + 1)) (ever_true _)
    fun _ _ => ⟨rfl, rfl⟩

/-- The committer at a number: (root, out-of-domain sample) is the first table's at the first two
digits. -/
theorem lowKey_commitW (i : I) (n : ℕ) :
    lowKey (((commitW W S cA h i).withCoins n).det g).1 =
      ((committerAtFixedCoins W S h.b₀ i (h.ri.e ⟨n % (h.ri.n + 1), Nat.mod_lt _ h.ri.n.succ_pos⟩)
        (cutS (2 ^ W.depth)
          (h.sl.e ⟨n / (h.ri.n + 1) % (h.sl.n + 1), Nat.mod_lt _ h.sl.n.succ_pos⟩))).det g).1 := by
  rw [commitW_withCoins]
  refine Ever.withCoins (g := g)
    (P := fun o : FullKey lam L aT aL × Isk lam L Bd aT aL => lowKey o.1 =
      ((committerAtFixedCoins W S h.b₀ i (h.ri.e ⟨n % (h.ri.n + 1), Nat.mod_lt _ h.ri.n.succ_pos⟩)
        (cutS (2 ^ W.depth)
          (h.sl.e ⟨n / (h.ri.n + 1) % (h.sl.n + 1), Nat.mod_lt _ h.sl.n.succ_pos⟩))).det g).1)
    _ _ ?_
  refine Ever.bind _ (ever_laterCoins W h g _ _) fun d hd => ?_
  refine ever_of_noCoin _ (noCoin_commitAt W S cA h i d) ?_
  show lowKey ((commitAt W S cA h i d).det g).1 = _
  rw [lowKey_commitAt, hd.1, hd.2]

end Typed

/-! ## 3. Over one hash function -/

/-- The first table's encoding randomness at the number n: the first digit. -/
def firstRandomness {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (h : HonestSide 256 L Bd aT aL) (n : ℕ) : L.EncodingRandomness :=
  h.ri.e ⟨n % (h.ri.n + 1), Nat.mod_lt _ h.ri.n.succ_pos⟩

/-- The first table's salts at the number n, as they are handed on: the second digit. -/
def firstSalts {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (h : HonestSide 256 L Bd aT aL) (leaves n : ℕ) : ℕ → Bits :=
  cutS leaves (h.sl.e ⟨n / (h.ri.n + 1) % (h.sl.n + 1), Nat.mod_lt _ h.sl.n.succ_pos⟩)

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  {J P' : Type} (idx : J → R.Index) (x₀ : R.Instance)

theorem readTold_C (i : R.Index) :
    (readTold T h).C i = T.Pub.bind fun d =>
      ((((commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i).overOne (T.m d)).bind fun k =>
        Rom.OComp.pure ((T.part d, k.1), k.2)).bind fun k => Rom.OComp.pure (k.1, (d, k.2))) := rfl

/-- The key of the scheme behind the public reading, at a number. -/
theorem det_readTold (noCoin : T.Pub.NoCoin) (i : R.Index) (n : ℕ) (g : Fam (rom 256)) :
    ((((readTold T h).C i).withCoins n).det g).1 =
      (T.part (T.Pub.det g),
        (((commitW R.queryLayout (T.Sd (T.Pub.det g)) (T.cA (T.Pub.det g)) (h (T.Pub.det g)) i).withCoins
          n).det (readBlocks (T.m (T.Pub.det g)) g)).1) := by
  rw [readTold_C, OComp.withCoins_bind_of_noCoin _ _ _ noCoin, OComp.det_bind,
    OComp.withCoins_bind_pure, OComp.det_bind, OComp.withCoins_bind_pure, OComp.det_bind,
    withCoins_overOne, det_overOne]
  rfl

theorem det_mapO {α γ : Type} (F : α → γ) (c : ZKCP.OComp 256 α) (f : ZKCP.Oracle 256) :
    (c.mapO F).det f = F (c.det f) := ZKCP.OComp.det_bind f c _

/-- The digest of a key, then a function of it. -/
theorem det_keyDigest_mapO {IVK γ : Type} (enc : IVK → Option ZKCP.Str) (key : IVK)
    (F : ZKCP.Digest 256 → γ) (f : ZKCP.Oracle 256) :
    ((ZKCP.keyDigest enc key).mapO F).det f = F (ZKCP.digestUnder f enc key) := by
  unfold ZKCP.keyDigest ZKCP.digestUnder
  cases enc key <;> rfl

/-- **THE VALUE OF THE COMPILED COMMITTER's COMMITMENT.** -/
theorem evaluate_commit_frontArgK (noCoin : T.Pub.NoCoin)
    (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')
    (Vf : ZKCP.Digest 256 → List Token × List Token → P' → ZKCP.OComp 256 Bool) (w : J) (n : ℕ)
    (f : Hash) :
    (deterministicOf ((((frontArgK T h idx x₀ (fun id _ => id) ϖ Vf).C w).withCoins n).mapO
        Prod.fst)).evaluate f =
      (T.commitAtCoins (h (T.Pub.det (_root_.Run.famOne f))).b₀ (idx w)
        (firstRandomness (h (T.Pub.det (_root_.Run.famOne f))) n)
        (firstSalts (h (T.Pub.det (_root_.Run.famOne f))) (2 ^ R.queryLayout.depth) n)).evaluate f := by
  have eC : (frontArgK T h idx x₀ (fun id _ => id) ϖ Vf).C w =
      (ofRom ((readTold T h).C (idx w))).bind fun keys =>
        (ZKCP.keyDigest (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1).mapO fun dg =>
          (dg, (keys.1.2, keys.2)) := rfl
  rw [OnBytes.Maker.ParsedRead.evaluate_deterministicOf_det, eC,
    ZKCP.OComp.withCoins_bind_of_drawsNoCoin _
      (fun keys => ZKCP.OComp.DrawsNoCoin.mapO _ _ (drawsNoCoin_keyDigest _ _)),
    withCoins_ofRom]
  rw [det_mapO, ZKCP.OComp.det_bind, _root_.Run.det_ofRom, det_keyDigest_mapO,
    evaluate_commitAtCoins]
  unfold LayoutsByPublicReading.keyAtCoins
  rw [OComp.det_bind, OComp.det_bind, det_overOne]
  show ZKCP.digestUnder f T.encT
      (((((readTold T h).C (idx w)).withCoins n).det (_root_.Run.famOne f)).1.1,
        lowKey ((((readTold T h).C (idx w)).withCoins n).det (_root_.Run.famOne f)).1.2) = _
  rw [det_readTold T h noCoin]
  show ZKCP.digestUnder f T.encT (_, lowKey _) = _
  rw [lowKey_commitW]
  rfl

end Johnson.Face

#print axioms Johnson.Face.lowKey_commitAt
#print axioms Johnson.Face.lowKey_commitW
#print axioms Johnson.Face.det_readTold
#print axioms Johnson.Face.evaluate_commit_frontArgK
