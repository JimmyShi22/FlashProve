-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/Sess.lean: THE TOKEN SIDE's PROVER OF ONE SHOWN REQUEST HAS THE RUN OF THE
SCHEME's PROVER, under every rule for answering queries. From Spec.sameRun
(Johnson/TokenSide/SpecSame.lean), which is a hypothesis here (it is proved in
Johnson/TokenSide/TieRun.lean), and the premises TokFit.

Lemmas of one step of a proof. This file states no goal of the release. The token programs are a
device of that step and stand in no statement on the scheme.

  TokFit W h tl   THE TOKEN SIDE's LETTERS FIT THE HONEST SIDE's: the lengths, starts and fixed
                  values of tl are those of which the laws on the honest side's lists of coins speak
                  (SaltsLaw, RunLaw, Johnson/WholeKey/CoinLaws.lean); the honest side's window holds
                  all trees of the three wires; the three wires are in order as far as places go. It
                  can be met wherever the premises of the statement of index privacy can
                  (tokFit_tokAt, Johnson/TokenSide2/AtPrem.lean).
  same_proveAt    the prover behind the coins that both sides draw from lists.
  same_sess       THE PROVER of one request that is shown.

The prover's key of the scheme is read off the key with tokens and the store. All that is asked of
key and store: the tokens of the salts in the key's trees are numbers of strings of the store.

-/
import Johnson.TokenSide2.Units

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- **The token side's letters fit the honest side's.** -/
structure TokFit (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (h : HonestSide lam L Bd aT aL)
    (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB) : Prop where
  sl : SaltsLaw h.sl (2 ^ W.depth) tl.preE tl.frE
  coT : RunLaw h.coT h.nR h.nK h.nJ tl.T.sFS tl.T.fr tl.T.rs tl.T.dq tl.T.pad tl.T.slot
  coL : RunLaw h.coL h.nR h.nK h.nJ tl.Lk.sFS tl.Lk.fr tl.Lk.rs tl.Lk.dq tl.Lk.pad tl.Lk.slot
  coB : RunLaw h.coB h.nR h.nK h.nJ tl.B.sFS tl.B.fr tl.B.rs tl.B.dq tl.B.pad tl.B.slot
  rsT : tl.T.rsw = h.rtail tl.T.slot
  rsL : tl.Lk.rsw = h.rtail tl.Lk.slot
  rsB : tl.B.rsw = h.rtail tl.B.slot
  stT : ∀ κ, tl.stT κ = h.startT (h.rvT κ)
  stL : ∀ κ, tl.stL κ = h.startL (h.rvL κ)
  stB : ∀ κ, tl.stB κ = h.startB (h.rvB κ)
  okT : (wTC W).OKG
  okL : (wLC W).OKG
  okB : (wBC W).OKG
  fitT : FitsWin h.nR h.nK h.nJ L.offline.shape aT (wTC W).sh 0
  fitL : FitsWin h.nR h.nK h.nJ L.link.shape aL (wLC W).sh 0
  fitB : FitsWin h.nR h.nK h.nJ L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh 0

variable {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {cA : L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
  {h : HonestSide lam L Bd aT aL} {tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB}

/-! ## The two texts, case by case -/

theorem proveAtT_none {k : IskT lam L Bd aT aL} (x : X) {j : ℕ} (κ : h.KB)
    (e : k.copies[j]? = none) :
    proveAtT W cA r₀ h tl k x ⟨j, κ⟩ = .pure ⟨j, h.nm j, none⟩ := by
  unfold proveAtT
  simp only [e]

theorem proveAtT_some {k : IskT lam L Bd aT aL} (x : X) {j : ℕ} (κ : h.KB)
    {t : TabT lam L Bd aT aL} (e : k.copies[j]? = some t) :
    proveAtT W cA r₀ h tl k x ⟨j, κ⟩ =
      (proveC Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀)
        (cmsBA cA t.tree.root (L.recOf k.i t.r t.seed).2) (x, L.recOf k.i t.r t.seed)
        (L.encodeIndex k.i t.r) (fun _ => t.tree) tl.preE (h.st.B k.i t.r t.seed x (h.nm j) κ) tl.B
        (tl.stB κ) h.capB (h.st.stopB k.i t.r t.seed x (h.nm j))).bind fun c =>
      .pure ⟨j, h.nm j, c⟩ := by
  unfold proveAtT
  simp only [e]

theorem proveAt_none {k : Isk lam L Bd aT aL} (x : X) {j : ℕ} (κ : h.KB)
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) (e : k.copies[j]? = none) :
    proveAt W cA r₀ h k x ⟨j, κ, co⟩ = .pure ⟨j, h.nm j, none⟩ := by
  unfold proveAt
  simp only [e]

theorem proveAt_some {k : Isk lam L Bd aT aL} (x : X) {j : ℕ} (κ : h.KB)
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) {t : TabK lam L Bd aT aL} (e : k.copies[j]? = some t) :
    proveAt W cA r₀ h k x ⟨j, κ, co⟩ =
      (proveBA W cA r₀ (fun _ => t.tree) (h.dressB (h.rvB κ) co) h.capB t.tree.root x
        (L.recOf k.i t.r t.seed) (L.encodeIndex k.i t.r) (h.st.B k.i t.r t.seed x (h.nm j) κ)).bind fun c =>
      .pure ⟨j, h.nm j, shown (h.st.stopB k.i t.r t.seed x (h.nm j)) c⟩ := by
  unfold proveAt
  simp only [e]

/-! ## The prover -/

/-- The prover behind the coins that both sides draw from lists. -/
theorem same_proveAt (hR : Spec.sameRun) (hf : TokFit W h tl) (k : IskT lam L Bd aT aL)
    (vs : List Bits) (hk : ∀ t ∈ k.copies, ∀ a ∈ t.tree.tok, a.1 < vs.length) (x : X) (j : ℕ)
    (κ : h.KB) :
    Same (fun p : RequestProof lam L × List Bits => p.1) (fun p => vs <+: p.2)
      (plainOf (proveAtT W cA r₀ h tl k x ⟨j, κ⟩) vs)
      (.sample h.coB.n fun e => proveAt W cA r₀ h
        ⟨k.i, k.copies.map (TabT.toK (fun u => vs.getD u []) tl.preE)⟩ x ⟨j, κ, h.coB.e e⟩) := by
  cases e : k.copies[j]? with
  | none =>
      have e' : (k.copies.map (TabT.toK (fun u => vs.getD u []) tl.preE))[j]? = none := by
        rw [List.getElem?_map, e]
        rfl
      rw [proveAtT_none x κ e]
      have e2 : (fun a => proveAt W cA r₀ h
          ⟨k.i, k.copies.map (TabT.toK (fun u => vs.getD u []) tl.preE)⟩ x ⟨j, κ, h.coB.e a⟩) =
          fun _ => .pure ⟨j, h.nm j, none⟩ := funext fun a => proveAt_none x κ _ e'
      rw [e2]
      exact (Same.pure (a := ((⟨j, h.nm j, none⟩ : RequestProof lam L), vs)) List.prefix_rfl).congr
        (Eqv.drop _ _)
  | some t =>
      have ht : t ∈ k.copies := List.mem_of_getElem? e
      have e' : (k.copies.map (TabT.toK (fun u => vs.getD u []) tl.preE))[j]? =
          some (t.toK (fun u => vs.getD u []) tl.preE) := by
        rw [List.getElem?_map, e]
        rfl
      have hx : ExtTie (wBC W).ext (fun _ => (t.toK (fun u => vs.getD u []) tl.preE).tree)
          (fun _ => t.tree) tl.preE vs := fun p =>
        ⟨rfl, rfl, fun a ha => hk t ht a (List.mem_of_getElem? ha)⟩
      rw [proveAtT_some x κ e, plainOf_bind, hf.stB κ]
      refine ((same_run hR Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀)
        (cmsBA cA t.tree.root (L.recOf k.i t.r t.seed).2) (x, L.recOf k.i t.r t.seed)
        (L.encodeIndex k.i t.r) (fun _ => (t.toK (fun u => vs.getD u []) tl.preE).tree) (fun _ => t.tree)
        tl.preE (h.st.B k.i t.r t.seed x (h.nm j) κ) tl.B (h.startB (h.rvB κ)) h.capB
        (h.st.stopB k.i t.r t.seed x (h.nm j)) h.coB h.rtail h.nR h.nK h.nJ h.fill vs hf.coB hf.rsB
        hf.okB hf.fitB hx).bind (f' := fun c => .pure ⟨j, h.nm j, c⟩) fun p hp =>
          Same.pure (a := ((⟨j, h.nm j, p.1⟩ : RequestProof lam L), p.2)) hp).congr (Eqv.of_eq ?_)
      refine congrArg (OComp.sample h.coB.n) (funext fun a => ?_)
      rw [proveAt_some x κ _ e', Tie.obind_assoc]
      rfl

/-- **The prover of one request that is shown.** -/
theorem same_sess (hR : Spec.sameRun) (hf : TokFit W h tl) (k : IskT lam L Bd aT aL)
    (vs : List Bits) (hk : ∀ t ∈ k.copies, ∀ a ∈ t.tree.tok, a.1 < vs.length) (x : X) :
    Same (fun p : List (RequestProof lam L) × List Bits => p.1) (fun p => vs <+: p.2)
      (plainOf (proveWT W cA r₀ h tl k [(x, (), true)]) vs)
      ((proveW W cA r₀ h ⟨k.i, k.copies.map (TabT.toK (fun u => vs.getD u []) tl.preE)⟩
        [(x, ())]).bind fun y => .pure y.val) := by
  refine Same.congr (c' := .sample h.M fun j => .sample h.kB.n fun c =>
    (OComp.sample h.coB.n fun e => proveAt W cA r₀ h
      ⟨k.i, k.copies.map (TabT.toK (fun u => vs.getD u []) tl.preE)⟩ x
      ⟨j.val, h.kB.e c, h.coB.e e⟩).bind fun π => .pure [π]) ?_ (Eqv.of_eq ?_)
  · show Same _ _ (.sample h.M fun j => .sample h.kB.n fun c =>
      plainOf ((proveAtT W cA r₀ h tl k x ⟨j.val, h.kB.e c⟩).bind fun π => Step.pure [π]) vs) _
    refine Same.sample fun j => Same.sample fun c => ?_
    rw [plainOf_bind]
    exact (same_proveAt hR hf k vs hk x j.val (h.kB.e c)).bind fun p hp =>
      Same.pure (a := ([p.1], p.2)) hp
  · show (OComp.sample h.M fun j => .sample h.kB.n fun c => .sample h.coB.n fun e =>
      ((proveAt W cA r₀ h ⟨k.i, k.copies.map (TabT.toK (fun u => vs.getD u []) tl.preE)⟩ x
        ⟨j.val, h.kB.e c, h.coB.e e⟩).bind fun π =>
          (OComp.pure ⟨[π], rfl⟩ : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL)
            (ZKCP.Gen.Slots (RequestProof lam L) [(x, ())]))).bind fun y => .pure y.val) = _
    refine congrArg _ (funext fun j => congrArg _ (funext fun c => congrArg _ (funext fun e => ?_)))
    rw [Tie.obind_assoc]
    rfl

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.same_sess
