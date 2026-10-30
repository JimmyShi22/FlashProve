-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/Setup.lean: THE TOKEN SIDE's COMMITTER HAS THE RUN OF THE SCHEME's COMMITTER
WRITTEN WITH EACH SECRET COIN DRAWN JUST BEFORE THE PART THAT READS IT (commitL,
Johnson/TokenSide2/Late.lean), under every rule for answering queries. From Spec.sameTab and
Spec.sameRun (Johnson/TokenSide/SpecSame.lean), which are hypotheses here (they are proved in
Johnson/TokenSide2/SameTab.lean and Johnson/TokenSide/TieRun.lean), and the premises TokFit
(Johnson/TokenSide2/Sess.lean).

Lemmas of one step of a proof. This file states no goal of the release. The token programs are a
device of that step and stand in no statement on the scheme.

The two programs have the same parts in the same order: a table, the copies' tables, the run on the
first table, the links. Each part is one of the two units (same_tab, same_run,
Johnson/TokenSide2/Units.lean), and the parts are composed by Same.bind. What is carried from part
to part: the token side hands on tables with tokens and a store, the plain side tables with strings.
  TabIs vs tT tK   the table with tokens tT is in order at the store vs, and tK is tT with the
                   store's values in the place of the tokens.
It stays when the store grows (TabIs.mono): the tokens of a table that is in order are numbers of
strings of the store, and a store only grows at its end (toK_store).

  same_tabs, same_test, same_link, same_links, same_commitAt   the parts.
  same_commit   THE COMMITTER. Its property of all outputs: every copy's table is in order at the
                last store.

-/
import Johnson.TokenSide2.Sess
import Johnson.TokenSide2.Late

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## A table with tokens, at a store that grows -/

theorem toK_store {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {ℓ d : ℕ} {vs ws : List Bits}
    {T : TreeT lam L} (hT : TreeOK ℓ d vs T) (hp : vs <+: ws) (pre : Bits) :
    T.toK (fun u => ws.getD u []) pre = T.toK (fun u => vs.getD u []) pre := by
  unfold TreeT.toK
  refine congrArg (fun f => (⟨f, T.lv⟩ : TreeK lam L)) (funext fun j => ?_)
  refine congrArg (fun s => (⟨T.body j, s⟩ : LeafIn L)) ?_
  cases e : T.tok[j]? with
  | none => rfl
  | some a =>
      show pre ++ ws.getD a.1 [] = pre ++ vs.getD a.1 []
      rw [getD_of_prefix hp (hT.2.1 a (List.mem_of_getElem? e)).1]

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

theorem tabToK_store {ℓ d : ℕ} {vs ws : List Bits} {t : TabT lam L Bd aT aL}
    (hT : TreeOK ℓ d vs t.tree) (hp : vs <+: ws) (pre : Bits) :
    t.toK (fun u => ws.getD u []) pre = t.toK (fun u => vs.getD u []) pre := by
  unfold TabT.toK
  rw [toK_store hT hp]

/-- The table with tokens tT is in order at the store vs, and tK is tT at the store's values. -/
def TabIs (ℓ d : ℕ) (pre : Bits) (vs : List Bits) (tT : TabT lam L Bd aT aL)
    (tK : TabK lam L Bd aT aL) : Prop :=
  TreeOK ℓ d vs tT.tree ∧ tK = tT.toK (fun u => vs.getD u []) pre

theorem TabIs.mono {ℓ d : ℕ} {pre : Bits} {vs ws : List Bits} {tT : TabT lam L Bd aT aL}
    {tK : TabK lam L Bd aT aL} (h : TabIs ℓ d pre vs tT tK) (hp : vs <+: ws) :
    TabIs ℓ d pre ws tT tK :=
  ⟨h.1.mono hp, by rw [h.2, tabToK_store h.1 hp]⟩

variable {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  {cA : L.OutOfDomainAnswer → List (Dig lam)} {h : HonestSide lam L Bd aT aL}
  {tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB}

/-! ## The parts -/

/-- The copies' tables. -/
theorem same_tabs (hT : Spec.sameTab) (hf : TokFit W h tl) (i : I) :
    ∀ (ds : List (DrawCopyD L h.KL)) (vs : List Bits),
    Same (fun q : List (TabT lam L Bd aT aL) × List Bits =>
        q.1.map (TabT.toK (fun u => q.2.getD u []) tl.preE))
      (fun q => vs <+: q.2 ∧ ∀ t ∈ q.1, TreeOK tl.frE W.depth q.2 t.tree)
      (plainOf (tabsT W S h tl i ds) vs) (tabsL W S h i ds)
  | [], vs => Same.pure (a := (([] : List (TabT lam L Bd aT aL)), vs))
      ⟨List.prefix_rfl, fun _ e => absurd e List.not_mem_nil⟩
  | d :: ds, vs => by
      rw [tabsT, tabsL, plainOf_bind]
      refine (same_tab hT W S h tl hf.sl h.b₀ i d.r vs).bind fun p hp => ?_
      beta_reduce
      rw [plainOf_bind]
      refine (same_tabs hT hf i ds p.2).bind fun q hq => ?_
      beta_reduce
      rw [← tabToK_store hp.2 hq.1 tl.preE]
      exact Same.pure (a := (p.1 :: q.1, q.2)) ⟨hp.1.trans hq.1, fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hp.2.mono hq.1
        · exact hq.2 t ht⟩

/-- The compiled run on the first table. -/
theorem same_test (hR : Spec.sameRun) (hf : TokFit W h tl) (i : I) (t₁ : TabT lam L Bd aT aL)
    (t₁K : TabK lam L Bd aT aL) (κ : h.KT) (vs : List Bits)
    (h1 : TabIs tl.frE W.depth tl.preE vs t₁ t₁K) :
    Same (fun p : Option (OneProtocolProof lam (batTC L aT)) × List Bits => p.1) (fun p => vs <+: p.2)
      (plainOf (proveC Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
        (cmsTA cA t₁.tree.root (L.recOf i t₁.r t₁.seed).2) (L.recOf i t₁.r t₁.seed)
        (L.encodeIndex i t₁.r) (fun _ => t₁.tree) tl.preE (h.st.T i t₁.r t₁.seed κ) tl.T (tl.stT κ) h.capT
        (h.st.stopT i t₁.r t₁.seed)) vs)
      (testL W cA h i t₁K κ) := by
  obtain ⟨hok, rfl⟩ := h1
  rw [hf.stT κ]
  exact same_run hR Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
    (cmsTA cA t₁.tree.root (L.recOf i t₁.r t₁.seed).2) (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
    (fun _ => (t₁.toK (fun u => vs.getD u []) tl.preE).tree) (fun _ => t₁.tree) tl.preE
    (h.st.T i t₁.r t₁.seed κ) tl.T (h.startT (h.rvT κ)) h.capT (h.st.stopT i t₁.r t₁.seed) h.coT
    h.rtail h.nR h.nK h.nJ h.fill vs hf.coT hf.rsT hf.okT hf.fitT fun p =>
      ⟨rfl, rfl, fun a ha => (hok.2.1 a (List.mem_of_getElem? ha)).1⟩

/-- One copy's entry in the key's list. -/
theorem same_link (hR : Spec.sameRun) (hf : TokFit W h tl) (i : I) (t₁ t₂ : TabT lam L Bd aT aL)
    (t₁K t₂K : TabK lam L Bd aT aL) (c : DrawCopyD L h.KL) (vs : List Bits)
    (h1 : TabIs tl.frE W.depth tl.preE vs t₁ t₁K) (h2 : TabIs tl.frE W.depth tl.preE vs t₂ t₂K) :
    Same (fun p : (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) × List Bits => p.1)
      (fun p => vs <+: p.2)
      (plainOf (linkT W cA h tl i t₁ t₂ c) vs) (linkL W cA h i t₁K t₂K c.κ) := by
  obtain ⟨ok1, rfl⟩ := h1
  obtain ⟨ok2, rfl⟩ := h2
  have hk : ∀ k : ℕ, (if k = 0 then (t₁.toK (fun u => vs.getD u []) tl.preE).tree
      else (t₂.toK (fun u => vs.getD u []) tl.preE).tree) =
      (if k = 0 then t₁.tree else t₂.tree).toK (fun u => vs.getD u []) tl.preE := fun k => by
    split <;> rfl
  have hok : ∀ k : ℕ, TreeOK tl.frE W.depth vs (if k = 0 then t₁.tree else t₂.tree) := fun k => by
    split
    · exact ok1
    · exact ok2
  have hx : ExtTie (wLC W).ext
      (fun k => if k = 0 then (t₁.toK (fun u => vs.getD u []) tl.preE).tree
        else (t₂.toK (fun u => vs.getD u []) tl.preE).tree)
      (fun k => if k = 0 then t₁.tree else t₂.tree) tl.preE vs := fun p =>
    ⟨congrArg TreeK.lv (hk ((wLC W).ext.which p)),
      congrArg (fun T : TreeK lam (typedOracleCarrier L Bd aT aL) => (T.inp ((wLC W).ext.leaf p)).salt)
        (hk ((wLC W).ext.which p)),
      fun a ha => ((hok _).2.1 a (List.mem_of_getElem? ha)).1⟩
  unfold linkT
  rw [plainOf_bind, hf.stL c.κ]
  refine ((same_run hR Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
    (cmsLA cA t₁.tree.root t₂.tree.root (L.recOf i t₁.r t₁.seed).2 (L.recOf i t₂.r t₂.seed).2)
    (L.recOf i t₁.r t₁.seed, L.recOf i t₂.r t₂.seed) (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r)
    (fun k => if k = 0 then (t₁.toK (fun u => vs.getD u []) tl.preE).tree
      else (t₂.toK (fun u => vs.getD u []) tl.preE).tree)
    (fun k => if k = 0 then t₁.tree else t₂.tree) tl.preE
    (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) c.κ) tl.Lk (h.startL (h.rvL c.κ)) h.capL
    (h.st.stopL i (t₁.r, t₁.seed) (t₂.r, t₂.seed)) h.coL h.rtail h.nR h.nK h.nJ h.fill vs hf.coL
    hf.rsL hf.okL hf.fitL hx).bind
    (f' := fun b => .pure (t₂.tree.root, L.recOf i t₂.r t₂.seed, b)) fun p hp =>
      Same.pure (a := ((t₂.tree.root, L.recOf i t₂.r t₂.seed, p.1), p.2)) hp).congr (Eqv.of_eq ?_)
  refine congrArg (OComp.sample h.coL.n) (funext fun a => ?_)
  rw [Tie.obind_assoc]
  rfl

/-- The entries of the key's list. -/
theorem same_links (hR : Spec.sameRun) (hf : TokFit W h tl) (i : I) (t₁ : TabT lam L Bd aT aL)
    (t₁K : TabK lam L Bd aT aL) :
    ∀ (l : List (DrawCopyD L h.KL × TabT lam L Bd aT aL)) (vs : List Bits),
      TabIs tl.frE W.depth tl.preE vs t₁ t₁K → (∀ a ∈ l, TreeOK tl.frE W.depth vs a.2.tree) →
    Same (fun p : List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) × List Bits => p.1)
      (fun p => vs <+: p.2)
      (plainOf (linksT W cA h tl i t₁ l) vs)
      (linksL W cA h i t₁K (l.map fun a => (a.1, a.2.toK (fun u => vs.getD u []) tl.preE)))
  | [], vs, _, _ => Same.pure
      (a := (([] : List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL)))), vs)) List.prefix_rfl
  | a :: l, vs, h1, h2 => by
      rw [List.map_cons, linksT, linksL, plainOf_bind]
      refine (same_link hR hf i t₁ a.2 t₁K _ a.1 vs h1 ⟨h2 a List.mem_cons_self, rfl⟩).bind
        fun p hp => ?_
      beta_reduce
      rw [plainOf_bind]
      have e : (l.map fun b => (b.1, b.2.toK (fun u => vs.getD u []) tl.preE)) =
          l.map fun b => (b.1, b.2.toK (fun u => p.2.getD u []) tl.preE) :=
        List.map_congr_left fun b hb => by
          rw [tabToK_store (h2 b (List.mem_cons_of_mem _ hb)) hp]
      rw [e]
      exact (same_links hR hf i t₁ t₁K l p.2 (h1.mono hp) fun b hb =>
        (h2 b (List.mem_cons_of_mem _ hb)).mono hp).bind fun q hq =>
          Same.pure (a := (p.1 :: q.1, q.2)) (hp.trans hq)

/-- The committer behind the coins that both sides draw from lists at the start. -/
theorem same_commitAt (hT : Spec.sameTab) (hR : Spec.sameRun) (hf : TokFit W h tl) (i : I)
    (d : DrawCD L h.KT h.KL) (vs : List Bits) :
    Same (fun y : (FullKey lam L aT aL × IskT lam L Bd aT aL) × List Bits =>
        (y.1.1, (⟨y.1.2.i, y.1.2.copies.map (TabT.toK (fun u => y.2.getD u []) tl.preE)⟩ :
          Isk lam L Bd aT aL)))
      (fun y => ∀ t ∈ y.1.2.copies, TreeOK tl.frE W.depth y.2 t.tree)
      (plainOf (commitAtT W S cA h tl i d) vs) (commitAtL W S cA h i d) := by
  unfold commitAtT commitAtL
  rw [plainOf_bind]
  refine (same_tab hT W S h tl hf.sl h.b₀ i d.r vs).bind fun p hp => ?_
  beta_reduce
  rw [plainOf_bind]
  refine (same_tabs hT hf i d.copies p.2).bind fun q hq => ?_
  beta_reduce
  rw [plainOf_bind]
  have h1 : TabIs tl.frE W.depth tl.preE q.2 p.1 (p.1.toK (fun u => p.2.getD u []) tl.preE) :=
    TabIs.mono ⟨hp.2, rfl⟩ hq.1
  refine (same_test hR hf i p.1 _ d.κ q.2 h1).bind fun a ha => ?_
  beta_reduce
  rw [plainOf_bind]
  have hz : ∀ b ∈ d.copies.zip q.1, b.2 ∈ q.1 := fun ⟨_, _⟩ hb => (List.of_mem_zip hb).2
  have ez : d.copies.zip (q.1.map (TabT.toK (fun u => q.2.getD u []) tl.preE)) =
      (d.copies.zip q.1).map fun b => (b.1, b.2.toK (fun u => a.2.getD u []) tl.preE) := by
    rw [List.zip_map_right]
    refine List.map_congr_left fun b hb => ?_
    rw [tabToK_store (hq.2 b.2 (hz b hb)) ha]
    rfl
  rw [ez]
  refine (same_links hR hf i p.1 _ (d.copies.zip q.1) a.2 (h1.mono ha) fun b hb =>
    (hq.2 b.2 (hz b hb)).mono ha).bind fun ls hls => ?_
  beta_reduce
  have e2 : q.1.map (TabT.toK (fun u => q.2.getD u []) tl.preE) =
      q.1.map (TabT.toK (fun u => ls.2.getD u []) tl.preE) :=
    List.map_congr_left fun t ht => (tabToK_store (hq.2 t ht) (ha.trans hls) tl.preE).symm
  rw [e2]
  exact Same.pure (a := (((⟨p.1.tree.root, L.recOf i p.1.r p.1.seed, a.1, ls.1⟩ : FullKey lam L aT aL),
    (⟨i, q.1⟩ : IskT lam L Bd aT aL)), ls.2)) fun t ht => (hq.2 t ht).mono (ha.trans hls)

/-! ## The committer -/

theorem plainOf_coinsCopiesT : ∀ (n : ℕ) (vs : List Bits),
    plainOf (coinsCopiesT W h n) vs = (coinsCopiesS W h n).bind fun ds => .pure (ds, vs)
  | 0, _ => rfl
  | n + 1, vs => by
      show OComp.sample h.ri.n (fun a => .sample h.kL.n fun c =>
          plainOf ((coinsCopiesT W h n).bind fun ds =>
            Step.pure ((⟨h.ri.e a, h.kL.e c⟩ : DrawCopyD L h.KL) :: ds)) vs) =
        OComp.sample h.ri.n fun a => .sample h.kL.n fun c =>
          ((coinsCopiesS W h n).bind fun ds =>
            OComp.pure ((⟨h.ri.e a, h.kL.e c⟩ : DrawCopyD L h.KL) :: ds)).bind
            fun ds => .pure (ds, vs)
      refine congrArg _ (funext fun a => congrArg _ (funext fun c => ?_))
      rw [plainOf_bind, plainOf_coinsCopiesT n vs, Tie.obind_assoc, Tie.obind_assoc]
      rfl

/-- **The committer.** -/
theorem same_commit (hT : Spec.sameTab) (hR : Spec.sameRun) (hf : TokFit W h tl) (i : I) :
    Same (fun y : (FullKey lam L aT aL × IskT lam L Bd aT aL) × List Bits =>
        (y.1.1, (⟨y.1.2.i, y.1.2.copies.map (TabT.toK (fun u => y.2.getD u []) tl.preE)⟩ :
          Isk lam L Bd aT aL)))
      (fun y => ∀ t ∈ y.1.2.copies, TreeOK tl.frE W.depth y.2 t.tree)
      (plainOf (commitT W S cA h tl i) []) (commitL W S cA h i) := by
  show Same _ _ (.sample h.ri.n fun a => .sample h.kT.n fun c =>
      plainOf (((coinsCopiesT W h (h.M + 1)).bind fun ds =>
        Step.pure (⟨h.ri.e a, h.kT.e c, ds⟩ : DrawCD L h.KT h.KL)).bind fun d =>
          commitAtT W S cA h tl i d) [])
    (.sample h.ri.n fun a => .sample h.kT.n fun c =>
      ((coinsCopiesS W h (h.M + 1)).bind fun ds =>
        OComp.pure (⟨h.ri.e a, h.kT.e c, ds⟩ : DrawCD L h.KT h.KL)).bind fun d =>
          commitAtL W S cA h i d)
  refine Same.sample fun a => Same.sample fun c => ?_
  rw [plainOf_bind, plainOf_bind, plainOf_coinsCopiesT, Tie.obind_assoc, Tie.obind_assoc,
    Tie.obind_assoc]
  exact Same.left _ fun ds => same_commitAt hT hR hf i ⟨h.ri.e a, h.kT.e c, ds⟩ []

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.same_commit
