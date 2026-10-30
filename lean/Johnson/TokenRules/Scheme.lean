-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/Scheme.lean: THE COMMITTER, THE PROVER AND EACH STEP OF THE CHALLENGER, AS TOKEN
PROGRAMS, KEEP THE RULES, GIVEN THAT THE CHAIN OF A COMPILED RUN DOES: the proofs of
Spec.safeCommit, Spec.safeProveW, Spec.safeStep and Spec.safeTwin (Johnson/TokenRules/Spec.lean)
from Spec.safeChain (Johnson/TokenRel/Rules.lean), which is a hypothesis here; it is proved in
that file, and the forms without a hypothesis are in
Johnson/TokenRules/Closed.lean.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

The programs (Johnson/TokenSide/Whole.lean) are put together from tables (safeTab,
Johnson/TokenRules/Table.lean), compiled runs (safeProveC, Johnson/TokenRules/EndC.lean) and coins
that are drawn from enumerations, which leave the state alone. Two things are carried from part to
part.
  What is known of a table's tokens (TreeOKT) stays along every part, because no part charges an old
  token (TreeOKT.keeps at GrowsO.charges): a compiled run on a table shows some of the table's
  tokens and charges none of them.
  The counts add up: h.M + 2 tables, one run on the first table, h.M + 1 links. That there are
  h.M + 1 copies is read off the committer's coins (safe_coinsCT).
The committer shows tokens of its own tables. Seen from the state before the committer these are new
tokens (TreeNewT), so the committer shows no old token.

-/
import Johnson.TokenRules.EndC
import Johnson.TokenRules.Table
import Johnson.TokenRules.Marks

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRules
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRel
open _root_.Compile.GlueB (GCall GAdm)
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (Marks)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

theorem one_more_le (n x : ℕ) : x + n * x ≤ (n + 1) * x :=
  le_of_eq (by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm])

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  {cA : L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec} {h : HonestSide lam L Bd aT aL}
  {tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB} {bl bf : ℕ}

/-! ## Coins from enumerations leave the state alone -/

section Coins
variable {Rl : Rules (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}

theorem safe_coinsCopyT (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    SafeO Rl (coinsCopyT W h) d fun _ d' => d' = d := by
  unfold coinsCopyT
  intro _ _
  exact rfl

theorem safe_coinsCopiesT : ∀ (n : ℕ) (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))),
    SafeO Rl (coinsCopiesT W h n) d fun ds d' => d' = d ∧ ds.length = n
  | 0, _ => ⟨rfl, rfl⟩
  | n + 1, d => by
      rw [coinsCopiesT]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_coinsCopyT d))
      rintro c _ rfl
      refine SafeO.bind _ _ _ (SafeO.mono ?_ _ _ (safe_coinsCopiesT n _))
      rintro ds _ ⟨rfl, hl⟩
      exact ⟨rfl, by rw [List.length_cons, hl]⟩

/-- The committer's coins: the state stays, and there are h.M + 1 copies. -/
theorem safe_coinsCT (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    SafeO Rl (coinsCT W h) d fun c d' => d' = d ∧ c.copies.length = h.M + 1 := by
  unfold coinsCT
  intro _ _
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_coinsCopiesT (h.M + 1) d))
  rintro ds _ ⟨rfl, hl⟩
  exact ⟨rfl, hl⟩

theorem safe_coinsPT (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    SafeO Rl (coinsPT W h) d fun _ d' => d' = d := by
  unfold coinsPT
  intro _ _
  exact rfl

end Coins

/-- the rules at the scheme's letters -/
local notation "RlW" => rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)

/-! ## The committer -/

/-- The copies' tables. -/
theorem safe_tabsT (hbl : bl ≤ tl.frE) (i : I) :
    ∀ (ds : List (DrawCopyD L h.KL)) (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))), TidyO RlW d →
    SafeO RlW (tabsT W S h tl i ds) d fun ts d' =>
      TidyO RlW d' ∧
      GrowsO noTok noTok (fun o => ds.length * eTab W.depth S.t o)
        (fun o => ds.length * mTab W.depth o) d d' ∧
      ts.length = ds.length ∧ ∀ t ∈ ts, TreeOKT d' [] t.tree ∧ TreeNewT d.vals.length t.tree
  | [], d, hd => ⟨hd, GrowsO.refl d, rfl, fun _ e => absurd e List.not_mem_nil⟩
  | a :: ds, d, hd => by
      rw [tabsT]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d
        (safeTab I X lam L Bd aT aL W S h tl bl bf h.b₀ i a.r d hbl hd))
      rintro t d₁ ⟨hd₁, hg₁, hT, hN⟩
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_tabsT hbl i ds d₁ hd₁))
      rintro ts d₂ ⟨hd₂, hg₂, hlen, hts⟩
      refine ⟨hd₂, hg₁.trans hg₂ (fun _ e => Or.inl e) (fun _ e => Or.inl e)
        (fun _ => one_more_le _ _) (fun _ => one_more_le _ _), by rw [List.length_cons, hlen,
          List.length_cons], ?_⟩
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact ⟨hT.keeps hg₂.charges fun _ _ e => e, hN⟩
      · exact ⟨(hts t' ht').1, fun u hu => le_trans hg₁.length_le ((hts t' ht').2 u hu)⟩

/-- The compiled run on the first table. -/
theorem safe_testT (hC : Spec.safeChain) (hl : LensOK bl bf tl) (i : I) (t₁ : TabT lam L Bd aT aL)
    (κ : h.KT) {d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hd : TidyO RlW d)
    (h1 : TreeOKT d [] t₁.tree) :
    SafeO RlW (proveC Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
      (cmsTA cA t₁.tree.root (L.recOf i t₁.r t₁.seed).2) (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
      (fun _ => t₁.tree) tl.preE (h.st.T i t₁.r t₁.seed κ) tl.T (tl.stT κ) h.capT
      (h.st.stopT i t₁.r t₁.seed)) d fun _ d' =>
      TidyO RlW d' ∧
      GrowsO noTok (TreeTokT t₁.tree) (eRun L.offline.shape aT (wTC W).sh)
        (mRun Tag.test L.offline.shape aT (wTC W).sh h.capT tl.T.dq) d d' := by
  refine SafeO.mono ?_ _ d (safeProveC hC _ _ lam W.K (typedOracleCarrier L Bd aT aL) bl bf (seedPts W S)
    Tag.test _ _ (batTC L aT) (wTC W) W.embT id (fun _ => none) _ _ _ (fun _ => t₁.tree) tl.preE _
    tl.T (tl.stT κ) h.capT _ d hl.frT hl.sT hl.dig hd fun _ => h1)
  rintro _ d₁ ⟨hd₁, hg⟩
  exact ⟨hd₁, hg.mono (fun _ e => Or.inl e) (fun _ ⟨_, hu⟩ => Or.inl hu) (fun _ => le_rfl)
    (fun _ => le_rfl)⟩

/-- One copy's entry in the key's list. -/
theorem safe_linkT (hC : Spec.safeChain) (hl : LensOK bl bf tl) (i : I)
    (t₁ t₂ : TabT lam L Bd aT aL) (c : DrawCopyD L h.KL)
    {d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hd : TidyO RlW d)
    (h1 : TreeOKT d [] t₁.tree) (h2 : TreeOKT d [] t₂.tree) :
    SafeO RlW (linkT W cA h tl i t₁ t₂ c) d fun _ d' =>
      TidyO RlW d' ∧
      GrowsO noTok (fun u => TreeTokT t₁.tree u ∨ TreeTokT t₂.tree u)
        (eRun L.link.shape aL (wLC W).sh)
        (mRun Tag.link L.link.shape aL (wLC W).sh h.capL tl.Lk.dq) d d' := by
  unfold linkT
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safeProveC hC _ _ lam W.K (typedOracleCarrier L Bd aT aL) bl bf
    (seedPts W S) Tag.link _ _ (batLC L aL) (wLC W) W.embL id (fun _ => none) _ _ _
    (fun k => if k = 0 then t₁.tree else t₂.tree) tl.preE _ tl.Lk (tl.stL c.κ) h.capL _ d hl.frL
    hl.sL hl.dig hd fun k => ?_))
  · rintro _ d₁ ⟨hd₁, hg⟩
    refine ⟨hd₁, hg.mono (fun _ e => Or.inl e) (fun u ⟨k, hk⟩ => Or.inl ?_) (fun _ => le_rfl)
      (fun _ => le_rfl)⟩
    have hk' : TreeTokT (if k = 0 then t₁.tree else t₂.tree) u := hk
    split at hk'
    · exact Or.inl hk'
    · exact Or.inr hk'
  · show TreeOKT d [] (if k = 0 then t₁.tree else t₂.tree)
    split
    · exact h1
    · exact h2

/-- The entries of the key's list. P: a set that holds the tokens of all tables. -/
theorem safe_linksT (hC : Spec.safeChain) (hl : LensOK bl bf tl) (i : I)
    (t₁ : TabT lam L Bd aT aL) (P : Tok → Prop) (hP : ∀ u, TreeTokT t₁.tree u → P u) :
    ∀ (l : List (DrawCopyD L h.KL × TabT lam L Bd aT aL))
      (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))), TidyO RlW d → TreeOKT d [] t₁.tree →
      (∀ a ∈ l, TreeOKT d [] a.2.tree ∧ ∀ u, TreeTokT a.2.tree u → P u) →
    SafeO RlW (linksT W cA h tl i t₁ l) d fun _ d' =>
      TidyO RlW d' ∧
      GrowsO noTok P (fun o => l.length * eRun L.link.shape aL (wLC W).sh o)
        (fun o => l.length * mRun Tag.link L.link.shape aL (wLC W).sh h.capL tl.Lk.dq o) d d'
  | [], d, hd, _, _ => ⟨hd, GrowsO.refl d⟩
  | a :: l, d, hd, h1, h2 => by
      rw [linksT]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d
        (safe_linkT hC hl i t₁ a.2 a.1 hd h1 (h2 a List.mem_cons_self).1))
      rintro _ d₁ ⟨hd₁, hg₁⟩
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_linksT hC hl i t₁ P hP l d₁ hd₁
        (h1.keeps hg₁.charges fun _ _ e => e) fun b hb =>
          ⟨(h2 b (List.mem_cons_of_mem _ hb)).1.keeps hg₁.charges fun _ _ e => e,
            (h2 b (List.mem_cons_of_mem _ hb)).2⟩))
      rintro _ d₂ ⟨hd₂, hg₂⟩
      exact ⟨hd₂, (hg₁.mono (Ch := noTok) (R := P) (fun _ e => Or.inl e)
        (fun u hu => Or.inl (hu.elim (hP u) ((h2 a List.mem_cons_self).2 u))) (fun _ => le_rfl)
        (fun _ => le_rfl)).trans hg₂ (fun _ e => Or.inl e) (fun _ e => Or.inl e)
        (fun _ => one_more_le _ _) (fun _ => one_more_le _ _)⟩

/-- The committer behind the coins that are drawn from enumerations. -/
theorem safe_commitAtT (hC : Spec.safeChain) (hl : LensOK bl bf tl) (i : I)
    (c : DrawCD L h.KT h.KL) (hc : c.copies.length = h.M + 1)
    {d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hd : TidyO RlW d) :
    SafeO RlW (commitAtT W S cA h tl i c) d fun o d' =>
      TidyO RlW d' ∧ IskOKT d' o.2 ∧ GrowsO noTok noTok (eSetup W S h) (mSetup W h tl) d d' := by
  unfold commitAtT
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d
    (safeTab I X lam L Bd aT aL W S h tl bl bf h.b₀ i c.r d hl.frE hd))
  rintro t₁ d₁ ⟨hd₁, hg₁, hT₁, hN₁⟩
  refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_tabsT hl.frE i c.copies d₁ hd₁))
  rintro ts d₂ ⟨hd₂, hg₂, hlen, hts⟩
  have hT₂ := hT₁.keeps hg₂.charges fun _ _ e => e
  refine SafeO.bind _ _ d₂ (SafeO.mono ?_ _ d₂ (safe_testT hC hl i t₁ c.κ hd₂ hT₂))
  rintro a d₃ ⟨hd₃, hg₃⟩
  have hT₃ := hT₂.keeps hg₃.charges fun _ _ e => e
  have hts₃ : ∀ t ∈ ts, TreeOKT d₃ [] t.tree := fun t ht =>
    (hts t ht).1.keeps hg₃.charges fun _ _ e => e
  have hz : ∀ b ∈ c.copies.zip ts, b.2 ∈ ts := fun ⟨_, _⟩ hb => (List.of_mem_zip hb).2
  have hzl : (c.copies.zip ts).length = h.M + 1 := by
    rw [List.length_zip, hlen, hc, Nat.min_self]
  refine SafeO.bind _ _ d₃ (SafeO.mono ?_ _ d₃ (safe_linksT hC hl i t₁
    (fun u => d.vals.length ≤ u) hN₁ (c.copies.zip ts) d₃ hd₃ hT₃ fun b hb =>
      ⟨hts₃ b.2 (hz b hb), fun u hu => le_trans hg₁.length_le ((hts b.2 (hz b hb)).2 u hu)⟩))
  rintro ls d₄ ⟨hd₄, hg₄⟩
  refine ⟨hd₄, fun t ht => (hts₃ t ht).keeps hg₄.charges fun _ _ e => e, ?_⟩
  refine ((hg₁.trans hg₂ (fun _ e => Or.inl e) (fun _ e => Or.inl e) (fun _ => le_rfl)
    (fun _ => le_rfl)).trans hg₃ (fun _ e => Or.inl e) (fun u hu => Or.inr (hN₁ u hu))
    (fun _ => le_rfl) (fun _ => le_rfl)).trans hg₄ (fun _ e => Or.inl e) (fun _ hu => Or.inr hu)
    ?_ ?_
  · intro o
    have h0 : eTab W.depth S.t o + (h.M + 1) * eTab W.depth S.t o ≤
        (h.M + 2) * eTab W.depth S.t o := one_more_le (h.M + 1) _
    simp only [eSetup, hzl, hc]
    omega
  · intro o
    have h0 : mTab W.depth o + (h.M + 1) * mTab W.depth o ≤ (h.M + 2) * mTab W.depth o :=
      one_more_le (h.M + 1) _
    simp only [mSetup, hzl, hc]
    omega

/-- **The committer**, given the chain. -/
theorem safeCommit (hC : Spec.safeChain) : Spec.safeCommit := by
  intro I X lam L Bd aT aL W S cA h tl bl bf i d hl hd
  unfold commitT
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_coinsCT d))
  rintro c _ ⟨rfl, hc⟩
  exact safe_commitAtT hC hl i c hc hd

/-! ## The prover -/

/-- The prover of one request behind the coins that are drawn from enumerations. -/
theorem safe_proveAtT (hC : Spec.safeChain) (hl : LensOK bl bf tl) (k : IskT lam L Bd aT aL)
    (x : X) (c : DrawPD h.KB) {d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hd : TidyO RlW d)
    (hk : IskOKT d k) :
    SafeO RlW (proveAtT W cA r₀ h tl k x c) d fun _ d' =>
      TidyO RlW d' ∧ GrowsO noTok (IskTokT k) (eSess W) (mSess W h tl) d d' := by
  unfold proveAtT
  split
  · exact ⟨hd, GrowsO.refl d⟩
  · rename_i t e
    have ht : t ∈ k.copies := List.mem_of_getElem? e
    refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safeProveC hC _ _ lam W.K (typedOracleCarrier L Bd aT aL) bl
      bf (seedPts W S) Tag.onl _ _ L.onlineBatch (wBC W) W.embB id (xinBA r₀) _ _ _ (fun _ => t.tree)
      tl.preE _ tl.B (tl.stB c.κ) h.capB _ d hl.frB hl.sB hl.dig hd fun _ => hk t ht))
    rintro _ d₁ ⟨hd₁, hg⟩
    exact ⟨hd₁, hg.mono (fun _ e => Or.inl e) (fun _ ⟨_, hu⟩ => Or.inl ⟨t, ht, hu⟩)
      (fun _ => le_rfl) (fun _ => le_rfl)⟩

/-- **The prover on a batch**, given the chain. -/
theorem safeProveW (hC : Spec.safeChain) : Spec.safeProveW := by
  intro I X lam L Bd aT aL W S cA r₀ h tl bl bf k b d hl hd hk
  unfold proveWT
  split
  · refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_coinsPT d))
    rintro c _ rfl
    refine SafeO.bind _ _ _ (SafeO.mono ?_ _ _ (safe_proveAtT hC hl k _ c hd hk))
    rintro _ d₁ ⟨hd₁, hg⟩
    exact ⟨hd₁, fun t ht => (hk t ht).keeps hg.charges fun _ _ e => e, hg⟩
  · exact ⟨hd, hk, GrowsO.refl d⟩

/-! ## The challenger -/

/-- **Each step of the challenger**, given the chain. -/
theorem safeStep (hC : Spec.safeChain) : Spec.safeStep := by
  intro I X lam L Bd aT aL W S cA r₀ h tl bl bf i s c d hl hI
  cases c with
  | setup =>
      cases s with
      | none =>
          show SafeO _ ((commitT W S cA h tl i).bind fun o => Step.pure (Sum.inl o.1, some o.2)) d _
          refine SafeO.bind _ _ d (SafeO.mono ?_ _ d
            (safeCommit hC I X lam L Bd aT aL W S cA h tl bl bf i d hl hI.1))
          rintro o d₁ ⟨hd₁, hk, hg⟩
          exact ⟨⟨hd₁, fun _ e => Option.some.inj e ▸ hk⟩,
            hg.mono (fun _ e => Or.inl e) (fun _ e => e.elim) (fun _ => le_rfl) (fun _ => le_rfl)⟩
      | some k =>
          exact safeStep_idle W S cA r₀ h tl bl bf i d (some k) .setup (Or.inr ⟨rfl, k, rfl⟩) hI
  | batch b =>
      cases s with
      | none =>
          exact safeStep_idle W S cA r₀ h tl bl bf i d none (.batch b) (Or.inl ⟨b, rfl, rfl⟩) hI
      | some k =>
          show SafeO _ ((proveWT W cA r₀ h tl k b).bind fun πs =>
            Step.pure (Sum.inr (_root_.Compile.GlueB.ownPf b πs), some k)) d _
          refine SafeO.bind _ _ d (SafeO.mono ?_ _ d
            (safeProveW hC I X lam L Bd aT aL W S cA r₀ h tl bl bf k b d hl hI.1 (hI.2 k rfl)))
          rintro _ d₁ ⟨hd₁, hk, hg⟩
          exact ⟨⟨hd₁, fun _ e => Option.some.inj e ▸ hk⟩,
            hg.mono (fun _ e => Or.inl e) (fun _ hu => Or.inl ⟨k, rfl, hu⟩) (fun _ => le_rfl)
              (fun _ => le_rfl)⟩

/-- **The token programs keep the rules**, given the chain. -/
theorem safeTwin (hC : Spec.safeChain) : Spec.safeTwin :=
  ⟨safeProveC hC, safeTab, safeCommit hC, safeProveW hC, safeStep hC, marksHash, marksTab⟩

end OnBytes.TokenRules

#print axioms OnBytes.TokenRules.safeCommit
#print axioms OnBytes.TokenRules.safeProveW
#print axioms OnBytes.TokenRules.safeStep
