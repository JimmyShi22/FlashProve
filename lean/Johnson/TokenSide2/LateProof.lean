-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/LateProof.lean: THE SCHEME's COMMITTER, WHICH DRAWS ALL ITS COINS FIRST, HAS THE
RUN OF THE PROGRAM THAT DRAWS EACH SECRET COIN JUST BEFORE THE PART THAT READS IT: the proof of
Spec.lateCommit (Johnson/TokenSide2/Late.lean). Theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

How a draw is carried inward. Two draws b, e stand in front of a program R b e. The program T is the
same text with each of the two draws at the place where its value is first read. T is tied to the
family (b, e) ↦ R b e (Tie, Johnson/TokenSide/Tie.lean) by one walk along the text: a part that
reads neither is one algorithm on both sides (Tie.left); at T's draw the drawn value is laid into
the pair (Tie.coin1, Tie.coin2); behind both draws the two texts are one (Tie.same). Eqv.of_tie2
turns the tie into "the same run under every rule for answering queries".

The copies. One induction on their number, with letters for what stands around the copies' parts
(late_copies): A, what is run before the copies' tables; B, between the tables and the links; G, at
the end; τ, which table the links start from.

The programs that draw late (Johnson/TokenSide2/Late.lean) are a device of one step of a proof. They
stand in no statement on the scheme.

Main names.
  Rom.Tie.same, Rom.Tie.coin1, Rom.Tie.coin2, Rom.Eqv.of_tie2   general in the family of oracles.
  OnBytes.TokenSide.late_copies   the copies.
  OnBytes.TokenSide.lateCommit    THE THEOREM.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide2.Late

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob
variable {S : OSpec} {α β : Type}

/-- An algorithm beside itself, as a family that does not read the coins. -/
theorem Tie.same {Ω : Type} (μ : PMF Ω) :
    ∀ c : OComp S α, Tie μ (fun a _ => a) (fun _ => True) c fun _ => c
  | .pure _ => .done trivial fun _ => rfl
  | .query _ _ k => .query (fun _ r => k r) (fun _ => rfl) fun r => Tie.same μ (k r)
  | .sample _ k => .draw (fun _ r => k r) (fun _ => rfl) fun r => Tie.same μ (k r)

section Two
variable {n m : ℕ} {φ : α → Fin (n + 1) × Fin (m + 1) → β} {Q : α → Prop}

/-- The coins are a pair of independent uniform draws: the left side draws the first. -/
theorem Tie.coin1 {k : Fin (n + 1) → OComp S α} {g : Fin (n + 1) × Fin (m + 1) → OComp S β}
    (hk : ∀ r, Tie (prod (unif (Fin (n + 1))) (unif (Fin (m + 1)))) φ Q (k r) fun ω => g (r, ω.2)) :
    Tie (prod (unif (Fin (n + 1))) (unif (Fin (m + 1)))) φ Q (.sample n k) g :=
  .coin (ν := unif (Fin (n + 1))) id (fun x ω => (x, ω.2)) (PMF.map_id _)
    ((Resamples.self (unif (Fin (n + 1)))).fst (unif (Fin (m + 1)))) hk

/-- The left side draws the second. -/
theorem Tie.coin2 {k : Fin (m + 1) → OComp S α} {g : Fin (n + 1) × Fin (m + 1) → OComp S β}
    (hk : ∀ r, Tie (prod (unif (Fin (n + 1))) (unif (Fin (m + 1)))) φ Q (k r) fun ω => g (ω.1, r)) :
    Tie (prod (unif (Fin (n + 1))) (unif (Fin (m + 1)))) φ Q (.sample m k) g :=
  .coin (ν := unif (Fin (m + 1))) id (fun x ω => (ω.1, x)) (PMF.map_id _)
    ((Resamples.self (unif (Fin (m + 1)))).snd (unif (Fin (n + 1)))) hk

end Two

/-- **Two draws in front of a program, or each where it is first read.** -/
theorem Eqv.of_tie2 {n m : ℕ} {R : Fin (n + 1) → Fin (m + 1) → OComp S α} {T : OComp S α}
    {Q : α → Prop}
    (h : Tie (prod (unif (Fin (n + 1))) (unif (Fin (m + 1)))) (fun a _ => a) Q T
      fun ω => R ω.1 ω.2) :
    Eqv (.sample n fun b => .sample m fun e => R b e) T := by
  intro σ hd s
  have e1 := h.sound_const hd s
  simp only [OComp.interp_sample]
  rw [bind_bind_eq_prod_bind (unif (Fin (n + 1))) (unif (Fin (m + 1)))
    fun b e => (R b e).interp hd s, e1]
  exact PMF.map_id _

end Rom

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL)

/-- **The copies**: their coins all first, or each secret coin just before the part that reads it.
-/
theorem late_copies (i : I) : ∀ (n : ℕ) {α β γ : Type}
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) α) (τ : α → TabK lam L Bd aT aL)
    (B : α → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) β)
    (G : α → List (TabK lam L Bd aT aL) → β →
      List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) →
      TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) γ),
    Eqv
      ((coinsCopies W h n).bind fun ds => A.bind fun x => (tabsO W S h i ds).bind fun ts =>
        (B x).bind fun y => (linksO W cA h i (τ x) (ds.zip ts)).bind fun ls => G x ts y ls)
      ((coinsCopiesS W h n).bind fun ds => A.bind fun x => (tabsL W S h i ds).bind fun ts =>
        (B x).bind fun y => (linksL W cA h i (τ x) (ds.zip ts)).bind fun ls => G x ts y ls)
  | 0, _, _, _, A, τ, B, G => Eqv.refl _
  | n + 1, α, β, γ, A, τ, B, G => by
    -- the first copy's four draws in front; behind them the claim for n copies
    refine Eqv.trans (c' := .sample h.ri.n fun a => .sample h.sl.n fun b => .sample h.kL.n fun c =>
      .sample h.coL.n fun e =>
      (coinsCopies W h n).bind fun ds =>
        (A.bind fun x => (tabO W S h.b₀ i (h.ri.e a) (cutS (2 ^ W.depth) (h.sl.e b))).bind fun t =>
          .pure (x, t)).bind fun p =>
        (tabsO W S h i ds).bind fun ts =>
        ((B p.1).bind fun y => (linkO W cA h i (τ p.1) p.2
          ⟨h.ri.e a, h.sl.e b, h.kL.e c, h.coL.e e⟩).bind fun en => .pure (y, en)).bind fun q =>
        (linksO W cA h i (τ p.1) (ds.zip ts)).bind fun ls => G p.1 (p.2 :: ts) q.1 (q.2 :: ls))
      (Eqv.of_eq ?_) ?_
    · simp only [coinsCopies, coinsCopy, tabsO, linksO, List.zip_cons_cons, Tie.obind_assoc,
        OComp.bind]
    refine Eqv.trans (Eqv.sample fun a => Eqv.sample fun b => Eqv.sample fun c => Eqv.sample fun e
        =>
      late_copies i n
        (A.bind fun x => (tabO W S h.b₀ i (h.ri.e a) (cutS (2 ^ W.depth) (h.sl.e b))).bind fun t =>
          .pure (x, t)) (fun p => τ p.1)
        (fun p => (B p.1).bind fun y => (linkO W cA h i (τ p.1) p.2
          ⟨h.ri.e a, h.sl.e b, h.kL.e c, h.coL.e e⟩).bind fun en => .pure (y, en))
        (fun p ts q ls => G p.1 (p.2 :: ts) q.1 (q.2 :: ls))) ?_
    refine Eqv.trans (Eqv.sample fun a => Eqv.swap _ _ _) ?_
    refine Eqv.trans (c' := .sample h.ri.n fun a => .sample h.kL.n fun c =>
      (coinsCopiesS W h n).bind fun ds => A.bind fun x =>
        .sample h.sl.n fun b =>
        (tabO W S h.b₀ i (h.ri.e a) (cutS (2 ^ W.depth) (h.sl.e b))).bind fun t =>
        (tabsL W S h i ds).bind fun ts => (B x).bind fun y =>
        .sample h.coL.n fun e =>
        (linkO W cA h i (τ x) t ⟨t.r, fun _ => [], h.kL.e c, h.coL.e e⟩).bind fun en =>
        (linksL W cA h i (τ x) (ds.zip ts)).bind fun ls => G x (t :: ts) y (en :: ls))
      (Eqv.sample fun a => Eqv.sample fun c => Eqv.of_tie2 (Q := fun _ => True) ?_) (Eqv.of_eq ?_)
    · refine Tie.congr (g := fun ω =>
        (coinsCopiesS W h n).bind fun ds => A.bind fun x =>
        (tabO W S h.b₀ i (h.ri.e a) (cutS (2 ^ W.depth) (h.sl.e ω.1))).bind fun t =>
        (tabsL W S h i ds).bind fun ts => (B x).bind fun y =>
        (linkO W cA h i (τ x) t ⟨t.r, fun _ => [], h.kL.e c, h.coL.e ω.2⟩).bind fun en =>
        (linksL W cA h i (τ x) (ds.zip ts)).bind fun ls => G x (t :: ts) y (en :: ls)) ?_ fun ω =>
            ?_
      · exact Tie.left _ fun ds => Tie.left _ fun x => Tie.coin1 fun b => Tie.left _ fun t =>
          Tie.left _ fun ts => Tie.left _ fun y => Tie.coin2 fun e => Tie.same _ _
      · simp only [Tie.obind_assoc, OComp.bind]
        rfl
    · simp only [coinsCopiesS, coinsCopyS, tabsL, tabL, linksL, linkL, List.zip_cons_cons,
        Tie.obind_assoc, OComp.bind]

/-- **The scheme's committer has the run of the program that draws each secret coin just before the
part that reads it.** -/
theorem lateCommit : Spec.lateCommit := by
  intro I X lam L Bd aT aL W S cA h i
  refine Eqv.trans (c' := .sample h.ri.n fun a => .sample h.sl.n fun b => .sample h.kT.n fun c =>
    .sample h.coT.n fun e =>
    (coinsCopies W h (h.M + 1)).bind fun ds =>
      (tabO W S h.b₀ i (h.ri.e a) (cutS (2 ^ W.depth) (h.sl.e b))).bind fun t₁ =>
      (tabsO W S h i ds).bind fun ts =>
      ((proveTA W cA (fun _ => t₁.tree) (h.dressT (h.rvT (h.kT.e c)) (h.coT.e e)) h.capT
        t₁.tree.root (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
        (h.st.T i t₁.r t₁.seed (h.kT.e c))).bind fun a' =>
        .pure (shown (h.st.stopT i t₁.r t₁.seed) a')).bind fun y =>
      (linksO W cA h i t₁ (ds.zip ts)).bind fun ls =>
      .pure ((⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, y, ls⟩ : FullKey lam L aT aL),
        (⟨i, ts⟩ : Isk lam L Bd aT aL))) (Eqv.of_eq ?_) ?_
  · simp only [commitW, coinsC, commitAt, Tie.obind_assoc, OComp.bind]
  refine Eqv.trans (Eqv.sample fun a => Eqv.sample fun b => Eqv.sample fun c => Eqv.sample fun e =>
    late_copies W S cA h i (h.M + 1)
      (tabO W S h.b₀ i (h.ri.e a) (cutS (2 ^ W.depth) (h.sl.e b))) id
      (fun t₁ => (proveTA W cA (fun _ => t₁.tree) (h.dressT (h.rvT (h.kT.e c)) (h.coT.e e)) h.capT
        t₁.tree.root (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
        (h.st.T i t₁.r t₁.seed (h.kT.e c))).bind fun a' =>
        .pure (shown (h.st.stopT i t₁.r t₁.seed) a'))
      (fun t₁ ts y ls => .pure ((⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, y, ls⟩ : FullKey lam L aT aL),
        (⟨i, ts⟩ : Isk lam L Bd aT aL)))) ?_
  refine Eqv.trans (Eqv.sample fun a => Eqv.swap _ _ _) ?_
  refine Eqv.trans (c' := .sample h.ri.n fun a => .sample h.kT.n fun c =>
    (coinsCopiesS W h (h.M + 1)).bind fun ds =>
      .sample h.sl.n fun b =>
      (tabO W S h.b₀ i (h.ri.e a) (cutS (2 ^ W.depth) (h.sl.e b))).bind fun t₁ =>
      (tabsL W S h i ds).bind fun ts =>
      .sample h.coT.n fun e =>
      (proveTA W cA (fun _ => t₁.tree) (h.dressT (h.rvT (h.kT.e c)) (h.coT.e e)) h.capT
        t₁.tree.root (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
        (h.st.T i t₁.r t₁.seed (h.kT.e c))).bind fun a' =>
      (linksL W cA h i t₁ (ds.zip ts)).bind fun ls =>
      .pure ((⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, shown (h.st.stopT i t₁.r t₁.seed) a', ls⟩ :
        FullKey lam L aT aL), (⟨i, ts⟩ : Isk lam L Bd aT aL)))
    (Eqv.sample fun a => Eqv.sample fun c => Eqv.of_tie2 (Q := fun _ => True) ?_) (Eqv.of_eq ?_)
  · refine Tie.congr (g := fun ω =>
      (coinsCopiesS W h (h.M + 1)).bind fun ds =>
      (tabO W S h.b₀ i (h.ri.e a) (cutS (2 ^ W.depth) (h.sl.e ω.1))).bind fun t₁ =>
      (tabsL W S h i ds).bind fun ts =>
      (proveTA W cA (fun _ => t₁.tree) (h.dressT (h.rvT (h.kT.e c)) (h.coT.e ω.2)) h.capT
        t₁.tree.root (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
        (h.st.T i t₁.r t₁.seed (h.kT.e c))).bind fun a' =>
      (linksL W cA h i t₁ (ds.zip ts)).bind fun ls =>
      .pure ((⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, shown (h.st.stopT i t₁.r t₁.seed) a', ls⟩ :
        FullKey lam L aT aL), (⟨i, ts⟩ : Isk lam L Bd aT aL))) ?_ fun ω => ?_
    · exact Tie.left _ fun ds => Tie.coin1 fun b => Tie.left _ fun t₁ => Tie.left _ fun ts =>
        Tie.coin2 fun e => Tie.same _ _
    · simp only [Tie.obind_assoc, OComp.bind, id]
  · simp only [commitL, coinsCS, commitAtL, tabL, testL, Tie.obind_assoc, OComp.bind]

end OnBytes.TokenSide

#print axioms Rom.Eqv.of_tie2
#print axioms OnBytes.TokenSide.late_copies
#print axioms OnBytes.TokenSide.lateCommit
