-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/Normal.lean: THE SETUP OF THE HONEST SIDE THAT LAYS LATE, IN ITS NORMAL FORM: the
proof of Spec.lateNormal (Johnson/LateWorld/SpecSetup.lean). Definitions for this proof alone, and
theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

Both sides are sequences of maps from a table of answers to a law on (value, table of answers) (Ker,
Johnson/TokenSide2/Ker.lean). Two things are used.
  (1) The making of a table does not hang on its encoding randomness but through the bodies that are
      put in at the end (tabK, Johnson/LateWorld/TabList.lean).
  (2) So a table's encoding randomness, and a strategy's coins, are first read behind all tables. A
      draw can be made where its value is first read (Ker.late and its rules). On the other side the
      committer's draws of these coins are read by nobody, and a draw that nobody reads can be left
      out (Ker.late_const).
Each text is first written in the language of these maps (the lemmas _eq, _nil, _cons, _succ: each
holds by unfolding), with the draws of encoding randomness and of strategies' coins as draws that
are to be carried inward. Then the rules, used from left to right, bring both texts to one.

The copies: one induction on their number, with letters for what stands around the copies' parts
(normal_copies). It follows the pattern of late_copiesK (Johnson/TokenSide2/LateDraws.lean), and the
lemmas that write the honest setup's text in the language of these maps (nTabs_cons, lateLinks_cons,
coinsCopies_succ, coinsC_eq, lateCommit_eq) follow that file's lemmas of the like names.

Main names (namespace OnBytes.LateWorld).
  tabReal        a table, off its encoding randomness and (tree over fillings, seed).
  nTab, nTabs, nTest, nLink   the parts of the honest setup.
  normal_copies   the copies.
  lateNormal   THE THEOREM.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.TabList

set_option autoImplicit false

noncomputable section

namespace Rom.Ker
variable {σ α γ : Type}

/-- A draw that nobody reads. -/
theorem late_const (μ : PMF γ) (m : Ker σ α) : (late μ fun _ => m) = m :=
  funext fun _ => PMF.bind_const _ _

end Rom.Ker

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL)

/-! ## The parts -/

/-- A table, off its encoding randomness and (tree over fillings, seed). -/
def tabReal (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (o : TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed) :
    TabK lam L Bd aT aL :=
  ⟨r, realTree W b₀ (L.encodeIndex i r) o.1, o.2⟩

theorem realTabs_cons (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (rs : List L.EncodingRandomness)
    (o : TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed)
    (os : List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed)) :
    realTabs W b₀ i (r :: rs) (o :: os) = tabReal W b₀ i r o :: realTabs W b₀ i rs os := rfl

theorem realTabs_nil (b₀ : Bd) (i : I) : realTabs W b₀ i [] [] = [] := rfl

def nTab (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) : Ker (Tb W) (TabK lam L Bd aT aL) :=
  Ker.ofDefer mkTab (tabO W S h.b₀ i r (cutS (2 ^ W.depth) s))

def nTabs (i : I) (ds : List (DrawCopy lam L Bd aT aL h.KL)) :
    Ker (Tb W) (List (TabK lam L Bd aT aL)) :=
  Ker.ofDefer mkTab (tabsO W S h i ds)

def nTest (i : I) (t₁ : TabK lam L Bd aT aL) (κ : h.KT) (co : Coins lam (typedOracleCarrier L Bd aT aL)) :
    Ker (Tb W) (Option (OneProtocolProof lam (batTC L aT))) :=
  lateTA W cA (fun _ => t₁.tree) (h.dressT (h.rvT κ) co) h.capT t₁.tree.root
    (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r) (h.st.stopT i t₁.r t₁.seed) (h.st.T i t₁.r t₁.seed κ)

def nLink (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (κ : h.KL) (co : Coins lam (typedOracleCarrier L Bd aT aL)) :
    Ker (Tb W) (Option (OneProtocolProof lam (batLC L aL))) :=
  lateLA W cA (fun k => if k = 0 then t₁.tree else t₂.tree) (h.dressL (h.rvL κ) co) h.capL
    t₁.tree.root t₂.tree.root (L.recOf i t₁.r t₁.seed) (L.recOf i t₂.r t₂.seed)
    (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r) (h.st.stopL i (t₁.r, t₁.seed) (t₂.r, t₂.seed))
    (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) κ)

/-! ## The honest setup's text -/

theorem nTab_eq (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) :
    nTab W S h i r s = Ker.bind (tabFR W S h.b₀ (cutS (2 ^ W.depth) s)) fun o =>
      Ker.pure (tabReal W h.b₀ i r o) :=
  tabK W S h.b₀ i r _

theorem nTabs_nil (i : I) : nTabs W S h i [] = Ker.pure [] := Ker.ofDefer_pure _ _

theorem nTabs_cons (i : I) (d : DrawCopy lam L Bd aT aL h.KL)
    (ds : List (DrawCopy lam L Bd aT aL h.KL)) :
    nTabs W S h i (d :: ds) = Ker.bind (nTab W S h i d.r d.s) fun t =>
      Ker.bind (nTabs W S h i ds) fun ts => Ker.pure (t :: ts) := by
  unfold nTabs nTab
  rw [tabsO, Ker.ofDefer_bind]
  refine congrArg _ (funext fun t => ?_)
  rw [Ker.ofDefer_bind]
  exact congrArg _ (funext fun ts => Ker.ofDefer_pure _ _)

theorem lateLinks_nil (i : I) (t₁ : TabK lam L Bd aT aL) :
    lateLinks W cA h i t₁ [] = Ker.pure [] := rfl

theorem lateLinks_cons (i : I) (t₁ : TabK lam L Bd aT aL)
    (a : DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL)
    (l : List (DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL)) :
    lateLinks W cA h i t₁ (a :: l) = Ker.bind (nLink W cA h i t₁ a.2 a.1.κ a.1.co) fun o =>
      Ker.bind (lateLinks W cA h i t₁ l) fun ls =>
      Ker.pure ((a.2.tree.root, L.recOf i a.2.r a.2.seed, o) :: ls) :=
  funext fun _ => rfl

theorem coinsCopies_zero : Ker.ofLazy (coinsCopies W h 0) = Ker.pure [] := rfl

/-- The coins of a copy: its encoding randomness and its strategy's coins are to be carried inward.
-/
theorem coinsCopies_succ (n : ℕ) :
    Ker.ofLazy (coinsCopies W h (n + 1)) =
      Ker.late (unif (Fin (h.ri.n + 1))) fun a => Ker.draw (unif (Fin (h.sl.n + 1))) fun b =>
      Ker.late (unif (Fin (h.kL.n + 1))) fun c => Ker.draw (unif (Fin (h.coL.n + 1))) fun e =>
      Ker.bind (Ker.ofLazy (coinsCopies W h n)) fun ds =>
      Ker.pure ((⟨h.ri.e a, h.sl.e b, h.kL.e c, h.coL.e e⟩ : DrawCopy lam L Bd aT aL h.KL) ::
          ds) := by
  show Ker.ofLazy (OComp.sample h.ri.n fun a => .sample h.sl.n fun b => .sample h.kL.n fun c =>
    .sample h.coL.n fun e => OComp.bind (coinsCopies W h n) fun ds =>
      OComp.pure ((⟨h.ri.e a, h.sl.e b, h.kL.e c, h.coL.e e⟩ : DrawCopy lam L Bd aT aL h.KL) :: ds))
    = _
  simp only [Ker.ofLazy_sample, Ker.ofLazy_bind, Ker.ofLazy_pure, Ker.late_eq_draw]

theorem coinsC_eq :
    Ker.ofLazy (coinsC W h) =
      Ker.late (unif (Fin (h.ri.n + 1))) fun a => Ker.draw (unif (Fin (h.sl.n + 1))) fun b =>
      Ker.late (unif (Fin (h.kT.n + 1))) fun c => Ker.draw (unif (Fin (h.coT.n + 1))) fun e =>
      Ker.bind (Ker.ofLazy (coinsCopies W h (h.M + 1))) fun ds =>
      Ker.pure (⟨h.ri.e a, h.sl.e b, h.kT.e c, h.coT.e e, ds⟩ : DrawC lam L Bd aT aL h.KT
          h.KL) := by
  unfold coinsC
  simp only [Ker.ofLazy_sample, Ker.ofLazy_bind, Ker.ofLazy_pure, Ker.late_eq_draw]

theorem lateCommit_eq (i : I) :
    lateCommit W S cA h i = Ker.bind (Ker.ofLazy (coinsC W h)) fun d =>
      Ker.bind (nTab W S h i d.r d.s) fun t₁ => Ker.bind (nTabs W S h i d.copies) fun ts =>
      Ker.bind (nTest W cA h i t₁ d.κ d.co) fun y =>
      Ker.bind (lateLinks W cA h i t₁ (d.copies.zip ts)) fun ls =>
      Ker.pure ((⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, y, ls⟩ : FullKey lam L aT aL),
        (⟨i, ts⟩ : Isk lam L Bd aT aL)) :=
  funext fun T => by
    simp only [lateCommit, Ker.bind, Ker.pure, Ker.ofLazy, nTab, nTabs, nTest, Ker.ofDefer,
      PMF.bind_map, Function.comp_def]

/-! ## The normal form's text -/

theorem drawRs_zero {α : Type} (f : List L.EncodingRandomness → Ker (Tb W) α) :
    Ker.draw (drawRs h 0) f = f [] := Ker.draw_of_pure _ _

theorem drawRs_succ {α : Type} (n : ℕ) (f : List L.EncodingRandomness → Ker (Tb W) α) :
    Ker.draw (drawRs h (n + 1)) f = Ker.late (unif (Fin (h.ri.n + 1))) fun a =>
      Ker.draw (drawRs h n) fun rs => f (h.ri.e a :: rs) := by
  rw [drawRs, Ker.draw_of_bind, Ker.late_eq_draw]
  refine congrArg _ (funext fun a => ?_)
  rw [Ker.draw_of_bind]
  exact congrArg _ (funext fun rs => Ker.draw_of_pure _ _)

theorem testM_eq (i : I) (t₁ : TabK lam L Bd aT aL) (co : Coins lam (typedOracleCarrier L Bd aT aL)) :
    testM W cA h i t₁ co =
      Ker.late (unif (Fin (h.kT.n + 1))) fun c => nTest W cA h i t₁ (h.kT.e c) co := rfl

theorem linkM_eq (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (co : Coins lam (typedOracleCarrier L Bd aT aL)) :
    linkM W cA h i t₁ t₂ co =
      Ker.late (unif (Fin (h.kL.n + 1))) fun c => nLink W cA h i t₁ t₂ (h.kL.e c) co := rfl

theorem linksM_nil (i : I) (t₁ : TabK lam L Bd aT aL) : linksM W cA h i t₁ [] = Ker.pure [] := rfl

theorem linksM_cons (i : I) (t₁ : TabK lam L Bd aT aL)
    (a : Coins lam (typedOracleCarrier L Bd aT aL) × TabK lam L Bd aT aL)
    (l : List (Coins lam (typedOracleCarrier L Bd aT aL) × TabK lam L Bd aT aL)) :
    linksM W cA h i t₁ (a :: l) = Ker.bind (linkM W cA h i t₁ a.2 a.1) fun o =>
      Ker.bind (linksM W cA h i t₁ l) fun ls =>
      Ker.pure ((a.2.tree.root, L.recOf i a.2.r a.2.seed, o) :: ls) :=
  funext fun _ => rfl

theorem normal_eq (i : I) :
    (fun T => (phase1 W S h T).bind (contC W cA h i)) =
      Ker.bind (Ker.ofLazy (coinsC W h)) fun d =>
      Ker.bind (tabFR W S h.b₀ (cutS (2 ^ W.depth) d.s)) fun o₁ =>
      Ker.bind (tabsFR W S h.b₀ (d.copies.map fun d => cutS (2 ^ W.depth) d.s)) fun os =>
      Ker.late (unif (Fin (h.ri.n + 1))) fun a => Ker.draw (drawRs h os.length) fun rs =>
      Ker.bind (testM W cA h i (tabReal W h.b₀ i (h.ri.e a) o₁) d.co) fun y =>
      Ker.bind (linksM W cA h i (tabReal W h.b₀ i (h.ri.e a) o₁)
        ((d.copies.map fun d => d.co).zip (realTabs W h.b₀ i rs os))) fun ls =>
      Ker.pure ((⟨(tabReal W h.b₀ i (h.ri.e a) o₁).tree.root,
        L.recOf i (tabReal W h.b₀ i (h.ri.e a) o₁).r (tabReal W h.b₀ i (h.ri.e a) o₁).seed, y, ls⟩ :
        FullKey lam L aT aL), (⟨i, realTabs W h.b₀ i rs os⟩ : Isk lam L Bd aT aL)) :=
  funext fun T => by
    simp only [phase1, contC, contAt, Ker.bind, Ker.pure, Ker.draw, Ker.late, Ker.ofLazy,
      PMF.bind_bind, PMF.pure_bind]
    rfl

/-! ## The copies -/

/-- **The copies**: their tables built by the honest builder and their links at the coins drawn at
the start; or their trees over fillings, fresh encoding randomness behind all tables, and fresh
coins of the strategy at each link. -/
theorem normal_copies (i : I) : ∀ (n : ℕ) {α β γ : Type} (A : Ker (Tb W) α)
    (τ : α → TabK lam L Bd aT aL) (B : α → Ker (Tb W) β)
    (G : α → List (TabK lam L Bd aT aL) → β →
      List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) → Ker (Tb W) γ),
    (Ker.bind (Ker.ofLazy (coinsCopies W h n)) fun ds => Ker.bind A fun x =>
      Ker.bind (nTabs W S h i ds) fun ts => Ker.bind (B x) fun y =>
      Ker.bind (lateLinks W cA h i (τ x) (ds.zip ts)) fun ls => G x ts y ls) =
    Ker.bind (Ker.ofLazy (coinsCopies W h n)) fun ds => Ker.bind A fun x =>
      Ker.bind (tabsFR W S h.b₀ (ds.map fun d => cutS (2 ^ W.depth) d.s)) fun os =>
      Ker.draw (drawRs h os.length) fun rs => Ker.bind (B x) fun y =>
      Ker.bind (linksM W cA h i (τ x) ((ds.map fun d => d.co).zip (realTabs W h.b₀ i rs os)))
        fun ls => G x (realTabs W h.b₀ i rs os) y ls
  | 0, _, _, _, A, τ, B, G => by
    simp only [coinsCopies_zero, Ker.pure_bind, nTabs_nil, List.map_nil, tabsFR_nil,
        List.length_nil,
      drawRs_zero, realTabs_nil, List.zip_nil_left, lateLinks_nil, linksM_nil]
  | n + 1, α, β, γ, A, τ, B, G => by
    have key := fun (a : Fin (h.ri.n + 1)) (b : Fin (h.sl.n + 1)) (c : Fin (h.kL.n + 1))
        (e : Fin (h.coL.n + 1)) => normal_copies i n
      (Ker.bind A fun x => Ker.bind (tabFR W S h.b₀ (cutS (2 ^ W.depth) (h.sl.e b))) fun o =>
        Ker.pure (x, o))
      (fun p => τ p.1)
      (fun p => Ker.bind (B p.1) fun y =>
        Ker.bind (nLink W cA h i (τ p.1) (tabReal W h.b₀ i (h.ri.e a) p.2) (h.kL.e c) (h.coL.e e))
          fun o => Ker.pure (y, o))
      (fun p ts q ls => G p.1 (tabReal W h.b₀ i (h.ri.e a) p.2 :: ts) q.1
        (((tabReal W h.b₀ i (h.ri.e a) p.2).tree.root,
          L.recOf i (tabReal W h.b₀ i (h.ri.e a) p.2).r (tabReal W h.b₀ i (h.ri.e a) p.2).seed, q.2)
              ::
          ls))
    simp only [Ker.bind_assoc, Ker.pure_bind] at key
    -- first the claim for n copies, behind the first copy's four draws
    simp only [coinsCopies_succ, Ker.draw_bind, Ker.late_bind, Ker.bind_assoc, Ker.pure_bind,
      nTabs_cons, nTab_eq, List.zip_cons_cons, lateLinks_cons, key]
    -- then each draw to the place where it is first read; what nobody reads is left out
    simp only [List.map_cons, tabsFR_cons, List.length_cons, drawRs_succ, realTabs_cons,
      List.zip_cons_cons, linksM_cons, linkM_eq, Ker.draw_bind, Ker.late_bind, Ker.bind_assoc,
      Ker.pure_bind, Ker.late_comm, Ker.late_draw, Ker.late_const]

/-! ## The setup -/

/-- **The honest setup in its normal form.** -/
theorem lateNormal : Spec.lateNormal := by
  intro I X lam L Bd aT aL W S cA h i T
  refine congrFun (Eq.trans ?_ (normal_eq W S cA h i).symm) T
  have key := fun (a : Fin (h.ri.n + 1)) (b : Fin (h.sl.n + 1)) (c : Fin (h.kT.n + 1))
      (e : Fin (h.coT.n + 1)) => normal_copies W S cA h i (h.M + 1)
    (tabFR W S h.b₀ (cutS (2 ^ W.depth) (h.sl.e b)))
    (fun o => tabReal W h.b₀ i (h.ri.e a) o)
    (fun o => nTest W cA h i (tabReal W h.b₀ i (h.ri.e a) o) (h.kT.e c) (h.coT.e e))
    (fun o ts y ls => Ker.pure ((⟨(tabReal W h.b₀ i (h.ri.e a) o).tree.root,
      L.recOf i (tabReal W h.b₀ i (h.ri.e a) o).r (tabReal W h.b₀ i (h.ri.e a) o).seed, y, ls⟩ :
      FullKey lam L aT aL), (⟨i, ts⟩ : Isk lam L Bd aT aL)))
  simp only [lateCommit_eq, coinsC_eq, Ker.draw_bind, Ker.late_bind, Ker.bind_assoc, Ker.pure_bind,
    nTab_eq, key]
  simp only [testM_eq, Ker.draw_bind, Ker.late_bind, Ker.bind_assoc, Ker.pure_bind, Ker.late_comm,
    Ker.late_draw, Ker.late_const]

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.normal_copies
#print axioms OnBytes.LateWorld.lateNormal
