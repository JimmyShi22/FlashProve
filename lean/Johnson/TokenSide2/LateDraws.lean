-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/LateDraws.lean: THE COMMITTER THAT LAYS LATE, WHICH DRAWS ALL ITS COINS FIRST
(lateCommit, Johnson/LateWorld/Defs.lean), IS THE SAME LAW WITH EACH SECRET COIN DRAWN JUST BEFORE
THE PART THAT READS IT (commitInward, Johnson/LateSide/Need.lean): the proof of Spec.lateDraws.

Lemmas of one step of a proof. This file states no goal of the release.

Both committers are sequences of maps from a table to a law on (value, table)
(Ker, Johnson/TokenSide2/Ker.lean). First each text is written in that language (the lemmas _eq,
_nil, _cons: each holds by unfolding). The secret draws (a table's salts, the coins of a compiled
run) are written as draws that are to be carried inward (Ker.late), the others as draws that stay
(Ker.draw). Then the rules of Johnson/TokenSide2/Ker.lean, used from left to right, carry each
secret draw to the first part that reads it, and the two texts are one.

The copies: one induction on their number, with letters for what stands around the copies' parts
(late_copiesK): A, what is run before the copies' tables; B, between the tables and the links; G, at
the end; τ, which table the links start from. It follows the pattern of late_copies
(Johnson/TokenSide2/LateProof.lean), which says the like of programs under one rule for all queries.

-/
import Johnson.LateSide.Need
import Johnson.TokenSide2.Ker

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.LateWorld
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL)

/-! ## The parts -/

/-- One table behind its salts: the scheme's builder, its leaves deferred; the log is dropped. -/
def kTab (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) : Ker (Tb W) (TabK lam L Bd aT aL) :=
  Ker.ofDefer mkTab (tabO W S h.b₀ i r (cutS (2 ^ W.depth) s))

/-- The copies' tables behind their salts. -/
def kTabs (i : I) (ds : List (DrawCopy lam L Bd aT aL h.KL)) :
    Ker (Tb W) (List (TabK lam L Bd aT aL)) :=
  Ker.ofDefer mkTab (tabsO W S h i ds)

/-- The proof on the first table behind its run's coins. -/
def kTest (i : I) (t₁ : TabK lam L Bd aT aL) (κ : h.KT) (co : Coins lam (typedOracleCarrier L Bd aT aL)) :
    Ker (Tb W) (Option (OneProtocolProof lam (batTC L aT))) :=
  lateTA W cA (fun _ => t₁.tree) (h.dressT (h.rvT κ) co) h.capT t₁.tree.root
    (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r) (h.st.stopT i t₁.r t₁.seed) (h.st.T i t₁.r t₁.seed κ)

/-- One copy's link proof behind its run's coins. -/
def kLink (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (κ : h.KL) (co : Coins lam (typedOracleCarrier L Bd aT aL)) :
    Ker (Tb W) (Option (OneProtocolProof lam (batLC L aL))) :=
  lateLA W cA (fun k => if k = 0 then t₁.tree else t₂.tree) (h.dressL (h.rvL κ) co) h.capL
    t₁.tree.root t₂.tree.root (L.recOf i t₁.r t₁.seed) (L.recOf i t₂.r t₂.seed)
    (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r) (h.st.stopL i (t₁.r, t₁.seed) (t₂.r, t₂.seed))
    (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) κ)

/-! ## The text that draws all coins first -/

theorem kTabs_nil (i : I) : kTabs W S h i [] = Ker.pure [] := Ker.ofDefer_pure _ _

theorem kTabs_cons (i : I) (d : DrawCopy lam L Bd aT aL h.KL)
    (ds : List (DrawCopy lam L Bd aT aL h.KL)) :
    kTabs W S h i (d :: ds) = Ker.bind (kTab W S h i d.r d.s) fun t =>
      Ker.bind (kTabs W S h i ds) fun ts => Ker.pure (t :: ts) := by
  unfold kTabs kTab
  rw [tabsO, Ker.ofDefer_bind]
  refine congrArg _ (funext fun t => ?_)
  rw [Ker.ofDefer_bind]
  exact congrArg _ (funext fun ts => Ker.ofDefer_pure _ _)

theorem lateLinks_nil (i : I) (t₁ : TabK lam L Bd aT aL) :
    lateLinks W cA h i t₁ [] = Ker.pure [] := rfl

theorem lateLinks_cons (i : I) (t₁ : TabK lam L Bd aT aL)
    (a : DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL)
    (l : List (DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL)) :
    lateLinks W cA h i t₁ (a :: l) = Ker.bind (kLink W cA h i t₁ a.2 a.1.κ a.1.co) fun o =>
      Ker.bind (lateLinks W cA h i t₁ l) fun ls =>
      Ker.pure ((a.2.tree.root, L.recOf i a.2.r a.2.seed, o) :: ls) :=
  funext fun _ => rfl

theorem coinsCopies_zero : Ker.ofLazy (coinsCopies W h 0) = Ker.pure [] := rfl

theorem coinsCopies_succ (n : ℕ) :
    Ker.ofLazy (coinsCopies W h (n + 1)) =
      Ker.draw (unif (Fin (h.ri.n + 1))) fun a => Ker.late (unif (Fin (h.sl.n + 1))) fun b =>
      Ker.draw (unif (Fin (h.kL.n + 1))) fun c => Ker.late (unif (Fin (h.coL.n + 1))) fun e =>
      Ker.bind (Ker.ofLazy (coinsCopies W h n)) fun ds =>
      Ker.pure
        ((⟨h.ri.e a, h.sl.e b, h.kL.e c, h.coL.e e⟩ : DrawCopy lam L Bd aT aL h.KL) :: ds) := by
  show Ker.ofLazy (OComp.sample h.ri.n fun a => .sample h.sl.n fun b => .sample h.kL.n fun c =>
    .sample h.coL.n fun e => OComp.bind (coinsCopies W h n) fun ds =>
      OComp.pure ((⟨h.ri.e a, h.sl.e b, h.kL.e c, h.coL.e e⟩ : DrawCopy lam L Bd aT aL h.KL) :: ds))
    = _
  simp only [Ker.ofLazy_sample, Ker.ofLazy_bind, Ker.ofLazy_pure, Ker.late_eq_draw]

theorem coinsC_eq :
    Ker.ofLazy (coinsC W h) =
      Ker.draw (unif (Fin (h.ri.n + 1))) fun a => Ker.late (unif (Fin (h.sl.n + 1))) fun b =>
      Ker.draw (unif (Fin (h.kT.n + 1))) fun c => Ker.late (unif (Fin (h.coT.n + 1))) fun e =>
      Ker.bind (Ker.ofLazy (coinsCopies W h (h.M + 1))) fun ds =>
      Ker.pure
        (⟨h.ri.e a, h.sl.e b, h.kT.e c, h.coT.e e, ds⟩ : DrawC lam L Bd aT aL h.KT h.KL) := by
  unfold coinsC
  simp only [Ker.ofLazy_sample, Ker.ofLazy_bind, Ker.ofLazy_pure, Ker.late_eq_draw]

theorem lateCommit_eq (i : I) :
    lateCommit W S cA h i = Ker.bind (Ker.ofLazy (coinsC W h)) fun d =>
      Ker.bind (kTab W S h i d.r d.s) fun t₁ => Ker.bind (kTabs W S h i d.copies) fun ts =>
      Ker.bind (kTest W cA h i t₁ d.κ d.co) fun y =>
      Ker.bind (lateLinks W cA h i t₁ (d.copies.zip ts)) fun ls =>
      Ker.pure ((⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, y, ls⟩ : FullKey lam L aT aL),
        (⟨i, ts⟩ : Isk lam L Bd aT aL)) :=
  funext fun T => by
    simp only [lateCommit, Ker.bind, Ker.pure, Ker.ofLazy, kTab, kTabs, kTest, Ker.ofDefer,
      PMF.bind_map, Function.comp_def]

/-! ## The text that draws each secret coin just before the part that reads it -/

theorem tabInward_eq (i : I) (r : L.EncodingRandomness) :
    tabInward W S h i r =
      Ker.late (unif (Fin (h.sl.n + 1))) fun b => kTab W S h i r (h.sl.e b) := rfl

theorem tabsInward_nil (i : I) : tabsInward W S h i [] = Ker.pure [] := rfl

theorem tabsInward_cons (i : I) (d : DrawCopyD L h.KL) (ds : List (DrawCopyD L h.KL)) :
    tabsInward W S h i (d :: ds) = Ker.bind (tabInward W S h i d.r) fun t =>
      Ker.bind (tabsInward W S h i ds) fun ts => Ker.pure (t :: ts) :=
  funext fun _ => rfl

theorem testInward_eq (i : I) (t₁ : TabK lam L Bd aT aL) (κ : h.KT) :
    testInward W cA h i t₁ κ =
      Ker.late (unif (Fin (h.coT.n + 1))) fun e => kTest W cA h i t₁ κ (h.coT.e e) := rfl

theorem linkInward_eq (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (κ : h.KL) :
    linkInward W cA h i t₁ t₂ κ =
      Ker.late (unif (Fin (h.coL.n + 1))) fun e => kLink W cA h i t₁ t₂ κ (h.coL.e e) := rfl

theorem linksInward_nil (i : I) (t₁ : TabK lam L Bd aT aL) :
    linksInward W cA h i t₁ [] = Ker.pure [] := rfl

theorem linksInward_cons (i : I) (t₁ : TabK lam L Bd aT aL)
    (a : DrawCopyD L h.KL × TabK lam L Bd aT aL)
    (l : List (DrawCopyD L h.KL × TabK lam L Bd aT aL)) :
    linksInward W cA h i t₁ (a :: l) = Ker.bind (linkInward W cA h i t₁ a.2 a.1.κ) fun o =>
      Ker.bind (linksInward W cA h i t₁ l) fun ls =>
      Ker.pure ((a.2.tree.root, L.recOf i a.2.r a.2.seed, o) :: ls) :=
  funext fun _ => rfl

theorem commitAtInward_eq (i : I) (d : DrawCD L h.KT h.KL) :
    commitAtInward W S cA h i d = Ker.bind (tabInward W S h i d.r) fun t₁ =>
      Ker.bind (tabsInward W S h i d.copies) fun ts =>
      Ker.bind (testInward W cA h i t₁ d.κ) fun y =>
      Ker.bind (linksInward W cA h i t₁ (d.copies.zip ts)) fun ls =>
      Ker.pure ((⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, y, ls⟩ : FullKey lam L aT aL),
        (⟨i, ts⟩ : Isk lam L Bd aT aL)) :=
  funext fun _ => rfl

theorem commitInward_eq (i : I) :
    commitInward W S cA h i = Ker.draw (unif (Fin (h.ri.n + 1))) fun a =>
      Ker.draw (unif (Fin (h.kT.n + 1))) fun c => Ker.draw (copiesInward h (h.M + 1)) fun ds =>
      commitAtInward W S cA h i ⟨h.ri.e a, h.kT.e c, ds⟩ :=
  funext fun _ => rfl

/-! ## The copies -/

/-- **The copies**: their coins all first, or each secret coin just before the part that reads it.
-/
theorem late_copiesK (i : I) : ∀ (n : ℕ) {α β γ : Type} (A : Ker (Tb W) α)
    (τ : α → TabK lam L Bd aT aL) (B : α → Ker (Tb W) β)
    (G : α → List (TabK lam L Bd aT aL) → β →
      List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) → Ker (Tb W) γ),
    (Ker.bind (Ker.ofLazy (coinsCopies W h n)) fun ds => Ker.bind A fun x =>
      Ker.bind (kTabs W S h i ds) fun ts => Ker.bind (B x) fun y =>
      Ker.bind (lateLinks W cA h i (τ x) (ds.zip ts)) fun ls => G x ts y ls) =
    Ker.draw (copiesInward h n) fun ds => Ker.bind A fun x =>
      Ker.bind (tabsInward W S h i ds) fun ts => Ker.bind (B x) fun y =>
      Ker.bind (linksInward W cA h i (τ x) (ds.zip ts)) fun ls => G x ts y ls
  | 0, _, _, _, A, τ, B, G => by
    simp only [coinsCopies_zero, copiesInward, Ker.draw_of_pure, Ker.pure_bind, kTabs_nil,
      tabsInward_nil, List.zip_nil_left, lateLinks_nil, linksInward_nil]
  | n + 1, α, β, γ, A, τ, B, G => by
    have key : ∀ (a : Fin (h.ri.n + 1)) (b : Fin (h.sl.n + 1)) (c : Fin (h.kL.n + 1))
        (e : Fin (h.coL.n + 1)),
        (Ker.bind (Ker.ofLazy (coinsCopies W h n)) fun ds => Ker.bind A fun x =>
          Ker.bind (kTab W S h i (h.ri.e a) (h.sl.e b)) fun t =>
          Ker.bind (kTabs W S h i ds) fun ts => Ker.bind (B x) fun y =>
          Ker.bind (kLink W cA h i (τ x) t (h.kL.e c) (h.coL.e e)) fun o =>
          Ker.bind (lateLinks W cA h i (τ x) (ds.zip ts)) fun ls =>
          G x (t :: ts) y ((t.tree.root, L.recOf i t.r t.seed, o) :: ls)) =
        Ker.draw (copiesInward h n) fun ds => Ker.bind A fun x =>
          Ker.bind (kTab W S h i (h.ri.e a) (h.sl.e b)) fun t =>
          Ker.bind (tabsInward W S h i ds) fun ts => Ker.bind (B x) fun y =>
          Ker.bind (kLink W cA h i (τ x) t (h.kL.e c) (h.coL.e e)) fun o =>
          Ker.bind (linksInward W cA h i (τ x) (ds.zip ts)) fun ls =>
          G x (t :: ts) y ((t.tree.root, L.recOf i t.r t.seed, o) :: ls) := by
      intro a b c e
      have ih := late_copiesK i n
        (Ker.bind A fun x => Ker.bind (kTab W S h i (h.ri.e a) (h.sl.e b)) fun t => Ker.pure (x, t))
        (fun p => τ p.1)
        (fun p => Ker.bind (B p.1) fun y =>
          Ker.bind (kLink W cA h i (τ p.1) p.2 (h.kL.e c) (h.coL.e e)) fun o => Ker.pure (y, o))
        (fun p ts q ls =>
          G p.1 (p.2 :: ts) q.1 ((p.2.tree.root, L.recOf i p.2.r p.2.seed, q.2) :: ls))
      simpa only [Ker.bind_assoc, Ker.pure_bind] using ih
    -- first the claim for n copies, behind the first copy's four draws; then the secret draws
    simp only [coinsCopies_succ, Ker.draw_bind, Ker.late_bind, Ker.bind_assoc, Ker.pure_bind,
      kTabs_cons, List.zip_cons_cons, lateLinks_cons, key]
    simp only [copiesInward, Ker.draw_of_bind, Ker.draw_of_pure, tabsInward_cons, tabInward_eq,
      linksInward_cons, linkInward_eq, List.zip_cons_cons, Ker.late_bind, Ker.bind_assoc,
      Ker.pure_bind, Ker.late_comm, Ker.late_draw]

/-! ## The committer -/

/-- **The committer that lays late is the same law with each secret coin drawn just before the part
that reads it.** -/
theorem lateDraws : Spec.lateDraws := by
  intro I X lam L Bd aT aL W S cA h i T
  refine congrFun ?_ T
  have key : ∀ (a : Fin (h.ri.n + 1)) (b : Fin (h.sl.n + 1)) (c : Fin (h.kT.n + 1))
      (e : Fin (h.coT.n + 1)), _ = _ := fun a b c e =>
    late_copiesK W S cA h i (h.M + 1) (kTab W S h i (h.ri.e a) (h.sl.e b)) id
      (fun t₁ => kTest W cA h i t₁ (h.kT.e c) (h.coT.e e))
      (fun t₁ ts y ls => Ker.pure ((⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, y, ls⟩ :
        FullKey lam L aT aL), (⟨i, ts⟩ : Isk lam L Bd aT aL)))
  simp only [id] at key
  simp only [lateCommit_eq, coinsC_eq, Ker.draw_bind, Ker.late_bind, Ker.bind_assoc, Ker.pure_bind,
    key]
  simp only [commitInward_eq, commitAtInward_eq, tabInward_eq, testInward_eq, Ker.late_bind,
    Ker.late_comm, Ker.late_draw]

end OnBytes.LateSide

#print axioms OnBytes.LateSide.late_copiesK
#print axioms OnBytes.LateSide.lateDraws
