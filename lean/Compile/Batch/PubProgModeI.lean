-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubProgModeI.lean: from mode R of the challenger with a prover that leaves out work
that is never shown, to mode I of the challenger with the prover that does the work. Generic in the
two programs (mode R, mode I: Rom/Defer.lean).

The challengers VCBPG pq₁ and VCBPG pq₂ of Compile/Batch/PubProg.lean (the experiment of index
privacy, with a function of the key published at the setup), for two programs with flags:

  `SafeFProg W p pq`  pq obeys the rules of deferred programming, for all flags (`SafeProg`,
                      Compile/Batch/CloseProg.lean).
  `SkipFProg pq₁ pq₂`  pq₂ is pq₁ without work that is never shown, for all flags (`SkipProg`).
  `PubG.modeI_cpl`, `PubG.within₂`  Under `SafeFProg W p pq₁` and `SkipFProg pq₁ pq₂`: in mode I
                                    whole runs against the two challengers can be sampled together,
                                    with equal outputs; so, for an admissible adversary with at most
                                    n batches, the runs against VCBPG pq₂ keep the rules and the
                                    counts too.
  `PubG.hopOf`  Under the same two, generic in the bound: for every h with `HopB W p h`
                (Compile/Batch/SpecHop.lean: what one passage to fresh answers costs at the counts
                of the scheme), mode R of VCBPG pq₂ is within h t n (once) of mode I of VCBPG pq₁,
                for an admissible adversary with at most t queries and n batches.

So an analysis of the first prover that goes through mode I of its challenger serves the second
prover from there on, with the same simulator and the same bound.

Notation:
  the rules and the counts: `d.Within e M ℓ os` (Rom/Defer.lean): what a run may do at most: e o
    plain and M o marked evaluations of o; marked ones only at oracles of os, each charged to a
    token of at least ℓ o bits; no violation of the rules; here e, M, ℓ, os are eAllB W p n, mAllB W
    p n, (rulesB ..).bits, osBG (maxMoreB W)
  the rules; shown: the head of Rom/Defer.lean
  a flag: `FProg`: a prover's program with flags: pq k fr xs: the key with tokens, for which
    requests a proof string is made, the instances (Compile/Batch/PubProg.lean)
  `w`: a `Wd`: how the tokens of two programs correspond (Rom/Skip.lean)
  `W`: a `QueryLayout lam L`, the wire record (Iop/BatchWire.lean); `WP`: a `WireBP L`: the prover's data
    for the three protocols, and the enumeration of the encoding randomness (Iop/BatchWireP.lean)
  `pw`: IVK lam L → WKey lam L → V, an arbitrary function (the head of Compile/Batch/PubChall.lean);
    `i`: I, the index; `N₀`: number N₀ of tokens of the setup (`LeafGame.sess`,
    Compile/Batch/OverrunGen.lean)
-/
import Compile.Batch.PubProgReal
import Compile.Batch.CloseProg
import Compile.Batch.SpecHop

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Prob
open scoped ENNReal
open Compile.GlueB (GCall GAdm)
open Compile.Life2 (virt up chall_reply run_bind run_fresh0)
open Compile.Disc (nEv)
open Disc Disc.VirtO WithinD ModeI

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X}

def SafeFProg (W : QueryLayout lam L) (p : Params) (pq : FProg lam L W.K) : Prop :=
  ∀ fr, SafeProg W p fun k xs => pq k fr xs
def SkipFProg {K : ℕ} (pq₁ pq₂ : FProg lam L K) : Prop :=
  ∀ fr, SkipProg (fun k xs => pq₁ k fr xs) (fun k xs => pq₂ k fr xs)

namespace PubG

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (pw : IVK lam L → WKey lam L → V) (i : I)

/-- under `SafeFProg`, `Spec.InvD`: every step of the challenger keeps the invariant and the counts,
in both modes -/
theorem step {pq : FProg lam L W.K} (hP : SafeFProg W p pq) (m : Bool) (s : Option (IskH lam L × ℕ))
    (d : DSt (spec lam W.K L)) (c : GCall X Unit) (hI : Spec.InvD W p s d) :
    ∀ y ∈ (((VCBPG W WP p pw pq i).step s c).run m d).support,
      Spec.InvD W p y.1.2 y.2 ∧
      ∀ o,
        y.2.nPlain o ≤ d.nPlain o + callCostB (eCB W p) ePB c o ∧
        nEv y.2 o ≤ nEv d o + callCostB (mCB W p) (mPB W) c o := by
  have triv : ∀ (a : BInP V lam L)
          (y : (BInP V lam L × Option (IskH lam L × ℕ)) × DSt (spec lam W.K L)),
        y ∈ ((Step.pure (a, s) : St lam W.K L (BInP V lam L × Option (IskH lam L × ℕ))).run
            m d).support →
        Spec.InvD W p y.1.2 y.2 ∧
        ∀ o,
          y.2.nPlain o ≤ d.nPlain o + callCostB (eCB W p) ePB c o ∧
          nEv y.2 o ≤ nEv d o + callCostB (mCB W p) (mPB W) c o := by
    intro a y hy
    simp only [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hI, fun o => ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩⟩
  intro y hy
  rcases c with _ | b
  · rcases s with _ | k
    · rw [HopRPG.VCBP_setupG W WP p pw pq i, run_bind, PMF.mem_support_bind_iff] at hy
      obtain ⟨z, hz, hy⟩ := hy
      rw [run_fresh0] at hy
      simp only [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      obtain ⟨h1, h2⟩ := WorldB.setup (i := i) safeCB m d (tidy_of_none hI) z hz
      exact ⟨⟨h1, lt_of_le_of_lt (Nat.zero_le _) ((makes_Cp W WP p i).run m d z hz)⟩, h2⟩
    · exact triv _ y hy
  · rcases s with _ | ⟨k, N₀⟩
    · exact triv _ y hy
    · by_cases hb : hasOwn b = true
      · rw [HopRPG.VCBP_ownG W WP p pw pq i k N₀ b hb, run_fresh0,
          run_bind, PMF.mem_support_bind_iff] at hy
        obtain ⟨z, hz, hy⟩ := hy
        simp only [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        obtain ⟨h1, h2⟩ := Prog.session W p (hP (ownFlag b)) m k N₀ (reqs b) d hI.1 z hz
        exact ⟨⟨h1, hI.2⟩, h2⟩
      · rw [HopRPG.VCBP_noneG W WP p pw pq i k N₀ b (by simpa using hb)] at hy
        exact triv _ y hy

/-- under `SafeFProg`, for an admissible adversary: every run against the challenger stays within
the rules and the counts, in both modes -/
theorem within {pq : FProg lam L W.K} (hP : SafeFProg W p pq) (ok : Gen.Batch X Unit → Prop)
    {α : Type} (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (n : ℕ) (m : Bool)
    (hA : GAdm ok A false n) :
    ∀ x ∈ (interact ((VCBPG W WP p pw pq i).world m) A (none, DSt.init _)).support,
      x.2.2.Within (eAllB W p n) (mAllB W p n) (rulesB W.K L lam p).bits (osBG (maxMoreB W)) := by
  intro x hx
  obtain ⟨hI, hc⟩ := within_interactB (VCBPG W WP p pw pq i) m (Spec.InvD W p) (eCB W p)
    (mCB W p) ePB (mPB W) WithinD.invD_table (step W WP p pw i hP m) ok A false n none
    (DSt.init _) hA (Or.inl rfl) x hx
  have ht : TidyO (rulesB W.K L lam p) x.2.2 := by
    rcases hs : x.2.1 with _ | ⟨k, N₀⟩
    · rw [hs] at hI; exact tidy_of_none hI
    · rw [hs] at hI; exact hI.1.1
  refine withinO' _ _ _ _ _ _ ht (fun o ho => zeroBG I X lam L W p n o ho) (fun o => ?_) fun o => ?_
  · have := (hc o).1
    simpa [eAllB, DSt.init] using this
  · have := (hc o).2
    simpa [mAllB, DSt.init, nEv] using this

/-- the step of a batch with an own request (the statement takes in a batch without one): under the
hypotheses below, the steps of `VCBPG` with pq₁ and with pq₂ on the batch b, from the state
some (k, N₀), stand in `Skip` (Rom/Skip.lean) at w, with equal results that keep that state -/
theorem skip_batch {pq₁ pq₂ : FProg lam L W.K} (hS : SkipFProg pq₁ pq₂) (k : IskH lam L) (N₀ : ℕ)
    (b : Gen.Batch X Unit) (w : Wd) (hpos : 0 < N₀) (hh : ∀ u, IskTokB k u → u < N₀)
    (g₁ : N₀ ≤ w.n₁) (g₂ : N₀ ≤ w.n₂) (hid : ∀ a, a < N₀ → w.ρ a a) :
    Skip (fun _ a₁ a₂ => a₁ = a₂ ∧ a₁.2 = some (k, N₀)) w
      ((VCBPG W WP p pw pq₁ i).step (some (k, N₀)) (.batch b))
      ((VCBPG W WP p pw pq₂ i).step (some (k, N₀)) (.batch b)) := by
  by_cases hb : hasOwn b = true
  · rw [HopRPG.VCBP_ownG W WP p pw pq₁ i k N₀ b hb, HopRPG.VCBP_ownG W WP p pw pq₂ i k N₀ b hb]
    refine Skip.fresh 0 fun t₁ t₂ f₁ f₂ => ?_
    have base := hS (ownFlag b) k (reqs b) (Wd.same N₀) ⟨rfl, hpos⟩ fun lf hlf s s' hs =>
      ⟨⟨rfl, hh s (Or.inr ⟨lf, hlf, s, s', hs, Or.inl rfl⟩)⟩,
        ⟨rfl, hh s' (Or.inr ⟨lf, hlf, s, s', hs, Or.inr rfl⟩)⟩⟩
    have hv := Skip.virt N₀ (t₁ + 1 - N₀) (t₂ + 1 - N₀) base (Nat.le_refl _) (Nat.le_refl _)
    have hle : liftW N₀ (t₁ + 1 - N₀) (t₂ + 1 - N₀) (Wd.same N₀) ≤ w.pair t₁ t₂ :=
      { n₁ := by show N₀ + (t₁ + 1 - N₀) ≤ t₁ + 1; omega
        n₂ := by show N₀ + (t₂ + 1 - N₀) ≤ t₂ + 1; omega
        ρ := by
          rintro a c ⟨a', b', ⟨rfl, ha⟩, rfl, rfl⟩
          have e₁ : up N₀ (t₁ + 1 - N₀) a' = a' := if_pos ha
          have e₂ : up N₀ (t₂ + 1 - N₀) a' = a' := if_pos ha
          rw [e₁, e₂]
          exact Or.inl (hid a' ha)
        dd := by rintro a ⟨a', h, -⟩; exact h.elim
        sl := by rintro a c ⟨a', b', h, -⟩; exact h.elim }
    refine Skip.bind (hv.mono hle fun _ _ _ _ _ h => h) fun v a₁ a₂ h => ?_
    subst h
    exact .pure ⟨rfl, rfl⟩
  · rw [HopRPG.VCBP_noneG W WP p pw pq₁ i k N₀ b (by simpa using hb),
      HopRPG.VCBP_noneG W WP p pw pq₂ i k N₀ b (by simpa using hb)]
    exact .pure ⟨rfl, rfl⟩

/-- under `SafeFProg`, `SkipFProg`: whole runs against the two challengers, in mode I, can be
sampled together -/
theorem modeI_cpl {pq₁ pq₂ : FProg lam L W.K} (hP : SafeFProg W p pq₁) (hS : SkipFProg pq₁ pq₂)
    {α : Type} (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) :
    Cpl (fun x y => x.1 = y.1 ∧ RelW W p x.2 y.2)
      (interact ((VCBPG W WP p pw pq₁ i).world true) A (none, DSt.init _))
      (interact ((VCBPG W WP p pw pq₂ i).world true) A (none, DSt.init _)) := by
  refine interact_cpl ((VCBPG W WP p pw pq₁ i).world true) ((VCBPG W WP p pw pq₂ i).world true)
    (RelW W p) ?_ ?_ A (none, DSt.init _) (none, DSt.init _)
    (RelW.refl (τ := none) (show Spec.InvD W p none (DSt.init _) from Or.inl rfl))
  · intro s₁ s₂ o q h
    show Cpl _ ((lazyAnswer s₁.2.table o q).map _) ((lazyAnswer s₂.2.table o q).map _)
    rw [← h.table]
    refine Cpl.map _ _ (Cpl.diag _) fun a b hab => ?_
    subst hab
    exact ⟨rfl, h.setTable a.2⟩
  · rintro ⟨τ₁, d₁⟩ ⟨τ₂, d₂⟩ c ⟨hτ, hI, hm⟩
    have hτ' : τ₁ = τ₂ := hτ
    subst hτ'
    rw [chall_reply, chall_reply]
    have hst := step W WP p pw i hP true τ₁ d₁ c hI
    rcases c with _ | b
    · rcases τ₁ with _ | ⟨k, N₀⟩
      · have e : d₁ = d₂ := hm
        subst e
        refine Cpl.map _ _ ((Cpl.diag _).and_left hst) fun x y hxy => ?_
        obtain ⟨rfl, hI', -⟩ := hxy
        exact ⟨rfl, RelW.refl hI'⟩
      · exact Cpl.map _ _
            (Cpl.pure (R := fun x y => x.1 = y.1 ∧ RelW W p (x.1.2, x.2) (y.1.2, y.2))
              ⟨rfl, rfl, hI, hm⟩) fun x y hxy =>
          ⟨congrArg (fun z : BInP V lam L × Option (IskH lam L × ℕ) => z.1) hxy.1, hxy.2⟩
    · rcases τ₁ with _ | ⟨k, N₀⟩
      · exact Cpl.map _ _
            (Cpl.pure (R := fun x y => x.1 = y.1 ∧ RelW W p (x.1.2, x.2) (y.1.2, y.2))
              ⟨rfl, rfl, hI, hm⟩) fun x y hxy =>
          ⟨congrArg (fun z : BInP V lam L × Option (IskH lam L × ℕ) => z.1) hxy.1, hxy.2⟩
      · obtain ⟨w, hs, g₁, g₂, hid⟩ := hm
        have hsk :=
          (skip_batch W WP p pw i hS k N₀ b w hI.2 hI.1.2.2.2 g₁ g₂ hid).keep (Wd.le_refl w)
        refine Cpl.map _ _ ((hsk.run d₁ d₂ hs).and_left hst) fun x y hxy => ?_
        obtain ⟨⟨w', ⟨hw, heq, hk⟩, hs'⟩, hI', -⟩ := hxy
        exact ⟨congrArg (fun z : BInP V lam L × Option (IskH lam L × ℕ) => z.1) heq,
          RelW.mk_some hk
            (congrArg (fun z : BInP V lam L × Option (IskH lam L × ℕ) => z.2) heq).symm hI' w' hs'
            (g₁.trans hw.n₁) (g₂.trans hw.n₂) fun a ha => hw.ρ _ _ (hid a ha)⟩

/-- under the hypotheses below: every run against the second challenger, in mode I, keeps the rules
and the counts -/
theorem within₂ {pq₁ pq₂ : FProg lam L W.K} (hP : SafeFProg W p pq₁) (hS : SkipFProg pq₁ pq₂)
    (ok : Gen.Batch X Unit → Prop) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (n : ℕ) (hA : GAdm ok A false n) :
    ∀ x ∈ (interact ((VCBPG W WP p pw pq₂ i).world true) A (none, DSt.init _)).support,
      x.2.2.Within (eAllB W p n) (mAllB W p n) (rulesB W.K L lam p).bits (osBG (maxMoreB W)) := by
  intro y hy
  obtain ⟨x, hx, -, hr⟩ := (modeI_cpl W WP p pw i hP hS A).exists_left y hy
  have hw := within W WP p pw i hP ok A n true hA x hx
  obtain ⟨a, τ₁, d₁⟩ := x
  obtain ⟨b, τ₂, d₂⟩ := y
  obtain ⟨-, -, hm⟩ := hr
  rcases τ₁ with _ | ⟨k, N₀⟩
  · have e : d₁ = d₂ := hm
    exact e ▸ hw
  · obtain ⟨w, hs, -⟩ := hm
    exact hs.within hw

/-- Under the hypotheses below: mode R of the second challenger is within one passage to fresh
answers (`HopB`) of mode I of the first. -/
theorem hopOf {h : ℕ → ℕ → ℝ≥0∞} (hh : HopB W p h) {pq₁ pq₂ : FProg lam L W.K}
    (hP : SafeFProg W p pq₁) (hS : SkipFProg pq₁ pq₂) (ok : Gen.Batch X Unit → Prop) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (t n : ℕ)
    (hT : A.TotalBound t (n + 1)) (hA : GAdm ok A false n) :
    tv ((interact ((VCBPG W WP p pw pq₂ i).world false) A (none, DSt.init _)).map Prod.fst)
        ((interact ((VCBPG W WP p pw pq₁ i).world true) A (none, DSt.init _)).map Prod.fst) ≤
      h t n := by
  rw [Cpl.map_eq _ _ ((modeI_cpl W WP p pw i hP hS A).mono fun _ _ h => h.1)]
  exact hh n _ _ _ _ (VCBPG W WP p pw pq₂ i) none A t (n + 1)
    hT (within₂ W WP p pw i hP hS ok A n hA)

end PubG

end Compile.Batch
