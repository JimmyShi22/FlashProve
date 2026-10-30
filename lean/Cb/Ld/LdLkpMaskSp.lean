-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskSp.lean: chains of masked blocks, with the claims between the blocks taken as "what
the honest run so far has made true".
This file is about the sequential composition of reductions.

Definitions, statements and proofs. Glue; no protocol of its own.

Why: in a long chain a block's claim may rest on rows that a much earlier block has left (they ride
along). The rule for chains (Cb/Ld/LdLkpMaskChain.lean) asks for a claim before each block that (a)
gives the block's own claim, (b) gives the next claim, (c) reads no mask of this or a later block.
Here the claim before a block is defined from the claim C with which the chain starts:
  `D.sp C x' k`: "x' is the explicit part that the honest messages at the entries k lead to, from an
    explicit part x with C x k, at some verifier messages".
Then (b) holds by definition; (c) follows from: the chain's first claim reads no mask of the chain,
and no block's messages read a later block's masks (`mjst_sp`); (a) follows from completeness, which
`mjsp_sound` takes among its hypotheses.

Main names, each theorem under the hypotheses of its statement:
  `MjStab C S`: the claim C does not read the entries in S.
  `D.MReads S`: the messages of D depend on the entries in S only.
  `D.Link H rdi rdo Sr Sw C`: the block, started with the claim C, fits (Cb/Ld/LdLkpMaskChain.lean:
    so it has the item "masked messages"); its messages read Sr; its own masks lie in Sw.
  `mjl_seq`: two in a row: the second is started with `D₁.sp C`. Asked: Sr₁ and Sw₂ are disjoint; C
    does not read Sw₂.
  `mjsp_sound`: if C gives "the joint A holds of the entries" and the block is complete from A to B,
    then `D.sp C` gives "the joint B holds of the entries".
  `mjl_mm`: under `h`: `Honest.MM` (Ior/Masked.lean) of H, at the data `(D.narrow C).data rdi`: D
    with the claim C.

n + 1 blocks in a row: `mjl_chain`, Cb/Ld/LdLkpMaskSpChain.lean.

Limits: what the head of Cb/Ld/LdLkpMaskChain.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskKit

set_option autoImplicit false

namespace Cb
open Iop IOR Prob Hiop

/-- The claim C does not read the entries in S. -/
def MjStab {E J X : Type} (C : X → (J → E) → Prop) (S : J → Prop) : Prop :=
  ∀ x k k', (∀ j, ¬ S j → k j = k' j) → C x k → C x k'

namespace MJ
variable {E J : Type} {Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}

/-- The messages depend on the entries in S only. -/
def MReads (D : MJ E J R) (S : J → Prop) : Prop :=
  ∀ k k' x ρ, (∀ j, S j → k j = k' j) → D.msg k x ρ = D.msg k' x ρ

/-- What the honest run of the block makes of a claim. -/
def sp (D : MJ E J R) (C : Xi → (J → E) → Prop) : Xo → (J → E) → Prop := fun x' k =>
  ∃ x ρ, C x k ∧ x' = D.nxt x (D.msg k x ρ) ρ

/-- The block, started with the claim C. -/
structure Link (D : MJ E J R) (H : R.Honest Wi Wo) (rdi : Wi → J → E) (rdo : Wo → J → E)
    (Sr Sw : J → Prop) (C : Xi → (J → E) → Prop) : Prop where
  fits   : (D.narrow C).Fits H rdi rdo
  reads  : D.MReads Sr
  writes : D.Writes Sw

end MJ

section Rules
variable {E J : Type} {X₁ X₂ X₃ Xi Xi' Xo Xo' : Type}
  {E₁ E₂ E₃ Ei Ei' Eo Eo' : ExtSpec} {W₁ W₂ W₃ Wi Wi' Wo Wo' : Type}

theorem mjst_mono {X : Type} {C : X → (J → E) → Prop} {S S' : J → Prop}
    (h : MjStab C S) (hs : ∀ j, S' j → S j) : MjStab C S' :=
  fun x k k' hk => h x k k' fun j hj => hk j fun hj' => hj (hs j hj')

theorem mjst_or {X : Type} {C : X → (J → E) → Prop} {S S' : J → Prop}
    (h : MjStab C S) (h' : MjStab C S') :
    MjStab C fun j => S j ∨ S' j := by
  classical
  intro x k k' hk hc
  have h1 : C x (fun j => if S j then k' j else k j) := h x k _ (fun j hj => by simp [hj]) hc
  refine h' x _ k' (fun j hj => ?_) h1
  by_cases hs : S j
  · simp [hs]
  · simp only [hs, if_false]
    exact hk j fun ho => ho.elim hs hj

theorem mjst_sp {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {C : Xi → (J → E) → Prop} {S Sr : J → Prop}
    (hC : MjStab C S) (hR : D.MReads Sr) (hd : ∀ j, Sr j → ¬ S j) : MjStab (D.sp C) S := by
  rintro x' k k' hk ⟨x, ρ, hc, rfl⟩
  exact ⟨x, ρ, hC x k k' hk hc, by rw [hR k k' x ρ fun j hj => hk j (hd j hj)]⟩

theorem mjsp_seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} (D₁ : MJ E J R₁) (D₂ : MJ E J R₂)
    (C : X₁ → (J → E) → Prop) (x' : X₃) (k : J → E) :
    (D₁.seq D₂).sp C x' k ↔ D₂.sp (D₁.sp C) x' k := by
  constructor
  · rintro ⟨x, ρ, hc, rfl⟩
    refine ⟨D₁.nxt x (D₁.msg k x (Rho.fst ρ)) (Rho.fst ρ), Rho.snd (s := R₁.shape) ρ,
      ⟨x, Rho.fst ρ, hc, rfl⟩, ?_⟩
    show D₂.nxt (D₁.nxt x (Plains.fst (Plains.app _ _)) (Rho.fst ρ))
        (Plains.snd (s := R₁.shape) (Plains.app _ _)) (Rho.snd (s := R₁.shape) ρ) = _
    rw [Plains.fst_app, Plains.snd_app]
  · rintro ⟨_, ρ₂, ⟨x, ρ₁, hc, rfl⟩, rfl⟩
    refine ⟨x, Rho.app ρ₁ ρ₂, hc, ?_⟩
    show _ = D₂.nxt (D₁.nxt x (Plains.fst (Plains.app _ _)) (Rho.fst (Rho.app ρ₁ ρ₂)))
        (Plains.snd (s := R₁.shape) (Plains.app _ _)) (Rho.snd (s := R₁.shape) (Rho.app ρ₁ ρ₂))
    rw [Plains.fst_app, Plains.snd_app, Rho.fst_app, Rho.snd_app]

theorem mjl_mono {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {H : R.Honest Wi Wo} {rdi : Wi → J → E}
    {rdo : Wo → J → E} {Sr Sw Sr' Sw' : J → Prop} {C : Xi → (J → E) → Prop}
    (h : D.Link H rdi rdo Sr Sw C) (hr : ∀ j, Sr j → Sr' j) (hw : ∀ j, Sw j → Sw' j) :
    D.Link H rdi rdo Sr' Sw' C :=
  ⟨h.fits, fun k k' x ρ hk => h.reads k k' x ρ fun j hj => hk j (hr j hj),
    fun M k j hj => h.writes M k j fun hj' => hj (hw j hj')⟩

/-- A stronger first claim, if it does not read `Sw`, in which the own masks lie. -/
theorem mjl_weaken {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {H : R.Honest Wi Wo} {rdi : Wi → J → E}
    {rdo : Wo → J → E} {Sr Sw : J → Prop} {C C' : Xi → (J → E) → Prop}
    (h : D.Link H rdi rdo Sr Sw C) (hc : ∀ x k, C' x k → C x k) (hs : MjStab C' Sw) :
    D.Link H rdi rdo Sr Sw C' :=
  ⟨mj_narrow E J _ _ _ _ R _ _ H (D.narrow C) rdi rdo C' h.fits hc fun x k M hk =>
      hs x k _ (fun j hj => (h.writes M k j hj).symm) hk,
    h.reads, h.writes⟩

/-- Two in a row. -/
theorem mjl_seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {H₁ : R₁.Honest W₁ W₂}
    {H₂ : R₂.Honest W₂ W₃} {D₁ : MJ E J R₁} {D₂ : MJ E J R₂} {rd₁ : W₁ → J → E} {rd₂ : W₂ → J → E}
    {rd₃ : W₃ → J → E} {Sr₁ Sw₁ Sr₂ Sw₂ : J → Prop} {C : X₁ → (J → E) → Prop}
    (h₁ : D₁.Link H₁ rd₁ rd₂ Sr₁ Sw₁ C) (h₂ : D₂.Link H₂ rd₂ rd₃ Sr₂ Sw₂ (D₁.sp C))
    (hd : ∀ j, Sr₁ j → ¬ Sw₂ j) (hC : MjStab C Sw₂) :
    (D₁.seq D₂).Link (H₁.seq H₂) rd₁ rd₃ (fun j => Sr₁ j ∨ Sr₂ j) (fun j => Sw₁ j ∨ Sw₂ j) C := by
  refine ⟨mj_seq E J _ _ _ _ _ _ _ _ _ R₁ R₂ H₁ H₂ (D₁.narrow C) (D₂.narrow (D₁.sp C))
      rd₁ rd₂ rd₃ h₁.fits h₂.fits
      ⟨fun M k x ρ => h₁.reads _ _ x ρ fun j hj => h₂.writes M k j (hd j hj),
        fun x k M hk => hC x k _ (fun j hj => (h₂.writes M k j hj).symm) hk⟩
      fun k x ρ hk => ⟨x, ρ, hk, rfl⟩,
    fun k k' x ρ hk => ?_,
    fun M k j hj => ?_⟩
  · show Plains.app (D₁.msg k x (Rho.fst ρ))
        (D₂.msg k (D₁.nxt x (D₁.msg k x (Rho.fst ρ)) (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ)) =
      Plains.app (D₁.msg k' x (Rho.fst ρ))
        (D₂.msg k' (D₁.nxt x (D₁.msg k' x (Rho.fst ρ)) (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ))
    rw [h₁.reads k k' x _ fun j hj => hk j (Or.inl hj),
      h₂.reads k k' _ _ fun j hj => hk j (Or.inr hj)]
  · show D₂.put M.2 (D₁.put M.1 k) j = k j
    rw [h₂.writes M.2 _ j fun h => hj (Or.inr h), h₁.writes M.1 k j fun h => hj (Or.inl h)]

theorem mjsp_post {R : IOR Xi Ei Xo Eo} (D : MJ E J R) (f : Xo → Option Xo') (g : ExtMap Eo Eo')
    (φ : Xo → Xo') (C : Xi → (J → E) → Prop) (x' : Xo') (k : J → E) :
    (D.post f g φ).sp C x' k ↔ ∃ x'', D.sp C x'' k ∧ x' = φ x'' :=
  ⟨fun ⟨x, ρ, hc, e⟩ => ⟨_, ⟨x, ρ, hc, rfl⟩, e⟩,
    fun ⟨_, ⟨x, ρ, hc, e'⟩, e⟩ => ⟨x, ρ, hc, by rw [e, e']; rfl⟩⟩

theorem mjsp_pre {R : IOR Xi Ei Xo Eo} (D : MJ E J R) (f : Xi' → Option Xi) (g : ExtMap Ei' Ei)
    (φ : Xi' → Xi) (C : Xi' → (J → E) → Prop) (x' : Xo) (k : J → E) :
    (D.pre f g φ).sp C x' k ↔ D.sp (fun x k => ∃ x₀, C x₀ k ∧ x = φ x₀) x' k :=
  ⟨fun ⟨x, ρ, hc, e⟩ => ⟨φ x, ρ, ⟨x, hc, rfl⟩, e⟩,
    fun ⟨_, ρ, ⟨x, hc, e'⟩, e⟩ => ⟨x, ρ, hc, by rw [e, e']; rfl⟩⟩

theorem mjl_post {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {H : R.Honest Wi Wo} {rdi : Wi → J → E}
    {rdo : Wo → J → E} {Sr Sw : J → Prop} {C : Xi → (J → E) → Prop} (h : D.Link H rdi rdo Sr Sw C)
    (f : Xo → Option Xo') (g : ExtMap Eo Eo') (φ : Xo → Xo') (m : Xo × Wo → Xo' × Wo')
    (rdo' : Wo' → J → E) (h1 : ∀ o, (m o).1 = φ o.1) (h2 : ∀ o, rdo' (m o).2 = rdo o.2) :
    (D.post f g φ).Link (H.post f g m) rdi rdo' Sr Sw C := by
  have hr : ∀ w x c ρ, ((H.post f g m).strat w x c).run ρ =
      (((H.strat w x c).run ρ).1, m ((H.strat w x c).run ρ).2) :=
    fun w x c ρ => Strat.run_map m (H.strat w x c) ρ
  refine ⟨⟨mm_post _ _ _ _ _ _ R _ _ _ H ((D.narrow C).data rdi) f g m h.fits.mm,
      fun w x c ρ => ?_, fun w x c ρ => ?_⟩,
    h.reads, h.writes⟩
  · rw [hr, h2]
    exact h.fits.same w x c ρ
  · rw [hr, h1]
    exact congrArg φ (h.fits.hand w x c ρ)

theorem mjl_pre {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {H : R.Honest Wi Wo} {rdi : Wi → J → E}
    {rdo : Wo → J → E} {Sr Sw : J → Prop} {C : Xi' → (J → E) → Prop} (f : Xi' → Option Xi)
    (g : ExtMap Ei' Ei) (φ : Xi' → Xi)
    (h : D.Link H rdi rdo Sr Sw fun x k => ∃ x₀, C x₀ k ∧ x = φ x₀) (hs : MjStab C Sw)
    (m : Xi' × Wi' → Xi × Wi) (rdi' : Wi' → J → E) (h1 : ∀ x w, (m (x, w)).1 = φ x)
    (h2 : ∀ x w, rdi (m (x, w)).2 = rdi' w) :
    (D.pre f g φ).Link (H.pre f g m) rdi' rdo Sr Sw C := by
  refine ⟨⟨⟨h.fits.mm.noOrc,
        fun w x => h.fits.mm.free (m (x, w)).2 (m (x, w)).1,
        fun w x c ρ => ?_, fun x k M hk => ?_,
        fun k x ρ hk => h.fits.mm.law k (φ x) ρ ⟨x, hk, rfl⟩⟩,
      fun w x c ρ => ?_, fun w x c ρ => ?_⟩,
    fun k k' x ρ => h.reads k k' (φ x) ρ,
    h.writes⟩
  · show ((H.strat (m (x, w)).2 (m (x, w)).1 c).run ρ).1.plains = D.msg (rdi' w) (φ x) ρ
    rw [← h1 x w, ← h2 x w]
    exact h.fits.mm.run _ _ c ρ
  · exact hs x k _ (fun j hj => (h.writes M k j hj).symm) hk
  · show rdo ((H.strat (m (x, w)).2 (m (x, w)).1 c).run ρ).2.2 = rdi' w
    rw [h.fits.same, h2]
  · show ((H.strat (m (x, w)).2 (m (x, w)).1 c).run ρ).2.1 = D.nxt (φ x) (D.msg (rdi' w) (φ x) ρ) ρ
    rw [← h1 x w, ← h2 x w]
    exact h.fits.hand _ _ c ρ

theorem mjl_draw {X X' : Type} (Dd : Type) [Fintype Dd] [Nonempty Dd] (nx : X → Dd → X')
    (Ex : ExtSpec) (W : Type) (Cl C : X → (J → E) → Prop) (rd : W → J → E) :
    (MJ.silent Dd nx Ex Cl).Link
      (Honest.draw Dd nx Ex W) rd rd (fun _ => False) (fun _ => False) C :=
  ⟨mj_draw E J X X' Dd nx Ex W C rd, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- What a draw makes of a claim. -/
theorem mjsp_draw {X X' : Type} (Dd : Type) [Fintype Dd] [Nonempty Dd] (nx : X → Dd → X')
    (Ex : ExtSpec) (Cl C : X → (J → E) → Prop) (x' : X') (k : J → E) :
    (MJ.silent (E := E) (J := J) Dd nx Ex Cl).sp C x' k ↔ ∃ x β, C x k ∧ x' = nx x β :=
  ⟨fun ⟨x, ρ, hc, e⟩ => ⟨x, ρ.1, hc, e⟩, fun ⟨x, β, hc, e⟩ => ⟨x, (β, ()), hc, e⟩⟩

/-- Under `h`: `Honest.MM` of H, at the data `(D.narrow C).data rdi`. -/
theorem mjl_mm {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {H : R.Honest Wi Wo} {rdi : Wi → J → E}
    {rdo : Wo → J → E} {Sr Sw : J → Prop} {C : Xi → (J → E) → Prop} (h : D.Link H rdi rdo Sr Sw C) :
    H.MM ((D.narrow C).data rdi) := h.fits.mm

/-- Under `h`, `hk`, `hrd`: the reading may forget what is not read. -/
theorem mjl_forget {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {H : R.Honest Wi Wi} {rd rd' : Wi → J → E}
    {Sr Sw : J → Prop} {C : Xi → (J → E) → Prop} (h : D.Link H rd rd Sr Sw C)
    (hk : ∀ w x c ρ, ((H.strat w x c).run ρ).2.2 = w) (hrd : ∀ w j, Sr j → rd' w j = rd w j) :
    D.Link H rd' rd' Sr Sw C :=
  ⟨⟨⟨h.fits.mm.noOrc, h.fits.mm.free,
      fun w x c ρ => (h.fits.mm.run w x c ρ).trans (h.reads _ _ x ρ fun j hj => (hrd w j hj).symm),
      h.fits.mm.stable, h.fits.mm.law⟩,
    fun w x c ρ => by rw [hk],
    fun w x c ρ => (h.fits.hand w x c ρ).trans (by
      show D.nxt x (D.msg (rd w) x ρ) ρ = D.nxt x (D.msg (rd' w) x ρ) ρ
      rw [h.reads (rd w) (rd' w) x ρ fun j hj => (hrd w j hj).symm])⟩, h.reads, h.writes⟩

end Rules

/-- Under the hypotheses below, completeness carries "the joint holds of the entries" through a
block. The block is taken at the tuple type J → E (the entries themselves); rd is its reading there.
-/
theorem mjsp_sound {E J K X₁ X₂ : Type} {Ex : ExtSpec} {R : IOR X₁ Ex X₂ Ex}
    {H : R.Honest ((J → E) × Unit) ((J → E) × Unit)} {D : MJ E J R}
    {A : Rels K X₁ Ex ((J → E) × Unit)} {B : Rels K X₂ Ex ((J → E) × Unit)}
    {rd : (J → E) × Unit → J → E} {Sr Sw : J → Prop} {C : X₁ → (J → E) → Prop} [Nonempty H.Coin]
    (hl : D.Link H rd rd Sr Sw C) (hrd : ∀ w j, Sr j → rd w j = w.1 j)
    (hk : ∀ w x c ρ, ((H.strat w x c).run ρ).2.2 = w) (hc : ∀ y τ, R.imp y τ = y)
    (ha : H.Acc A.rel B.rel) (hC : ∀ x k, C x k → mjClOf A x k) :
    ∀ x' k, D.sp C x' k → mjClOf B x' k := by
  rintro _ k ⟨x, ρ, hx, rfl⟩ y
  obtain ⟨c⟩ := (inferInstance : Nonempty H.Coin)
  have h1 := (ha x y (k, ()) c ρ (hC x k hx y) (by rw [hl.fits.mm.free]; exact fun hh => hh)).2
  rw [hc, hk, hl.fits.hand] at h1
  have e : D.msg (rd (k, ())) x ρ = D.msg k x ρ := hl.reads _ _ x ρ fun j hj => hrd (k, ()) j hj
  have h2 : (D.narrow C).nxt x ((D.narrow C).msg (rd (k, ())) x ρ) ρ = D.nxt x (D.msg k x ρ) ρ := by
    show D.nxt x (D.msg (rd (k, ())) x ρ) ρ = _
    rw [e]
  rw [h2] at h1
  exact h1

section Links
variable (E : Type) [Field E] [Fintype E]

/-- The sumcheck as a link: started with any claim that gives its sum claim and does not read its
own masks. (not all hypotheses are named here: see the statement below) -/
theorem mjl_psc (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E) (O O' : Y.Own)
    (hV : Y.VarsOK) (hD : Y.DegOK) (hO : Y.OwnOK O) (hO' : Y.OwnOK O') (hne : Y.fmt ≠ [])
    (C : E × Y.St → (Y.J → E) → Prop) (hC : ∀ x k, C x k → Y.SumHolds x k)
    (hs : MjStab C fun j => ∃ i, j = O.at i) :
    (Y.mj Ex O).Link (Y.hon Ex msg) (fun w => O.cut (msg w)) (fun w => O.cut (msg w)) O'.Rd
      (fun j => ∃ i, j = O.at i) C :=
  ⟨mj_narrow E Y.J _ _ _ _ _ _ _ _ (Y.mj Ex O) _ _ C (mjPsc_fits E Y Ex Wt msg O hV hD hO hne) hC
      fun x k M hk => hs x k _ (fun j hj => (mjPsc_writes E Y Ex O M k j hj).symm) hk,
    (mjPsc_reads E Y Ex O O' hO').msg,
    mjPsc_writes E Y Ex O⟩

end Links
end Cb
