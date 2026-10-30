-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskKit.lean: a calculus for chains of masked blocks: the bundle `Piece` and how it goes
through the ways of building a chain.
This file is book-keeping for the sequential composition of reductions: how one bundle of properties
passes through composition, maps on the explicit part, and a renaming of entries.

Definitions, statements and proofs. Glue; no protocol of its own.

Main names, each theorem under the hypotheses of its statement:
  `D.Piece H rdi rdo Sr Sw`: the letters D (`MJ`, Cb/Ld/LdLkpMaskChain.lean) fit the honest side H;
    messages and claim read the entries in Sr only; the own masks lie in Sw.
  `mjp_seq`, `mjp_chain`: two in a row, n + 1 in a row: asked: what an earlier block reads and what
    a later block writes are disjoint; each claim steps to the next. The whole reads the union and
    writes the union.
  `MJ.post`, `MJ.pre`, `mjp_post`, `mjp_pre`: a map on the explicit part after or before a block:
    no round.
  `mjp_narrow`, `mjp_reJ`, `mjp_mono`: a stronger claim; entries named otherwise; larger sets.
  `mjp_draw`, `mjp_psc`, `mjp_in`: the links: the verifier draws a value; the sumcheck for a
    polynomial summand; the step into a sumcheck.
  `mj_forget`: the reading may forget all entries that the block does not read.
  `mj_step_of_acc`: where the steps come from: if a block is complete from a joint A to a joint B
    (at the tuple type J → E, the entries themselves), only copies its oracles, and D fits it, then
    "A holds of the entries" steps to "B holds of the entries": so the theorems on completeness that
    stand give all steps of a chain whose claims are `mjClOf` of its joints.
  `mjClOf A`: the claim on entries that a joint at the base makes: `A.rel` at the tuple k, at every
    value of the oracles.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskPscProofs
import Cb.Ld.LdLkpFormat
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Prob Hiop

namespace MJ
variable {E J J' : Type} {X₁ X₂ X₃ Xi Xi' Xo Xo' : Type}
  {E₁ E₂ E₃ Ei Ei' Eo Eo' : ExtSpec} {W₁ W₂ W₃ Wi Wi' Wo Wo' : Type}

/-- The bundle: D fits the honest side H; messages and claim read the entries in Sr only; the own
masks lie in Sw. -/
structure Piece {R : IOR Xi Ei Xo Eo} (D : MJ E J R) (H : R.Honest Wi Wo) (rdi : Wi → J → E)
    (rdo : Wo → J → E) (Sr Sw : J → Prop) : Prop where
  fits   : D.Fits H rdi rdo
  reads  : D.Reads Sr
  writes : D.Writes Sw

/-- A map on the explicit part after a block. -/
def post {R : IOR Xi Ei Xo Eo} (D : MJ E J R) (f : Xo → Option Xo')
    (g : ExtMap Eo Eo') (φ : Xo → Xo') : MJ E J (R.post f g) where
  Mk  := D.Mk
  put := D.put
  Cl  := D.Cl
  msg := D.msg
  nxt := fun x pl ρ => φ (D.nxt x pl ρ)
  sim := D.sim

/-- A map on the explicit part before a block. -/
def pre {R : IOR Xi Ei Xo Eo} (D : MJ E J R) (f : Xi' → Option Xi)
    (g : ExtMap Ei' Ei) (φ : Xi' → Xi) : MJ E J (R.pre f g) where
  Mk  := D.Mk
  put := D.put
  Cl  := fun x k => D.Cl (φ x) k
  msg := fun k x ρ => D.msg k (φ x) ρ
  nxt := fun x pl ρ => D.nxt (φ x) pl ρ
  sim := fun x ρ => D.sim (φ x) ρ

end MJ

section Rules
variable {E J J' : Type} {X₁ X₂ X₃ Xi Xi' Xo Xo' : Type}
  {E₁ E₂ E₃ Ei Ei' Eo Eo' : ExtSpec} {W₁ W₂ W₃ Wi Wi' Wo Wo' : Type}

theorem mjp_mono {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {H : R.Honest Wi Wo} {rdi : Wi → J → E}
    {rdo : Wo → J → E} {Sr Sw Sr' Sw' : J → Prop} (h : D.Piece H rdi rdo Sr Sw)
    (hr : ∀ j, Sr j → Sr' j) (hw : ∀ j, Sw j → Sw' j) : D.Piece H rdi rdo Sr' Sw' :=
  ⟨h.fits, ⟨fun k k' x ρ hk => h.reads.msg k k' x ρ fun j hj => hk j (hr j hj),
      fun k k' x hk => h.reads.cl k k' x fun j hj => hk j (hr j hj)⟩,
    fun M k j hj => h.writes M k j fun hj' => hj (hw j hj')⟩

theorem mjp_seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {H₁ : R₁.Honest W₁ W₂}
    {H₂ : R₂.Honest W₂ W₃} {D₁ : MJ E J R₁} {D₂ : MJ E J R₂} {rd₁ : W₁ → J → E} {rd₂ : W₂ → J → E}
    {rd₃ : W₃ → J → E} {Sr₁ Sw₁ Sr₂ Sw₂ : J → Prop} (h₁ : D₁.Piece H₁ rd₁ rd₂ Sr₁ Sw₁)
    (h₂ : D₂.Piece H₂ rd₂ rd₃ Sr₂ Sw₂) (hd : ∀ j, Sr₁ j → ¬ Sw₂ j) (hs : D₁.Step D₂) :
    (D₁.seq D₂).Piece (H₁.seq H₂) rd₁ rd₃ (fun j => Sr₁ j ∨ Sr₂ j) fun j => Sw₁ j ∨ Sw₂ j := by
  refine ⟨mj_seq E J _ _ _ _ _ _ _ _ _ R₁ R₂ H₁ H₂ D₁ D₂ rd₁ rd₂ rd₃ h₁.fits h₂.fits
      (mj_blind_of E J _ _ _ _ _ _ _ _ R₁ R₂ D₁ D₂ Sr₁ Sw₂ h₁.reads h₂.writes hd) hs,
    ⟨fun k k' x ρ hk => ?_, fun k k' x hk => h₁.reads.cl k k' x fun j hj => hk j (Or.inl hj)⟩,
    fun M k j hj => ?_⟩
  · show Plains.app (D₁.msg k x (Rho.fst ρ))
        (D₂.msg k (D₁.nxt x (D₁.msg k x (Rho.fst ρ)) (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ)) =
      Plains.app (D₁.msg k' x (Rho.fst ρ))
        (D₂.msg k' (D₁.nxt x (D₁.msg k' x (Rho.fst ρ)) (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ))
    rw [h₁.reads.msg k k' x _ fun j hj => hk j (Or.inl hj),
      h₂.reads.msg k k' _ _ fun j hj => hk j (Or.inr hj)]
  · show D₂.put M.2 (D₁.put M.1 k) j = k j
    rw [h₂.writes M.2 _ j fun h => hj (Or.inr h), h₁.writes M.1 k j fun h => hj (Or.inl h)]

theorem mjp_chain {K M : Type} {Ex : ExtSpec} {Wp : Type} (X : ℕ → Type)
    (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (D : ∀ l, MJ E J (b l).R)
    (rd : M × Wp → J → E) (Sr Sw : ℕ → J → Prop) :
    ∀ n, (∀ l ≤ n, (D l).Piece (b l).H rd rd (Sr l) (Sw l)) →
      (∀ l l', l < l' → l' ≤ n → ∀ j, Sr l j → ¬ Sw l' j) → (∀ l < n, (D l).Step (D (l + 1))) →
      (MJ.chain X b D n).Piece (BkA.chain X b n).H rd rd
        (fun j => ∃ l ≤ n, Sr l j) fun j => ∃ l ≤ n, Sw l j
  | 0, hP, _, _ =>
    mjp_mono (hP 0 (le_refl 0)) (fun _ h => ⟨0, le_refl 0, h⟩) fun _ h => ⟨0, le_refl 0, h⟩
  | n + 1, hP, hd, hs =>
      mjp_mono (mjp_seq
          (mjp_chain X b D rd Sr Sw n (fun l hl => hP l (Nat.le_succ_of_le hl))
            (fun l l' h1 h2 => hd l l' h1 (Nat.le_succ_of_le h2))
            fun l hl => hs l (Nat.lt_succ_of_lt hl))
          (hP (n + 1) (le_refl _))
          (fun j ⟨l, hl, hj⟩ => hd l (n + 1) (Nat.lt_succ_of_le hl) (le_refl _) j hj)
          (mj_chain_step X b D n (D (n + 1))
            (fun l hl => hs l (Nat.lt_succ_of_lt hl)) (hs n (Nat.lt_succ_self n))))
        (fun _ h =>
          h.elim (fun ⟨l, hl, hj⟩ => ⟨l, Nat.le_succ_of_le hl, hj⟩) fun hj =>
            ⟨n + 1, le_refl _, hj⟩) fun _ h =>
              h.elim (fun ⟨l, hl, hj⟩ => ⟨l, Nat.le_succ_of_le hl, hj⟩) fun hj =>
                ⟨n + 1, le_refl _, hj⟩

theorem mjp_post {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {H : R.Honest Wi Wo} {rdi : Wi → J → E}
    {rdo : Wo → J → E} {Sr Sw : J → Prop} (h : D.Piece H rdi rdo Sr Sw) (f : Xo → Option Xo')
    (g : ExtMap Eo Eo') (φ : Xo → Xo') (m : Xo × Wo → Xo' × Wo') (rdo' : Wo' → J → E)
    (h1 : ∀ o, (m o).1 = φ o.1) (h2 : ∀ o, rdo' (m o).2 = rdo o.2) :
    (D.post f g φ).Piece (H.post f g m) rdi rdo' Sr Sw := by
  have hr : ∀ w x c ρ, ((H.post f g m).strat w x c).run ρ =
      (((H.strat w x c).run ρ).1, m ((H.strat w x c).run ρ).2) :=
    fun w x c ρ => Strat.run_map m (H.strat w x c) ρ
  refine ⟨⟨mm_post _ _ _ _ _ _ R _ _ _ H (D.data rdi) f g m h.fits.mm,
      fun w x c ρ => ?_, fun w x c ρ => ?_⟩,
    ⟨h.reads.msg, h.reads.cl⟩,
    h.writes⟩
  · rw [hr, h2]
    exact h.fits.same w x c ρ
  · rw [hr, h1]
    exact congrArg φ (h.fits.hand w x c ρ)

theorem mjp_pre {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {H : R.Honest Wi Wo} {rdi : Wi → J → E}
    {rdo : Wo → J → E} {Sr Sw : J → Prop} (h : D.Piece H rdi rdo Sr Sw) (f : Xi' → Option Xi)
    (g : ExtMap Ei' Ei) (φ : Xi' → Xi) (m : Xi' × Wi' → Xi × Wi) (rdi' : Wi' → J → E)
    (h1 : ∀ x w, (m (x, w)).1 = φ x) (h2 : ∀ x w, rdi (m (x, w)).2 = rdi' w) :
    (D.pre f g φ).Piece (H.pre f g m) rdi' rdo Sr Sw := by
  refine ⟨⟨⟨h.fits.mm.noOrc,
        fun w x => h.fits.mm.free (m (x, w)).2 (m (x, w)).1,
        fun w x c ρ => ?_,
        fun x k M => h.fits.mm.stable (φ x) k M,
        fun k x ρ => h.fits.mm.law k (φ x) ρ⟩,
      fun w x c ρ => ?_, fun w x c ρ => ?_⟩,
    ⟨fun k k' x ρ => h.reads.msg k k' (φ x) ρ, fun k k' x => h.reads.cl k k' (φ x)⟩,
    h.writes⟩
  · show ((H.strat (m (x, w)).2 (m (x, w)).1 c).run ρ).1.plains = D.msg (rdi' w) (φ x) ρ
    rw [← h1 x w, ← h2 x w]
    exact h.fits.mm.run _ _ c ρ
  · show rdo ((H.strat (m (x, w)).2 (m (x, w)).1 c).run ρ).2.2 = rdi' w
    rw [h.fits.same, h2]
  · show ((H.strat (m (x, w)).2 (m (x, w)).1 c).run ρ).2.1 = D.nxt (φ x) (D.msg (rdi' w) (φ x) ρ) ρ
    rw [← h1 x w, ← h2 x w]
    exact h.fits.hand _ _ c ρ

theorem mjp_narrow {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {H : R.Honest Wi Wo} {rdi : Wi → J → E}
    {rdo : Wo → J → E} {Sr Sw : J → Prop} (h : D.Piece H rdi rdo Sr Sw) (Cl' : Xi → (J → E) → Prop)
    (h1 : ∀ x k, Cl' x k → D.Cl x k) (h2 : ∀ x k M, Cl' x k → Cl' x (D.put M k))
    (h3 : ∀ k k' x, (∀ j, Sr j → k j = k' j) → Cl' x k → Cl' x k') :
    (D.narrow Cl').Piece H rdi rdo Sr Sw :=
  ⟨mj_narrow E J _ _ _ _ R _ _ H D rdi rdo Cl' h.fits h1 h2, ⟨h.reads.msg, h3⟩, h.writes⟩

theorem mjp_reJ {R : IOR Xi Ei Xo Eo} {D : MJ E J' R} {H : R.Honest Wi Wo} (e : J' ≃ J)
    {rdi : Wi → J → E} {rdo : Wo → J → E} {Sr Sw : J' → Prop}
    (h : D.Piece H (fun w j' => rdi w (e j')) (fun w j' => rdo w (e j')) Sr Sw) :
    (D.reJ e).Piece H rdi rdo (fun j => Sr (e.symm j)) fun j => Sw (e.symm j) :=
  ⟨mj_reJ E J J' _ _ _ _ R _ _ H D e rdi rdo h.fits,
    ⟨fun k k' x ρ hk => h.reads.msg _ _ x ρ fun j' hj => hk (e j') (by rwa [e.symm_apply_apply]),
      fun k k' x hk => h.reads.cl _ _ x fun j' hj => hk (e j') (by rwa [e.symm_apply_apply])⟩,
    fun M k j hj => by
      show D.put M (fun j' => k (e j')) (e.symm j) = k j
      rw [h.writes M _ _ hj, e.apply_symm_apply]⟩

/-- Under `h`, `hR`, `hk`, `hrd`: the reading may forget what the block does not read. -/
theorem mj_forget {R : IOR Xi Ei Xo Eo} {D : MJ E J R} {H : R.Honest Wi Wi} {rd rd' : Wi → J → E}
    {Sr : J → Prop} (h : D.Fits H rd rd) (hR : D.Reads Sr)
    (hk : ∀ w x c ρ, ((H.strat w x c).run ρ).2.2 = w) (hrd : ∀ w j, Sr j → rd' w j = rd w j) :
    D.Fits H rd' rd' :=
  ⟨⟨h.mm.noOrc, h.mm.free,
      fun w x c ρ => (h.mm.run w x c ρ).trans (hR.msg _ _ x ρ fun j hj => (hrd w j hj).symm),
      h.mm.stable, h.mm.law⟩,
    fun w x c ρ => by rw [hk],
    fun w x c ρ =>
      (h.hand w x c ρ).trans (by rw [hR.msg (rd w) (rd' w) x ρ fun j hj => (hrd w j hj).symm])⟩

theorem mjp_draw {X X' : Type} (Dd : Type) [Fintype Dd] [Nonempty Dd] (nx : X → Dd → X')
    (Ex : ExtSpec) (W : Type) (Cl : X → (J → E) → Prop) (rd : W → J → E) (Sr : J → Prop)
    (h : ∀ k k' x, (∀ j, Sr j → k j = k' j) → Cl x k → Cl x k') :
    (MJ.silent Dd nx Ex Cl).Piece (Honest.draw Dd nx Ex W) rd rd Sr fun _ => False :=
  ⟨mj_draw E J X X' Dd nx Ex W Cl rd, ⟨fun _ _ _ _ _ => rfl, h⟩, fun _ _ _ _ => rfl⟩

end Rules

/-- The claim on entries that a joint at the base makes. -/
def mjClOf {E J K X : Type} {Ex : ExtSpec} (A : Rels K X Ex ((J → E) × Unit)) :
    X → (J → E) → Prop :=
  fun x k => ∀ y, A.rel x y (k, ())

/-- Under the hypotheses below, completeness gives the steps. -/
theorem mj_step_of_acc {E J K X₁ X₂ : Type} {Ex : ExtSpec} {R : IOR X₁ Ex X₂ Ex}
    {H : R.Honest ((J → E) × Unit) ((J → E) × Unit)} {D : MJ E J R}
    {A : Rels K X₁ Ex ((J → E) × Unit)} {B : Rels K X₂ Ex ((J → E) × Unit)} [Nonempty H.Coin]
    (hf : D.Fits H (fun w => w.1) fun w => w.1) (hc : ∀ y τ, R.imp y τ = y) (ha : H.Acc A.rel B.rel)
    (k : J → E) (x : X₁) (ρ : Rho R.shape) (h : mjClOf A x k) :
    mjClOf B (D.nxt x (D.msg k x ρ) ρ) k := by
  intro y
  obtain ⟨c⟩ := (inferInstance : Nonempty H.Coin)
  have h1 := (ha x y (k, ()) c ρ (h y) (by rw [hf.mm.free]; exact fun hh => hh)).2
  rw [hc, hf.hand] at h1
  have h2 : ((H.strat (k, ()) x c).run ρ).2.2 = (k, ()) := Prod.ext (hf.same (k, ()) x c ρ) rfl
  rw [h2] at h1
  exact h1

section Links
variable (E : Type) [Field E] [Fintype E]

/-- Under `hV`, `hD`, `hO`, `hO'`, `hne`: the sumcheck as a piece: reading "the entries in O.Rd"; it
reads `O'.Rd`; its own masks lie at `O.at`. -/
theorem mjp_psc (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E) (O O' : Y.Own)
    (hV : Y.VarsOK) (hD : Y.DegOK) (hO : Y.OwnOK O) (hO' : Y.OwnOK O') (hne : Y.fmt ≠ []) :
    (Y.mj Ex O).Piece (Y.hon Ex msg) (fun w => O.cut (msg w)) (fun w => O.cut (msg w))
      O'.Rd fun j => ∃ i, j = O.at i :=
  ⟨mjPsc_fits E Y Ex Wt msg O hV hD hO hne, mjPsc_reads E Y Ex O O' hO', mjPsc_writes E Y Ex O⟩

/-- The step into a sumcheck as a piece. -/
theorem mjp_in (Z : PscIn E) (Ex : ExtSpec) (W : Type) (rd : W → Z.T.J → E) (Sr : Z.T.J → Prop)
    (h : ∀ k k' st, (∀ j, Sr j → k j = k' j) → Z.AllHold st k → Z.AllHold st k') :
    (Z.mj Ex).Piece (Honest.draw Z.ev.D Z.nxX Ex W) rd rd Sr fun _ => False :=
  mjp_draw Z.ev.D Z.nxX Ex W Z.AllHold rd Sr h

end Links
end Cb
