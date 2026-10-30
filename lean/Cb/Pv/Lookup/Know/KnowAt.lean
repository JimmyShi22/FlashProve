-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Know/KnowAt.lean.
Blocks without an honest side, and the rules that join their knowledge soundness.

The library's property of a good block (`GoodAt`, Cb/Ld/LdSigLift.lean; `BkA.Good`,
Cb/Ld/LdLkpTreeP.lean) speaks of a verifier and an honest prover together. Knowledge soundness needs
the verifier alone. TWhole.KnowAt (Cb/G6/Cut.lean) is that half: the four fields of GoodAt that name
no honest side.

States: knowAt_congr (KnowAt reads of its two joints the condition and the relaxed relation alone);
knowAt_seq_ext, knowAt_postMap, knowAt_preMap, knowAt_draw: the rules of Cb/G6/Join.lean with all
their arguments written out;
  BkK: a verifier with its list of errors; BkK.Know: KnowAt of it, the extractor the identity; seq,
    preM, postM, chain on such blocks; drawK: a draw as such a block; know_seq, know_chain,
    know_postM, know_preM; toK: a block of the library's kind without its honest side;
    know_of_good.
Limits: Know says nothing on what a verifier accepts.
Terms: lean/GLOSSARY.md.

-/
import Cb.G6.Join
import Cb.Ld.LdLkpFormat
import Cb.Ld.LdLkpTreePProofs

set_option autoImplicit false

namespace Cb.LdLkp.Kn
open Iop Prob Hiop IOR TWhole

/-- KnowAt reads of its joints the fields on and relR alone. -/
theorem knowAt_congr {K K' M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {A' : IOR.Rels K' Xi Ei (M × Wi)} {B' : IOR.Rels K' Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    (g : KnowAt R A B ext ε) (h1 : A'.on = A.on) (h2 : A'.relR = A.relR) (h3 : B'.on = B.on)
    (h4 : B'.relR = B.relR) : KnowAt R A' B' ext ε :=
  ⟨g.point, g.isLocal, by rw [h1, h3]; exact g.onOut, by rw [h1, h2, h4]; exact g.know⟩

theorem knowAt_seq_ext (K M X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (W₁ W₂ W₃ : Type)
    (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
    (A : Rels K X₁ E₁ (M × W₁)) (B : Rels K X₂ E₂ (M × W₂)) (C : Rels K X₃ E₃ (M × W₃))
    (e₁ : M → X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : M → X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
    (ext : M → X₁ × E₁.Str → Tr (R₁.shape ++ R₂.shape) → W₃ → W₁) (ε₁ : Err R₁.shape)
    (ε₂ : Err R₂.shape) (g₁ : KnowAt R₁ A B e₁ ε₁) (g₂ : KnowAt R₂ B C e₂ ε₂)
    (he : ∀ m a (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) b w,
      R₁.red.out a τ₁ = some b → ext m a (Tr.app τ₁ τ₂) w = e₁ m a τ₁ (e₂ m b τ₂ w)) :
    KnowAt (R₁.seq R₂) A C ext (Err.app ε₁ ε₂) :=
  TWhole.knowAt_seq_ext ext g₁ g₂ he

/-- A map on the explicit part after a block. -/
theorem knowAt_postMap (K M Xi Xo Xo' : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo)
    (A : Rels K Xi Ei (M × Wi)) (B : Rels K Xo Eo (M × Wo)) (B' : Rels K Xo' Eo (M × Wo))
    (ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape) (φ : Xo → Xo')
    (hG : KnowAt R A B ext ε) (h2 : ∀ x y, B.on (x, y) → B'.on (φ x, y))
    (h4 : ∀ x y w, B.on (x, y) → B'.relR (φ x, y) w → B.relR (x, y) w) :
    KnowAt (R.post (fun x => some (φ x)) (ExtMap.id Eo)) A B' ext ε :=
  TWhole.knowAt_postMap φ hG h2 h4

/-- A map on the explicit part before a block. -/
theorem knowAt_preMap (K M Xi Xi' Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo)
    (A' : Rels K Xi' Ei (M × Wi)) (A : Rels K Xi Ei (M × Wi)) (B : Rels K Xo Eo (M × Wo))
    (ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape) (φ : Xi' → Xi)
    (h2 : ∀ x y, A'.on (x, y) → A.on (φ x, y))
    (h4 : ∀ x y w, A'.on (x, y) → A.relR (φ x, y) w → A'.relR (x, y) w) (hG : KnowAt R A B ext ε) :
    KnowAt (R.pre (fun x => some (φ x)) (ExtMap.id Ei)) A' B
      (fun u a τ w => ext u (φ a.1, a.2) τ w) ε :=
  TWhole.knowAt_preMap φ h2 h4 hG

/-- A draw. -/
theorem knowAt_draw (K M X X' : Type) (Ex : ExtSpec) (Wp D : Type) [Fintype D] [Nonempty D]
    (nx : X → D → X') (A : Rels K X Ex (M × Wp)) (A' : Rels K X' Ex (M × Wp)) (err : ℕ)
    (hon : ∀ x y β, A.on (x, y) → A'.on (nx x β, y))
    (hcnt : ∀ x y (m : M), A.on (x, y) →
      cnt (fun β => ∃ wp, A'.relR (nx x β, y) (m, wp) ∧ ¬ A.relR (x, y) (m, wp)) ≤ err) :
    KnowAt (IOR.draw D nx Ex) A A' (fun _ _ _ wp => wp) ((err, ()) : ℕ × Unit) :=
  TWhole.knowAt_draw nx A A' err hon hcnt

/-! ### blocks without an honest side -/

/-- A block at the base: the verifier's side and its errors. -/
structure BkK (Xi Xo : Type) (Ex : ExtSpec) where
  R : IOR Xi Ex Xo Ex
  e : Err R.shape

namespace BkK
variable {X₁ X₂ X₃ : Type} {Ex : ExtSpec}

/-- Know: for each fixed tuple of messages; the identity extracts. -/
def Know {K M Wp : Type} (b : BkK X₁ X₂ Ex) (A : Rels K X₁ Ex (M × Wp)) (B : Rels K X₂ Ex (M × Wp))
    :
    Prop :=
  KnowAt b.R A B (fun _ _ _ wp => wp) b.e

noncomputable def seq (a : BkK X₁ X₂ Ex) (b : BkK X₂ X₃ Ex) : BkK X₁ X₃ Ex :=
  ⟨a.R.seq b.R, Err.app a.e b.e⟩

noncomputable def chain (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) :
    ∀ n, BkK (X 0) (X (n + 1)) Ex
  | 0 => b 0
  | n + 1 => (chain X b n).seq (b (n + 1))

noncomputable def preM (b : BkK X₂ X₃ Ex) (φ : X₁ → X₂) : BkK X₁ X₃ Ex :=
  ⟨b.R.pre (fun x => some (φ x)) (ExtMap.id Ex), b.e⟩
noncomputable def postM (b : BkK X₁ X₂ Ex) (φ : X₂ → X₃) : BkK X₁ X₃ Ex :=
  ⟨b.R.post (fun x => some (φ x)) (ExtMap.id Ex), b.e⟩

end BkK

/-- A draw as a block. -/
def drawK {X X' : Type} (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (Ex : ExtSpec)
    (err : ℕ) : BkK X X' Ex :=
  ⟨IOR.draw D nx Ex, ((err, ()) : ℕ × Unit)⟩

/-- A block of the library's kind, without its honest side. -/
def toK {K M X₁ X₂ : Type} {Ex : ExtSpec} {Wp : Type} (b : BkA K M X₁ X₂ Ex Wp) : BkK X₁ X₂ Ex :=
  ⟨b.R, b.P.err⟩

section
variable {K M X₁ X₂ X₃ : Type} {Ex : ExtSpec} {Wp : Type}

theorem toK_seq (a : BkA K M X₁ X₂ Ex Wp) (b : BkA K M X₂ X₃ Ex Wp) :
    toK (a.seq b) = (toK a).seq (toK b) := rfl
theorem toK_preM (b : BkA K M X₂ X₃ Ex Wp) (φ : X₁ → X₂) : toK (b.preM φ) = (toK b).preM φ := rfl
theorem toK_postM (b : BkA K M X₁ X₂ Ex Wp) (φ : X₂ → X₃) : toK (b.postM φ) = (toK b).postM φ := rfl
theorem toK_chain (X : ℕ → Type) (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) :
    ∀ n, toK (BkA.chain X b n) = BkK.chain X (fun l => toK (b l)) n
  | 0 => rfl
  | n + 1 => by
    show (toK (BkA.chain X b n)).seq (toK (b (n + 1))) = _
    rw [toK_chain X b n]
    rfl

/-- A good block of the library's kind gives Know of its verifier's side. -/
theorem know_of_good {b : BkA K M X₁ X₂ Ex Wp} {A : Rels K X₁ Ex (M × Wp)}
    {B : Rels K X₂ Ex (M × Wp)} (g : b.Good A B) : (toK b).Know A B := ((goodAt_iff _ _ _ _ _ _).1
        g).1

theorem know_seq {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} {A : Rels K X₁ Ex (M × Wp)}
    {B : Rels K X₂ Ex (M × Wp)} {C : Rels K X₃ Ex (M × Wp)} (ha : a.Know A B) (hb : b.Know B C) :
    (a.seq b).Know A C :=
  TWhole.knowAt_seq ha hb

theorem know_chain (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex)
    (A : ∀ l, Rels K (X l) Ex (M × Wp)) (n : ℕ) :
    (∀ l ≤ n, (b l).Know (A l) (A (l + 1))) → (BkK.chain X b n).Know (A 0) (A (n + 1)) := by
  induction n with
  | zero => exact fun h => h 0 (Nat.le_refl 0)
  | succ n ih =>
    intro h
    exact know_seq (ih fun l hl => h l (Nat.le_succ_of_le hl)) (h (n + 1) (Nat.le_refl _))

theorem know_postM {b : BkK X₁ X₂ Ex} {A : Rels K X₁ Ex (M × Wp)} {B : Rels K X₂ Ex (M × Wp)}
    {B' : Rels K X₃ Ex (M × Wp)} (φ : X₂ → X₃) (g : b.Know A B)
    (h2 : ∀ x y, B.on (x, y) → B'.on (φ x, y))
    (h4 : ∀ x y w, B.on (x, y) → B'.relR (φ x, y) w → B.relR (x, y) w) : (b.postM φ).Know A B' :=
  TWhole.knowAt_postMap φ g h2 h4

theorem know_preM {b : BkK X₂ X₃ Ex} {A' : Rels K X₁ Ex (M × Wp)} {A : Rels K X₂ Ex (M × Wp)}
    {B : Rels K X₃ Ex (M × Wp)} (φ : X₁ → X₂) (h2 : ∀ x y, A'.on (x, y) → A.on (φ x, y))
    (h4 : ∀ x y w, A'.on (x, y) → A.relR (φ x, y) w → A'.relR (x, y) w) (g : b.Know A B) :
    (b.preM φ).Know A' B :=
  TWhole.knowAt_preMap φ h2 h4 g

end
end Cb.LdLkp.Kn
