-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/LinksBack.lean: the description of a file's three chains, each a typed reduction
read over the chain's written rounds; and the list of hypotheses for the statements of a batch, from
the typed reductions' clauses.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.


OnBytes/TypedOracleCompiler/Joined/MidLinks.lean asks of a description that each chain be a link with keys over the
chain's own, written rounds (`Links.KnowsJ`). Typed protocols have rounds of their own. Here a
description is made of three typed reductions and maps from the written rounds to theirs (`CarryS`,
`backS`, OnBytes/Flat/CarrySkip.lean), and `Links.KnowsJ` is had from their clauses:
  the first and the third chain, whose rounds are local: the clause `Know` for one statement,
    carried by `backS_know`;
  the second chain, in which only the shared part speaks: a link with keys for the statements of a
    batch (`LinkJ`; from a link of the library by `LinkJ.ofKB`), carried by `LinkJ.backS`
    (OnBytes/TypedOracleCompiler/Joined/CarryJ.lean).

Main names:
  `LinkJ.backSLo`: a typed reduction with the clause `Know`, read over written local rounds, as a
    link.
  `linksBack`: the description.
  `linksBack_knowsJ`: THE LIST `Links.KnowsJ` of it.

What is asked, by name: hJ: in the joining round only the shared part speaks; know₁, know₃: the
typed clauses of the first and third chain; l₂: the typed link of the second; f₁, f₂, f₃: the
written errors bear the typed ones (`CarryS.Fits`); law₁: the key of what the first chain hands on
is a function of the external string; hg: the typed key is a function of that key; hands₁, hands₂.

Limits: nothing here shows a clause, or maps with `Fits`, of any protocol. The second chain's maps
read a statement through its key alone. What a skipped round sends is read by no typed verifier.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Joined.CarryJ
import OnBytes.TypedOracleCompiler.Joined.MidLinks

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains)
open _root_.CompileK.Joined (AllKind allKind_const)
open OnBytes.Flat (CarryS backS backS_know)

/-- A typed reduction with the clause `Know`, read over written local rounds, as a link with keys:
the new key is a function G of the old. -/
theorem LinkJ.backSLo {A A' B' WA' WB' κ κ₂ : Type} {s : Shape} {K' : Reduction A' B'}
    (F : A → CarryS s K'.shape) (fa : A → A') {on' : A' → Prop} {RA' : A' → WA' → Prop}
    {RB' : B' → WB' → Prop} {ext' : A' → Tr K'.shape → WB' → WA'} {ε : Err K'.shape} {ε' : Err s}
    (hF : ∀ a, (F a).Fits ε ε') (tr₀ : Tr K'.shape) (h : K'.Know on' RA' RB' ext' ε)
    (An : RoundSplits s) (hAn : AllKind .lo s An) (N : ℕ) (key : A → κ) (key₂ : B' → κ₂) (G : κ → κ₂)
    (hG : ∀ a τ b, (OnBytes.Flat.backS K' F fa).out a τ = some b → key₂ b = G (key a)) :
    LinkJ (OnBytes.Flat.backS K' F fa) An N key key₂ (fun a => on' (fa a))
      (fun a w => RA' (fa a) w) RB' (fun a τ w => ext' (fa a) (((F a).tr τ).getD tr₀) w) ε' :=
  LinkJ.ofLocal (K := OnBytes.Flat.backS K' F fa) hAn N
    (backS_know K' F ε ε' hF fa on' RA' RB' ext' tr₀ h) G hG

section Back
variable {G : Chains} {Y : Type} {E : ExtSpec} {X₁ X₂ X₃ A₁ A₂ W₀ W₁ W₂ κ : Type}
  (K₁ : Reduction X₁ A₁) (K₂ : Reduction X₂ A₂) (K₃ : Reduction X₃ Unit)
  (F₁ : Y × E.Str → CarryS G.c₁ K₁.shape) (k₁ : A₁ → κ) (F₂ : κ → CarryS G.c₂ K₂.shape)
  (F₃ : A₂ → CarryS G.c₃ K₃.shape) (a₁ : Y × E.Str → X₁) (a₂ : A₁ → X₂) (a₃ : A₂ → X₃)
  (on₀ : X₁ → Prop) (on₁ : X₂ → Prop) (on₂ : X₃ → Prop) (R₀ : X₁ → W₀ → Prop)
  (R₁ : X₂ → W₁ → Prop) (R₂ : X₃ → W₂ → Prop) (e₁ : X₁ → Tr K₁.shape → W₁ → W₀)
  (e₂ : X₂ → Tr K₂.shape → W₂ → W₁) (e₃ : X₃ → Tr K₃.shape → Unit → W₂) (ε₁ : Err G.c₁)
  (ε₂ : Err G.c₂) (ε₃ : Err G.c₃) (t₁ : Tr K₁.shape) (t₂ : Tr K₂.shape) (t₃ : Tr K₃.shape)
  (d₀ : W₀) (d₁ : W₁)

/-- **The description of a file whose three chains are typed reductions read over the written
rounds.** a₁, a₂, a₃: the typed statement of a written one; t₁, t₂, t₃: any typed transcripts, for
the extractors' values where a written transcript has no image. -/
def linksBack : Links G (Y × E.Str) where
  A₁ := A₁
  A₂ := A₂
  W₀ := W₀
  W₁ := W₁
  W₂ := W₂
  out₁ := (backS K₁ F₁ a₁).out
  out₂ := (backS K₂ (fun a => F₂ (k₁ a)) a₂).out
  out₃ := (backS K₃ F₃ a₃).out
  on₀ := fun a => on₀ (a₁ a)
  on₁ := fun a => on₁ (a₂ a)
  on₂ := fun a => on₂ (a₃ a)
  R₀ := fun a w => R₀ (a₁ a) w
  R₁ := fun a w => R₁ (a₂ a) w
  R₂ := fun a w => R₂ (a₃ a) w
  e₁ := fun a τ w => e₁ (a₁ a) (((F₁ a).tr τ).getD t₁) w
  e₂ := fun a τ w => e₂ (a₂ a) (((F₂ (k₁ a)).tr τ).getD t₂) w
  e₃ := fun a τ w => e₃ (a₃ a) (((F₃ a).tr τ).getD t₃) w
  ε₁ := ε₁
  ε₂ := ε₂
  ε₃ := ε₃
  d₀ := d₀
  d₁ := d₁

variable {K₁ K₂ K₃ F₁ k₁ F₂ F₃ a₁ a₂ a₃ on₀ on₁ on₂ R₀ R₁ R₂ e₁ e₂ e₃ ε₁ ε₂ ε₃}

/-- **The list for the statements of a batch, from the typed reductions' clauses.** The relations
between the chains are the typed ones at the images: so the first typed reduction ends in R₁ at a₂,
the second in R₂ at a₃. -/
theorem linksBack_knowsJ {N : ℕ} {κ' κ₂ : Type} {δ₁ : Err K₁.shape} {δ₂ : Err K₂.shape}
    {δ₃ : Err K₃.shape} {key' : X₂ → κ'} {k₂ : A₂ → κ₂}
    (hJ : G.aJ = RAnn.ofShared .sh G.rJ)
    (know₁ : K₁.Know on₀ R₀ (fun b w => R₁ (a₂ b) w) e₁ δ₁)
    (l₂ : LinkJ K₂ (shA K₂.shape) N key' k₂ on₁ R₁ (fun b w => R₂ (a₃ b) w) e₂ δ₂)
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ δ₃)
    (f₁ : ∀ a, (F₁ a).Fits δ₁ ε₁) (f₂ : ∀ k, (F₂ k).Fits δ₂ ε₂) (f₃ : ∀ a, (F₃ a).Fits δ₃ ε₃)
    (g₁ : E.Str → κ) (law₁ : ∀ a τ b, (backS K₁ F₁ a₁).out a τ = some b → k₁ b = g₁ a.2)
    (g : κ → κ') (hg : ∀ a, key' (a₂ a) = g (k₁ a))
    (hands₁ : ∀ a τ b, on₀ (a₁ a) → (backS K₁ F₁ a₁).out a τ = some b → on₁ (a₂ b))
    (hands₂ : ∀ a τ b, on₁ (a₂ a) →
      (backS K₂ (fun a => F₂ (k₁ a)) a₂).out a τ = some b → on₂ (a₃ b)) :
    (linksBack K₁ K₂ K₃ F₁ k₁ F₂ F₃ a₁ a₂ a₃ on₀ on₁ on₂ R₀ R₁ R₂ e₁ e₂ e₃ ε₁ ε₂ ε₃ t₁ t₂ t₃ d₀
      d₁).KnowsJ N k₁ k₂ where
  l₁ := LinkJ.backSLo F₁ a₁ f₁ t₁ know₁ G.A₁ (allKind_const (fun _ => rfl) G.c₁) N Prod.snd k₁ g₁
    law₁
  l₂ := by
    have hA : G.A₂ = shA G.c₂ := by
      show (G.aJ, RoundSplits.const (RAnn.ofShared .sh) G.s₂) =
        (RAnn.ofShared .sh G.rJ, RoundSplits.const (RAnn.ofShared .sh) G.s₂)
      rw [hJ]
    rw [hA]
    exact l₂.backS k₁ F₂ a₂ f₂ t₂ g hg
  l₃ := LinkJ.backSLo F₃ a₃ f₃ t₃ know₃ G.A₃ (allKind_const (fun _ => rfl) G.c₃) N k₂
    (fun _ : Unit => ()) (fun _ => ()) fun _ _ _ _ => rfl
  hands₁ := hands₁
  hands₂ := hands₂

end Back

end TypedOracleCompiler.Joined
