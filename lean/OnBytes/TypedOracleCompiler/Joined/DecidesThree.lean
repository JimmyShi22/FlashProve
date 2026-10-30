-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/DecidesThree.lean: "where the file's verifier accepts, no chain rejects", from
one success equation for each of the file's three chains, laid in a row at the contexts between
them.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.


The tops of this folder (`row_sndBKT_links`, `proofSound_at_links`,
OnBytes/TypedOracleCompiler/Joined/MidLinks.lean, and their like) ask of a description `decides`: where the file's
verifier accepts, the three chains in a row put out. A file's verifier is a program that runs a
routine on each chain, one behind the other, and hands a context from each to the next. So the
hypothesis is shown chain by chain. Here it is cut into three: contexts, readings and runs are
letters.

Main names:
  `Links.tr₁`, `tr₂`, `tr₃`: the three chains' parts of a transcript of the whole file.
  `Links.all_out_iff`: the three chains in a row put out if and only if each puts out, the second
    at what the first has handed on, the third at what the second has.
  `ThreeRuns Ctx C`: for each chain a reading of contexts as the chain's statements (`rd₀`, `rd₁`,
    `rd₂`) and a relation "the routine runs from c to c' at the chain's written rounds" (`run₁`,
    `run₂`, `run₃`), with THE THREE SUCCESS EQUATIONS `eq₁`, `eq₂`, `eq₃`: if c reads as a and the
    routine runs from c to c' at σ, then the chain puts out some b at (a, σ), and c' reads as b.
  `ThreeRuns.Ran W a τ`: the three routines have run in a row over τ from a context that reads as a.
  `ThreeRuns.puts`: then the three chains in a row put out.
  `decides_of_three`, `decides_rec_of_three`: `decides` in the two forms in which the tops ask it.

Limits: one direction. No routine, reading or equation of any file is given here. That the file's
verifier, where it accepts, has run the three routines in a row (`Ran`) is a premise. The equations
alone say nothing: at runs that never hold they are met; they bind only together with `Ran`.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Joined.Top

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

namespace Links
variable {G : Chains} {A : Type} (C : Links G A)

/-- the first chain's part of a transcript of the whole file -/
abbrev tr₁ (τ : Tr C.all.shape) : Tr G.c₁ := Tr.fst τ
/-- the second chain's part -/
abbrev tr₂ (τ : Tr C.all.shape) : Tr G.c₂ := Tr.fst (Tr.snd (s := G.c₁) τ)
/-- the third chain's part -/
abbrev tr₃ (τ : Tr C.all.shape) : Tr G.c₃ := Tr.snd (s := G.c₂) (Tr.snd (s := G.c₁) τ)

/-- **The three chains in a row put out if and only if each does**, at what the chain before it has
handed on. -/
theorem all_out_iff (a : A) (τ : Tr C.all.shape) :
    C.all.out a τ = some () ↔
      ∃ b₁ b₂, C.out₁ a (C.tr₁ τ) = some b₁ ∧ C.out₂ b₁ (C.tr₂ τ) = some b₂ ∧
        C.out₃ b₂ (C.tr₃ τ) = some () := by
  have e : C.all.out a τ = (C.out₁ a (C.tr₁ τ)).bind fun b₁ =>
      (C.out₂ b₁ (C.tr₂ τ)).bind fun b₂ => C.out₃ b₂ (C.tr₃ τ) := rfl
  rw [e]
  constructor
  · intro h
    obtain ⟨b₁, h₁, h'⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b₂, h₂, h₃⟩ := Option.bind_eq_some_iff.1 h'
    exact ⟨b₁, b₂, h₁, h₂, h₃⟩
  · rintro ⟨b₁, b₂, h₁, h₂, h₃⟩
    rw [h₁]
    show (C.out₂ b₁ (C.tr₂ τ)).bind _ = _
    rw [h₂]
    exact h₃

end Links

/-- For each chain of a file: how a context reads as the chain's statement, what it means that the
chain's routine runs over the chain's written rounds, and the chain's success equation. -/
structure ThreeRuns (Ctx : Type) {G : Chains} {A : Type} (C : Links G A) where
  /-- a context before the first chain reads as a statement of the file -/
  rd₀ : Ctx → A → Prop
  /-- a context between the first chain and the second -/
  rd₁ : Ctx → C.A₁ → Prop
  /-- a context between the second chain and the third -/
  rd₂ : Ctx → C.A₂ → Prop
  /-- the first chain's routine runs from c to c' at the chain's written rounds -/
  run₁ : Ctx → Tr G.c₁ → Ctx → Prop
  /-- the second chain's -/
  run₂ : Ctx → Tr G.c₂ → Ctx → Prop
  /-- the third chain's -/
  run₃ : Ctx → Tr G.c₃ → Ctx → Prop
  /-- the first chain's success equation -/
  eq₁ : ∀ c a σ c', rd₀ c a → run₁ c σ c' → ∃ b, C.out₁ a σ = some b ∧ rd₁ c' b
  /-- the second chain's -/
  eq₂ : ∀ c a σ c', rd₁ c a → run₂ c σ c' → ∃ b, C.out₂ a σ = some b ∧ rd₂ c' b
  /-- the third chain's -/
  eq₃ : ∀ c a σ c', rd₂ c a → run₃ c σ c' → C.out₃ a σ = some ()

namespace ThreeRuns
variable {Ctx : Type} {G : Chains} {A : Type} {C : Links G A} (W : ThreeRuns Ctx C)

/-- The three routines have run in a row over τ, from a context that reads as a. -/
def Ran (a : A) (τ : Tr C.all.shape) : Prop :=
  ∃ c₀ c₁ c₂ c₃, W.rd₀ c₀ a ∧ W.run₁ c₀ (C.tr₁ τ) c₁ ∧ W.run₂ c₁ (C.tr₂ τ) c₂ ∧
    W.run₃ c₂ (C.tr₃ τ) c₃

/-- **Where the three routines have run in a row, the three chains in a row put out.** -/
theorem puts {a : A} {τ : Tr C.all.shape} (h : W.Ran a τ) : C.all.out a τ = some () := by
  obtain ⟨c₀, c₁, c₂, c₃, h₀, r₁, r₂, r₃⟩ := h
  obtain ⟨b₁, e₁, h₁⟩ := W.eq₁ c₀ a _ c₁ h₀ r₁
  obtain ⟨b₂, e₂, h₂⟩ := W.eq₂ c₁ b₁ _ c₂ h₁ r₂
  exact (C.all_out_iff a τ).2 ⟨b₁, b₂, e₁, e₂, W.eq₃ c₂ b₂ _ c₃ h₂ r₃⟩

end ThreeRuns

/-- **`decides`, as `row_sndBKT_links` asks it.** -/
theorem decides_of_three {Ctx : Type} {G : Chains} {Y : Type} {E : ExtSpec}
    {C : Links G (Y × E.Str)} (W : ThreeRuns Ctx C) (D : Desc G Y E) (early : Y → Y)
    (ran : ∀ x y (τ : Tr G.sh), D.accept x y τ = true → W.Ran (early x, y) τ) :
    ∀ x y (τ : Tr G.sh), D.accept x y τ = true → (C.all.out (early x, y) τ).isSome = true :=
  fun x y τ ha => by
    rw [W.puts (ran x y τ ha)]
    rfl

/-- **`decides`, as the tops with a record ask it.** -/
theorem decides_rec_of_three {Ctx : Type} {G : Chains} {X Rec : Type} {E : ExtSpec}
    {C : Links G ((X × Rec) × E.Str)} (W : ThreeRuns Ctx C) (D : Desc G (X × Rec) E)
    (early : X → X)
    (ran : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      W.Ran ((early x, rec), y) τ) :
    ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (C.all.out ((early x, rec), y) τ).isSome = true :=
  fun x rec y τ ha => by
    rw [W.puts (ran x rec y τ ha)]
    rfl

end TypedOracleCompiler.Joined
