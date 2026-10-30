-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/Lens.lean: THE COINS OF A COMPILED RUN AS A FAMILY OF COORDINATES, each a string
of bits that can be read and written, and A MEMBER: coins for which the law that the ties of this
folder ask does hold. Definitions, and one theorem-like definition whose fields are proved.

General definitions. This file states no goal of the release.

  CoinLens Ω μ ι len Z   The coins are a letter Ω with a law μ. ι names coordinates; coordinate c
      has len c bits. get reads a coordinate, upd writes one. Within the set Z: what is written is
      read back, and the coordinate is len c uniform bits, independent of all the rest (Resamples,
      Rom/Handle/Coins.lean). Writing one coordinate leaves every other as it is.
  CoinLens.finset F   A MEMBER, for every finite set F of coordinates: Ω is the type of all tuples
      of bits over F, μ is uniform, Z is F. A coordinate outside F reads as the empty string.
  RunCo, lenRun   the coordinates of a compiled run's coins: the first salt; the free bits of the
      string behind the slot value; the sibling digests; the free bits of each leaf's salt.
  RunLens   CoinLens at these.
  RunLens.leaf   its leaves' part, in the form in which the ties on trees take it (LeafLens,
      Johnson/TokenSide/TieTree.lean).
  coRun   the compiled prover's coins (Coins, OnBytes/Prover/Defs.lean) at ω.

Why no law is asked outside Z: a compiled run's coins hold a salt for every natural number of a
round, a tree and a leaf. No law on such coins makes all of them uniform and independent. A run
reads finitely many.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.TieTree
import Johnson.TokenSide.Finish

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- **Coins as a family of coordinates.** -/
structure CoinLens (Ω : Type) (μ : PMF Ω) (ι : Type) (len : ι → ℕ) (Z : ι → Prop) where
  get : Ω → ι → Bits
  upd : (c : ι) → (Fin (len c) → Bool) → Ω → Ω
  get_same : ∀ c u ω, Z c → get (upd c u ω) c = List.ofFn u
  get_ne : ∀ c u ω c', c' ≠ c → get (upd c u ω) c' = get ω c'
  law : ∀ c, Z c → Resamples μ (unif (Fin (len c) → Bool)) (upd c)

/-- **A member**: all tuples of bits over a finite set F of coordinates, uniform. -/
def CoinLens.finset {ι : Type} [DecidableEq ι] (len : ι → ℕ) (F : Finset ι) :
    CoinLens (∀ c : {c // c ∈ F}, Fin (len c.1) → Bool)
      (unif (∀ c : {c // c ∈ F}, Fin (len c.1) → Bool)) ι len (fun c => c ∈ F) where
  get := fun ω c => if h : c ∈ F then List.ofFn (ω ⟨c, h⟩) else []
  upd := fun c u ω => if h : c ∈ F then Function.update ω ⟨c, h⟩ u else ω
  get_same := fun c u ω h => by
    simp only [dif_pos h, Function.update_self]
  get_ne := fun c u ω c' hne => by
    by_cases h : c ∈ F
    · by_cases h' : c' ∈ F
      · simp only [dif_pos h, dif_pos h']
        rw [Function.update_of_ne fun e => hne (congrArg Subtype.val e)]
      · simp only [dif_neg h']
    · simp only [dif_neg h]
  law := fun c h => by
    have := (Resamples.self (unif (Fin (len c) → Bool))).pi
      (C := fun c : {c // c ∈ F} => Fin (len c.1) → Bool) ⟨c, h⟩
    refine this.congr fun u ω => ?_
    simp only [dif_pos h]

/-! ## The coins of a compiled run -/

/-- the coordinates of a compiled run's coins -/
inductive RunCo
  /-- the first salt -/
  | salt
  /-- the free bits of the string behind the slot value -/
  | rs
  /-- sibling digest number n of the request path -/
  | path (n : ℕ)
  /-- the free bits of a leaf's salt: round, own component?, tree, leaf -/
  | leaf (i : ℕ) (b : Bool) (k j : ℕ)
  deriving DecidableEq

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- the number of bits of a coordinate -/
def lenRun (ln : RunLen lam L) : RunCo → ℕ
  | .salt => ln.sFS
  | .rs => ln.rs
  | .path _ => lam
  | .leaf _ _ _ _ => ln.fr

/-- the coins of a compiled run, as coordinates -/
abbrev RunLens (Ω : Type) (μ : PMF Ω) (ln : RunLen lam L) (Z : RunCo → Prop) : Type :=
  CoinLens Ω μ RunCo (lenRun ln) Z

variable {Ω : Type} {μ : PMF Ω} {ln : RunLen lam L} {Z : RunCo → Prop}

/-- the leaves' part -/
def RunLens.leaf (rl : RunLens Ω μ ln Z) :
    LeafLens Ω μ ln.fr (fun i b k j => Z (.leaf i b k j)) where
  get := fun ω i b k j => rl.get ω (.leaf i b k j)
  upd := fun i b k j u ω => rl.upd (.leaf i b k j) u ω
  get_same := fun i b k j u ω h => rl.get_same (.leaf i b k j) u ω h
  get_ne := fun i b k j u ω i' b' k' j' h => rl.get_ne (.leaf i b k j) u ω (.leaf i' b' k' j')
    fun e => h (by cases e; exact ⟨rfl, rfl, rfl, rfl⟩)
  law := fun i b k j h => rl.law (.leaf i b k j) h

/-- **The compiled prover's coins at ω.** A leaf's salt: its start, then its free bits. The string
behind the slot value: its free bits, then its public end. -/
def coRun (rl : RunLens Ω μ ln Z) (pre : ℕ → Bool → Bits → Bits) (ω : Ω) : Coins lam L :=
  ⟨rl.get ω .salt, fun i b k j => pre i b (rl.get ω .salt) ++ rl.get ω (.leaf i b k j), ln.pad,
    ln.slot, (List.range ln.dq).map fun n => digOf lam (rl.get ω (.path n)),
    rl.get ω .rs ++ ln.rsw⟩

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.CoinLens.finset
