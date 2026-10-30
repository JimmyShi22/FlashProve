-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Joined/BatchMid.lean: three joined chains, where the soundness clause of the second chain
is given in the form for the statements of a batch, with its own list of errors.

A second form of the compiler's verifier side, beside the library's own. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

CompileK/Joined/ExtractKnow.lean counts the errors of the second chain, whose verifier messages all
slots share, from a clause on one slot: all of them once for each slot (`sndBKT_of_three`), or those
of a head once for each slot and those of a tail once (`sndBKT_of_four`). The library has chains of
links with a clause for the statements of a batch (`IOR.KnowB`, Ior/BatchSeq.lean), in which each
link's list of errors says itself what is counted how often. Here such a clause is taken for the
whole second chain as it is.

Main names:
  `knowJ_iff_knowB`: the clause `KnowJ` of ExtractKnow.lean, at the reduction of an IOR, is the
    library's `IOR.KnowB`. By unfolding.
  `OneKey₁`: for slots with one external string, whatever the batch's transcript of the first chain:
    the statements that the first chain hands on have one key.
  `knowJ_mid`, `sndBKT_of_mid`: the first and the third chain with the clause `Know`, in local
    rounds; the second with `KnowJ` for the vectors of statements with one key; `OneKey₁`. Then the
    three in a row are sound round by round, with a witness, at late = none; the errors are the
    three lists in a row, as they are.

Limits: nothing here shows a clause of any protocol. All of `KnowJ`'s content hangs on which vectors
are admissible (Ior/BatchSeq.lean's own Limits): here "one key", which `OneKey₁` must supply.
In `sndBKT_of_mid` the relation is "on₀ (early x, y) → R₀ (early x, y) w": where on₀ fails every w
is a witness, and what `early` drops of an instance is bound by nothing. Asked beside the three
clauses, the two hand-overs and `OneKey₁`: that Q has the shape and the annotation of the three in a
row, and that where Q's verifier accepts the three in a row put out a statement.
No other file of the library uses `knowJ_mid` yet.

Terms: lean/GLOSSARY.md.

-/
import CompileK.Joined.ExtractKnow

set_option autoImplicit false

namespace CompileK.Joined
open Iop Prob

/-- `KnowJ` at the reduction of an IOR is the library's clause for the links of a batch. -/
theorem knowJ_iff_knowB {Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} (R : IOR Xi Ei Xo Eo)
    (A : RoundSplits R.shape) (N : ℕ) (adm : (Fin N → Option (Xi × Ei.Str)) → Prop)
    (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape) :
    KnowJ R.red A N adm on RA RB ext ε ↔ R.KnowB A N adm on RA RB ext ε :=
  Iff.rfl

section Mid
variable {Y W₀ : Type} {E : ExtSpec} {A₁ A₂ W₁ W₂ κ : Type} (Q : BatchInteractiveOracleProof Y E) (N : ℕ)
  (early : Y → Y) (K₁ : Reduction (Y × E.Str) A₁) (K₂ : Reduction A₁ A₂) (K₃ : Reduction A₂ Unit)
  (An₁ : RoundSplits K₁.shape) (An₂ : RoundSplits K₂.shape) (An₃ : RoundSplits K₃.shape)

/-- For slots with one external string, whatever the batch's transcript of the first chain: the
statements that the first chain hands on have one key. -/
def OneKey₁ (key : A₁ → κ) : Prop :=
  ∀ a₀ : Fin N → Option (Y × E.Str), SameStr a₀ → ∀ τ₁ : BTr N K₁.shape An₁,
    IOR.SameKey key fun j => (a₀ j).bind fun a => K₁.out a (τ₁.slot j)

variable (lo₁ : AllKind .lo K₁.shape An₁) (lo₃ : AllKind .lo K₃.shape An₃)
  {on₀ : Y × E.Str → Prop} {on₁ : A₁ → Prop} {on₂ : A₂ → Prop} {R₀ : Y × E.Str → W₀ → Prop}
  {R₁ : A₁ → W₁ → Prop} {R₂ : A₂ → W₂ → Prop} {e₁ : Y × E.Str → Tr K₁.shape → W₁ → W₀}
  {e₂ : A₁ → Tr K₂.shape → W₂ → W₁} {e₃ : A₂ → Tr K₃.shape → Unit → W₂} {ε₁ : Err K₁.shape}
  {ε₂ : Err K₂.shape} {ε₃ : Err K₃.shape} (d₀ : W₀) (d₁ : W₁)

include lo₁ lo₃ in
/-- The three chains in a row have the clause for the statements of a batch, for the vectors with
one external string. -/
theorem knowJ_mid (know₁ : K₁.Know on₀ R₀ R₁ e₁ ε₁) (key : A₁ → κ)
    (mid : KnowJ K₂ An₂ N (IOR.SameKey key) on₁ R₁ R₂ e₂ ε₂)
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (hands₂ : ∀ a τ b, on₁ a → K₂.out a τ = some b → on₂ b)
    (oneKey : OneKey₁ N K₁ An₁ key) :
    KnowJ (K₁.seq (K₂.seq K₃)) (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)) N SameStr on₀ R₀
      (fun _ (_ : Unit) => True)
      (Reduction.extSeq K₁ (K₂.seq K₃) e₁ (Reduction.extSeq K₂ K₃ e₂ e₃ d₁) d₀)
      (Err.app ε₁ (Err.app ε₂ ε₃)) :=
  knowJ_seq ((knowJ_lo lo₁ N know₁).adm fun _ _ => trivial)
    (knowJ_seq mid (knowJ_lo lo₃ N know₃) hands₂ (fun _ _ _ => trivial) d₁) hands₁ oneKey d₀

include lo₁ lo₃ in
/-- **Three chains in a row, the second with a clause for the statements of a batch, with a
witness**, at late = none. The witness map is the three extractors in a row, the later chain's
first; the errors are the three lists in a row, as they are. -/
theorem sndBKT_of_mid (know₁ : K₁.Know on₀ R₀ R₁ e₁ ε₁) (key : A₁ → κ)
    (mid : KnowJ K₂ An₂ N (IOR.SameKey key) on₁ R₁ R₂ e₂ ε₂)
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (hands₂ : ∀ a τ b, on₁ a → K₂.out a τ = some b → on₂ b)
    (oneKey : OneKey₁ N K₁ An₁ key)
    (hs : Q.loc.shape = (K₁.seq (K₂.seq K₃)).shape)
    (ha : HEq Q.ann (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (K₂.seq K₃)).out (early x, y) (cast (congrArg Tr hs) τ)).isSome = true) :
    Q.SndBKT N early none (fun x y w => on₀ (early x, y) → R₀ (early x, y) w)
      (fun x y τ => Reduction.extSeq K₁ (K₂.seq K₃) e₁ (Reduction.extSeq K₂ K₃ e₂ e₃ d₁) d₀
        (early x, y) (cast (congrArg Tr hs) τ) ())
      (cast (congrArg Err hs.symm) (Err.app ε₁ (Err.app ε₂ ε₃))) :=
  sndBKT_of_knowJ Q N early (K₁.seq (K₂.seq K₃)) (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)) on₀ R₀ _ _
    (knowJ_mid N K₁ K₂ K₃ An₁ An₂ An₃ lo₁ lo₃ d₀ d₁ know₁ key mid know₃ hands₁ hands₂ oneKey)
    hs ha hacc

end Mid

end CompileK.Joined
