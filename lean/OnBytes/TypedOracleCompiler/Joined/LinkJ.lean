-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/LinkJ.lean: links with keys, for the statements of a batch, over reductions; and
three joined chains each of which is such a link.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The library's chains for a batch are made of links with keys (`ldk_LinkB`,
Cb/Ld/LdLinBProofs.lean): a link has the soundness clause for the vectors of statements with one
key, and takes such vectors to vectors with one key; its list of errors says itself what is counted
once and what once for each slot. Here the same notion is said over reductions (`LinkJ`), so that
the chains of a file can be laid as such links, with the library's lists as they are.

Main names:
  `LinkJ K An N key key' on RA RB ext ε`: `know`: the clause `KnowJ`
    (CompileK/Joined/ExtractKnow.lean) for the vectors with one key; `adm`: on every transcript of
    the whole batch, what the link hands on has one key.
  `LinkJ.seq`: two links in a row.
  `LinkJ.ofLocal`: a reduction with the clause `Know`, in local rounds, whose new key is a function
    of the old: the same errors.
  `LinkJ.ofShared`: the same under shared verifier messages: the errors once for each slot.
  `LinkJ.ofKB`: a link of the library, at the reduction of its IOR. By unfolding.
  `sndBKT_of_links`: three chains in a row, each a link; the first one's key is the external
    string. Then the three in a row are sound round by round, with a witness, at late = none; the
    errors are the three lists in a row, as they are.

Limits: nothing here shows a clause of any protocol. All of a link's content hangs on its keys: at
a key that tells all statements apart `know` speaks of vectors with one statement alone.
In `sndBKT_of_links` the relation is "on₀ (early x, y) → R₀ (early x, y) w": where on₀ fails every w
is a witness, and what `early` drops of an instance is bound by nothing. Asked beside the three
links: the two hand-overs, that Q has the shape and the annotation of the three in a row, and that
where Q's verifier accepts the three in a row put out a statement.

Terms: lean/GLOSSARY.md.

-/
import CompileK.Joined.BatchMid
import Cb.Ld.LdLinBProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Iop
open _root_.CompileK.Joined (KnowJ AllKind knowJ_seq knowJ_lo knowJ_sh sndBKT_of_knowJ)

/-- A link of a chain in a batch, with keys, over a reduction: knowledge sound for the vectors with
one key, and it takes such vectors to vectors with one key. -/
structure LinkJ {A B κ κ' WA WB : Type} (K : Reduction A B) (An : RoundSplits K.shape) (N : ℕ)
    (key : A → κ) (key' : B → κ') (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
    (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape) : Prop where
  know : KnowJ K An N (IOR.SameKey key) on RA RB ext ε
  adm : ∀ a, IOR.SameKey key a →
    ∀ τ : BTr N K.shape An, IOR.SameKey key' fun j => (a j).bind fun aj => K.out aj (τ.slot j)

section Rules
variable {A B C κ₁ κ₂ κ₃ WA WB WC : Type} {N : ℕ}

/-- Two links in a row: errors in a row; the second's extractor, then the first's. -/
theorem LinkJ.seq {K₁ : Reduction A B} {K₂ : Reduction B C} {A₁ : RoundSplits K₁.shape}
    {A₂ : RoundSplits K₂.shape} {k₁ : A → κ₁} {k₂ : B → κ₂} {k₃ : C → κ₃} {on₁ : A → Prop}
    {on₂ : B → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop} {RC : C → WC → Prop}
    {e₁ : A → Tr K₁.shape → WB → WA} {e₂ : B → Tr K₂.shape → WC → WB} {ε₁ : Err K₁.shape}
    {ε₂ : Err K₂.shape} (h₁ : LinkJ K₁ A₁ N k₁ k₂ on₁ RA RB e₁ ε₁)
    (h₂ : LinkJ K₂ A₂ N k₂ k₃ on₂ RB RC e₂ ε₂)
    (hon : ∀ a τ b, on₁ a → K₁.out a τ = some b → on₂ b) (d : WA) :
    LinkJ (K₁.seq K₂) (RoundSplits.app A₁ A₂) N k₁ k₃ on₁ RA RC (Reduction.extSeq K₁ K₂ e₁ e₂ d)
      (Err.app ε₁ ε₂) :=
  ⟨knowJ_seq h₁.know h₂.know hon h₁.adm d, fun a ha τ => by
    have h := h₂.adm _ (h₁.adm a ha (ldk_fstB τ)) (ldk_sndB τ)
    refine cast (congrArg (IOR.SameKey k₃) (funext fun j => ?_)) h
    rw [Option.bind_assoc]
    refine congrArg (a j).bind (funext fun aj => ?_)
    rw [← ldk_slot_fstB, ← ldk_slot_sndB]⟩

variable {K : Reduction A B} {An : RoundSplits K.shape} {key : A → κ₁} {key' : B → κ₂} {on : A → Prop}
  {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA} {ε : Err K.shape}

/-- A reduction with the clause `Know`, in local rounds; the new key is a function F of the old. -/
theorem LinkJ.ofLocal (hAn : AllKind .lo K.shape An) (N : ℕ) (h : K.Know on RA RB ext ε)
    (F : κ₁ → κ₂) (hF : ∀ a τ b, K.out a τ = some b → key' b = F (key a)) :
    LinkJ K An N key key' on RA RB ext ε :=
  ⟨(knowJ_lo hAn N h).adm fun _ _ => trivial, fun _ ha τ =>
    ldk_sameKey_bind (fun j aj => K.out aj (τ.slot j)) F (fun _ aj b hb => hF aj _ b hb) ha⟩

/-- The same under shared verifier messages: the errors once for each slot. -/
theorem LinkJ.ofShared (hAn : AllKind .sh K.shape An) (N : ℕ) (h : K.Know on RA RB ext ε)
    (F : κ₁ → κ₂) (hF : ∀ a τ b, K.out a τ = some b → key' b = F (key a)) :
    LinkJ K An N key key' on RA RB ext (Err.times N ε) :=
  ⟨(knowJ_sh hAn N h).adm fun _ _ => trivial, fun _ ha τ =>
    ldk_sameKey_bind (fun j aj => K.out aj (τ.slot j)) F (fun _ aj b hb => hF aj _ b hb) ha⟩

end Rules

/-- A link of the library, at the reduction of its IOR. -/
theorem LinkJ.ofKB {Xi Xo κ κ' : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {A : RoundSplits R.shape} {N : ℕ} {key : Xi × Ei.Str → κ} {key' : Xo × Eo.Str → κ'}
    {RA : Xi × Ei.Str → Wi → Prop} {RB : Xo × Eo.Str → Wo → Prop}
    {ext : Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    (h : ldk_LinkB R A N key key' RA RB ext ε) :
    LinkJ R.red A N key key' (fun _ => True) RA RB ext ε :=
  ⟨h.know, h.adm⟩

section Row
variable {Y W₀ : Type} {E : ExtSpec} {A₁ A₂ W₁ W₂ κ₁ κ₂ : Type} (Q : BatchInteractiveOracleProof Y E) (N : ℕ)
  (early : Y → Y) (K₁ : Reduction (Y × E.Str) A₁) (K₂ : Reduction A₁ A₂) (K₃ : Reduction A₂ Unit)
  (An₁ : RoundSplits K₁.shape) (An₂ : RoundSplits K₂.shape) (An₃ : RoundSplits K₃.shape)
  {on₀ : Y × E.Str → Prop} {on₁ : A₁ → Prop} {on₂ : A₂ → Prop} {R₀ : Y × E.Str → W₀ → Prop}
  {R₁ : A₁ → W₁ → Prop} {R₂ : A₂ → W₂ → Prop} {e₁ : Y × E.Str → Tr K₁.shape → W₁ → W₀}
  {e₂ : A₁ → Tr K₂.shape → W₂ → W₁} {e₃ : A₂ → Tr K₃.shape → Unit → W₂} {ε₁ : Err K₁.shape}
  {ε₂ : Err K₂.shape} {ε₃ : Err K₃.shape} (d₀ : W₀) (d₁ : W₁)

/-- **Three chains in a row, each a link with keys, with a witness**, at late = none. The first
chain's key is the external string. The errors are the three lists in a row, as they are. -/
theorem sndBKT_of_links (k₁ : A₁ → κ₁) (k₂ : A₂ → κ₂)
    (l₁ : LinkJ K₁ An₁ N (Prod.snd : Y × E.Str → E.Str) k₁ on₀ R₀ R₁ e₁ ε₁)
    (l₂ : LinkJ K₂ An₂ N k₁ k₂ on₁ R₁ R₂ e₂ ε₂)
    (l₃ : LinkJ K₃ An₃ N k₂ (fun _ : Unit => ()) on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (hands₂ : ∀ a τ b, on₁ a → K₂.out a τ = some b → on₂ b)
    (hs : Q.loc.shape = (K₁.seq (K₂.seq K₃)).shape)
    (ha : HEq Q.ann (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (K₂.seq K₃)).out (early x, y) (cast (congrArg Tr hs) τ)).isSome = true) :
    Q.SndBKT N early none (fun x y w => on₀ (early x, y) → R₀ (early x, y) w)
      (fun x y τ => Reduction.extSeq K₁ (K₂.seq K₃) e₁ (Reduction.extSeq K₂ K₃ e₂ e₃ d₁) d₀
        (early x, y) (cast (congrArg Tr hs) τ) ())
      (cast (congrArg Err hs.symm) (Err.app ε₁ (Err.app ε₂ ε₃))) :=
  sndBKT_of_knowJ Q N early (K₁.seq (K₂.seq K₃)) (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)) on₀ R₀ _ _
    (l₁.seq (l₂.seq l₃ hands₂ d₁) hands₁ d₀).know hs ha hacc

end Row

end TypedOracleCompiler.Joined
