-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpFormatBlind.lean: under the hypotheses below, a base chain that reads only some entries
is blind to the masks of later blocks.

Definitions, statements and proofs. Glue; no protocol.

Why: a chain of masked blocks is honest-verifier zero knowledge if each block's own masks are still
fresh when the block begins, in this sense: `(H₁.seq H₂).ExactWith`, the conclusion of
`Spec.exact_seq_masked` (Ior/KnowCollRulesMask.lean), under its hypotheses (one is `H₁.Fresh`). For
the bundles the sense is `GoodT`, the conclusion of `Spec.goodT_seq_masked` in the same file, under
its hypotheses (one is `H₁.Fresh`). For that (`H₁.Fresh`) every earlier block must not look at them
(`Honest.Blind kc kc Mk put put`): if the later block's reading kc of a second witness is "put M"
(M : Mk) of its reading of the first, then the earlier block's honest run shows the same transcript
and the same explicit output at both, and hands the relation between the two readings on.

Main names:
  `b.SameOn msg Rd`: at the base (`BkA`, Cb/Ld/LdLkpTreeP.lean): at two witnesses whose entries (msg
    of the tuple of messages) agree on Rd, the honest run of b has the same transcript and the same
    explicit output, at every explicit input, coin and verifier messages. "b reads the entries in Rd
    only".
  `blind_of_sameOn`: over a signature: b `BkA.Plain` (Cb/Ld/LdLkpFormat.lean; of its fields the
    proof uses: its honest prover ends with the witness with which it began) and `b.SameOn msg Rd`:
    then `S.liftH b.H` is blind (`Honest.Blind kc kc Mk put put`) for every kc, Mk, put such that,
    whenever kc of a second witness is put m of kc of the first, the two witnesses' entries in Rd
    agree.
  `blind_base`: the same at the base.

`H.Blind kci kco Mk puti puto` (`Honest.Blind`) asks that, for all input witnesses w and w', every M
in `Mk`, every explicit part x of an input statement, all coins c of the honest prover and every
value ρ of the verifier's randomness, if `kci w' = puti M (kci w)`, then the honest prover's runs
from w' and from w, at x, c and ρ, have the same full transcript and end with the same explicit part
of the output statement, and `kco` of the output witness with which the run from w' ends is `puto M`
of `kco` of the output witness with which the run from w ends. In `blind_base` and `blind_of_sameOn`
it stands as the conclusion.

Limits: this file does not say which entries a given chain reads.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpFormat
import Ior.KnowCollRulesMask

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob

/-- The honest run reads the entries in Rd only: at two witnesses whose entries (msg of the tuple of
messages) agree on Rd, the honest run of b has the same transcript and the same explicit output, at
every explicit input, coin and verifier messages. -/
def BkA.SameOn {K M X₁ X₂ : Type} {Ex : ExtSpec} {Wp E J : Type} (b : BkA K M X₁ X₂ Ex Wp)
    (msg : M → J → E) (Rd : J → Prop) : Prop :=
  ∀ (u u' : M × Wp) (x : X₁) (c : b.H.Coin) (ρ : Rho b.R.shape),
    (∀ j, Rd j → msg u'.1 j = msg u.1 j) →
    ((b.H.strat u' x c).run ρ).1 = ((b.H.strat u x c).run ρ).1 ∧
    ((b.H.strat u' x c).run ρ).2.1 = ((b.H.strat u x c).run ρ).2.1

section
variable {K M X₁ X₂ : Type} {Ex : ExtSpec} {Wp E J : Type}

theorem sameOn_mono {b : BkA K M X₁ X₂ Ex Wp} {msg : M → J → E} {Rd Rd' : J → Prop}
    (h : b.SameOn msg Rd) (hs : ∀ j, Rd j → Rd' j) : b.SameOn msg Rd' :=
  fun u u' x c ρ hu => h u u' x c ρ fun j hj => hu j (hs j hj)

theorem blind_base {b : BkA K M X₁ X₂ Ex Wp} (hp : b.Plain) {msg : M → J → E} {Rd : J → Prop}
    (h : b.SameOn msg Rd) {Kk : Type} (kc : M × Wp → Kk) (Mk : Type) (put : Mk → Kk → Kk)
    (hk : ∀ w w' m, kc w' = put m (kc w) → ∀ j, Rd j → msg w'.1 j = msg w.1 j) :
    b.H.Blind kc kc Mk put put := by
  intro w w' m x c ρ hw
  obtain ⟨h1, h2⟩ := h w w' x c ρ (hk w w' m hw)
  refine ⟨h1, h2, ?_⟩
  rw [hp.keepsW, hp.keepsW]
  exact hw

end

theorem blind_of_sameOn {E : Type} (S : Sig E) {K St X' Wp J : Type} {E₀ : ExtSpec}
    {b : BkA K S.Msg St X' E₀ Wp} (hp : b.Plain) {msg : S.Msg → J → E} {Rd : J → Prop}
    (h : b.SameOn msg Rd) {Kk : Type} (kc : S.Wit × Wp → Kk) (Mk : Type) (put : Mk → Kk → Kk)
    (hk : ∀ w w' m, kc w' = put m (kc w) → ∀ j, Rd j → msg (S.msgs w'.1) j = msg (S.msgs w.1) j) :
    (S.liftH b.H).Blind kc kc Mk put put := by
  intro w w' m x c ρ hw
  obtain ⟨h1, h2⟩ := h (S.msgs w.1, w.2) (S.msgs w'.1, w'.2) x.1 c ρ (hk w w' m hw)
  have run : ∀ v : S.Wit × Wp, ((S.liftH b.H).strat v x c).run ρ =
      (((b.H.strat (S.msgs v.1, v.2) x.1 c).run ρ).1,
        ((((b.H.strat (S.msgs v.1, v.2) x.1 c).run ρ).2.1, x.2),
          (v.1, ((b.H.strat (S.msgs v.1, v.2) x.1 c).run ρ).2.2.2))) := by
    intro v
    show (((b.H.keep S.Smp S.ext).mapW (fun w : S.Wit × Wp => (S.msgs w.1, w.2))
          fun w o => (w.1, o.2)).strat
        v x c).run ρ = _
    rw [Honest.mapW_run]
    show ((((b.H.keepX S.Smp).strat (S.msgs v.1, v.2) x c).run ρ).1,
        ((((b.H.keepX S.Smp).strat (S.msgs v.1, v.2) x c).run ρ).2.1,
          (v.1, (((b.H.keepX S.Smp).strat (S.msgs v.1, v.2) x c).run ρ).2.2.2))) = _
    rw [Honest.keepX_run]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [run, run]
    exact h1
  · rw [run, run]
    exact congrArg (fun o => (o, x.2)) h2
  · rw [lift_keepsW S hp, lift_keepsW S hp]
    exact hw

end Cb
