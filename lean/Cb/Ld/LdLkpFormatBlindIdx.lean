-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpFormatBlindIdx.lean: blindness of a base chain whose entries are read off the messages
and the further witness; the case of an encoded index.

Definitions, statements and proofs. Glue; no protocol.

Cb/Ld/LdLkpFormatBlind.lean has: a plain base chain whose honest run is the same at tuples of
messages that agree on Rd is blind for all kc, Mk, put that change no entry in Rd (exactly: the
premise `hk` in its statement, `blind_of_sameOn`, which speaks of all pairs of witnesses whose
readings by kc differ by the overwriting: `kc w' = put m (kc w)`). There the entries are read off
the tuple of messages alone. In the preamble of weights-formedness the entries are (matrix of the
index) and (entries of the messages), and the honest prover reads the index's message off its
further witness (its prover encoded index: Cb/Ld/LdWfIdx.lean: `idxH`). Here is the rule for a
reading rd of (messages, further witness).

Main names:
  `b.SameOnW rd Rd`: at two witnesses whose entries rd agree on Rd the honest run of b has the same
    transcript and the same explicit output.
  `blind_of_sameOnW`: over a signature: b plain, `b.SameOnW rd Rd` ⇒ `S.liftH b.H` is blind
    (`Honest.Blind kc kc Mk put put`, Ior/KnowCollRulesMask.lean) for every kc, Mk, put such that,
    whenever kc of a second witness is put m of kc of the first, the two witnesses' entries rd in Rd
    agree.
  `sameOnW_idx`: a block on tuples (message of the index, messages), with the honest side `idxH`:
    `SameOn msg Rd` (`BkA.SameOn`, Cb/Ld/LdLkpFormatBlind.lean) on those tuples gives `SameOnW` for
    the reading (m, (prover encoded index, ..)) ↦ msg (its message, m).
  `Spec.ldLkpFmt_blindIdx`: the assembled lookup `LkAsm` (Cb/Ld/LdLkpAsm.lean) with keys over an
    encoded index (Cb/Ld/LdLkpAsmPull.lean: `A.subIN ι C S msg`): from a Piece
    (Cb/Ld/LdLkpMaskKit.lean) on `A.baseN` at tuples (message of the index, messages), with both
    reading maps `fun w => msg w.1` and sets Sr, Sw: blind (`Honest.Blind kc kc Mk put put`) for
    every kc, Mk, put such that, whenever kc of a second witness is put m of kc of the first, the
    two witnesses' entries in Sr, the entries that the lookup reads, agree. The preamble's own
    lookups are `LkAsm2` (Cb/Ld/LdWfBlocks.lean).

`H.Blind kci kco Mk puti puto` (`Honest.Blind`) asks that, for all input witnesses w and w', every M
in `Mk`, every explicit part x of an input statement, all coins c of the honest prover and every
value ρ of the verifier's randomness, if `kci w' = puti M (kci w)`, then the honest prover's runs
from w' and from w, at x, c and ρ, have the same full transcript and end with the same explicit part
of the output statement, and `kco` of the output witness with which the run from w' ends is `puto M`
of `kco` of the output witness with which the run from w ends. In `blind_of_sameOnW` and
`Spec.ldLkpFmt_blindIdx` it stands as the conclusion.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpFormatPiece
import Cb.Ld.LdLkpAsmPullProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

/-- The honest run reads the entries in Rd only, the entries being read off the whole witness: at
two witnesses whose entries rd agree on Rd the honest run of b has the same transcript and the same
explicit output. -/
def BkA.SameOnW {K M X₁ X₂ : Type} {Ex : ExtSpec} {Wp E J : Type} (b : BkA K M X₁ X₂ Ex Wp)
    (rd : M × Wp → J → E) (Rd : J → Prop) : Prop :=
  ∀ (u u' : M × Wp) (x : X₁) (c : b.H.Coin) (ρ : Rho b.R.shape), (∀ j, Rd j → rd u' j = rd u j) →
    ((b.H.strat u' x c).run ρ).1 = ((b.H.strat u x c).run ρ).1 ∧
    ((b.H.strat u' x c).run ρ).2.1 = ((b.H.strat u x c).run ρ).2.1

theorem sameOnW_of_sameOn {K M X₁ X₂ : Type} {Ex : ExtSpec} {Wp E J : Type}
    {b : BkA K M X₁ X₂ Ex Wp} {msg : M → J → E} {Rd : J → Prop} (h : b.SameOn msg Rd) :
    b.SameOnW (fun w => msg w.1) Rd := h

theorem blind_of_sameOnW {E : Type} (S : Sig E) {K St X' Wp J : Type} {E₀ : ExtSpec}
    {b : BkA K S.Msg St X' E₀ Wp} (hp : b.Plain) {rd : S.Msg × Wp → J → E} {Rd : J → Prop}
    (h : b.SameOnW rd Rd) {Kk : Type} (kc : S.Wit × Wp → Kk) (Mk : Type) (put : Mk → Kk → Kk)
    (hk : ∀ w w' m,
      kc w' = put m (kc w) → ∀ j, Rd j → rd (S.msgs w'.1, w'.2) j = rd (S.msgs w.1, w.2) j) :
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

/-- With an encoded index. -/
theorem sameOnW_idx {K M X X' Wp E J : Type} (C : ConfigurationWithOutOfDomainSample) {b : BkA K (C.Msg × M) X X' C.E0 Wp}
    {msg : C.Msg × M → J → E} {Rd : J → Prop} (h : b.SameOn msg Rd) :
    (⟨b.R, idxH C b.H, b.P⟩ : BkA K M X X' C.E0 (C.PIdx × Wp)).SameOnW
      (fun w => msg (w.2.1.1.1, w.1)) Rd := by
  intro u u' x c ρ hu
  obtain ⟨h1, h2⟩ := h (idxIn C u) (idxIn C u') x c ρ hu
  show (((b.H.mapW (idxIn C) fun w o => (w.1, (w.2.1, o.2))).strat u' x c).run ρ).1 =
      (((b.H.mapW (idxIn C) fun w o => (w.1, (w.2.1, o.2))).strat u x c).run ρ).1 ∧
    (((b.H.mapW (idxIn C) fun w o => (w.1, (w.2.1, o.2))).strat u' x c).run ρ).2.1 =
      (((b.H.mapW (idxIn C) fun w o => (w.1, (w.2.1, o.2))).strat u x c).run ρ).2.1
  rw [Honest.mapW_run, Honest.mapW_run]
  exact ⟨h1, h2⟩

theorem noOrcs_baseN {E : Type} [Field E] [Fintype E] (A : LkAsm E) {N : Type} (ι : N → A.J)
    (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) :
    noOrcs (A.baseN ι Ex M Wp Kc msg).R.shape :=
  noOrcs_base Ex M Wp Kc A msg

namespace Spec

/-- Under the hypotheses below, the assembled lookup with keys over an encoded index is blind to the
masks of later blocks. -/
def ldLkpFmt_blindIdx : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (A : LkAsm E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E)
      (msg : C.Msg × S.Msg → A.J → E)
      (D : MJ E A.J (A.baseN ι C.E0 (C.Msg × S.Msg) Unit Unit msg).R) (Sr Sw : A.J → Prop),
    D.Piece (A.baseN ι C.E0 (C.Msg × S.Msg) Unit Unit msg).H (fun w => msg w.1)
      (fun w => msg w.1) Sr Sw →
    ∀ (Kk : Type) (kc : S.Wit × (C.PIdx × Unit) → Kk) (Mk : Type) (put : Mk → Kk → Kk),
      (∀ w w' m, kc w' = put m (kc w) →
        ∀ j, Sr j → msg (w'.2.1.1.1, S.msgs w'.1) j = msg (w.2.1.1.1, S.msgs w.1) j) →
      (A.subIN ι C S msg).H.Blind kc kc Mk put put

end Spec

theorem ldLkpFmt_blindIdx :
    Spec.ldLkpFmt_blindIdx := fun E _ _ A N ι C S msg _ _ _ hP _ kc Mk put hk =>
  blind_of_sameOnW (b := A.baseIN ι C S.Msg msg) S (ldLkpAsmN_plainI E A N ι C S.Msg msg)
    (sameOnW_idx C (sameOn_of_piece (noOrcs_baseN A ι C.E0 (C.Msg × S.Msg) Unit Unit msg) hP))
    kc Mk put hk

end Cb
