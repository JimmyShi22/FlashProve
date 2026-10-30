-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldWfSpec.lean: the conditions on the parameters of the builder of Cb/Ld/LdBldWf.lean, and
statements that under these conditions the data that it builds meet part of what later theorems take
as hypotheses.

A record and statements; the proofs are in Cb/Ld/LdBldWfDef.lean (what holds by the definitions and
by numbers), Cb/Ld/LdBldWfPlace.lean (places), Cb/Ld/LdBldWfProofs.lean. Generic: any finite fields
F, Fp and any finite field E that is an algebra over both, any number of forests. Nothing assumed
beyond the hypotheses of the statements and whatever the arguments hold as proofs.
X : `BldWf F E Fp` is the builder's record of parameters; `X.Zw hpl` and `X.V hpl` are what it
builds: all data of weights-formedness (`LdWfE`, Cb/Ld/LdWfEnd.lean) and the standard sender's data
beside them.

Main names:
  `X.Room p`: the conditions. pos: every forest has a key variable; adm: the lookup's three
    conditions on numbers (`Adm`, Cb/Ld/LdLkp.lean): the digits that count have positions; 2^(key
    variables) < 2^(digits); 2^(table variables) · (2^(digits) - 1) < p; injB, injM: the two
    placings are injective; zOK: the batching's zero-evader is one; fair: the seeds are fair; supR:
    the public support of each row of forest f holds the fixed name, the digits of f and all own
    masks of its lookup but the two inner masks of the last level of the keys' tree; describes, the
    model's one clause: a message of the encoded index holds an index if and only if the keys of all
    forests lie in their tables.
  `Spec.bldWf_hpl`: `X.Room p` ⇒ the masks of all blocks stand at different free entries (`X.Hpl`):
    the argument that `X.Zw`, `X.V` take.
  `Spec.bldWf_std`: `X.Room p` ⇒ for every hpl, the six clauses on the standard sender's data of
    `Gl.FinalPP` (Cb/Gl/GlFinalPpP.lean) and its kin, in their words (wfStd, wfBody, wfBd, wfAtL,
    wfAtB, wfNoPad), at `X.Zw hpl`, `X.V hpl`, with `X.finWfI` as the term for "finitely many
    vectors of masks".
  `Spec.bldWf_rest2`: `X.Room p` ⇒ for every hpl, `(X.Zw hpl).Rest2 p`: all eighteen fields. `Rest2`
    (Cb/Ld/LdWfEnd.lean) has the conditions on `LdWfE` that speak neither of a code of an oracle
    message, nor of a list, nor of the sender (but for: its seeds are fair; the vectors that it
    computes are the multiplicities).
  `Spec.bldWf_where`: where the places stand, for whoever builds the offline plan; no `X.Room p` is
    asked. For a forest f ≤ `X.n`: the names in the support of a claim's mask form are exactly the
    two inner masks of the last level of the forest's keys' tree; every own mask of the forest's
    lookup stands at the free entry that pM gives it; a hiding coefficient of the batching stands at
    the free entry that pM gives it.

Notation: `p`: a natural number, the argument of `X.Room` and `Rest2`; `hpl`: a proof of `X.Hpl`.

Limits: this file says nothing on codes, lists, samples of the messages. It
does not say that `X.Room p` can be met.

Beyond the conditions of
`X.Room p` and the fields of `Rest2`, this file says nothing on the size of anything.
It is asked of nobody which messages there are. With two messages, pB into the first, pM sending the
inner masks of the last levels and the batching's coefficients into the second and all other masks
into the first, and gR f b := "stands in the first", supR holds and the placement is the
write-up's (by reading).
Declared, against the write-up (by reading).
(1) The order of digits: a corner of a cube is listed top digit first here (`Alg.bits`), lowest
digit first there; so a column point is (code row, place inside) here and (low coordinates, high
coordinates) there: a renaming of the coordinates of a verifier's point; as numbers code row, place
and key are the same.
(2) Wider here, harmless: the number of key row variables may differ from forest to forest; offsets
and coefficients lie in E; a table is any function; any number of messages.
(3) An oddity: off the ranges a mask's place is the fixed data name `X.dN`, and supR asks `X.dN` in
every row's support: the records want place maps that are total on ℕ; no row reads `X.dN` on that
account: gR is "what a row may read".
(4) For the write-up's placement whole a value has to add, beside the two placings: digits
in main rows, masks in mask rows; each message's pad in a mask row; the second message has mask rows
only; both go out in one prover message under one joint seed.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdBldWf

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

/-- The conditions. -/
structure BldWf.Room {F E Fp : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    [Field Fp] [Fintype Fp] [Algebra Fp E] (X : BldWf F E Fp) (p : ℕ) : Prop where
  pos   : ∀ f, f ≤ X.n → 1 ≤ X.rv f + X.num.k
  adm   : ∀ f, f ≤ X.n →
    X.nd f + 1 ≤ 2 ^ X.w f ∧
    2 ^ (X.rv f + X.num.k) < 2 ^ (X.nd f + 1) ∧
    2 ^ X.d f * (2 ^ (X.nd f + 1) - 1) < p
  injB  : Function.Injective X.pB
  injM  : Function.Injective X.pM
  zOK   : X.Z.OK
  fair  : X.Sd.Fair
  supR  : ∀ f, f ≤ X.n →
    ∀ b,
      X.gR f b X.dN ∧
      (∀ u j, X.gR f b (X.bitN f u j)) ∧
      ∀ a : X.num.LkM E f, (∀ h c, a ≠ .k (X.num.v' f) h (Sum.inr c)) → X.gR f b (X.mkN f a)
  /-- the model's one clause -/
  describes : ∀ U,
    (X.Cf.conf.held U).isSome ↔
    ∀ f, f ≤ X.n → InTable (X.rv f + X.num.k) (X.d f) (X.key f U) (X.tab f)

namespace Spec
section
variable (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E]

def bldWf_hpl : Prop := ∀ (X : BldWf F E Fp) (p : ℕ), X.Room p → X.Hpl

/-- States: `X.Room p` gives, for every `hpl`, the six clauses on the standard sender's data. -/
def bldWf_std : Prop :=
  ∀ (X : BldWf F E Fp) (p : ℕ), X.Room p →
    ∀ hpl : X.Hpl,
      ((⟨(X.Zw hpl).D, (X.Zw hpl).X⟩ : Σ D, (X.Zw hpl).K.MaskPl D (X.Zw hpl).Rl) =
        ⟨(X.Zw hpl).W.P.stdD (X.V hpl).Y (X.V hpl).dat (X.V hpl).w0,
          @LdWfP.Lks.stdX E _ _ _ _ (X.Zw hpl).K Fp _ _ _ (X.Zw hpl).Rl X.finWfI (X.V hpl).Y
            (X.V hpl).dat (X.V hpl).w0 (X.V hpl).nAt (X.V hpl).RdW (X.V hpl).atL
            (X.V hpl).pl (X.V hpl).hpl⟩) ∧
      (∀ m, (X.Zw hpl).W.P.body m = (X.V hpl).bd ((X.V hpl).Y.dataOf m)) ∧
      (∀ b, (X.V hpl).bd ((X.V hpl).dat b) = b) ∧
      (∀ l i, (X.V hpl).nAt ((X.V hpl).atL l i) = (X.V hpl).Y.entF ((X.V hpl).pl (some l) i)) ∧
      (∀ i, (X.V hpl).nAt ((X.Zw hpl).W.P.wAt i) = (X.V hpl).Y.entF ((X.V hpl).pl none i)) ∧
      ∀ n, (X.V hpl).RdW n → (X.V hpl).Y.NoPad n

/-- States: `X.Room p` gives, for every `hpl`, all eighteen fields of `(X.Zw hpl).Rest2 p`. -/
def bldWf_rest2 : Prop := ∀ (X : BldWf F E Fp) (p : ℕ), X.Room p → ∀ hpl : X.Hpl, (X.Zw hpl).Rest2 p

/-- States, for f ≤ `X.n`, where the places stand. -/
def bldWf_where : Prop :=
  ∀ (X : BldWf F E Fp) (f : ℕ), f ≤ X.n →
    (∀ n, X.P.gC f n ↔ ∃ c, n = X.mkN f (.k (X.num.v' f) (le_refl _) (Sum.inr c))) ∧
    (∀ (h : f ≤ X.n) (a : X.num.LkM E f),
      X.nAt (X.mkN f a) = X.Y.entF (X.pM (Sum.inl ⟨⟨f, h⟩, a⟩))) ∧
    ∀ i, X.nAt (X.P.wAt i) = X.Y.entF (X.pM (Sum.inr i))

end
end Spec
end Cb
