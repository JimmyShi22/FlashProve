-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFrontRefWide.lean: under the hypotheses of `Spec.frontWide_psc` and
`Spec.frontWide_lkp`, the facts that the masked blocks of a segment's front need follow from wide
facts.

Statements (in `Cb.Spec`); the proofs are in Cb/Req1/LdSegFrontRefWideProofs.lean. Rules of the
framework; nothing of a text is rendered here.
It uses Cb/Req1/LdSegRefFactG.lean (`segWide_readG`: from the wide fact to the fact of a block that
reads a vector on names, some of them virtual), Cb/Req1/LdSegFront.lean (`frFact`: the fact of a
sumcheck of the front), Cb/Req1/LdSegRefLkpPreZk.lean (`F.dm Rd C`: the letters of the front's
lookup) and Cb/Ld/LdLkpMaskPutLkp2.lean (the own masks of the assembled lookup are "overwrite the
entries at named places").

A fact is a `MaskFact` (Cb/Req1/LdSegFresh.lean). A `MaskFact W` is a reading `kc` of witnesses of
type W into a type `Kc`, a finite, non-empty type `Mk`, and a map `put : Mk → Kc → Kc`.
Why: along a request the wide fact (`LdStage.wideFact`) is laid down and carried
(Cb/Req1/LdSegCarry.lean). The front's blocks ask narrow facts, each in its own letters
(Cb/Req1/LdSegRefAllZk.lean: `A.FrontFacts`): of a sumcheck: `frFact`; of the lookup:
`(F.dm RdK C).fact`. Both read a vector msg m on names J, cut to a set of names; some names may be
virtual (computed off several entries). The one new datum: at': where the block's own names are
among the entries of the messages. Asked, for each block:
   (p1) at an own name, msg m is the entry at' of m;
   (p2) at a name that the block reads and that is no own name, msg m is the same for messages that
     agree on the entries in Rd that are not own;
   the entries at' are own, and lie in Rd; the values of the wide fact at them are the block's mask
     values.

Main names:
  `Spec.frontWide_psc`: under the hypotheses of its statement, a sumcheck (any T : PscOur E, any
    reading RdT with its own names in it, these pairwise different): after any chain, the wide fact
    with mask type `(T.own RdT).Mk` gives `frFact Kc T .. msg RdT`.
  `Spec.frontWide_lkp`: under the hypotheses of its statement, the lookup (any F : LdPreD ..,
    `F.A.MaskOK Dt`, its own names in RdK): the wide fact with the mask type of the lookup's letters
    gives `(F.dm RdK C).fact`. Own names and values: `F.A.plChain`'s (P.pl, P.ve).
At which stage: a fact is a reading of a witness; the witness of every stage over S with the further
witness Wp has one type. Both statements hold after any chain that ends at any such stage (explicit
part, further oracles and claim are free): so at the segment's entry, where `A.FrontFacts` asks the
facts, as well as just before the block.
(The facts of the two kinds of sumchecks of a front's table, `B.f0 Rd0` and `B.f i Rd` of
Cb/Req1/LdSegFrontTabZk.lean, are `frFact ..` by definition: the first statement applies to them as
it stands.)

Limits: this file does not say that the wide facts are fresh. It says nothing on the "quiet"
clauses. The mask type is the block's from the start: no rule changes it.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefFactG
import Cb.Req1.LdSegFrontRefZk
import Cb.Ld.LdLkpMaskPutLkp2

set_option autoImplicit false

namespace Cb
namespace Spec
open Iop Prob Hiop IOR IOR.Chain Cb.LdLkp

/-- A sumcheck of the front. -/
def frontWide_psc : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (A : Joint Kc) (a : LdStage E Kc)
      (c : Chain Kc A a.J) (base : MaskFact A.W → Prop) (Rd : a.S.Ent → Prop)
      (Rr : a.S.O → Prop) (own : a.S.Ent → Prop) (T : PscOur E)
      (A0 : Rels Kc T.St a.E₀ (a.S.Msg × a.Wp)) (msg : a.S.Msg → T.J → E) (RdT : T.J → Prop)
      (val : (T.own RdT).Mk → a.S.Ent → E) (at' : PIdx T.par.fmt ⊕ T.A → a.S.Ent),
    Function.Injective (T.own RdT).at → (∀ i, RdT ((T.own RdT).at i)) →
    (∀ m i, msg m ((T.own RdT).at i) = a.S.ents m (at' i)) →
    (∀ m m' j, RdT j → (∀ i, (T.own RdT).at i ≠ j) →
      (∀ n : a.S.Ent, Rd n → ¬ own n → m' n.1 n.2 = m n.1 n.2) → msg m' j = msg m j) →
    (∀ i, own (at' i)) → (∀ i, Rd (at' i)) → (∀ M i, val M (at' i) = Sum.elim M.1 M.2 i) →
    c.FreshGiven base (a.wideFact Rd Rr own (T.own RdT).Mk val) →
    c.FreshGiven base (frFact Kc T a.S a.E₀ a.Wp A0 msg RdT)

/-- The lookup of the front. -/
def frontWide_lkp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (F : LdPreD E Kc S E₀ Wp) (St' : Type) (E₀' : ExtSpec) (A' : Rels Kc St' E₀' (S.Msg × Wp))
      (A : Joint Kc) (c : Chain Kc A (⟨S, St', E₀', Wp, A'⟩ : LdStage E Kc).J)
      (base : MaskFact A.W → Prop) (Rd : S.Ent → Prop) (Rr : S.O → Prop) (own : S.Ent → Prop)
      (Dt RdK : F.A0.J → Prop) (C : F.St × E → (F.A0.J → E) → Prop)
      (val : (F.dm RdK C).Mk → S.Ent → E) (at' : (F.A.plChain E₀ S.Msg Wp Kc F.msg RdK).I → S.Ent),
    F.A.MaskOK Dt → (∀ i, RdK ((F.A.plChain E₀ S.Msg Wp Kc F.msg RdK).pl i)) →
    (∀ m i, F.msg m ((F.A.plChain E₀ S.Msg Wp Kc F.msg RdK).pl i) = S.ents m (at' i)) →
    (∀ m m' j, RdK j → (∀ i, (F.A.plChain E₀ S.Msg Wp Kc F.msg RdK).pl i ≠ j) →
      (∀ n : S.Ent, Rd n → ¬ own n → m' n.1 n.2 = m n.1 n.2) → F.msg m' j = F.msg m j) →
    (∀ i, own (at' i)) → (∀ i, Rd (at' i)) →
    (∀ M i, val M (at' i) = (F.A.plChain E₀ S.Msg Wp Kc F.msg RdK).ve M i) →
    c.FreshGiven base
      ((⟨S, St', E₀', Wp, A'⟩ : LdStage E Kc).wideFact Rd Rr own (F.dm RdK C).Mk val) →
    c.FreshGiven base (F.dm RdK C).fact

end Spec
end Cb
