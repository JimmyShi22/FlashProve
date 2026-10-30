-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectTail.lean: from a tail of a chain to the parameter list of a sub-protocol that ends
in the trivial statement: the test for linear constraints at one instance, the link.

In standard terms: auxiliary lemmas that connect two interfaces: given that a chain of interactive
oracle reductions is a tail (`TailTr`), and under four bridging facts (see Main names), it has the
list of properties that the generic construction of the proof system asks of a test.

Statements (in `Cb.Spec`) and proofs. No protocol, no code occurs here: any configuration with a
record, any "what a preamble leaves". Hiop/RecSubs.lean asks of the test for linear constraints (one
instance) a list without knowledge soundness (`LinListR`) and an item on knowledge soundness whose
extractor is "decode the statement" (`LinKnowR`); of the link `LinkListR` and `LinkKnowR`. The tests
are built as chains that end in the trivial statement; what their theorems give is "a tail of a
chain" (`TailTr`, Cb/Ld/LdTowerKit.lean) from a joint A (`Rels`, Ior/Chain.lean) of the chain's own,
with witnesses of the chain's own type and an extractor that runs backwards. This file joins the
two. (For a preamble the same is done in Cb/Ld/LdWfClose.lean.) `TailTr`, a tail of a chain, asks of
a reduction from a joint to a joint whose statements have no oracles the bundle `IOR.GoodT` and
three further clauses, `noHid`, `tied` and `bears`, which Cb/Ld/LdTowerKit.lean states (through
`IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).

Main names:
  `Spec.ldObj_lin`: a tail Q from A, and four bridging facts:
    (a) the constraint relation gives A's exact relation (`A.rel`), at the witness fi w (the honest
        prover's witness is re-typed: `Honest.mapW`);
    (b) a collision-free statement has A's condition (`A.on`);
    (c) on collision-free statements A's relaxed relation (`A.relR`) gives the relaxed constraint
        relation, at the message fr w that is read off the witness;
    (d) a set of positions within the tail's bound holds at most q positions of the encoded index.
    Then `LinListR` and `LinKnowR` hold of Q: same errors, same probability of the public bad set;
    the budget of further reads is "none"; the extractor is the decoder of the statement.
  `Spec.ldObj_link`: the same for the link, with `ConfigurationWithOutOfDomainSample.Req`, `ConfigurationWithOutOfDomainSample.ReqR` for the constraint
    relation and its relaxation, `ConfigurationWithOutOfDomainSample.onEq` for "collision-free" in (b), (c) and two bounds qpar,
    qch in (d): nothing is extracted.
  `Spec.ldObj_fit`: under the hypotheses of its statement, the line "the preamble's budget (`bud`)
    bears what the test (`Q`) reads of the oracles left" holds. Among these hypotheses: the preamble
    bears what follows (`F.Bears bud qa qi`, Ior/Bears.lean) at the tail's bound (`qi`); and that
    bound is closed under subsets.

Why the extractor is the decoder: the relaxed constraint relation determines its witness (the
oracles left decode to it), so the chain's extractor may be replaced by the decoder (`know_of_det`,
Ior/KnowColl.lean).

Notation: `d0`: a value of `S.AMsg` (what `S.decA`, Hiop/RecConf.lean, returns where `S.adec`
returns nothing).

Limits: no tail is given. Honest-verifier zero knowledge is at no further reads: the lists ask no
more of a test (their clause bud0). This file says nothing on a batch.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerKit
import Hiop.RecBuild
import Ior.KnowCollRulesFrameProofs
import Blocks.ClosingBlock
import Cb.Gen.Code

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

namespace Spec

open Classical in
/-- States, under the hypotheses below: a tail of a chain is a test for linear constraints at one
instance. -/
def ldObj_lin : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : C.Left) (Wi : Type) (Q : IOR (S.Xl × C.Rec) S.El Unit extNone)
      (H : Q.Honest Wi Unit) (A : Rels Unit (S.Xl × C.Rec) S.El Wi)
      (ext : (S.Xl × C.Rec) × S.El.Str → Tr Q.shape → Unit → Wi) (P : Nums Unit Q)
      (qi : Finset S.El.Pos → Prop) (q : ℕ) (fi : C.PIdx × S.WAux → Wi)
      (fr : Wi → S.AMsg) (d0 : S.AMsg),
    TailTr Q H A trivRels ext P qi → (∀ x y w, S.Rlin x y w → A.rel x y (fi w)) →
    (∀ a, S.cond a → A.on a) → (∀ a w, S.cond a → A.relR a w → S.RlinR a (fr w)) →
    (∀ U, qi U → (U.filter fun p => p.isLeft).card ≤ q) →
    LinListR S Q (H.mapW fi fun _ u => u) ⟨P.err, P.pBad, q, fun _ T => T = ∅⟩ ∧
    LinKnowR S Q d0 P.err

open Classical in
/-- States, under the hypotheses below: a tail of a chain is a link. -/
def ldObj_link : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (Wi : Type) (Q : IOR (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg) Unit extNone)
      (H : Q.Honest Wi Unit) (A : Rels Unit (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg) Wi)
      (ext : (C.Rec × C.Rec) × (twoExternalStrings C.n C.Sg).Str → Tr Q.shape → Unit → Wi) (P : Nums Unit Q)
      (qi : Finset (twoExternalStrings C.n C.Sg).Pos → Prop) (qpar qch : ℕ) (fi : C.PIdx × C.PIdx → Wi),
    TailTr Q H A trivRels ext P qi → (∀ x y w, C.Req x y w → A.rel x y (fi w)) →
    (∀ a, C.onEq a → A.on a) → (∀ a w, C.onEq a → A.relR a w → C.ReqR a ()) →
    (∀ U,
      qi U → (U.filter fun p => p.isLeft).card ≤ qpar ∧ (U.filter fun p => p.isRight).card ≤ qch) →
    LinkListR Q (H.mapW fi fun _ u => u) ⟨P.err, P.pBad, qpar, qch, fun _ T => T = ∅⟩ ∧
    LinkKnowR Q P.err

open Classical in
/-- Under the hypotheses below, the preamble's budget bears what the test reads of the oracles
left. -/
def ldObj_fit : Prop :=
  ∀ (Xi Xm : Type) (Ei Em : ExtSpec) (F : IOR Xi Ei Xm Em)
      (Q : IOR Xm Em Unit extNone) (bud : Rho F.shape → Finset (OPos F.shape) → Prop)
      (qa : Finset Ei.Pos → Prop) (qi : Finset Em.Pos → Prop),
    F.Bears bud qa qi → (∀ U V, V ⊆ U → qi U → qi V) →
    (∀ ρ, qi (Q.given ρ ∅) ∧ Q.extReads ρ ⊆ Q.given ρ ∅) →
    ∀ ρ₁ ρ₂, bud ρ₁ ((Q.extReads ρ₂).biUnion (F.srcO ρ₁))

end Spec

/-- Knowledge soundness under a map of the extracted witness. -/
theorem know_mapW {A B WA WA' WB : Type} {K : Reduction A B} {on on' : A → Prop}
    {RA : A → WA → Prop} {RA' : A → WA' → Prop} {RB : B → WB → Prop}
    {ext : A → Tr K.shape → WB → WA} {ε : Err K.shape} (fr : WA → WA') (h : K.Know on RA RB ext ε)
    (ho : ∀ a, on' a → on a) (hA : ∀ a w, on' a → RA a w → RA' a (fr w)) :
    K.Know on' RA' RB (fun a τ w => fr (ext a τ w)) ε :=
  fun a ha => Doomed.mono _ _ (fun _ hτ b w hb hw => hA a _ ha (hτ b w hb hw)) (h a (ho a ha))

theorem ldObj_lin : Spec.ldObj_lin := by
  classical
  intro C S Wi Q H A ext P qi q fi fr d0 h ha hb hc hd
  obtain ⟨hp, hl, hacc, hnh, hbad, hknow, ⟨Sm, hex⟩, htied, hq⟩ :=
    tailTr_end _ _ _ _ _ _ _ _ _ _ _ _ _ h
  refine ⟨{ point := hp, isLocal := hl, acc := ?_, noHid := fun w x => hnh (fi w) x, prBad := hbad,
            exact := ⟨Sm, ?_⟩, bud0 := fun _ => rfl, tied := htied, idxReads := fun ρ => ?_ },
    ?_⟩
  · intro x y w c ρ hR hρ
    rw [Honest.mapW_run]
    exact ⟨(hacc x y (fi w) c ρ (ha x y w hR) hρ).1, trivial⟩
  · exact exact_mapW _ _ _ _ _ _ _ _ _ H fi (fun _ u => u) A.rel S.Rlin _ Sm ha hex
  · exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (hq ρ).2)) (hd _ (hq ρ).1)
  · refine know_of_det _ _ _ _ _ _ _ _ _ _ (fun a => S.decA d0 a.1.1 a.2.2)
      ?_ (know_mapW fr hknow hb hc)
    rintro a w - ⟨U, -, h2, -⟩
    show w = (S.adec a.1.1 a.2.2).getD d0
    rw [h2]
    rfl

theorem ldObj_link : Spec.ldObj_link := by
  classical
  intro C Wi Q H A ext P qi qpar qch fi h ha hb hc hd
  obtain ⟨hp, hl, hacc, hnh, hbad, hknow, ⟨Sm, hex⟩, htied, hq⟩ :=
    tailTr_end _ _ _ _ _ _ _ _ _ _ _ _ _ h
  refine ⟨{ point := hp, isLocal := hl, acc := ?_, noHid := fun w x => hnh (fi w) x,
            prBad := hbad, exact := ⟨Sm, ?_⟩, bud0 := fun _ => rfl, tied := htied,
            cntPar := fun ρ => ?_, cntCh := fun ρ => ?_ },
    ?_⟩
  · intro x y w c ρ hR hρ
    rw [Honest.mapW_run]
    exact ⟨(hacc x y (fi w) c ρ (ha x y w hR) hρ).1, trivial⟩
  · exact exact_mapW _ _ _ _ _ _ _ _ _ H fi (fun _ u => u) A.rel C.Req _ Sm ha hex
  · exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (hq ρ).2)) (hd _ (hq ρ).1).1
  · exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (hq ρ).2)) (hd _ (hq ρ).1).2
  · exact know_mapW (fun _ => ()) hknow hb hc

theorem ldObj_fit : Spec.ldObj_fit := by
  intro Xi Xm Ei Em F Q bud qa qi hB hmono hq ρ₁ ρ₂
  exact (hB ρ₁ _ (hmono _ _ (hq ρ₂).2 (hq ρ₂).1)).1

end Cb
