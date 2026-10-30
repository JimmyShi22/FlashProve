-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectBatch.lean: knowledge soundness of a test that is run for up to N instances at once
on one encoded index: from the form that a chain of reductions gives to the form that the
holographic IOP requires, under two bridging facts.

Statements (in `Cb.Spec`) and proofs. No protocol, no code: any configuration with a record
(`ConfigurationWithOutOfDomainSample`), any "what a preamble leaves" (`ConfigurationWithOutOfDomainSample.Left`; both in Hiop/RecConf.lean).

The item of the list: Hiop/RecSubs.lean requires (`LinBKnowR`), of the test for linear constraints
for at most N instances, knowledge soundness for the instances of a batch, in the form that the
object (`HolographicProtocol`, Hiop/RecInterface.lean) takes (`SndBKT`, Ior/KnowWide.lean), with the extractor
"decode the statement": for each record, with that record in all slots, on the collision-free
statements whose encoded index decodes with the record.
A chain in a batch: a test for at most N instances is built as a chain with an annotation; what its
theorem gives is `IOR.KnowB` (Ior/BatchSeq.lean), for the vectors of statements that share the
encoded index and its record, from a joint of the chain's own, with an extractor that runs
backwards.

Main names:
  `Spec.ldObj_linB_know`: `KnowB` of the chain, for vectors with one (index, record), and two
    bridging facts give `LinBKnowR`, with the same errors. The facts:
    (b) a collision-free statement (`cond`, Hiop/RecConf.lean) whose index decodes has the chain's
      condition;
    (c) there the chain's relaxed relation gives the relaxed constraint relation (`RlinR`,
      Hiop/RecConf.lean), at the message `fr w` read off the witness.

Limits: this file says nothing on the honest side of a batch (`LinBListR`). No chain is given.

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecBuild
import Ior.KnowWideB

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

namespace Spec

/-- KnowB under a map of the explicit part. -/
def ldObj_knowB_comap : Prop :=
  ∀ (Xi Xi' Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (f : Xi' → Xi)
      (A : RoundSplits R.shape) (N : ℕ) (adm : (Fin N → Option (Xi × Ei.Str)) → Prop)
      (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
    R.KnowB A N adm on RA RB ext ε →
    (R.comapX f).KnowB A N (fun a => adm fun j => (a j).map fun aj => (f aj.1, aj.2))
      (fun a => on (f a.1, a.2)) (fun a => RA (f a.1, a.2)) RB (fun a => ext (f a.1, a.2)) ε

/-- Under the two bridging facts below, knowledge soundness of a chain in a batch (`KnowB`) gives
the item of the list (`LinBKnowR`). -/
def ldObj_linB_know : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : C.Left) (Wi : Type) (Q : BIOP (S.Xl × C.Rec) S.El) (N : ℕ)
      (on : (S.Xl × C.Rec) × S.El.Str → Prop) (RA : (S.Xl × C.Rec) × S.El.Str → Wi → Prop)
      (ext : (S.Xl × C.Rec) × S.El.Str → Tr Q.ior.shape → Unit → Wi) (ε : Err Q.ior.shape)
      (fr : Wi → S.AMsg) (d0 : S.AMsg),
    Q.ior.KnowB Q.ann N (SameKey fun a => (a.2.1, a.1.2)) on RA (fun _ (_ : Unit) => True) ext ε →
    (∀ a, (C.dcd a.2.1 a.1.2).isSome → S.cond a → on a) →
    (∀ a w, (C.dcd a.2.1 a.1.2).isSome → S.cond a → RA a w → S.RlinR a (fr w)) →
    LinBKnowR S Q N d0 ε

end Spec

theorem ldObj_knowB_comap : Spec.ldObj_knowB_comap := by
  intro Xi Xi' Xo Ei Eo Wi Wo R f A N adm on RA RB ext ε ⟨bad, hc, hJ⟩
  refine ⟨fun a => bad (f a.1, a.2),
    fun a τ b w ha hτ hb hw => hc (f a.1, a.2) τ b w ha hτ hb hw,
    fun a ha => ?_⟩
  have := hJ _ ha
  simpa only [Option.map_map, Function.comp_def] using this

theorem ldObj_linB_know : Spec.ldObj_linB_know := by
  intro C S Wi Q N on RA ext ε fr d0 h hb hc rec
  have h1 :=
    ldObj_knowB_comap _ S.Xl _ _ _ _ _ Q.ior (fun xl => (xl, rec)) Q.ann N _ on RA _ ext ε h
  refine sndBKT_of_knowB S.Xl S.AMsg Wi C.E0 S.Ej (Q.comapX fun xl => (xl, rec)) N
    (fun a => on ((a.1, rec), a.2)) (fun a => RA ((a.1, rec), a.2))
    (fun a => ext ((a.1, rec), a.2)) ε _ _ ?_ ?_
  · obtain ⟨bad, c1, c2⟩ := h1
    refine ⟨bad, c1, fun a ha => c2 a ?_⟩
    intro j j' aj aj' e1 e2
    obtain ⟨b, hb1, rfl⟩ := Option.map_eq_some_iff.1 e1
    obtain ⟨b', hb2, rfl⟩ := Option.map_eq_some_iff.1 e2
    exact Prod.ext (ha j j' b b' hb1 hb2) rfl
  · intro a y0 τ hR hd hcnd
    have h2 := hc ((a.1, rec), (y0, a.2)) _ hd hcnd (hR (hb _ hd hcnd))
    obtain ⟨U, -, h3, -⟩ := h2
    have h4 : S.decA d0 a.1 a.2 = fr (ext ((a.1, rec), (y0, a.2)) τ ()) := by
      show (S.adec a.1 a.2).getD d0 = _
      rw [h3]
      rfl
    rw [h4]
    exact hc ((a.1, rec), (y0, a.2)) _ hd hcnd (hR (hb _ hd hcnd))

end Cb
