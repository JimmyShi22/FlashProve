-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfOwn.lean: a hypothesis of the batching of tensor rows (`OwnOK`) follows from conditions on
places (`P.OwnPlaces`) and, if a record exists, gives them.

A definition, statements (in `Cb.Spec`) and proofs.

Why: Cb/Ld/LdBatt.lean asks (`OwnOK`: its fields `wS`, `rdS`), at all states: no incoming mask form
reads an own entry of the batching; an incoming form is 0 outside the entries that the batching
reads. In the preamble of weights-formedness the incoming forms are the mask forms of the claims
that the lookups have filed: data of the state. Read as they stand they are free, and both clauses
are false at some state: the hypothesis could not be met and the preamble's theorem said nothing.
So every use reads a filed form cut to a public support (Cb/Ld/LdWf.lean: `gC`, `P.clAt`). Here: the
hypothesis follows from places, and only from places.

Main names:
  `P.OwnPlaces Rd`: the own places are different entries (`inj`); the batching reads (`Rd`) them
    (`own`), all entries of the matrix of the index (`mat`), and every entry in the support
    (`P.gC q`) of a claim's mask form (`rdC`); no own place lies in the support of a claim's mask
    form (`off`).
  `Spec.ldWfOwn_ok`: `P.OwnPlaces Rd` gives `P.bt.OwnOK Rd`.
  `Spec.ldWfOwn_conv`: and conversely, if a record exists (`Nonempty C.Rec`): so nothing else is
    hidden in the hypothesis.

Limits: this file does not say that places with `P.OwnPlaces` exist for given lookups.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfProofsRel

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

/-- The conditions on places. -/
structure LdWfP.OwnPlaces {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample}
    (P : LdWfP E C) (Rd : P.bt.J → Prop) : Prop where
  inj : Function.Injective P.wAt
  own : ∀ i, Rd (Sum.inr (P.wAt i))
  mat : ∀ a, Rd (Sum.inl a)
  rdC : ∀ (q : Fin (P.n + 1)) n, P.gC q n → Rd (Sum.inr n)
  off : ∀ (q : Fin (P.n + 1)) i, ¬ P.gC q (P.wAt i)

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

def ldWfOwn_ok : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (Rd : P.bt.J → Prop), P.OwnPlaces Rd → P.bt.OwnOK Rd

def ldWfOwn_conv : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (Rd : P.bt.J → Prop),
    Nonempty C.Rec → P.bt.OwnOK Rd → P.OwnPlaces Rd

end
end Spec

section
variable {E : Type} [Field E] [Fintype E]

theorem ldWfOwn_ok : Spec.ldWfOwn_ok E := fun C P Rd h =>
  { inj := fun i i' e => h.inj (Sum.inr.inj e)
    own := h.own
    rdM := h.mat
    rdS := fun q st j hj => by
      cases j with
      | inl a => rfl
      | inr n => exact LdWfP.wfCut_out _ _ fun hg => hj (h.rdC q n hg)
    wM := fun i a e => by cases e
    wS := fun q st i => LdWfP.wfCut_out _ _ (h.off q i) }

open Classical in
theorem ldWfOwn_conv : Spec.ldWfOwn_conv E := by
  intro C P Rd ⟨rec⟩ h
  -- a state all of whose filed forms are 1 everywhere
  let st : P.WSt := (rec, fun _ => ⟨fun _ => 0, fun _ => 1, 0⟩, fun _ _ => ⟨fun _ => 0, 0⟩)
  have hv : ∀ (q : Fin (P.n + 1)) n, P.gC q n → P.bt.slM q st (Sum.inr n) = 1 := fun q n hg =>
    if_pos hg
  exact
    { inj := fun i i' e => h.inj (congrArg Sum.inr e)
      own := h.own
      mat := h.rdM
      rdC := fun q n hg => by
        by_contra hr
        have h0 := h.rdS q st (Sum.inr n) hr
        rw [hv q n hg] at h0
        exact one_ne_zero h0
      off := fun q i hg => by
        have h0 := h.wS q st i
        have h1 : P.bt.slM q st (Sum.inr (P.wAt i)) = 1 := hv q _ hg
        exact one_ne_zero (h1.symm.trans h0) }

end
end Cb
