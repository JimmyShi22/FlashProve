-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefPendEnds.lean: the list of moves of a batching of tensor rows ends exactly where a
later batching begins: the pending row enters it as its one claim, by definition of the stages and
by one theorem, under its hypotheses.

Definitions, statements (in `Cb.Spec`) and proofs.
A batching of tensor rows has the data `X : LdTenD E Kc`; a tensor row is a claim of the form of
one clause of `LdTenD.TenOK`; the list of moves is `X.prog` (all in Cb/Req1/LdSegRefTen.lean). A
stage (`LdStage`, Cb/Req1/LdSegKit.lean) is the data of a joint over oracle messages with samples.
The three moves of X end at "rows on all entries, beside Az" (`X.tgt`), Az a parameter with four
laws (`X.Ends`). By Cb/Req1/LdSegRefPend.lean, if 1 ≤ X.n, what X leaves (the pending row) is again
a tensor row whose parts are readers (functions) of its last claim z. Here Az is chosen (`X.AzA`) so
that the last stage is the first stage of a later batching on the same encoded index, beside the
same rows.

Main names:
  `X.after Z' n' wAt' A0' Rd'`: the later batching's data. Its state is the earlier batching's last
    claim z, as it stands. It has one claim, read off z: row vector, point, coefficients on the
    names of the earlier batching's own masks and of its incoming forms, at their fixed places. It
    has its own evader, degree, places of own masks, and reading Rd'.
  `X.fzA`, `X.AzA`: see their docstrings; `X.AzA` claims: the index is decoded, A0', and the one
    tensor row holds.
  `X.Rides A0'`: what else was claimed goes over into A0': the exact relation (`rel`) forwards, the
    relaxed one (`relR`) backwards where the condition (`on`) of `X.A0` holds, the condition
    forwards, equal cores.
  `Spec.ldSegRef_pe_src`: the last stage of the earlier list is the first stage of the later one: by
    definition.
  `Spec.ldSegRef_pe_ends`: see its docstring.
  `Spec.ldSegRef_pe_own`: the later batching's conditions on places (`LdTenD.Own`), if its own
    places are pairwise different, are read (in Rd'), and differ from the earlier batching's own
    places and from the places of its incoming forms, and these are read.

Limits: this file says nothing on several pending rows (one for each earlier segment): the same
readers, a state that holds all the last claims. It does not say that the message with these masks
is kept at every closing between.
-/
import Cb.Req1.LdSegRefPend
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.RngPk IOR

namespace LdTenD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc)

/-- The later batching's data: one claim, the pending row of X. -/
@[reducible] def after (Z' : Evader E Unit) (n' : ℕ)
    (wAt' : PIdx (List.replicate X.k (pfCube E n')) → X.S.Ent)
    (A0' : Rels Kc X.bt.par.Mid X.C.E0 ((X.C.Msg × X.S.Msg) × X.Wp)) (Rd' : X.S.Ent → Prop) :
    LdTenD E Kc :=
  { S := X.S, C := X.C, Wp := X.Wp, Bn := X.Bn, Sb := X.Sb, sl := X.sl, Rw := X.Rw, k := X.k,
    mat := X.mat, St := X.bt.par.Mid, rc := fun z => X.rc (X.stOf z).2, Q := Unit,
    g := fun z _ => X.pG z, pt := fun z _ => X.pPt z, Nm := X.PN, mf := fun z _ => X.pMf z,
    μAt := X.pAt, Z := Z', n := n', wAt := wAt', A0 := A0', Rd := Rd' }

/-- the explicit part of the later batching's claims, from the earlier one's last claim -/
def fzA (z : X.bt.par.Mid) : (Unit → E) × X.bt.par.Mid := (fun _ => X.pTg z, z)

/-- what is claimed beside the rows -/
@[reducible] def AzA (Z' : Evader E Unit) (n' : ℕ)
    (wAt' : PIdx (List.replicate X.k (pfCube E n')) → X.S.Ent)
    (A0' : Rels Kc X.bt.par.Mid X.C.E0 ((X.C.Msg × X.S.Msg) × X.Wp)) (Rd' : X.S.Ent → Prop) :
    Rels Kc ((Unit → E) × X.bt.par.Mid) X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp)) :=
  idxAt X.C (fun x => X.rc (X.stOf x.2).2) (X.after Z' n' wAt' A0' Rd').tenA

/-- What else was claimed goes over into A0'. -/
structure Rides (A0' : Rels Kc X.bt.par.Mid X.C.E0 ((X.C.Msg × X.S.Msg) × X.Wp)) : Prop where
  fw   : ∀ z y w, X.A0.rel (X.stOf z).2 y w → A0'.rel z y w
  bw   : ∀ z y w, X.A0.on ((X.stOf z).2, y) → A0'.relR (z, y) w → X.A0.relR ((X.stOf z).2, y) w
  on   : ∀ z y, X.A0.on ((X.stOf z).2, y) → A0'.on (z, y)
  core : ∀ w, A0'.core w = X.A0.core w

end LdTenD

namespace Spec

def ldSegRef_pe_src : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate X.k (pfCube E n')) → X.S.Ent)
      (A0' : Rels Kc X.bt.par.Mid X.C.E0 ((X.C.Msg × X.S.Msg) × X.Wp)) (Rd' : X.S.Ent → Prop),
    X.tgt ((Unit → E) × X.bt.par.Mid) (X.AzA Z' n' wAt' A0' Rd') = (X.after Z' n' wAt' A0' Rd').src

/-- States: if 1 ≤ X.n and `X.Rides A0'`, the pending row enters the later batching: `X.Ends` holds
of `X.fzA` and `X.AzA`. -/
def ldSegRef_pe_ends : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate X.k (pfCube E n')) → X.S.Ent)
      (A0' : Rels Kc X.bt.par.Mid X.C.E0 ((X.C.Msg × X.S.Msg) × X.Wp)) (Rd' : X.S.Ent → Prop),
    1 ≤ X.n → X.Rides A0' → X.Ends ((Unit → E) × X.bt.par.Mid) X.fzA (X.AzA Z' n' wAt' A0' Rd')

def ldSegRef_pe_own : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate X.k (pfCube E n')) → X.S.Ent)
      (A0' : Rels Kc X.bt.par.Mid X.C.E0 ((X.C.Msg × X.S.Msg) × X.Wp)) (Rd' : X.S.Ent → Prop),
    Function.Injective wAt' → (∀ i, Rd' (wAt' i)) → (∀ i, Rd' (X.wAt i)) → (∀ a, Rd' (X.μAt a)) →
    (∀ i j, wAt' i ≠ X.wAt j) → (∀ i a, wAt' i ≠ X.μAt a) → (X.after Z' n' wAt' A0' Rd').Own

end Spec

theorem ldSegRef_pe_src : Spec.ldSegRef_pe_src := fun _ _ _ _ _ _ _ _ _ _ => rfl

theorem ldSegRef_pe_ends : Spec.ldSegRef_pe_ends := by
  intro E Kc _ _ X Z' n' wAt' A0' Rd' hn hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro z y w ⟨hE, ⟨_, hA⟩, hM⟩
    exact ⟨hE, hR.fw z y _ hA, fun _ => (ldSegRef_pend E Kc X hn z _).1 hM⟩
  · rintro z y w ⟨_, ho⟩ hrow ⟨U, hU, hA, hT⟩
    exact ⟨U, hU, ⟨hrow, hR.bw z y _ ho hA⟩, (ldSegRef_pend E Kc X hn z _).2 (hT ())⟩
  · rintro z y ⟨hc, ho⟩
    exact ⟨hc, hR.on z y ho⟩
  · intro w
    exact hR.core _

theorem ldSegRef_pe_own : Spec.ldSegRef_pe_own := by
  intro E Kc _ _ X Z' n' wAt' A0' Rd' hi h1 h2 h3 h4 h5
  refine ⟨hi, h1, ?_, ?_⟩
  · rintro (i | a)
    · exact h2 _
    · exact h3 a
  · rintro i (j | a)
    · exact h4 i _
    · exact h5 i a

end Cb
