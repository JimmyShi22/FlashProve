-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Seg/Dict.lean

The dictionary between names of cells and places in the segments' matrices, at the head with the
cost ledger.

Cm/SegLayout.lean states the dictionary for every number h : `Hd` of features of the head's matrices
hf and hr that are cells. `Hd.main` is the head of Inst/Model/Head/: all 1,232,768 features of hf
and all 120 bytes of hr. The library's laws (Cm/SegLayoutProofs.lean) are used at h := `Hd.main`,
with `mainOK`. This file adds what the library states at the plain head alone:
`lay_below_main`: the bound `Cm.Below` (Cm/Rel.lean) is the bound on all own cells at `Hd.main`;
`ReadsAtMain`, `readsAtMain_ofMat`, `readsAtMain_toMat`: integer matrices hold the cells that this
head reads. And it compares the two heads: `reads_plain_sub`: what a segment reads at the plain
head it reads at this head.

Limits: nothing on conditions, codes or protocols. The bits of a look-up's multiplicities have no
name in the dictionary: they are no cells.
-/
import Cm.Rel
import Cm.SegLayoutProofs
import Cm.TargetSegLayoutPlainProofs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Policy
open Inst.Model Inst.Model.All Cm.Seg

theorem mainOK : Hd.main.OK := Cm.lay_figures.2.2.2.2.1

/-- States: a trace meets the bound `Cm.Below B` if and only if all its own cells at `Hd.main` are
below B in absolute value. -/
def Spec.lay_below_main : Prop := ∀ (B : ℤ) (T : Trace), Cm.Below B T ↔ BelowN Hd.main B T

theorem lay_below_main : Spec.lay_below_main := by
  intro B T
  constructor
  · intro hB n hn
    cases n with
    | ff g c =>
      have := hB.ff g hn.1 c hn.2.1
      rw [vFF_eq, ownFF_own hn.2.2] at this
      exact this
    | att g c =>
      have := hB.att g hn.1 c hn.2.1
      rw [vAtt_eq, ownAtt_own hn.2.2] at this
      exact this
    | hf φ i => exact hB.hf i hn.2 φ hn.1
    | hd φ i => exact hB.hd i hn.2 φ hn.1
    | hr φ i => exact hB.hr i hn.2 φ hn.1
  · intro hN
    exact
      { ff := fun g hg c hc => by rw [vFF_eq]; exact hN _ (ownFF_valid _ hg hc)
        att := fun g hg c hc => by rw [vAtt_eq]; exact hN _ (ownAtt_valid _ hg hc)
        hf := fun i hi φ hφ => hN (.hf φ i) ⟨hφ, hi⟩
        hd := fun i hi φ hφ => hN (.hd φ i) ⟨hφ, hi⟩
        hr := fun i hi φ hφ => hN (.hr φ i) ⟨hφ, hi⟩ }

/-- integer cells t are what the integer matrices M hold at the places of the names that the head
with the ledger reads -/
structure ReadsAtMain (t : Head.Cells ℤ) (M : ℕ → ℕ → ℕ → ℤ) : Prop where
  hf : ∀ φ < Head.nFeat .hf, ∀ i < Head.nT, t.hf φ i = at' M (Name.hf φ i).place
  hd : ∀ φ < Head.nFeat .hd, ∀ i < Head.nT, t.hd φ i = at' M (Name.hd φ i).place
  hr : ∀ φ < Head.nFeat .hr, ∀ i < Head.nT, t.hr φ i = at' M (Name.hr φ i).place
  x : ∀ φ < Head.nFeat .x, ∀ i < Head.nT, t.x φ i = at' M (ownX φ i).place

theorem readsAtMain_ofMat (M : ℕ → ℕ → ℕ → ℤ) : ReadsAtMain (ofMat Hd.main M).vHead M :=
  have h := Cm.lay_read_ofMat Hd.main M
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem readsAtMain_toMat (T : Trace) : ReadsAtMain T.vHead (toMat Hd.main T) :=
  have h := Cm.lay_read_toMat Hd.main mainOK T
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- A name that is an own cell at the plain head is one at this head. -/
theorem valid_main {n : Name} (h : n.Valid Hd.plain) : n.Valid Hd.main := by
  obtain ⟨h1, h2⟩ := Cm.lay_figures.2.2.2.2.2
  cases n with
  | ff g c => exact h
  | att g c => exact h
  | hf φ i => exact ⟨lt_of_lt_of_le h.1 h1, h.2⟩
  | hd φ i => exact h
  | hr φ i => exact ⟨lt_of_lt_of_le h.1 h2, h.2⟩

/-- What a segment reads at the plain head it reads at this head. -/
theorem reads_plain_sub (k : ℕ) : reads Hd.plain k ⊆ reads Hd.main k := by
  rintro p (a | a | ⟨e, ⟨n, hn, h1, h2⟩ | a⟩)
  · exact Or.inl a
  · exact Or.inr (Or.inl a)
  · exact Or.inr (Or.inr ⟨e, Or.inl ⟨n, valid_main hn, h1, h2⟩⟩)
  · exact Or.inr (Or.inr ⟨e, Or.inr a⟩)

end Policy
