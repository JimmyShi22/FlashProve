-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookPubH.lean.
The calls' lookup of the head's sub-proof: its share of the link's public record, as a value made of
the byte-level verifier's own layout.

Main names:
  `pubAsk_pub`: Forest.pubAsk does not read the record's own field pub.
  `shapeOf_headLayout`: Head.layout h tauFC = .ok L gives ShapeOf L.cl L.fs.pub h.LIDB L.fs, with no
    run of Forest.pad, and 5 ≤ h.lmbH ≤ L.fs.kT + 5.
  `IxH`: what the sub-proof's committed messages hold, by names: the cells of the head's matrices
    and of the committed matrix of weights (H.NameH), and the mask row's slots.
  `JH`, `cellH`, `wH`, `maskH`, `cellOfH`: the entries: cells in two boxes and slots below a bound;
    an index beyond a bound is laid at the bound.
  `lookPubH rdH P .. St`: the record, over any base reading M₀ that is read at the names IxH by rdH,
    at what is public at the head (H.PubH): h := P.L.fs; the keys are H.kvH at the cells; the mask
    entries are the slots from 0 on; the bits of the counts lie in the matrix number P.h.NHf + 2, of
    2^lmbH rows.
  `lookPubH_layout`: where Head.layout returns P.L at P.h: Fo.Pub2.LookPubOK of it, at the calls,
    numbers of padding keys and cap of that layout.
  `lookPubH_ok`: so where Verify.publicOf returns X, at P.h = X.hS and P.L = X.HLy.
Premises of lookPubH_ok: Verify.publicOf has returned X; P.h = X.hS; P.L = X.HLy. The other fields
of P (the stream's record, the covered positions, the tokens checked there, the weights' layout) are
free; the keys read them.
Limits: all six bounds of the boxes are free arguments: none is written from the plan. No clause
here asks that different places are different entries, and beyond the bounds they are not: below
P.h.NHf + 2 matrices the cells of the counts' bits fall on another matrix's. Of Fo.Pub2.LookPubOK
the two laws on the masks and on the cells hold by unfolding. That the matrix of the counts' bits
has the number P.h.NHf + 2 in the program's own list is not shown here. That the first slot of the
lookup in a run is 0 is Fo.slots_nextH (OnBytes/Tie/Pv/Lookup/Ends/FoDoors.lean). The covered
positions and the tokens checked there are the request's, not the parameter files'. The keys do not
read the caller's state.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubA
import OnBytes.Tie.Pv.Lookup.Ends.H

set_option autoImplicit false

namespace Fo.Pub2
open Cb Cb.Fo OnBytes OnBytes.Model OnBytes.Ends OnBytes.Ends.H
open Fo.BatRows (bindE_ok)

/-! ### the shape, at the layout -/

theorem pubAsk_pub (h : Forest.Shape) (p pub : Array ℕ) :
    Forest.pubAsk { h with pub := p } pub = Forest.pubAsk h pub := rfl

theorem shapeOf_headLayout {h : Head.Shape} {tauFC : Array F} {L : Head.HL}
    (e : Head.layout h tauFC = .ok L) :
    ShapeOf L.cl L.fs.pub h.LIDB L.fs ∧ 5 ≤ h.lmbH ∧ h.lmbH ≤ L.fs.kT + 5 := by
  unfold Head.layout at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨L0, _, e⟩ := bindE_ok e
  obtain ⟨calls, _, e⟩ := bindE_ok e
  dsimp only at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨fs, hs, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨kb, hk, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨pub, _, e⟩ := bindE_ok e
  obtain ⟨_, hp, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain rfl := Except.ok.inj e
  refine ⟨⟨_, shape_iota ?_ hs, ?_, rfl⟩, Fo.Pay.planeCols_bounds hk⟩
  · apply Array.ext <;> simp [strip]
  · exact hp

/-! ### the entries -/

/-- The names at the head: the cells of its matrices and of the weights, and the mask row's
slots. -/
abbrev IxH : Type := NameH ⊕ ℕ

/-- Cells in two boxes, and slots below a bound. -/
abbrev JH (nM nR nC wR wC nS : ℕ) : Type :=
  (Fin (nM + 1) × Fin (nR + 1) × Fin (nC + 1)) ⊕ (Fin (wR + 1) × Fin (wC + 1)) ⊕ Fin (nS + 1)

variable {nM nR nC wR wC nS : ℕ}

/-- The entry of a cell of one of the head's matrices. -/
def cellH (M r c : ℕ) : JH nM nR nC wR wC nS := .inl (upTo nM M, upTo nR r, upTo nC c)

/-- The entry of a cell of the committed matrix of weights. -/
def wH (r c : ℕ) : JH nM nR nC wR wC nS := .inr (.inl (upTo wR r, upTo wC c))

/-- The entry of a slot of the mask row. -/
def maskH (j : ℕ) : JH nM nR nC wR wC nS := .inr (.inr (upTo nS j))

/-- The cells by their names, read in the entries. -/
def cellOfH (μ : JH nM nR nC wR wC nS → Cb.Gl.E) : NameH → Cb.Gl.E
  | .cell M r c => μ (cellH M r c)
  | .w r c => μ (wH r c)

/-! ### the value -/

/-- The calls' lookup's share of the public record of the head's sub-proof. -/
def lookPubH {M₀ : Type} (rdH : M₀ → IxH → Cb.Gl.E) (P : PubH)
    (nM nR nC wR wC nS : ℕ) (St : Type) : LookPub M₀ St where
  h := P.L.fs
  J₀ := JH nM nR nC wR wC nS
  L :=
    { K := fun _ μ q i => kvH P (cellOfH μ) q i
      bc := fun t c j => cellH (P.h.NHf + 2) (FoNums.cellRC P.L.fs P.h.lmbH (t, c, j)).1
        (FoNums.cellRC P.L.fs P.h.lmbH (t, c, j)).2
      mkS := fun s => maskH (0 + s) }
  rd₀ := fun b => Sum.elim (fun n => rdH b (.inl (.cell n.1.val n.2.1.val n.2.2.val)))
    (Sum.elim (fun n => rdH b (.inl (.w n.1.val n.2.val))) fun s => rdH b (.inr s.val))

theorem lookPubH_layout {M₀ : Type} (rdH : M₀ → IxH → Cb.Gl.E) (P : PubH) {tauFC : Array F}
    (e : Head.layout P.h tauFC = .ok P.L) (nM nR nC wR wC nS : ℕ) (St : Type) :
    LookPubOK (lookPubH rdH P nM nR nC wR wC nS St) P.L.cl P.L.fs.pub P.h.LIDB P.h.lmbH 0 maskH
      (cellH (P.h.NHf + 2)) := by
  obtain ⟨s1, s2, s3⟩ := shapeOf_headLayout e
  exact ⟨s1, s2, s3, fun _ => rfl, fun _ _ _ _ => rfl⟩

theorem lookPubH_ok {M₀ : Type} (rdH : M₀ → IxH → Cb.Gl.E) {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Verify.Public} (h : Verify.publicOf pol KL layout = .ok X)
    (P : PubH) (hh : P.h = X.hS) (hL : P.L = X.HLy) (nM nR nC wR wC nS : ℕ) (St : Type) :
    LookPubOK (lookPubH rdH P nM nR nC wR wC nS St) P.L.cl P.L.fs.pub P.h.LIDB P.h.lmbH 0 maskH
      (cellH (P.h.NHf + 2)) :=
  lookPubH_layout rdH P (tauFC := X.layers.y.tauFC)
    (by rw [hh, hL]; exact Fo.Pub.publicOf_headLayout h) nM nR nC wR wC nS St

end Fo.Pub2
