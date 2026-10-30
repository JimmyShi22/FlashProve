-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookPubHX.lean.
The calls' lookup of the head's sub-proof: its share of the link's public record, closed over the
parameter files' public numbers alone.

Fo.Pub2.lookPubH (OnBytes/Tie/Pv/Lookup/Ends/FoLookPubH.lean) takes all that is public at the head
(H.PubH) as one argument.
Two of its fields are the request's: the covered positions and the tokens that are checked there. A
link's public record may hold what the parameter files give, and no more: the request is part of the
statement. A layout's keys may read the caller's state. So here the record is made of X, what
Verify.publicOf returns, and the two fields of the request are read off the state.

Main names:
  `pubHAt X cov win`: what is public at the head: the shape X.hS, the layout X.HLy, the record of
    the stream's matrix (Verify.borderOf X.layers.y) and the layout of the committed weights
    (X.layers.wsLay) from X; cov and win as given.
  `lookPubHX rdH X rq .. `: the record: as lookPubH, but the keys at the state st are H.kvH at
    pubHAt X (rq st).1 (rq st).2. The lookup's record of public numbers, the cells of the counts'
    bits and the mask entries do not read the state.
  `lookPubHX_ok`: where Verify.publicOf returns X: Fo.Pub2.LookPubOK of it. No further premise.
  `lookPubHX_at`: at a state st the keys are those of lookPubH at pubHAt X (rq st).1 (rq st).2.
Limits: those of OnBytes/Tie/Pv/Lookup/Ends/FoLookPubH.lean: the six bounds of the boxes are free
arguments here too, none is written from X, and no clause asks that different places are different
entries. How a state holds the request (rq) is a free argument: nothing ties it to a call's request.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubH

set_option autoImplicit false

namespace Fo.Pub2
open Cb Cb.Fo OnBytes OnBytes.Model OnBytes.Ends OnBytes.Ends.H

/-- What is public at the head: the parameter files' share from X, the request's as given. -/
def pubHAt (X : Verify.Public) (cov : Head.Covered) (win : Array ℕ) : PubH :=
  { h := X.hS, L := X.HLy, b := Verify.borderOf X.layers.y, cov := cov, win := win,
    lay := X.layers.wsLay }

/-- The record, closed over X alone: the keys read the request off the state. -/
def lookPubHX {M₀ : Type} (rdH : M₀ → IxH → Cb.Gl.E) (X : Verify.Public) {St : Type}
    (rq : St → Head.Covered × Array ℕ) (nM nR nC wR wC nS : ℕ) : LookPub M₀ St where
  h := X.HLy.fs
  J₀ := JH nM nR nC wR wC nS
  L :=
    { K := fun st μ q i => kvH (pubHAt X (rq st).1 (rq st).2) (cellOfH μ) q i
      bc := fun t c j => cellH (X.hS.NHf + 2) (FoNums.cellRC X.HLy.fs X.hS.lmbH (t, c, j)).1
        (FoNums.cellRC X.HLy.fs X.hS.lmbH (t, c, j)).2
      mkS := fun s => maskH (0 + s) }
  rd₀ := fun b => Sum.elim (fun n => rdH b (.inl (.cell n.1.val n.2.1.val n.2.2.val)))
    (Sum.elim (fun n => rdH b (.inl (.w n.1.val n.2.val))) fun s => rdH b (.inr s.val))

theorem lookPubHX_ok {M₀ : Type} (rdH : M₀ → IxH → Cb.Gl.E) {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Verify.Public} (h : Verify.publicOf pol KL layout = .ok X)
    {St : Type} (rq : St → Head.Covered × Array ℕ) (nM nR nC wR wC nS : ℕ) :
    LookPubOK (lookPubHX rdH X rq nM nR nC wR wC nS) X.HLy.cl X.HLy.fs.pub X.hS.LIDB X.hS.lmbH 0
      maskH (cellH (X.hS.NHf + 2)) := by
  obtain ⟨s1, s2, s3⟩ := shapeOf_headLayout (Fo.Pub.publicOf_headLayout h)
  exact ⟨s1, s2, s3, fun _ => rfl, fun _ _ _ _ => rfl⟩

/-- At a state the keys are those of the record at that state's request. -/
theorem lookPubHX_at {M₀ : Type} (rdH : M₀ → IxH → Cb.Gl.E) (X : Verify.Public) {St : Type}
    (rq : St → Head.Covered × Array ℕ) (nM nR nC wR wC nS : ℕ) (st : St) :
    (lookPubHX rdH X rq nM nR nC wR wC nS).L.K st =
      (lookPubH rdH (pubHAt X (rq st).1 (rq st).2) nM nR nC wR wC nS St).L.K st := rfl

end Fo.Pub2
