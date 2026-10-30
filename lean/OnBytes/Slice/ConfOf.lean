-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ConfOf.lean: the library's configuration (`Hiop.ConfigurationWithOutOfDomainSample`,
Hiop/RecConf.lean) made of a decoder of a stored table (`DecR`,
OnBytes/Slice/DecoderRec.lean) and of what the statements read of a decoded table (`DecR.Claims`).

Why. The library states the soundness of the link between two encoded indices as `LinkKnowR`
(Hiop/RecSubs.lean), over a configuration: on statements whose first word decodes to an index and
whose second has no collision, a yes means that both words decode to the same index. The written
link's soundness (OnBytes/Slice/LinkSoundRec.lean) is stated for a language of four clauses on
stored tables. This file gives the configuration at which the two meet.

Main names.
 `DecR.RelationsAndEncoding A`     what a configuration holds beside the verifier's side: the honest side's data
                   (encoding, pads, the answers of a message, cells) and the cells' two relations.
                   Letters: no statement of this file reads them.
 `DecR.configurationOfStoredTable A R`   the configuration. A word has 2^a symbols of a stored table; a seed and the
                   answers are the record's; `coll` and `dcd` are the decoder's; an index is a
                   matrix; THE INDEX THAT A MESSAGE HOLDS IS ITS MATRIX, IF THAT IS IN RANGE.
 `conf_held`       messages that agree before the pads hold the same index.
 `conf_D`          the index decoder, written out.
 `conf_req`        ON THE STATEMENTS OF WHICH THE LINK's SOUNDNESS SPEAKS (`onEq`), THE LANGUAGE OF
                   FOUR CLAUSES GIVES THE LINK's RELATION (`ReqR`): the condition shuts the three
                   ways out, and the fourth clause gives equal indices.

Not claimed. No law of a configuration (`ConfigurationWithOutOfDomainSample.Props`) is shown: not that an honest word decodes,
not that a word has a collision at few seeds, nothing on hiding. The condition `onEq` is narrower
than "the three ways out are shut": it also asks that the first table's matrix is in range.

-/
import OnBytes.Slice.DecoderRec
import Hiop.RecConf

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Hiop

namespace DecR
variable (D : DecR) {X : Type} (A : D.Claims X)

/-- What a configuration holds beside the verifier's side. -/
structure RelationsAndEncoding where
  /-- the cells of a request -/
  Cells : Type
  /-- the exact relation and its relaxation -/
  Ryes : A.Mat → X → Cells → Prop
  /-- See `Ryes`. -/
  Rno : A.Mat → X → Cells → Prop
  /-- the encoding randomness -/
  Rnd : Type
  [finRnd : Fintype Rnd]
  [neRnd : Nonempty Rnd]
  /-- the encoding of a message -/
  enc : (D.ix.Row × D.toDec.En → GE) → Rnd → (Fin (2 ^ D.T.a) → Run.PQ.SgX)
  /-- the pads -/
  Pad : Type
  [finPad : Fintype Pad]
  [nePad : Nonempty Pad]
  /-- the message that holds an index, with these pads -/
  hold : A.Mat → Pad → (D.ix.Row × D.toDec.En → GE)
  /-- the answers of a message to a seed -/
  smp : D.Z.D → (D.ix.Row × D.toDec.En → GE) → (D.ix.Row × D.Z.S → GE)
  /-- the cells that the honest prover computes -/
  trace : A.Mat → X → Cells
  /-- a fixed value of cells -/
  cells0 : Cells

attribute [instance] RelationsAndEncoding.finRnd RelationsAndEncoding.neRnd RelationsAndEncoding.finPad RelationsAndEncoding.nePad

variable {D}

open Classical in
/-- **The configuration of a stored table with a record.** -/
noncomputable def configurationOfStoredTable (R : D.RelationsAndEncoding A) : ConfigurationWithOutOfDomainSample where
  I := A.Mat
  X := X
  Cells := R.Cells
  Ryes := R.Ryes
  Rno := R.Rno
  n := 2 ^ D.T.a
  Sg := Run.PQ.SgX
  Msg := D.ix.Row × D.toDec.En → GE
  Rnd := R.Rnd
  enc := R.enc
  Pad := R.Pad
  hold := R.hold
  held := fun u => if A.inRange (A.mat u) then some (A.mat u) else none
  Seed := D.Z.D
  Ans := D.ix.Row × D.Z.S → GE
  smp := R.smp
  coll := D.coll
  dcd := D.dcd
  trace := R.trace
  cells0 := R.cells0

variable (R : D.RelationsAndEncoding A)

open Classical in
/-- Messages that agree before the pads hold the same index. -/
theorem conf_held (u u' : D.ix.Row × D.toDec.En → GE) (h : D.Agree u u') :
    (configurationOfStoredTable A R).held u = (configurationOfStoredTable A R).held u' := by
  show (if A.inRange (A.mat u) then some (A.mat u) else none) =
    if A.inRange (A.mat u') then some (A.mat u') else none
  rw [A.mat_cut u u' h]

open Classical in
/-- The index decoder, written out. -/
theorem conf_D (y : Fin (2 ^ D.T.a) → Run.PQ.SgX) (rec : D.Rec) :
    (configurationOfStoredTable A R).D y rec =
      if D.coll y rec.1 then none else (D.dcd y rec).bind (configurationOfStoredTable A R).held := rfl

/-- **On the statements of which the link's soundness speaks, the language of four clauses gives the
link's relation.** -/
theorem conf_req (r : D.Rec × D.Rec)
    (y : (Fin (2 ^ D.T.a) → Run.PQ.SgX) × (Fin (2 ^ D.T.a) → Run.PQ.SgX))
    (hon : (configurationOfStoredTable A R).onEq (r, y))
    (hL : D.dcd y.1 r.1 = none ∨ D.coll y.1 r.1.1 ∨ D.coll y.2 r.2.1 ∨
      ∃ u₀ u₁, D.dcd y.1 r.1 = some u₀ ∧ D.dcd y.2 r.2 = some u₁ ∧ D.Agree u₁ u₀) :
    (configurationOfStoredTable A R).ReqR (r, y) () := by
  classical
  obtain ⟨h0, h1⟩ := hon
  have h1' : ¬ D.coll y.2 r.2.1 := h1
  have h0' : ((configurationOfStoredTable A R).D y.1 r.1).isSome = true := h0
  rw [conf_D] at h0'
  by_cases hc : D.coll y.1 r.1.1
  · rw [if_pos hc] at h0'
    cases h0'
  · rw [if_neg hc] at h0'
    rcases hL with h | h | h | ⟨u₀, u₁, e0, e1, hag⟩
    · rw [h] at h0'
      cases h0'
    · exact absurd h hc
    · exact absurd h h1'
    · show (configurationOfStoredTable A R).D y.2 r.2 = (configurationOfStoredTable A R).D y.1 r.1
      rw [conf_D, conf_D, if_neg hc, if_neg h1', e0, e1]
      exact conf_held A R u₁ u₀ hag

end DecR

end OnBytes.Slice

#print axioms OnBytes.Slice.DecR.conf_held
#print axioms OnBytes.Slice.DecR.conf_req
