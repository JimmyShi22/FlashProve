-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecConf.lean: this file fixes the abstract setting of the holographic interactive oracle proof:
the indexed relation, the encoding of an index as an oracle, the record phase with the index
decoder, the laws asked of a configuration (`ConfigurationWithOutOfDomainSample.Props`), what a preamble
leaves (`Left`), and the relations between which its sub-protocols reduce.

Definitions only; no code, no distance, no field occurs
here.

Main names:
  `ConfigurationWithOutOfDomainSample`, what a configuration holds: the indexed relation pair
    (Ryes, Rno on index, instance, cells); the word length and alphabet; `trace`, the cells that the
    honest prover computes. Further:
    `Msg`, `Rnd`, `enc`: a message of an encoded index, pads included, is encoded under encoding
      randomness.
    `Pad`, `hold i η`: the encoded index has pads off the layout: the committer draws η uniformly
      and encodes the message `hold i η`.
      The committer's randomness is (η, encoding randomness); pads of different encoded
      indices are independent because each has its own committer's randomness. (By type `Pad` is any
      finite, non-empty type. It enters `hold`; the committer's randomness and encoding: `EncodingRandomness`, `encodeIndex`
      of `SubsR.lhr`, Hiop/RecBuild.lean; a uniform η: among others `Props.hides`, and, with a new
      draw of `EncodingRandomness` for each encoded index, `start`, `fresh` of `realHostR`, Hiop/RecWhole.lean.)
    `held m`: the index that a message holds, or none; that it does not read the pads is the law
      `held_hold`, for every η.
    `Seed`, `Ans`, `smp s m`: the record phase: the answers of the message m (pads included) to the
      seed s. By type the encoding randomness is not read. (In the construction: one answer for each
      row of the index; Hiop/RecRows.lean.)
    `coll y s`: the word y has a collision at s; `dcd y rec`: decoding with the record: a message or
      none. Both abstract.
    `D y rec`: the index decoder: none at a collision; else `held` of the decoded message.
    `PIdx`: a prover encoded index: (message, encoding randomness), kept with its record. (The
      committer itself outputs the word and (message, encoding randomness); that whoever builds a
      prover makes the record once and keeps it there is a remark for them, which these types
      follow.)
  `ConfigurationWithOutOfDomainSample.Props b eR`: `sub`, `admits`, decoding of honest words, `held_hold`,
    that honest words have no collision (`free_enc`), and two laws of the record: it binds (`rcd`:
    every word has a collision at no more than eR seeds) and it hides (`hides`: at every seed the
    law of (answers, any b positions of the word) does not depend on the index). Both are hypotheses
    on the configuration here; for an index in rows with pads (`Rows.Laws`), with a strong encoding
    (`C.Strong b`), the second is derived in Hiop/RecRows.lean.
  The relations. Exact ones are `Rwf`, `Rreq`, `Req`, `Rlin` (in `Req`: the same index; the pads may
    differ), with the prover encoded index as (part of) the witness, and say in addition that the
    record of the statement is the record kept with it and holds the answers of its message (`Enc`).
    Relaxed relations hold no prover encoded index and no encoding randomness: an oracle with a
    record is decoded by the statement.
    `RwfR (rec, y)`: no witness: the index decoder answers.
    `RreqR ((x, rec), y) c`: the witness is the cells: they are valid in Rno for the decoded index.
    `ReqR ((rec, rec'), y)`: no witness: the further encoded index decodes to the same index as the
      first (an equation between two values of `D`: both may be none; `onEq` asks that the first
      decodes).
    `S.RlinR ((xl, rec), y) m`: the witness is the message to which the oracles left decode
      (`adec`): the claims hold of (U, m), U the message to which (y.1, rec) decodes; U may lie
      outside the index set; false if there is none.
    One relaxation of the constraint relation serves both phases.
  `S.cond`: the collision-free statements of the constraint relation. `C.free`, `C.onEq`: the
    statements on which soundness of the offline IOP and of the link is stated (`Spec.rec_offline`,
    Hiop/RecMain.lean; `LinkKnowR`, Hiop/RecSubs.lean).
  `Left`, what a preamble leaves: oracles under an encoding, explicit claims, and
    when the claims hold; here the oracles left are decoded with the samples that stand in the
    claims (`adec xl y`), may have collisions at their own seeds (`afree`), and the claims may read
    the record. Beside the record they read messages only, by type.



Limits: DECLARED: "holds" is given the WHOLE message of the encoded index, pads too; on paper the
claims read the index that it holds, and a pad enters no revealed value but its answer. Wider; no
loss for soundness.
This file says nothing on which code, distance or model; nothing on whether a configuration with
these laws exists. A silly decoding drives an error or a bad set of the sub-protocols' parameter
lists up to 1.
The relations follow the worked example named in lean/CREDITS.md and this protocol's technical
report, which follows the paper that this protocol builds on.

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecInterface
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Hiop
open Iop Prob

/-- A configuration with a record. -/
structure ConfigurationWithOutOfDomainSample where
  I     : Type
  X     : Type
  Cells : Type
  /-- the indexed relation and its relaxation -/
  Ryes  : I → X → Cells → Prop
  Rno   : I → X → Cells → Prop
  /-- the encoded index: a word of n symbols -/
  n     : ℕ
  Sg    : Type
  /-- the messages of an encoded index, pads included -/
  Msg   : Type
  /-- the encoding randomness -/
  Rnd   : Type
  [finRnd : Fintype Rnd]
  [neRnd  : Nonempty Rnd]
  enc   : Msg → Rnd → (Fin n → Sg)
  /-- the pads: what the committer puts, uniformly, at fixed places off the layout (by type any
  finite, non-empty type; it enters `hold`; among the clauses on it: `Props.held_hold`,
  `Props.hides`) -/
  Pad   : Type
  [finPad : Fintype Pad]
  [nePad  : Nonempty Pad]
  /-- the message that holds an index, with these pads -/
  hold  : I → Pad → Msg
  /-- the index that a message holds, if it is in the index set -/
  held  : Msg → Option I
  /-- the record phase: seeds, answers -/
  Seed  : Type
  [finSeed : Fintype Seed]
  [neSeed  : Nonempty Seed]
  Ans   : Type
  /-- the answers of a message to a seed; the encoding randomness is not read -/
  smp   : Seed → Msg → Ans
  /-- the word has a collision at the seed -/
  coll  : (Fin n → Sg) → Seed → Prop
  /-- decoding with the record: a message (pads included), or none -/
  dcd   : (Fin n → Sg) → Seed × Ans → Option Msg
  /-- the cells that the honest prover computes -/
  trace : I → X → Cells
  /-- a fixed value of cells, where there is nothing to extract from -/
  cells0 : Cells

attribute [instance] ConfigurationWithOutOfDomainSample.finRnd ConfigurationWithOutOfDomainSample.neRnd ConfigurationWithOutOfDomainSample.finPad ConfigurationWithOutOfDomainSample.nePad ConfigurationWithOutOfDomainSample.finSeed ConfigurationWithOutOfDomainSample.neSeed

namespace ConfigurationWithOutOfDomainSample
variable (C : ConfigurationWithOutOfDomainSample)

/-- the oracle kind of the encoded index -/
abbrev E0 : ExtSpec := oneExternalString C.n C.Sg
/-- a record -/
abbrev Rec : Type := C.Seed × C.Ans
/-- a prover encoded index: message and encoding randomness, kept with its record -/
abbrev PIdx : Type := (C.Msg × C.Rnd) × C.Rec

open Classical in
/-- The index decoder: none at a collision; none if the word does not decode with the record; none
if the decoded message holds no index of the index set. -/
def D (y : C.E0.Str) (rec : C.Rec) : Option C.I :=
  if C.coll y rec.1 then none else (C.dcd y rec).bind C.held

/-- the private input of the honest sides for one encoded index: index, pads, encoding randomness,
the seed of its record -/
abbrev Priv : Type := C.I × (C.Pad × C.Rnd) × C.Seed

/-- the prover encoded index that belongs to it -/
def pidx (i : C.I) (r : C.Pad × C.Rnd) (s : C.Seed) : C.PIdx :=
  ((C.hold i r.1, r.2), (s, C.smp s (C.hold i r.1)))

/-- What a configuration has to satisfy; b is the number of positions that an encoded index hides
beside its record, eR the number of seeds at which a word may have a collision. -/
structure Props (b eR : ℕ) : Prop where
  sub       : ∀ i x w, C.Ryes i x w → C.Rno i x w
  admits    : ∀ i x w, C.Ryes i x w → C.Ryes i x (C.trace i x)
  /-- an honest word with an honest record decodes, and has no collision -/
  dcd_enc   : ∀ m r s, C.dcd (C.enc m r) (s, C.smp s m) = some m
  free_enc  : ∀ m r s, ¬ C.coll (C.enc m r) s
  /-- the pads are not read (exactly: `held (hold i η)` is `some i` for every i and η) -/
  held_hold : ∀ i η, C.held (C.hold i η) = some i
  /-- the record binds: every word has a collision at no more than eR seeds -/
  rcd       : ∀ y, cnt (fun s => C.coll y s) ≤ eR
  /-- the record hides: at every seed, the law of (answers, the encoded index at any b positions),
  over pads and encoding randomness, does not depend on the index -/
  hides     : ∀ (S : Finset (Fin C.n)), S.card ≤ b →
    ∀ (s : C.Seed) i i',
      (unif (C.Pad × C.Rnd)).map
          (fun r => (C.smp s (C.hold i r.1), fun p : S => C.enc (C.hold i r.1) r.2 p)) =
        (unif (C.Pad × C.Rnd)).map
          (fun r => (C.smp s (C.hold i' r.1), fun p : S => C.enc (C.hold i' r.1) r.2 p))

/-! ### The relations of the preambles -/

/-- y is the encoding of the prover encoded index w, and rec is its record, with the answers of its
message -/
def Enc (rec : C.Rec) (y : C.E0.Str) (w : C.PIdx) : Prop :=
  y = C.enc w.1.1 w.1.2 ∧ w.2 = rec ∧ rec.2 = C.smp rec.1 w.1.1

/-- a statement without a collision -/
def free (a : C.Rec × C.E0.Str) : Prop := ¬ C.coll a.2 a.1.1

/-- weights-formedness -/
def Rwf : C.Rec → C.E0.Str → C.PIdx → Prop := fun rec y w =>
  C.Enc rec y w ∧ ∃ i η, w.1.1 = C.hold i η
/-- its relaxation: no witness; the index is decoded by the statement -/
def RwfR : C.Rec × C.E0.Str → Unit → Prop := fun a _ => (C.D a.2 a.1).isSome

/-- the request relation -/
def Rreq : C.X × C.Rec → C.E0.Str → C.PIdx × C.Cells → Prop := fun x y w =>
  C.Enc x.2 y w.1 ∧ ∃ i η, w.1.1.1 = C.hold i η ∧ C.Ryes i x.1 w.2
/-- its relaxation: the witness holds the cells alone -/
def RreqR : (C.X × C.Rec) × C.E0.Str → C.Cells → Prop := fun a c =>
  ∃ i, C.D a.2 a.1.2 = some i ∧ C.Rno i a.1.1 c

/-- the equality relation on two encoded indices: the same index; the pads may differ -/
def Req : C.Rec × C.Rec → (twoExternalStrings C.n C.Sg).Str → C.PIdx × C.PIdx → Prop := fun rr y w =>
  C.Enc rr.1 y.1 w.1 ∧ C.Enc rr.2 y.2 w.2 ∧ ∃ i η η', w.1.1.1 = C.hold i η ∧ w.2.1.1 = C.hold i η'
/-- its relaxation: no witness -/
def ReqR : (C.Rec × C.Rec) × (twoExternalStrings C.n C.Sg).Str → Unit → Prop := fun a _ =>
  C.D a.2.2 a.1.2 = C.D a.2.1 a.1.1
/-- the statements on which the link's soundness is stated: the first encoded index decodes to an
index, the further one has no collision -/
def onEq (a : (C.Rec × C.Rec) × (twoExternalStrings C.n C.Sg).Str) : Prop :=
  (C.D a.2.1 a.1.1).isSome ∧ ¬ C.coll a.2.2 a.1.2.1

/-- What a preamble leaves: oracles of the kind Ej under an encoding, explicit claims Xl (which hold
the samples of these oracles), and when a claim holds of the message of the encoded index and the
message of these oracles. -/
structure Left where
  Ej    : ExtSpec
  Xl    : Type
  /-- messages and encoding randomness of the oracles left -/
  AMsg  : Type
  ARnd  : Type
  /-- the oracles y are the encoding of the message under the randomness.  (A relation, not a map:
  oracles may be sent in a format, say over a subfield, in which not every pair has a word.) -/
  aEnc  : Ej.Str → AMsg → ARnd → Prop
  /-- decoding with the samples that stand in the claims -/
  adec  : Xl → Ej.Str → Option AMsg
  /-- none of the oracles left has a collision at its seed -/
  afree : Xl → Ej.Str → Prop
  /-- the claims; beside the record they read messages only -/
  holds : Xl → C.Rec → C.Msg → AMsg → Prop

variable {C}
namespace Left
variable (S : C.Left)

abbrev El : ExtSpec := C.E0.prod S.Ej
abbrev WAux : Type := S.AMsg × S.ARnd
/-- a statement: (claims, the record), (encoded index, oracles left) -/
abbrev St : Type := (S.Xl × C.Rec) × S.El.Str

/-- the constraint relation -/
def Rlin : S.Xl × C.Rec → S.El.Str → C.PIdx × S.WAux → Prop := fun x y w =>
  C.Enc x.2 y.1 w.1 ∧ S.aEnc y.2 w.2.1 w.2.2 ∧ S.holds x.1 x.2 w.1.1.1 w.2.1
/-- its relaxation: the witness holds the message to which the oracles left decode (`adec`), and
nothing else: no prover encoded index, no encoding randomness. The claims are read on the message U
to which the statement decodes; U need not hold an index of the index set; false if there is none.
-/
def RlinR : S.St → S.AMsg → Prop := fun a m =>
  ∃ U, C.dcd a.2.1 a.1.2 = some U ∧ S.adec a.1.1 a.2.2 = some m ∧ S.holds a.1.1 a.1.2 U m
/-- a collision-free statement: neither the encoded index at its record's seed nor an oracle left at
its sample's seed has a collision -/
def cond (a : S.St) : Prop := ¬ C.coll a.2.1 a.1.2.1 ∧ S.afree a.1.1 a.2.2

/-- decode the oracles left; the fixed value d0 where they do not decode -/
def decA (d0 : S.AMsg) (xl : S.Xl) (y : S.Ej.Str) : S.AMsg := (S.adec xl y).getD d0

end Left
end ConfigurationWithOutOfDomainSample
end Hiop
