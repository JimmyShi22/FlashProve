-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartNext.lean: a reduction step, without interaction, between two pairs of relations: from
what the sub-protocol that ends segment k (its closing) leaves of the model's claims to the relation
at which segment k + 1 starts; it is in order (`StepWOK`, Cb/Ld/LdStepW.lean) for every partition
with its laws, under the hypotheses of `Spec.ldPartNext_step`.

Definitions and one statement (`Cb.Spec.ldPartNext_step`); the proof is in
Cb/Part/LdPartNextProofs.lean.
`StepWOK` asks of a step without a round: exact relation and condition forth, core kept, relaxed
relation back where the condition holds.

Why: a segment of a request that is
built after the one before it asks of the model
a step without a round, messages untouched, from the model's part of what
stands after the closing to the model's own entry relation. In a write-up of ours
(lean/CREDITS.md) the two relations are equal by definition: behind segment k the relation holds the
conditions of segment k +
1 and of all later segments, the cells of k + 1 now being read off the messages just sent. Here they
are two readings, and their agreement, in the sense of `StepWOK` and under the hypotheses of
`Spec.ldPartNext_step`, is a theorem (Cb/Part/LdPartNextProofs.lean).
Of the partition's laws the proof uses: well-formedness; a segment reads places of itself and of
earlier segments, inside the shapes (`reads`); a row of an earlier segment that a later one reads is
kept behind every segment in between (`keeps`).



Main names:
  `Spec.ldPartNext_step`: `P.Props p`, k + 1 < P.n, the ties, a map f of states that keeps instance
    and record ⇒ `StepWOK` from `ldPartBehind` (index decoded; `rideB` k at Ok) to (index decoded;
    `entry` (k + 1) at O'), with f. The further witness is not touched, in either direction, and no
    message is read by the step's maps.

Limits: for arbitrary parameters: no closing, no body occurs; what is used of them is a record of
ties.
Declared (by inspection). (1) `rideB`'s relaxed side claims no packing of the kept rows, where the
write-up's riding predicate of a later segment covers the earlier matrices that it reads:
weaker,
and harmless for the chain (the way back needs less). (2) `O'.pkR` is to speak of the rows of the
new body's matrix alone: going backwards it must come out of that body's range check. If that matrix
holds all kept rows, also those that only a later segment reads, every body checks them again: more
digits than in the write-up. (3) `P.kept k` is a set of rows; the description keeps whole
matrices. (4) One further witness type in all segments, never touched by a step, a layer overwritten
at a closing: so a record that asks "what is left of the further witness determines it" for all
values cannot be met by such a closing; the builder's target does not ask it.
This file does not say that the ties hold (Cb/Part/LdPartCells.lean's reading, the closing's places,
unique packing), or that the front's entry stage is "index decoded;
entry". It says nothing on the pending rows and the closing's rows (they ride by the wrappers).
Nothing on masks.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Part.LdPartRide
import Cb.Ld.LdStepW
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb

open Iop Prob Hiop Blocks Finset Cb.RngPk IOR

namespace LdPartD
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E} (P : LdPartD Cf)
  (K : LdPartPk) {S : Sig E} {St : Type}

/-- What rides after the read stage of segment k and through its closing: the riding relation
(`ride`, Cb/Part/LdPartRide.lean) without the relaxed clause "packed" (`O.pkR`). From the read stage
on that clause stands in the range check's own relation; behind the range check it is one of the
rows. -/
def rideB (k : ℕ) (O : LdPartOut E S) (x : St → Cf.Xm) (rc : St → Cf.conf.Rec)
    (bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop) :
    Rels LdPartGh St Cf.conf.E0 ((Cf.conf.Msg × S.Msg) × (LdPartW E × LdPartGh)) :=
  { P.ride K k O x rc bitX with
    relR := fun a t =>
        (∀ j, k < j → j < P.n → Packed K.P (2 * P.D) K.rdx (P.layW K t.2.1 j)) ∧
        ∀ j, k < j → j < P.n →
          (P.seg j).Holds P.fmt (x a.1) (P.matU t.1.1) (P.world K k O t.1.2 t.2.1) }

/-- The entry relation of segment k, on tuples: the riding relation of k, and segment k's own
conditions at the cells read off the messages (both worlds), and, exact only, `vld`: its lookup's
bits in the messages are valid. -/
def entry (k : ℕ) (O : LdPartOut E S) (x : St → Cf.Xm) (rc : St → Cf.conf.Rec)
    (bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop)
    (vld : St → Cf.conf.Msg × S.Msg → Prop) :
    Rels LdPartGh St Cf.conf.E0 ((Cf.conf.Msg × S.Msg) × (LdPartW E × LdPartGh)) where
  rel  := fun st y t =>
    (P.ride K k O x rc bitX).rel st y t ∧
    (P.seg k).Holds P.fmt (x st) (P.matU t.1.1) (O.A t.1.2) ∧
    vld st t.1
  relR := fun a t =>
    (P.ride K k O x rc bitX).relR a t ∧ (P.seg k).Holds P.fmt (x a.1) (P.matU t.1.1) (O.A t.1.2)
  on   := (P.ride K k O x rc bitX).on
  core := fun t => t.2.2

end LdPartD

/-- A relation A on (kept messages, further witness), read after a closing: at (the kept messages of
m, the further witness with the layer just sent overwritten by what is read off m). -/
def ldPartBehind {E Kc St Pi : Type} [Field E] {E₀ : ExtSpec} {Sk S' : Sig E}
    (A : Rels Kc St E₀ (Sk.Msg × (Pi × (LdPartW E × LdPartGh))))
    (kept : S'.Msg → Sk.Msg) (ov : S'.Msg → LdPartW E → LdPartW E) :
    Rels Kc St E₀ (S'.Msg × (Pi × (LdPartW E × LdPartGh))) where
  rel  := fun st y w => A.rel st y (kept w.1, (w.2.1, (ov w.1 w.2.2.1, w.2.2.2)))
  relR := fun a w => A.relR a (kept w.1, (w.2.1, (ov w.1 w.2.2.1, w.2.2.2)))
  on   := A.on
  core := fun w => A.core (kept w.1, (w.2.1, (ov w.1 w.2.2.1, w.2.2.2)))

/-- The ties between the reading Ok of the kept messages before a closing, the reading O' of the
open messages after it, and the overwriting ov. `ovPk`, `ovBit`: ov touches layer k + 1 alone. In
the exact world: `pkX`: kept rows packed before, and layer k + 1 (read off m) the packing of the
ghost's matrix ⇒ all rows of the new body's matrix are packed; `rdX`: packed ⇒ `O'.A m` is the ghost
at the places that segment k + 1 reads; `bits`: packed, and honest bits in layer k + 1 (read off m)
⇒ `vld`. In the relaxed world, each under `O'.pkR m`: `pkR`: layer k + 1 (read off m) is a packing;
`rdOwn`: `O'.A m (k + 1)` is what is unpacked from it, inside the segment's shape; `rdKept`:
`O'.A m` is `Ok.A (kept m)` on the rows kept behind k. -/
structure LdPartTie {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E}
    (P : LdPartD Cf) (K : LdPartPk) (k : ℕ) {Sk S' : Sig E} (Ok : LdPartOut E Sk)
    (O' : LdPartOut E S') (kept : S'.Msg → Sk.Msg) (ov : S'.Msg → LdPartW E → LdPartW E)
    {St' : Type} (x' : St' → Cf.Xm) (bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop)
    (vld : St' → Cf.conf.Msg × S'.Msg → Prop) : Prop where
  ovPk   : ∀ m w j, j ≠ k + 1 → (ov m w).pk j = w.pk j
  ovBit  : ∀ m w j, j ≠ k + 1 → (ov m w).bit j = w.bit j
  pkX    : ∀ m w g, Ok.pkX (kept m) g →
    PackBy P.B K.rdx (P.layX K g (k + 1)) (P.layW K (ov m w) (k + 1)) → O'.pkX m g
  rdX    : ∀ m g, O'.pkX m g →
    ∀ q ∈ (P.seg (k + 1)).places, O'.A m q.1 q.2.1 q.2.2 = ((g q.1 q.2.1 q.2.2 : ℤ) : E)
  bits   : ∀ st U m w g,
    O'.pkX m g → bitX (k + 1) (x' st) (P.matU U) g ((ov m w).bit (k + 1)) → vld st (U, m)
  pkR    : ∀ m w, O'.pkR m → Packed K.P (2 * P.D) K.rdx (P.layW K (ov m w) (k + 1))
  rdOwn  : ∀ m w, O'.pkR m →
    ∀ r c, r < 2 ^ (P.seg (k + 1)).rowsLog → c < (P.seg (k + 1)).cols →
      O'.A m (k + 1) r c = P.cellsW K (ov m w) (k + 1) r c
  rdKept : ∀ m, O'.pkR m → ∀ q ∈ P.kept k, ∀ c, O'.A m q.1 q.2 c = Ok.A (kept m) q.1 q.2 c

namespace Spec

/-- The model's step at the head of segment k + 1. -/
def ldPartNext_step : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (p k : ℕ) (Sk S' : Sig E) (Ok : LdPartOut E Sk) (O' : LdPartOut E S')
      (kept : S'.Msg → Sk.Msg) (ov : S'.Msg → LdPartW E → LdPartW E) (St St' : Type)
      (x : St → Cf.Xm) (rc : St → Cf.conf.Rec) (x' : St' → Cf.Xm) (rc' : St' → Cf.conf.Rec)
      (f : St → St') (bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop)
      (vld : St' → Cf.conf.Msg × S'.Msg → Prop),
    P.Props p → k + 1 < P.n → LdPartTie P K k Ok O' kept ov x' bitX vld →
    (∀ st, x' (f st) = x st) → (∀ st, rc' (f st) = rc st) →
    StepWOK S' (ldPartBehind (idxAt Cf.conf rc (P.rideB K k Ok x rc bitX)) kept ov)
      (idxAt Cf.conf rc' (P.entry K (k + 1) O' x' rc' bitX vld)) f (fun _ w => w.2) (fun _ w => w.2)

end Spec

end Cb
