-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/TokSeat.lean: a token sumcheck seated behind another block.

A sub-proof runs its blocks one behind the other. Where what a later sumcheck is about is public, or
fixed by the entries, before the earlier blocks run, the caller's claim on its sum can ride through
them. This file has the one rule by which a token sumcheck (Cb/Pv/Head/Tok.lean) is put behind any
block with the four items of soundness (KnowAt, Cb/G6/Cut.lean).

Seat: the data. X1 is the statement that the earlier block hands on. Point, weights and tables of
the sumcheck are read off it. rest is what stands after the earlier block without the caller's claim
on the sum; psi is that claim.

tok_behind: if the joint after the earlier block follows from rest and psi at the true sum plus its
mask entry, then the two blocks in a row have the four items, from the earlier block's first joint
to: rest, psi at the scalar that was sent, and the sumcheck's output claims. The errors are the two
lists, one behind the other.

The property speaks of each fixed tuple of entries. It is of use only where all entries in J are
committed before the first element of this block (in a row of blocks: of the first block) is drawn.
That is the caller's to show.

What is not claimed: see Cb/Pv/Head/Tok.lean.


-/
import Cb.Pv.Head.TokMeans
import Cb.G6.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Tok
open Iop Prob Finset Johnson.L5.Layers Johnson.L5.Door TWhole

/-- A token sumcheck behind a block that hands on a statement in X1: the data. -/
structure Seat (E : Type) (k : TokKind) (X1 : Type) where
  /-- the entries: cells of committed arrays, and the mask row -/
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  /-- the place of the mask entry of a slot -/
  msk : ℕ → J
  /-- the point over the positions -/
  zt : X1 → Fin k.lt → E
  /-- the weights of the products -/
  om : X1 → Fin k.np → E
  /-- the tables of the maps -/
  tab : X1 → (J → E) → Fin k.shown → ℕ → E
  Kc : Type
  /-- the committed messages -/
  M : Type
  Wp : Type
  Ex : ExtSpec
  /-- the entries of the committed messages -/
  msg : M → J → E
  /-- what stands after the earlier block, without the caller's claim on the sum -/
  rest : IOR.Rels Kc X1 Ex (M × Wp)
  /-- the caller's claim on the scalar for the sum -/
  psi : X1 → E → (J → E) → Prop

attribute [instance] Seat.finJ Seat.decJ

section
variable {E : Type} [Field E] {k : TokKind} {X1 : Type}

/-- The entries and tables. All that the earlier block hands on is public. -/
@[reducible] def Seat.world (S : Seat E k X1) : TokWorld E k where
  Pb := X1
  J := S.J
  msk := S.msk
  tab := S.tab

/-- The sumcheck's state. -/
def Seat.st (S : Seat E k X1) (x : X1) : TokSt E X1 k := ⟨S.zt x, S.om x, x⟩

/-- What rides through the sumcheck. -/
def Seat.frame (S : Seat E k X1) : TokFrame E k S.world where
  Kc := S.Kc
  M := S.M
  Wp := S.Wp
  Ex := S.Ex
  A0 :=
    ⟨fun st y w => S.rest.rel st.pb y w, fun a w => S.rest.relR (a.1.pb, a.2) w,
      fun a => S.rest.on (a.1.pb, a.2), S.rest.core⟩
  msg := S.msg
  psi := fun st t m => S.psi st.pb t m

/-- The true sum plus the mask entry of the first slot. -/
def Seat.sum (S : Seat E k X1) (x : X1) (m : S.J → E) : E :=
  Blocks.ext k.vars (tokAt k S.world (S.st x) m) (Blocks.nat (S.st x).pt) + m (S.msk k.sCl)

variable [Fintype E]

/-- The sumcheck, taking the earlier block's statement. -/
noncomputable def Seat.R (S : Seat E k X1) :
    IOR X1 S.Ex ((TokSt E X1 k × E) × (tokT k S.world).par.Out) S.Ex :=
  (tokR k S.world S.Ex).pre (fun x => some (S.st x)) (ExtMap.id S.Ex)

/-- The joint after the sumcheck. -/
noncomputable def Seat.out (S : Seat E k X1) :
    IOR.Rels S.Kc ((TokSt E X1 k × E) × (tokT k S.world).par.Out) S.Ex (S.M × S.Wp) :=
  tokOut k S.world S.frame

/-- What the joint after the sumcheck says. -/
theorem Seat.out_relR (S : Seat E k X1)
    (b : (TokSt E X1 k × E) × (tokT k S.world).par.Out) (y : S.Ex.Str) (w : S.M × S.Wp) :
    S.out.relR (b, y) w ↔ S.rest.relR (b.1.1.pb, y) w ∧ S.psi b.1.1.pb b.1.2 (S.msg w.1) ∧
      (tokT k S.world).par.OutHolds b.2 (S.msg w.1) :=
  Iff.rfl

/-- **The rule.** -/
theorem tok_behind (S : Seat E k X1) {X0 : Type} {E0 : ExtSpec} {R1 : IOR X0 E0 X1 S.Ex}
    {A1 : IOR.Rels S.Kc X0 E0 (S.M × S.Wp)} {B1 : IOR.Rels S.Kc X1 S.Ex (S.M × S.Wp)}
    {ε1 : Err R1.shape} (g1 : KnowAt R1 A1 B1 (fun _ _ _ wp => wp) ε1)
    (ho : ∀ x y, B1.on (x, y) → S.rest.on (x, y))
    (hB : ∀ x y w, B1.on (x, y) → S.rest.relR (x, y) w →
      S.psi x (S.sum x (S.msg w.1)) (S.msg w.1) → B1.relR (x, y) w) :
    KnowAt (R1.seq S.R) A1 S.out (fun _ _ _ wp => wp)
      (Err.app ε1 (tokErr k S.world S.Ex)) :=
  knowAt_seq g1
    (knowAt_preMap (A' := B1) S.st ho
      (fun x y w hx h => by
        obtain ⟨h0, h1⟩ := h
        have h1' : S.psi x (Cb.Pv.Lay.tsum (tokT k S.world).par (S.st x) (S.msg w.1))
            (S.msg w.1) := h1
        rw [tok_tsum] at h1'
        exact hB x y w hx h0 h1')
      (tok_knowAt k S.world S.frame))

/-- The errors of the two blocks in a row. -/
theorem tok_behind_nums (S : Seat E k X1) {s : Shape} (ε1 : Err s) :
    errList (Err.app ε1 (tokErr k S.world S.Ex)) = errList ε1 ++ k.errs := by
  rw [errList_app, tok_nums]

end

end Cb.Pv.Head.Tok

#print axioms Cb.Pv.Head.Tok.tok_behind
#print axioms Cb.Pv.Head.Tok.tok_behind_nums
