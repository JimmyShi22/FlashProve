-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/TokSeat2.lean: two token sumchecks seated behind another block, with one claim of the
caller on both sums.

The output head's second and third token sumcheck start from two hidden values that one later claim
of the verifier names together. This file puts both behind any block with the four items of
soundness (KnowAt, Cb/G6/Cut.lean), by two uses of the rule of Cb/Pv/Head/TokSeat.lean.

Seat2: the data. X1 is the statement that the earlier block hands on. Points and tables of the two
sumchecks are read off it; both have one product with the weight 1. rest is what stands after the
earlier block without the caller's claim on the two sums; join is that claim, on two scalars.

two_behind: if the joint after the earlier block follows from rest and join at the two true sums,
each plus its mask entry, then the three blocks in a row have the four items, from the earlier
block's first joint to: rest, join at the two scalars that were sent, and the output claims of both
sumchecks (two_out). two_nums: the errors are the three lists, one behind the other.

The property speaks of each fixed tuple of entries. It is of use only where all entries in J are
committed before the first element of the first block is drawn. That is the caller's to show.

What is not claimed: see Cb/Pv/Head/Tok.lean. The joints after the two sumchecks have the empty
exact relation: the four items of soundness do not read it.


-/
import Cb.Pv.Head.TokSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Tok
open Iop Prob Finset Johnson.L5.Layers Johnson.L5.Door TWhole

/-- Two token sumchecks behind a block that hands on a statement in X1: the data. -/
structure Seat2 (E : Type) (kN kH : TokKind) (X1 : Type) where
  /-- the entries: cells of committed arrays, and the mask row -/
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  /-- the place of the mask entry of a slot -/
  msk : ℕ → J
  /-- the two points over the positions -/
  ztN : X1 → Fin kN.lt → E
  ztH : X1 → Fin kH.lt → E
  /-- the tables of the maps -/
  tabN : X1 → (J → E) → Fin kN.shown → ℕ → E
  tabH : X1 → (J → E) → Fin kH.shown → ℕ → E
  Kc : Type
  /-- the committed messages -/
  M : Type
  Wp : Type
  Ex : ExtSpec
  /-- the entries of the committed messages -/
  msg : M → J → E
  /-- what stands after the earlier block, without the caller's claim on the two sums -/
  rest : IOR.Rels Kc X1 Ex (M × Wp)
  /-- the caller's claim on the two scalars -/
  join : X1 → E → E → (J → E) → Prop

attribute [instance] Seat2.finJ Seat2.decJ

noncomputable section
variable {E : Type} [Field E] {kN kH : TokKind} {X1 : Type} (S : Seat2 E kN kH X1)

/-- The entries and tables of the later sumcheck, with X1 as what is public. -/
@[reducible] def Seat2.wH : TokWorld E kH where
  Pb := X1
  J := S.J
  msk := S.msk
  tab := S.tabH

/-- The later true sum plus the mask entry of its first slot. -/
def Seat2.sumH (x : X1) (m : S.J → E) : E :=
  Blocks.ext kH.vars (tokAt kH S.wH ⟨S.ztH x, fun _ => 1, x⟩ m)
    (Blocks.nat (TokSt.pt (k := kH) (Pb := X1) ⟨S.ztH x, fun _ => 1, x⟩)) + m (S.msk kH.sCl)

/-- The earlier sumcheck of the two: the later sum stands at its true value. -/
@[reducible] def Seat2.seatN : Seat E kN X1 where
  J := S.J
  msk := S.msk
  zt := S.ztN
  om := fun _ _ => 1
  tab := S.tabN
  Kc := S.Kc
  M := S.M
  Wp := S.Wp
  Ex := S.Ex
  msg := S.msg
  rest := S.rest
  psi := fun x t m => S.join x t (S.sumH x m) m

/-- The earlier true sum plus the mask entry of its first slot. -/
def Seat2.sumN (x : X1) (m : S.J → E) : E := S.seatN.sum x m

variable [Fintype E]

/-- What the earlier sumcheck of the two hands on. -/
abbrev Seat2.X2 : Type := (TokSt E X1 kN × E) × (tokT kN S.seatN.world).par.Out

/-- The later sumcheck. -/
@[reducible] def Seat2.seatH : Seat E kH S.X2 where
  J := S.J
  msk := S.msk
  zt := fun x => S.ztH x.1.1.pb
  om := fun _ _ => 1
  tab := fun x => S.tabH x.1.1.pb
  Kc := S.Kc
  M := S.M
  Wp := S.Wp
  Ex := S.Ex
  msg := S.msg
  rest :=
    ⟨fun _ _ _ => False,
      fun a w => S.rest.relR (a.1.1.1.pb, a.2) w ∧
        (tokT kN S.seatN.world).par.OutHolds a.1.2 (S.msg w.1),
      fun a => S.rest.on (a.1.1.1.pb, a.2), S.rest.core⟩
  psi := fun x t m => S.join x.1.1.pb x.1.2 t m

/-- **The rule.** -/
theorem two_behind {X0 : Type} {E0 : ExtSpec} {R1 : IOR X0 E0 X1 S.Ex}
    {A1 : IOR.Rels S.Kc X0 E0 (S.M × S.Wp)} {B1 : IOR.Rels S.Kc X1 S.Ex (S.M × S.Wp)}
    {ε1 : Err R1.shape} (g1 : KnowAt R1 A1 B1 (fun _ _ _ wp => wp) ε1)
    (ho : ∀ x y, B1.on (x, y) → S.rest.on (x, y))
    (hB : ∀ x y w, B1.on (x, y) → S.rest.relR (x, y) w →
      S.join x (S.sumN x (S.msg w.1)) (S.sumH x (S.msg w.1)) (S.msg w.1) → B1.relR (x, y) w) :
    KnowAt ((R1.seq S.seatN.R).seq S.seatH.R) A1 S.seatH.out (fun _ _ _ wp => wp)
      (Err.app (Err.app ε1 (tokErr kN S.seatN.world S.Ex)) (tokErr kH S.seatH.world S.Ex)) :=
  tok_behind S.seatH (tok_behind S.seatN g1 ho hB) (fun _ _ h => h)
    fun _ _ _ _ h0 h1 => ⟨h0.1, h1, h0.2⟩

/-- What the joint after the three blocks says. -/
theorem two_out (b : (TokSt E S.X2 kH × E) × (tokT kH S.seatH.world).par.Out) (y : S.Ex.Str)
    (w : S.M × S.Wp) :
    S.seatH.out.relR (b, y) w ↔
      (S.rest.relR (b.1.1.pb.1.1.pb, y) w ∧
        (tokT kN S.seatN.world).par.OutHolds b.1.1.pb.2 (S.msg w.1)) ∧
      S.join b.1.1.pb.1.1.pb b.1.1.pb.1.2 b.1.2 (S.msg w.1) ∧
      (tokT kH S.seatH.world).par.OutHolds b.2 (S.msg w.1) :=
  Iff.rfl

/-- The errors of the three blocks in a row. -/
theorem two_nums {s : Shape} (ε1 : Err s) :
    errList (Err.app (Err.app ε1 (tokErr kN S.seatN.world S.Ex))
      (tokErr kH S.seatH.world S.Ex)) = errList ε1 ++ kN.errs ++ kH.errs := by
  rw [tok_behind_nums S.seatH, tok_behind_nums S.seatN]

end

end Cb.Pv.Head.Tok

#print axioms Cb.Pv.Head.Tok.two_behind
#print axioms Cb.Pv.Head.Tok.two_nums
