--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/LibBackWhole.lean: THE WAY BACK, WHOLE: from the landed Policy.HeadCl
(Policy/Seg/Head.lean: every key of the nine families is an entry of its table · the 17 identities ·
the ledger's two lines at every position · its two sums), over the base field, at the library's
record made of the kind's cells (cellsN c), to the nine keys' fields of the kind's two relations on
cells (NineKeys, Law/OutCallBack.lean) and the two guests' corner values (CornerGuests,
Law/K06Statement.lean). Statements and proofs. NO ACCEPTANCE OF ANY TEXT THAT RUNS IS CLAIMED.

Why. Law/LibWhole.lean's headCl_of_two leads from the kind's two relations to HeadCl: what soundness
spends. Here is the other way, as far as the lookup on the head's calls asks it: the keys and the
guests.

Main names.
  rf_of_headCl   HeadCl and "the cells are small" give the library's field relation over the field
    in which the program's elements are read (Johnson/Road/HeadDown.lean: ledgerRF_gl, from right to
    left).
  nine_of_rf, guests_of_rf   from that relation: Law/LibBack.lean and Law/LibBackNorm.lean, joined.
  nine_of_headCl   THE STATEMENT: NineKeys tab c and CornerGuests c.toCells.

Limits. ONE WAY. NOT CONCLUDED: the fields small, smallS, rows of CellRelN and sums of CellRelH: so
not the two relations whole. PREMISES, those of headCl_of_two to the letter: the tests on the plan
and the request · the next token is a token · Same · Wide (NO PADDING: V = JV = 202048) · More · the
kind's table is the library's EX on 16 bits · c.Wh IS the output matrix that the library reads in
Wz, AS FUNCTIONS: a record of cells whose weights part from it outside k < d, v < V does not meet
this premise (from such a record: SameCells, Law/CellsAlike.lean). And one more: the library's
clause Small of cellsN c. That cellsN c is what any committed integers spell is not said. The full
size alone. No chance in it.
Not claimed: anything on completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Kinds.Law.LibWhole
import Johnson.Desc.Kinds.Law.LibBack
import Johnson.Desc.Kinds.Law.LibBackNorm
import Johnson.Desc.Kinds.Law.OutCallBack
import Johnson.Desc.Kinds.Law.K06Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Inst.Model (ppref AcceptancePolicy Mat Instance)
open VerifiableInference.Desc.Kinds.HeadJoin
open Norm (lt ls d S2 T)

variable [Sizes] [Policy] [Request] [Token]

/-- **From the base field to the field in which the program's elements are read.** -/
theorem rf_of_headCl (c : NCells) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref)
    (hW : c.Wh = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H)
    (small : Inst.Model.Head.Small (cellsN c))
    (h : _root_.Policy.HeadCl npOf pol Wz x (cellsN c)) :
    _root_.Policy.LedgerHead.RF npOf (weightsOf c.toCells) (Inst.Model.Head.Req.of pol x)
      (cellsN c) := by
  have R2 : _root_.Policy.LedgerHead.RF (F := ZMod Cb.Gl.p) npOf
      (fun j v => (((Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H j v : ℤ) :
        ZMod Cb.Gl.p)) (Inst.Model.Head.Req.of pol x) (cellsN c) :=
    ⟨small, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  rw [← hW] at R2
  exact (OnBytes.Road.Hd.Down.ledgerRF_gl (Hz := c.Wh)).2 R2

/-- The nine keys' fields, from the library's field relation. -/
theorem nine_of_rf (sT : Nat) (tab : Nat → Nat) (c : NCells) (Y : Inst.Model.Head.Req)
    (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : Token.y < V) (S : Same Y)
    (Wd : Wide) (M : More Y) (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (R : _root_.Policy.LedgerHead.RF npOf (weightsOf c.toCells) Y (cellsN c)) :
    NineKeys tab c := by
  have P := planFacts hplan
  have hS : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have RH : _root_.Policy.LedgerHead.RF npOf (weightsOf c.toCells) Y
      (cellsOf c.toCells c.stream) := R
  have RN : _root_.Policy.LedgerHead.RF npOf (fun j v => ((c.Wh j v : ℤ) : K)) Y (cellsN c) := R
  exact ⟨top_back P hreq hy S Wd M RH, mid_back P S Wd RH, low_back P S Wd RH,
    rowA_back P S Wd M htab RH, rowB_back P S Wd M htab RH, remLow_back S.T Wd.d hS RN,
    remHigh_back S.T Wd.d hS RN, clamp_back S.T Wd.d hS RN, digits_back S.T RN⟩

/-- The two guests' corner values, from the library's field relation. -/
theorem guests_of_rf (sT : Nat) (c : NCells) (Y : Inst.Model.Head.Req)
    (hplan : planOk sT = true) (S : Same Y) (Wd : Wide)
    (R : _root_.Policy.LedgerHead.RF npOf (weightsOf c.toCells) Y (cellsN c)) :
    CornerGuests c.toCells :=
  lines_back (X := c.stream) (planFacts hplan) S Wd R

/-- **THE LANDED HeadCl GIVES THE NINE KEYS' FIELDS AND THE GUESTS.** -/
theorem nine_of_headCl (sT : Nat) (tab : Nat → Nat) (c : NCells) (pol : AcceptancePolicy) (Wz : Mat)
    (x : Instance ppref) (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : Token.y < V) (S : Same (Inst.Model.Head.Req.of pol x)) (Wd : Wide)
    (M : More (Inst.Model.Head.Req.of pol x))
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : c.Wh = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H)
    (small : Inst.Model.Head.Small (cellsN c))
    (h : _root_.Policy.HeadCl npOf pol Wz x (cellsN c)) :
    NineKeys tab c ∧ CornerGuests c.toCells :=
  ⟨nine_of_rf sT tab c _ hplan hreq hy S Wd M htab (rf_of_headCl c pol Wz x hW small h),
    guests_of_rf sT c _ hplan S Wd (rf_of_headCl c pol Wz x hW small h)⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rf_of_headCl
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.nine_of_rf
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.guests_of_rf
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.nine_of_headCl
