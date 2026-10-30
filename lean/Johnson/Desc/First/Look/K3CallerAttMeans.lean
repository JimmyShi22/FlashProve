-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerAttMeans.lean: FROM THE JOINT IN FRONT OF THE LOOKUP ON AN ATTENTION
LINK's CALLS, AT THE CLOSED CALLER (K3CallerAtt.lean: att_says), TO TWO CLAUSES OF THE MEANING's
ROW: «every looked-up value is an entry of its table» and «the denominator is the sum of the row's
weights», in that row's own letters. Definitions, statements and proofs. NO SOUNDNESS OF ANY TEXT
THAT RUNS IS CLAIMED.

Why. The integer model's row on the meaning of a proof file rests on a structure Means of named
clauses on hidden integer matrices (Johnson/Goal/Meaning/Row.lean). Two of them
name the lookup: attKey [K3 with K5] and attRidden [at K3's point]. Both are stated over the base
field Cb.Gl.F at the cells castT (cellsA S Z), S the sub-proof's shape and Z the sub-proof's list of
integer matrices. This file shows that the closed caller's joint in front IS these two clauses,
under one named reading of the cells and two premises on public data.

Main names:
  `CellsAre m Z`: THE NAMED READING: the cells that the caller reads off the messages m are the
    casts of the cells that the library's rule of addresses reads in the integer matrices Z.
  `zsOf s Mz`, `attCells_cast`: the reading is PAID where the committed symbols are the packing of
    small integers Mz (Cb.Pv.Tail.BaseAt: the smallness test's clause), at Z := these integers as
    total matrices, 0 outside the bounds.
  `TabsAre S h`: premise on public data: every row of the verifier's table of call c is a row of
    the library's table of call c.
  `att_attRidden`: the joint in front and the reading give the clause attRidden, TO THE LETTER of
    Meaning/Row.lean at S := Hd.shapeA X g, Z := w.MA g.
  `att_attKey`: with TabsAre and «the pieces of each call fit into it» they give the clause attKey,
    to the letter likewise.

Limits. Meaning/Row.lean is not imported: «to the letter» is held by eye against its text,
not by Lean. The step from E to F is by the two fields' one characteristic. TabsAre is
shown at no value here; the library's Hd.IsLut (Johnson/Road/HeadTabs.lean) with isLut_layCall
(Johnson/Road/Lane5AttTabs.lean) is meant to pay it, at a shape with kFD = 16. The limits of
K3CallerAtt.lean stand: above all that addrA and keyVec are what the programs lay is shown by no
theorem, and AttOK has been run at no real link in full.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAtt
import Cb.Pv.Tail.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open OnBytes.Road.L5 (Zs dimOf sclOf tbOf addrA cellsA)
open Inst.Model.AttSeg (Raw Idn idnVal keyVec lut lutSet castT)
open Cb.Pv.Tail (JCell BaseAt)

noncomputable section
open Johnson.Pack VerifiableInference.OnPublicFiles

/-- Integers at the cells of the list's matrices, as total matrices (number in the list, row,
column): 0 outside the bounds. -/
def zsOf (s : Cb.Pv.Tail.Size) (Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ) : Zs :=
  fun a r c =>
    if h : a < s.NM ∧ c < s.k a ∧ r < s.m a then Mz ⟨a, h.1⟩ ⟨c, h.2.1⟩ ⟨r, h.2.2⟩ else 0

/-- **Every row of the verifier's table of a call is a row of the library's**, as elements of the
base field (so a row that the library writes as a negative integer is not shut out). On public
data. -/
def TabsAre (S : Attention.Shape) (h : Forest.Shape) : Prop :=
  ∀ (c : Fin 4) (u : ℕ), u < 2 ^ Cb.LdLkp.Port.kOf h c →
    ∃ ι : ℕ, ι < (lut (scl := sclOf S) (dimOf S) (tbOf S) c).rows ∧
      ((FoNums.tauN h c u : ℕ) : Cb.Gl.F) =
        (((lut (scl := sclOf S) (dimOf S) (tbOf S) c).row ι : ℤ) : Cb.Gl.F)

section
variable {set : Params.Setting} {x : Place} {S : Attention.Shape} {tl : HTailF2} {D : Sent}
  {rad : OracleShape → Nat} (Ex : Iop.ExtSpec) (Wp : Type)

/-- **THE NAMED READING.** -/
def CellsAre (x : Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat)
    (m : (attSg x D rad).Msg) (Z : Zs) : Prop :=
  attCells x S tl D rad m = (castT (cellsA S Z) : Raw → Cb.Gl.E)

/-- **The reading is paid where the committed symbols are the packing of small integers.** -/
theorem attCells_cast (m : (attSg x D rad).Msg)
    (Mz : ∀ μ : Fin (szOf tl).NM, Fin ((szOf tl).k μ) → Fin ((szOf tl).m μ) → ℤ)
    (B : BaseAt (symAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl m) Mz) :
    CellsAre x S tl D rad m (zsOf (szOf tl) Mz) := by
  funext r
  show msgAtt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl x.ns m
      (enCell x.ns tl (addrA S r).1 (addrA S r).2.1 (addrA S r).2.2) =
    ((zsOf (szOf tl) Mz (addrA S r).1 (addrA S r).2.1 (addrA S r).2.2 : ℤ) : Cb.Gl.E)
  unfold enCell cellJ zsOf
  by_cases h : (addrA S r).1 < (szOf tl).NM ∧ (addrA S r).2.2 < (szOf tl).k (addrA S r).1 ∧
      (addrA S r).2.1 < (szOf tl).m (addrA S r).1
  · rw [dif_pos h, dif_pos h]
    exact B.2.2 ⟨⟨_, h.1⟩, ⟨_, h.2.1⟩, ⟨_, h.2.2⟩⟩
  · rw [dif_neg h, dif_neg h]
    exact Int.cast_zero.symm

/-- **THE CLAUSE attRidden**: the denominator is the sum of the row's weights: over the base field,
at the casts of the integer cells. -/
theorem att_attRidden (H : AttOK set x S tl D rad) (a : Unit × Ex.Str)
    (w : (attSg x D rad).Msg × Wp)
    (h : ((kLookupCR [attRider x S tl D rad Ex Wp]).A (attRider x S tl D rad Ex Wp)).relR a w)
    (Z : Zs) (hZ : CellsAre x S tl D rad w.1 Z) :
    ∀ b g' n, (Idn.at3 b g' n).Valid (dimOf S) →
      idnVal (dimOf S) (castT (cellsA S Z) : Raw → Cb.Gl.F) (.at3 b g' n) = 0 := by
  intro b g' n hv
  have h1 := ((att_says Ex Wp H a w).1 h).2 b g' n hv
  rw [hZ, Inst.Model.AttSeg.idn_cast] at h1
  rw [Inst.Model.AttSeg.idn_cast]
  exact (CharP.intCast_eq_zero_iff Cb.Gl.F Cb.Gl.p _).2
    ((CharP.intCast_eq_zero_iff Cb.Gl.E Cb.Gl.p _).1 h1)

/-- **THE CLAUSE attKey**: every looked-up value in a piece is an entry of its table: over the base
field, at the casts of the integer cells. hU: the pieces of each call fit into it. -/
theorem att_attKey (H : AttOK set x S tl D rad) (a : Unit × Ex.Str)
    (w : (attSg x D rad).Msg × Wp)
    (h : ((kLookupCR [attRider x S tl D rad Ex Wp]).A (attRider x S tl D rad Ex Wp)).relR a w)
    (Z : Zs) (hZ : CellsAre x S tl D rad w.1 Z) (hT : TabsAre S x.fs)
    (hU : ∀ c : Fin 4, (dimOf S).used c ≤ 2 ^ Cb.LdLkp.Port.nOf x.fs c) :
    ∀ (c : Fin 4) (n : ℕ), n < (dimOf S).used c →
      keyVec (scl := sclOf S) (dimOf S) (tbOf S) (castT (cellsA S Z) : Raw → Cb.Gl.F) c n ∈
        lutSet (lut (scl := sclOf S) (dimOf S) (tbOf S) c) := by
  intro c n hn
  obtain ⟨u, hu, e⟩ := ((att_says Ex Wp H a w).1 h).1 c.val
    (by rw [H.four]; exact c.isLt) n (lt_of_lt_of_le hn (hU c))
  rw [attLay_K] at e
  have e2 : keyVec (scl := sclOf S) (dimOf S) (tbOf S) (attCells x S tl D rad w.1) c n =
      ((FoNums.tauN x.fs c u : ℕ) : Cb.Gl.E) := e
  rw [hZ, Inst.Model.AttSeg.key_cast (scl := sclOf S) (dimOf S) (tbOf S) (cellsA S Z) n c] at e2
  obtain ⟨ι, hι, er⟩ := hT c u hu
  refine ⟨ι, hι, ?_⟩
  rw [Inst.Model.AttSeg.key_cast (scl := sclOf S) (dimOf S) (tbOf S) (cellsA S Z) n c]
  have e3 : ((keyVec (scl := sclOf S) (dimOf S) (tbOf S) (cellsA S Z) c n : ℤ) : Cb.Gl.E) =
      (((FoNums.tauN x.fs c u : ℕ) : ℤ) : Cb.Gl.E) := by
    rw [e2, Int.cast_natCast]
  have e4 : ((keyVec (scl := sclOf S) (dimOf S) (tbOf S) (cellsA S Z) c n : ℤ) : Cb.Gl.F) =
      (((FoNums.tauN x.fs c u : ℕ) : ℤ) : Cb.Gl.F) :=
    (CharP.intCast_eq_intCast Cb.Gl.F Cb.Gl.p).2
      ((CharP.intCast_eq_intCast Cb.Gl.E Cb.Gl.p).1 e3)
  rw [e4, Int.cast_natCast]
  exact er

end

end

#print axioms attCells_cast
#print axioms att_attRidden
#print axioms att_attKey

end VerifiableInference.Desc.First.Look
