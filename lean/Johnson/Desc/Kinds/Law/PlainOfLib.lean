-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlainOfLib.lean: FROM TWO OF THE LIBRARY'S CLAUSES ON THE OUTPUT HEAD BACK
TO THE PART "idn" OF THE SUB-PROTOCOL'S OWN RELATION ON CELLS: the 17 identities of
the final normalisation and the two sums sB2, sB3, over the base field, at the cells `cellsN c`
(Johnson/Desc/Kinds/Law/LibJoinNorm.lean), give `IdnPlain` (Johnson/Desc/Kinds/Law/IdnPlain.lean) at
c. THE CONVERSE OF `lib_of_plain` (Johnson/Desc/Kinds/Law/LibIdn.lean), which says of itself "One
way alone". A lemma on cells: it reads nothing of the honest prover's definitions.

  `fieldZero`        an integer whose image in the base field is 0 has the image 0 in the extension
                     field. No side condition: `baseZero` (Law/LibIdn.lean) the other way round
  `rows_of_lib`      at every position's corner the row's 17 forms are 0. CONDITIONAL: hT (1,024
                     positions) · hd (5,120 features) · h (the library's 17 identities)
  `plainB2_of_lib`, `plainB3_of_lib`   the two plain sums. CONDITIONAL: S (the request and the
                     policy are the library's: `Same`) · h (sB2, sB3 are 0)
  `plain_of_lib`     THE CONVERSE. CONDITIONAL: S · hd · h17 · h2 · h3: to the letter what
                     `lib_of_plain` ends in

WHAT "0" IS. IN THE TWO SUMS: 0 MODULO THE FIELD'S PRIME: an integer's image in the field.
`IdnPlain` says no more than that either. That the sums are 0 as integers, so that the policy's mean
and cap hold of the numbers themselves, wants ranges on the cells, which this file neither asks nor
gives.

How. No arithmetic is typed here. Every step of the proofs in Law/LibIdn.lean but one is an equation
or an "if and only if": these are read the other way (`N.map_idn'`, `map_sB2`, `map_sB3`,
`HeadJoin.Dv_eq`, `HeadJoin.bl_eq`, `HeadJoin.sB2_int`, `HeadJoin.sB3_int`). The one that is not
(`idn_modEq`) is not wanted: the way from the integers to the rows is the proof of the field rows in
`cellRelN_of_int` (Johnson/Desc/Kinds/Law/NormHonest.lean), line by line, with "0 in the integers"
weakened to "the image in the field is 0".

Limits. THE FULL SIZE ALONE (1,024 positions through `Same`; 5,120 features). The three other
clauses on the head from which the library's meaning follows are not touched. That the premises hold
of any cells is not shown here; they hold wherever `IdnPlain` does (`lib_of_plain`). No chance in
it. Nothing on any property.
-/
import Johnson.Desc.Kinds.Law.LibIdn
import Johnson.Desc.Kinds.Law.NormHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Inst.Model.Head (Req nT nD sB2 sB3)
open VerifiableInference.Desc.Kinds.HeadJoin (Same cellsN)
open Norm (lt ls d lPd S2 T)

/-- An integer whose image in the base field is 0 has the image 0 in the extension field. -/
theorem fieldZero {z : Int} (h : ((z : Int) : Cb.Gl.F) = 0) : ((z : Int) : K) = 0 :=
  (CharP.intCast_eq_zero_iff K Code.pGold z).2
    ((ZMod.intCast_zmod_eq_zero_iff_dvd z Code.pGold).1 h)

variable [Sizes] [Policy] [Request] {c : NCells} {Y : Req}

/-- **The row's 17 forms are 0 at every position's corner**, from the library's 17 identities over
the base field. CONDITIONAL: hT, hd: the full size; h: the identities. -/
theorem rows_of_lib (hT : T = 1024) (hd : d = 5120)
    (h : ∀ i < nT, ∀ k < 17, Inst.Model.Head.N.idn npOf ((cellsN c).cast Cb.Gl.F) i k = 0) :
    ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0 := by
  intro t ht v hv
  haveI : Token := ⟨0⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
  have hk' : k < 17 := by rw [rowsAt_length] at hk; exact hk
  have hi : t < nT := by rw [hT] at ht; exact ht
  have e0 : Inst.Model.Head.N.idn npOf (cellsN c) t k
      = Inst.Model.Ledger.idn npOf (Inst.Model.Ledger.Wsum d (limbZ c t)) (digZ c t) k := by
    unfold Inst.Model.Head.N.idn
    rw [HeadJoin.Dv_eq, show (fun l j => Inst.Model.Head.bl (cellsN c) l j t) = limbZ c t from
      funext fun l => funext fun j => HeadJoin.bl_eq hd l j t, hd]
    rfl
  have hF : ((Inst.Model.Head.N.idn npOf (cellsN c) t k : Int) : Cb.Gl.F) = 0 :=
    (Inst.Model.Head.N.map_idn' (Int.castRingHom Cb.Gl.F) npOf (cellsN c) t k).trans
      (h t hi k hk')
  rw [e0] at hF
  have hz := fieldZero hF
  apply eq_of_rd (okE_rowsAt c _ hv) okE_zero
  have e := rd_rowsAt c (bits lt t) (size_bits lt t) hk'
  rw [List.getD_eq_getElem _ _ hk, ext_corner ht, vecK_eq_cast, hz] at e
  rw [e, rd_zero]

/-- (B2), back. The sum is 0 modulo the field's prime. CONDITIONAL: S; h. -/
theorem plainB2_of_lib (S : Same Y) (h : sB2 ((cellsN c).cast Cb.Gl.F) Y = 0) :
    ((((Finset.range T).sum (fun i =>
      if costed i = true then numZ c.toCells .paid i + (C : Int) * numZ c.toCells .over i
        + numZ c.toCells .slackMean i
      else 0) - (theta : Int) * (RC : Int) : Int) : K) = 0) := by
  have hF : ((sB2 (cellsN c) Y : Int) : Cb.Gl.F) = 0 :=
    (Inst.Model.Head.map_sB2 (Int.castRingHom Cb.Gl.F) (cellsN c) Y).trans h
  rw [show sB2 (cellsN c) Y = _ from HeadJoin.sB2_int (c := c.toCells) (X := c.stream) S] at hF
  exact fieldZero hF

/-- (B3), back. The sum is 0 modulo the field's prime. CONDITIONAL: S; h. -/
theorem plainB3_of_lib (S : Same Y) (h : sB3 ((cellsN c).cast Cb.Gl.F) Y = 0) :
    ((((Finset.range T).sum (fun i =>
      if costed i = true then numZ c.toCells .over i + numZ c.toCells .slackCap i else 0)
        - ((if RC > 0 then cap else 0 : Nat) : Int) : Int) : K) = 0) := by
  have hF : ((sB3 (cellsN c) Y : Int) : Cb.Gl.F) = 0 :=
    (Inst.Model.Head.map_sB3 (Int.castRingHom Cb.Gl.F) (cellsN c) Y).trans h
  rw [show sB3 (cellsN c) Y = _ from HeadJoin.sB3_int (c := c.toCells) (X := c.stream) S] at hF
  exact fieldZero hF

/-- **FROM THE LIBRARY'S TWO CLAUSES BACK TO THE SUB-PROTOCOL'S "idn".** The converse of
`lib_of_plain`. CONDITIONAL: S; hd; h17, h2, h3: what `lib_of_plain` ends in. -/
theorem plain_of_lib (S : Same Y) (hd : d = 5120)
    (h17 : ∀ i < nT, ∀ k < 17, Inst.Model.Head.N.idn npOf ((cellsN c).cast Cb.Gl.F) i k = 0)
    (h2 : sB2 ((cellsN c).cast Cb.Gl.F) Y = 0) (h3 : sB3 ((cellsN c).cast Cb.Gl.F) Y = 0) :
    IdnPlain ‹Sizes› ‹Policy› ‹Request› c :=
  ⟨rows_of_lib S.T hd h17, plainB2_of_lib S h2, plainB3_of_lib S h3⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.fieldZero
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rows_of_lib
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.plainB2_of_lib
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.plainB3_of_lib
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.plain_of_lib
