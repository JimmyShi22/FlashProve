-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/Back/IdnOfHeadCl.lean: FROM THREE CLAUSES OF THE LIBRARY's RELATION ON
THE OUTPUT HEAD (`Policy.HeadCl`: the 17 identities of the final normalisation, the ledger's two
lines at every position, its two sums), over the base field, at the library's cells made of ours
(`cellsN c`), BACK TO TWO PARTS OF THE HEAD's RELATION ON CELLS: "idn" (`IdnPlain`,
Law/IdnPlain.lean) and the rider (`clipAt` and `tableAt` are 0 at every position's corner). The
converses of `lib_of_plain` (Law/LibIdn.lean) and `lib_lines` (Law/LibRider.lean). Statements with
their proofs. Over the library alone.

What it is not. Nothing says that the library's relation holds at any cells: the statements are
CONDITIONAL on it, on "the letters are the library's" (`Same`), on d = 5120, and for the rider on
the tests on the plan and `Wide`. The keys (the part lookCalls) are not here. No bound on a cell is
used, and no equation over the integers is claimed: both sides say that the field's prime divides an
integer. The full size alone. No chance in it. Nothing on soundness, completeness or hiding.

  `upZero`                an integer whose image in the base field is 0 has the image 0 in our field
  `rows_of_idn`           the 17 identities at every position give that the 17 forms are 0 as words
  `plain_sB2`, `plain_sB3`   the two sums, as integers read in our field
  `clip_of_dB4`, `table_of_dZ`   the two lines at every position give that the two corner values
                          are 0
  `idnPlain_of_headCl`, `rider_of_headCl`   the two statements

How. `upZero` is two of Mathlib's equivalences; all else is calls. What ties the library's
expressions to integers, and these to ours, are the equations that the two forward files call, read
the other way: a ring homomorphism commutes with the library's expressions (`map_idn'`, `map_sB2`,
`map_sB3`, `map_dB4`, `map_dZ`); the library's integer is ours (`sB2_int`, `sB3_int`, `dB4_int`,
`dZ_int`, `Dv_eq`, `bl_eq`); the two corner values are read as the images of these integers
(`rd_clip`, `rd_table`). How the 17 forms are read (`rd_rowsAt`, `ext_corner`, `vecK_eq_cast`), and
that a canonical word which is read as 0 is the word 0 (`eq_of_rd`, `zero_of_rd`, with `okE_rowsAt`,
`okE_clipAt`, `okE_tableAt`), are called as Law/NormHonest.lean and Law/HeadPartsAtX.lean call them,
the same way round.

Words. "Our field": the library's extension field K (`Cb.Gl.E`), in which the program's words are
read (`rd`). (B2), (B3), (B4), (Z): the library's labels for `sB2`, `sB3`, `dB4`, `dZ`
(Inst.Model.Head).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.LibParts
import Johnson.Desc.Kinds.Law.LibIdn
import Johnson.Desc.Kinds.Law.LibRider
import Johnson.Desc.Kinds.Law.HeadPartsAtX
import Johnson.Desc.Kinds.Law.NormHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (AcceptancePolicy Mat Instance ppref)
open Inst.Model.Head (Req nT sB2 sB3 dB4 dZ)
open VerifiableInference.Desc.Kinds.HeadJoin (Same Wide More cellsN)
open Norm (lt ls d S2 T)

/-- An integer whose image in the base field is 0 has the image 0 in our field: baseZero
(Law/LibIdn.lean) the other way, by the other halves of the same two equivalences. -/
theorem upZero {z : Int} (h : ((z : Int) : Cb.Gl.F) = 0) : ((z : Int) : K) = 0 :=
  (CharP.intCast_eq_zero_iff K Code.pGold z).2
    ((ZMod.intCast_zmod_eq_zero_iff_dvd z Code.pGold).1 h)

section Idn
variable [Sizes] [Policy] [Request] {c : NCells} {Y : Req}

/-- **The 17 identities over the base field give the 17 forms' being 0, as words, at every
position's corner.** -/
theorem rows_of_idn (hT : T = 1024) (hd : d = 5120)
    (h : ∀ i < nT, ∀ k < 17, Inst.Model.Head.N.idn npOf ((cellsN c).cast Cb.Gl.F) i k = 0) :
    ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0 := by
  intro t ht v hv
  -- lemmas called below take a token as an instance; the statement has none
  haveI : Token := ⟨0⟩
  have ht' : t < nT := by
    have h1 := ht
    rw [hT] at h1
    exact h1
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
  have hk' : k < 17 := by rw [rowsAt_length] at hk; exact hk
  -- the library's integer is ours: the text of lib_idn's own step (Law/LibIdn.lean)
  have e : Inst.Model.Head.N.idn npOf (cellsN c) t k
      = Inst.Model.Ledger.idn npOf (Inst.Model.Ledger.Wsum d (limbZ c t)) (digZ c t) k := by
    unfold Inst.Model.Head.N.idn
    rw [HeadJoin.Dv_eq, show (fun l j => Inst.Model.Head.bl (cellsN c) l j t) = limbZ c t from
      funext fun l => funext fun j => HeadJoin.bl_eq hd l j t, hd]
    rfl
  have hz : ((Inst.Model.Head.N.idn npOf (cellsN c) t k : Int) : Cb.Gl.F) = 0 :=
    (Inst.Model.Head.N.map_idn' (Int.castRingHom Cb.Gl.F) npOf (cellsN c) t k).trans
      (h t ht' k hk')
  rw [e] at hz
  apply eq_of_rd (okE_rowsAt c _ hv) okE_zero
  have e2 := rd_rowsAt c (bits lt t) (size_bits lt t) hk'
  rw [List.getD_eq_getElem _ _ hk, ext_corner ht, vecK_eq_cast] at e2
  rw [e2, rd_zero]
  exact upZero hz

/-- (B2), as an integer read in our field. -/
theorem plain_sB2 (S : Same Y) (h : sB2 ((cellsN c).cast Cb.Gl.F) Y = 0) :
    ((((Finset.range T).sum (fun i =>
      if costed i = true then numZ c.toCells .paid i + (C : Int) * numZ c.toCells .over i
        + numZ c.toCells .slackMean i
      else 0) - (theta : Int) * (RC : Int) : Int) : K) = 0) := by
  have h1 : ((sB2 (cellsN c) Y : Int) : Cb.Gl.F) = 0 :=
    (Inst.Model.Head.map_sB2 (Int.castRingHom Cb.Gl.F) (cellsN c) Y).trans h
  rw [show sB2 (cellsN c) Y = _ from HeadJoin.sB2_int (c := c.toCells) (X := c.stream) S] at h1
  exact upZero h1

/-- (B3), as an integer read in our field. -/
theorem plain_sB3 (S : Same Y) (h : sB3 ((cellsN c).cast Cb.Gl.F) Y = 0) :
    ((((Finset.range T).sum (fun i =>
      if costed i = true then numZ c.toCells .over i + numZ c.toCells .slackCap i else 0)
        - ((if RC > 0 then cap else 0 : Nat) : Int) : Int) : K) = 0) := by
  have h1 : ((sB3 (cellsN c) Y : Int) : Cb.Gl.F) = 0 :=
    (Inst.Model.Head.map_sB3 (Int.castRingHom Cb.Gl.F) (cellsN c) Y).trans h
  rw [show sB3 (cellsN c) Y = _ from HeadJoin.sB3_int (c := c.toCells) (X := c.stream) S] at h1
  exact upZero h1

end Idn

section Rider
variable [Sizes] [Policy] [Request] [Token] {c : NCells} {Y : Req}

/-- (B4) at every position gives the clip's corner value 0 at every position. -/
theorem clip_of_dB4 (S : Same Y) (h : ∀ i < nT, dB4 ((cellsN c).cast Cb.Gl.F) Y i = 0) :
    ∀ t, t < T → clipAt c.toCells (corner 0 t) = 0 := by
  intro t ht
  have ht' : t < nT := by
    have h0 := ht
    rw [S.T] at h0
    exact h0
  have h1 : ((dB4 (cellsN c) Y t : Int) : Cb.Gl.F) = 0 :=
    (Inst.Model.Head.map_dB4 (Int.castRingHom Cb.Gl.F) (cellsN c) Y t).trans (h t ht')
  rw [show dB4 (cellsN c) Y t = _ from
    HeadJoin.dB4_int (c := c.toCells) (X := c.stream) S t] at h1
  apply zero_of_rd (okE_clipAt _ _)
  rw [rd_clip ht]
  by_cases hc : costed t = true
  · rw [if_pos hc] at h1 ⊢
    exact upZero h1
  · rw [if_neg hc]

/-- (Z) at every position gives the table's corner value 0 at every position. -/
theorem table_of_dZ (S : Same Y) (Wd : Wide) (P : PlanFacts)
    (h : ∀ i < nT, dZ ((cellsN c).cast Cb.Gl.F) Y i = 0) :
    ∀ t, t < T → tableAt c.toCells (corner 0 t) = 0 := by
  intro t ht
  have ht' : t < nT := by
    have h0 := ht
    rw [S.T] at h0
    exact h0
  have h1 : ((dZ (cellsN c) Y t : Int) : Cb.Gl.F) = 0 :=
    (Inst.Model.Head.map_dZ (Int.castRingHom Cb.Gl.F) (cellsN c) Y t).trans (h t ht')
  rw [show dZ (cellsN c) Y t = _ from
    HeadJoin.dZ_int (c := c.toCells) (X := c.stream) S Wd t] at h1
  apply zero_of_rd (okE_tableAt _ _)
  rw [rd_table P ht]
  by_cases hc : costed t = true
  · rw [if_pos hc] at h1 ⊢
    exact upZero h1
  · rw [if_neg hc]

end Rider

/-- **FROM THE LIBRARY's 17 IDENTITIES AND TWO SUMS BACK TO "idn".** CONDITIONAL: the letters are
the library's; d = 5120; the library's relation. -/
theorem idnPlain_of_headCl [sz : Sizes] [po : Policy] [rq : Request] (c : NCells) (pol : AcceptancePolicy)
    (Wz : Mat) (x : Instance ppref) (S : Same (Inst.Model.Head.Req.of pol x)) (hd : d = 5120)
    (H : _root_.Policy.HeadCl npOf pol Wz x (cellsN c)) : IdnPlain sz po rq c := by
  obtain ⟨_, hI, _, h2, h3⟩ := H
  exact ⟨rows_of_idn S.T hd hI, plain_sB2 S h2, plain_sB3 S h3⟩

/-- **FROM THE LEDGER's TWO LINES BACK TO THE RIDER.** CONDITIONAL: the tests on the plan; the
letters are the library's; the library's relation. -/
theorem rider_of_headCl [Sizes] [Policy] [Request] [Token] (sT : Nat) (c : NCells) (pol : AcceptancePolicy)
    (Wz : Mat) (x : Instance ppref) (hplan : planOk sT = true)
    (S : Same (Inst.Model.Head.Req.of pol x)) (Wd : Wide)
    (H : _root_.Policy.HeadCl npOf pol Wz x (cellsN c)) :
    ∀ t, t < T → clipAt c.toCells (corner 0 t) = 0 ∧ tableAt c.toCells (corner 0 t) = 0 := by
  obtain ⟨_, _, hJ, _⟩ := H
  have P : PlanFacts := planFacts (sT := sT) hplan
  exact fun t ht => ⟨clip_of_dB4 S (fun i hi => (hJ i hi).1) t ht,
    table_of_dZ S Wd P (fun i hi => (hJ i hi).2) t ht⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.upZero
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rows_of_idn
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.plain_sB2
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.plain_sB3
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.clip_of_dB4
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.table_of_dZ
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.idnPlain_of_headCl
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rider_of_headCl
