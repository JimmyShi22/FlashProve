-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LibIdn.lean: TWO OF THE FIVE CLAUSES ON THE OUTPUT HEAD FROM WHICH THE GOALS' "Means" FOLLOWS (means_of_fifteen, Johnson/Goal/Meaning/MeansParts.lean; Policy.HeadCl, Johnson/Road/Lane5SplitH.lean's HeadR0): THE 17 IDENTITIES OF THE FINAL NORMALISATION (Inst.Model.Head.N.idn) AT EVERY POSITION AND THE LEDGER's TWO SUMS (sB2, sB3), OVER THE BASE FIELD, AT THE LIBRARY's RECORD MADE OF OUR
CELLS (Law/LibJoinNorm.lean: cellsN c): FROM K6's FILES' "idn" ALONE (Law/IdnPlain.lean: IdnPlain, which Law/RowFront.lean's FrontIdn gives, which K6's law closes): what ONE item of the table closes, not the whole relation on cells: STATED AND PROVED.
  baseZero       an integer whose image in our field is 0 has the image 0 in the base field.
  lib_idn · lib_sB2 · lib_sB3 · lib_of_plain : Same Y → d = 5120 → IdnPlain sz pol rq c → the 17 ∧ sB2 = 0 ∧ sB3 = 0.
THE ARITHMETIC IS NOT THIS FILE's: every identity between the library's expressions and ours is CALLED from Law/LibJoin.lean | Law/LibJoinNorm.lean, which are ported whole from texts of this project that are not in this repository, as their heads say.
WHAT IT DOES NOT SAY. The three other clauses (SmallH · dB4 | dZ: Law/LibRider.lean · the keys: Law/LibWhole.lean, from the whole relations). Same Y (T = 1024; Y's two positions and policy are ours) and d = 5120 ARE PREMISES (Law/LibAtSeat.lean pays Same at the seat's letters). That cellsN c is what the committed integers of segment 24 spell (Hd.cellsH … = cellsN c) is the reading of the
witness's duty (Law/K6Own.lean's rd6, a letter still). FULL SIZE ALONE. One way alone. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.LibJoinNorm
import Johnson.Desc.Kinds.Law.IdnPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Inst.Model.Head (Req nT nD sB2 sB3)
open VerifiableInference.Desc.Kinds.HeadJoin (Same cellsN)
open Norm (lt ls d lPd S2 T)

/-- An integer whose image in our field is 0 has the image 0 in the base field. -/
theorem baseZero {z : Int} (h : ((z : Int) : K) = 0) : ((z : Int) : Cb.Gl.F) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd z Code.pGold).2
    ((CharP.intCast_eq_zero_iff K Code.pGold z).1 h)

variable [Sizes] [Policy] [Request] {c : NCells} {Y : Req}

/-- **The 17 identities of the final normalisation, in the library's own words, over the base field.** -/
theorem lib_idn (hT : T = 1024) (hd : d = 5120)
    (h : ∀ i, i < T → ∀ v, v ∈ rowsAt c (bits lt i) → v = 0) :
    ∀ i < nT, ∀ k < 17, Inst.Model.Head.N.idn npOf ((cellsN c).cast Cb.Gl.F) i k = 0 := by
  intro i hi k _
  have hi' : i < T := by rw [hT]; exact hi
  haveI : Token := ⟨0⟩
  have hm := idn_modEq (c := c) (t := i) hi' (h i hi') k
  have e : Inst.Model.Head.N.idn npOf (cellsN c) i k
      = Inst.Model.Ledger.idn npOf (Inst.Model.Ledger.Wsum d (limbZ c i)) (digZ c i) k := by
    unfold Inst.Model.Head.N.idn
    rw [HeadJoin.Dv_eq, show (fun l j => Inst.Model.Head.bl (cellsN c) l j i) = limbZ c i from
      funext fun l => funext fun j => HeadJoin.bl_eq hd l j i, hd]
    rfl
  have hz : ((Inst.Model.Head.N.idn npOf (cellsN c) i k : Int) : Cb.Gl.F) = 0 := by
    rw [e]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ Code.pGold).2 (Int.modEq_zero_iff_dvd.1 hm)
  exact (Inst.Model.Head.N.map_idn' (Int.castRingHom Cb.Gl.F) npOf (cellsN c) i k).symm.trans hz

/-- (B2). -/
theorem lib_sB2 (S : Same Y)
    (h : ((((Finset.range T).sum (fun i =>
      if costed i = true then numZ c.toCells .paid i + (C : Int) * numZ c.toCells .over i
        + numZ c.toCells .slackMean i
      else 0) - (theta : Int) * (RC : Int) : Int) : K) = 0)) :
    sB2 ((cellsN c).cast Cb.Gl.F) Y = 0 := by
  refine (Inst.Model.Head.map_sB2 (Int.castRingHom Cb.Gl.F) (cellsN c) Y).symm.trans ?_
  rw [show sB2 (cellsN c) Y = _ from HeadJoin.sB2_int (c := c.toCells) (X := c.stream) S]
  exact baseZero h

/-- (B3). -/
theorem lib_sB3 (S : Same Y)
    (h : ((((Finset.range T).sum (fun i =>
      if costed i = true then numZ c.toCells .over i + numZ c.toCells .slackCap i else 0)
        - ((if RC > 0 then cap else 0 : Nat) : Int) : Int) : K) = 0)) :
    sB3 ((cellsN c).cast Cb.Gl.F) Y = 0 := by
  refine (Inst.Model.Head.map_sB3 (Int.castRingHom Cb.Gl.F) (cellsN c) Y).symm.trans ?_
  rw [show sB3 (cellsN c) Y = _ from HeadJoin.sB3_int (c := c.toCells) (X := c.stream) S]
  exact baseZero h

/-- **FROM OUR "idn" TO THE LIBRARY's TWO CLAUSES.** -/
theorem lib_of_plain (S : Same Y) (hd : d = 5120) (h : IdnPlain ‹Sizes› ‹Policy› ‹Request› c) :
    (∀ i < nT, ∀ k < 17, Inst.Model.Head.N.idn npOf ((cellsN c).cast Cb.Gl.F) i k = 0) ∧
      (sB2 ((cellsN c).cast Cb.Gl.F) Y = 0 ∧ sB3 ((cellsN c).cast Cb.Gl.F) Y = 0) :=
  ⟨lib_idn S.T hd h.1, lib_sB2 S h.2.1, lib_sB3 S h.2.2⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.lib_idn
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.lib_of_plain
