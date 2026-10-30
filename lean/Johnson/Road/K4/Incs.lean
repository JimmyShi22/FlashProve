-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Incs.lean: THE TYPED CHAIN's INCOMING MASKS' FORM IS WHAT K4's START FORM MAKES OF
THE LEDGER's FACTORS AND THE MASK, at six of the seven sumchecks of a layers' sub-proof's own
rounds, at the library's value (`FullPar.own`; a sub-proof that is not the first). Statements and
proofs. They are meant as the premise hinc of `d2_of_public` (Johnson/Road/K4/OwnD2.lean): the typed
half of the condition (D2) on a sumcheck's own row. The twin, for the masks, of
Johnson/Road/K4/Claims.lean.

How each is stated. OwnD2.lean writes, for a form C, a ledger H, a mask row and a table of entries:
`maskSum H C mask` (over C's slots: coefficient, read, times H's factor under the slot, read, times
the mask's entry at the slot) and `entSum C entry`. Here `Y.inc st m = maskSum H C mask - entSum C
entry` at Y the stage's parameters and C the start form of K4's text.

  `maskWorld`, `zeroWorld`, `mask_less`: that difference is the form's value in the world whose
    slots hold factor times mask entry and whose entries are the negatives, less its value in the
    world of zeros. So the formulas for the forms' values, which hold in every world, can be used.
  `hinc1` (the sums of squares) · `hinc2` (the products of the rows) · `hinc3` (the terms) ·
  `hinc5` (the gated products) · `hinc6` (the routed experts' gated products) · `hinc7` (the merge).

Limits. EVERY TIE BETWEEN A PART OF THE TYPED STATE, OR AN ENTRY OF m, AND WHAT THE LEDGER HOLDS IS
A PREMISE: the points and powers (hp, hg, hr), that the typed factor is the reading of the ledger's
factor (hb), that the entry of m under the typed name is the mask's entry at K4's slot (hm; in
`hinc1`, `hinc2`, `hinc3`: times the factor). Sizes are premises too. The batched sumcheck's form
(the fourth) is not here. Equations alone: nothing on soundness or on what a mask hides.

-/
import Johnson.Road.K4.OwnD2
import Johnson.Road.K4.IncTyped
import Johnson.Road.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay aff0 normsStart)
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)
open OnBytes.Desc.First.P1 (gl)
open OnBytes.Slice (GE)

/-! ### The difference as a difference of two values -/

/-- The world whose slots hold the ledger's factor, read, times the mask's entry, and whose entries
are the negatives of the table's. -/
def maskWorld (H : Fork) (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) : World GE :=
  ⟨fun j => gl.val (H.mf.getD j zeroE) * mask j, fun a b c => -entry a b c⟩

/-- The world of zeros. -/
def zeroWorld : World GE := ⟨fun _ => 0, fun _ _ _ => 0⟩

theorem mask_less (H : Fork) (C : Aff) (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) :
    maskSum H C mask - entSum C entry =
      C.value gl (maskWorld H mask entry) - C.value gl zeroWorld := by
  have e1 : ∀ l : List Ent, (l.map (Ent.value gl (maskWorld H mask entry))).sum =
      -(l.map fun x => gl.val x.coef * entry x.tree x.row x.idx).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      simp only [Ent.value, maskWorld]
      ring
  have e2 : (C.ents.toList.map (Ent.value gl zeroWorld)).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      simp [Ent.value, zeroWorld]
  have e3 : (C.slots.toList.map (slotValue gl zeroWorld)).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      simp [slotValue, zeroWorld]
  have e4 : (C.slots.toList.map (slotValue gl (maskWorld H mask entry))).sum =
      maskSum H C mask := rfl
  unfold Aff.value
  rw [e1, e2, e3, e4]
  unfold entSum
  ring

/-! ### The six forms -/

variable [scl : Scl] {M X : Type} (P : FullPar GE M X) (H : Fork) (mask : ℕ → GE)
  (entry : ℕ → ℕ → ℕ → GE)

/-- **The sums of squares.** -/
theorem hinc1 (st : P.nr.sq.St1 × (Fin (P.D.lL + 1) → GE)) (m : P.J → GE) {yl : Lay} {sW : ℕ}
    {gp rhoI PV : Array E} (hNI : yl.NI = P.D.nNu) (hNS : ledNS yl.h.xl = 9)
    (hlPd : yl.lPd = lDd P.D) (hhalf : gl.val (invE (ofNat 2)) * 2 = 1)
    (hz : rhoI.size = P.D.lL + 1)
    (hp : ∀ j : Fin (P.D.lL + 1), st.2 j = gl.val (rhoI.getD j.val zeroE))
    (hg : ∀ s : Fin 9, gl.val (gp.getD s.val zeroE) = st.1.2 ^ s.val)
    (hm : ∀ (i : Fin P.D.nNu) (s : Fin 9), m (P.nr.sq.mkS i s) =
      gl.val (H.mf.getD (sW + 9 * i.val + s.val) zeroE) * mask (sW + 9 * i.val + s.val)) :
    P.own.toOwn.tail.s1.L.T.par.inc st m =
      maskSum H (normsStart yl sW gp rhoI PV).1 mask -
        entSum (normsStart yl sW gp rhoI PV).1 entry := by
  have hh : gl.val (invE (ofNat 2)) = (2⁻¹ : GE) := eq_inv_of_mul_eq_one_left hhalf
  have hn : P.D.nNu ≤ 2 ^ (P.D.lL + 1) := by
    unfold Inst.Model.FFSeg.Dim.nNu Inst.Model.FFSeg.Dim.nl
    rw [pow_succ, Nat.mul_comm]
  have z0 : (normsStart yl sW gp rhoI PV).1.value gl zeroWorld = 0 := by
    rw [normsStart_value gl zeroWorld]
    simp [zeroWorld]
  rw [inc1, mask_less, z0, sub_zero, normsStart_value gl (maskWorld H mask entry), hNI, hNS,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [gl.pow, hh, hlPd, eqTab_nat gl rhoI hz st.2 hp i.val (lt_of_lt_of_le i.isLt hn), hg s,
    hm i s]
  show _ = _ * (gl.val (H.mf.getD (sW + 9 * i.val + s.val) zeroE) * mask (sW + 9 * i.val + s.val))
  ring

/-- **The products of the rows.** -/
theorem hinc2 (st : P.own.toOwn.tail.s2.L.T.par.St) (m : P.J → GE) {j : ℕ}
    (hm : m P.nr.rows.rJ = gl.val (H.mf.getD j zeroE) * mask j) :
    P.own.toOwn.tail.s2.L.T.par.inc st m =
      maskSum H (Aff.slot j) mask - entSum (Aff.slot j) entry := by
  rw [inc2, maskSum_slot, entSum_slot, sub_zero, hm]

/-- **The terms.** -/
theorem hinc3 (st : P.own.toOwn.tail.s3.L.T.par.St) (m : P.J → GE) {j : ℕ}
    (hm : m P.rT = gl.val (H.mf.getD j zeroE) * mask j) :
    P.own.toOwn.tail.s3.L.T.par.inc st m =
      maskSum H (Aff.slot j) mask - entSum (Aff.slot j) entry := by
  rw [inc3, maskSum_slot, entSum_slot, sub_zero, hm]

/-- **The gated products.** -/
theorem hinc5 (st : St5 GE P.D) (m : P.J → GE) {sH1 : ℕ}
    (hb : st.be = gl.val (H.mf.getD sH1 zeroE)) (hm : m (P.cI (.inl (aH1 P.D))) = mask sH1) :
    P.own.toOwn.tail.s5.L.T.par.inc st m =
      maskSum H (Aff.slot sH1) mask - entSum (Aff.slot sH1) entry := by
  rw [inc5, maskSum_slot, entSum_slot, sub_zero, hb, hm]

/-- **The routed experts' gated products.** -/
theorem hinc6 (st : St6 GE P.D × (Fin (P.D.lL - 1) → GE)) (m : P.J → GE) {LamM sH1 : ℕ}
    {rhoM : Array E} (hL : LamM = P.D.ne) (hz : rhoM.size = P.D.lL - 1)
    (hp : ∀ j : Fin (P.D.lL - 1), st.2 j = gl.val (rhoM.getD j.val zeroE))
    (hb : ∀ i : Fin P.D.ne, st.1.be = gl.val (H.mf.getD (sH1 + 1 + i.val) zeroE))
    (hm : ∀ i : Fin P.D.ne, m (P.cI (.inl (aH2 P.D i))) = mask (sH1 + 1 + i.val)) :
    P.own.toOwn.tail.s6.L.T.par.inc st m =
      maskSum H ((List.range LamM).foldl
        (fun (C : Aff) lm => C.addMul (Aff.slot (sH1 + 1 + lm)) ((eqTab rhoM).getD lm zeroE))
        aff0) mask -
      entSum ((List.range LamM).foldl
        (fun (C : Aff) lm => C.addMul (Aff.slot (sH1 + 1 + lm)) ((eqTab rhoM).getD lm zeroE))
        aff0) entry := by
  have hn : P.D.ne ≤ 2 ^ (P.D.lL - 1) := P.fp.rt.hn
  have v : ∀ W : World GE, ((List.range LamM).foldl
      (fun (C : Aff) lm => C.addMul (Aff.slot (sH1 + 1 + lm)) ((eqTab rhoM).getD lm zeroE))
      aff0).value gl W =
      ∑ i : Fin P.D.ne, gl.val ((eqTab rhoM).getD i.val zeroE) * W.slot (sH1 + 1 + i.val) := by
    intro W
    rw [foldAdds_value gl W _
      (fun lm => gl.val ((eqTab rhoM).getD lm zeroE) * W.slot (sH1 + 1 + lm))
      (fun a lm => by rw [Aff.value_addMul, Aff.value_slot]), aff0_value, zero_add,
      list_range_sumM, hL, Finset.sum_range]
  rw [inc6, mask_less, v, v]
  have z0 : ∑ i : Fin P.D.ne, gl.val ((eqTab rhoM).getD i.val zeroE) *
      zeroWorld.slot (sH1 + 1 + i.val) = 0 := by simp [zeroWorld]
  rw [z0, sub_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eqTab_nat gl rhoM hz st.2 hp i.val (lt_of_lt_of_le i.isLt hn), hb i, hm i]
  rfl

/-- **The merge.** -/
theorem hinc7 (st : P.wp0.wt.St × GE) (m : P.J → GE) {sv : Array Nat} {rho : Array E}
    (hn : sv.size = P.nW) (hr : ∀ a : Fin P.nW, gl.val (rho.getD a.val zeroE) = st.2 ^ a.val)
    (hb : ∀ a : Fin P.nW, P.wp0.wt.be a st.1 = gl.val (H.mf.getD (sv.getD a.val 0) zeroE))
    (hm : ∀ a : Fin P.nW, m (P.wp0.wt.nm a) = mask (sv.getD a.val 0)) :
    P.own.toOwn.tail.s7.L.T.par.inc st m =
      maskSum H (wsForkStart sv rho) mask - entSum (wsForkStart sv rho) entry := by
  have z0 : (wsForkStart sv rho).value gl zeroWorld = 0 := by
    rw [forkStart_value]
    simp [zeroWorld]
  rw [inc7, mask_less, z0, sub_zero, forkStart_value, hn, Finset.sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hr a, hb a, hm a]
  show _ = _ * (gl.val (H.mf.getD (sv.getD a.val 0) zeroE) * mask (sv.getD a.val 0))
  ring

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.mask_less
#print axioms OnBytes.Road.K4.hinc1
#print axioms OnBytes.Road.K4.hinc2
#print axioms OnBytes.Road.K4.hinc3
#print axioms OnBytes.Road.K4.hinc5
#print axioms OnBytes.Road.K4.hinc6
#print axioms OnBytes.Road.K4.hinc7
