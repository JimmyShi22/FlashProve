-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/AtSlots.lean: the letters of the merge's record at a place, out of the numbers of the slots; and the two premises (D1), (D2) of the library's theorem on a sumcheck's row (SumSaid.row, OnBytes/Tie/Pv/Lay/SumSaid.lean) paid at them.

The record G (Caller.lean) leaves the names of the mask entries, the state and its reading as letters. Here they are filled from numbers that a plan gives (Nums):
    Jm   := the entries of the sub-proof's mask row (one for each slot) and the entries of the request's index-mask message
    nm a := the mask entry of the slot sv a, under which the value of claim a was sent
    wAt  := the mask entries of the sumcheck's own 2 lk + 2 slots, from the slot «first» on, in the order of OnBytes.Road.Hd.place (OnBytes/Tie/Pv/Psc/StepWalk.lean): OnBytes.Tie.Pv.slotP (OnBytes/Tie/Pv/SeamRun.lean)
    cAt  := entry c of the index-mask message
    St   := the claims as the program holds them, and the sub-proof's ledger (OnBytes.Model.Fork); rd reads the factors, sh a := what was shown under sv a, be a := the factor under sv a
Main theorems:
    tg_at          the record's target behind the draw is the ledger's public part of the program's start form (wsForkStart), read
    D1_at, D2_at   the premises (D1) and (D2), in the spelling L.toSum.T.par of Cb/Pv/Lay/OwnParts.lean, in every world that gives the own slots their mask entries (w1) and the claims' slots
                   «shown - factor * mask entry» (w2)
    zip_ofFn       two arrays, paired, as a list over Fin n: for the premise «recs». (For hr: OnBytes.Tie.Pv.Tail.Port.powers_val and powers_size, OnBytes/Tie/Pv/Tail/EndClaimsB.lean.)
    world_at       the world of a ledger (Fork.worldOf) is such a world, if the ledger holds 0 and -1 under the own slots and what the state's ledger holds under the claims' slots
BESIDE THIS FILE. OnBytes/Tie/Pv/SeamRun.lean has the slots' order (slotP, slotNo, place_slotNo) and (D1) for any sumcheck's parameters in the world of a ledger (hw_of, hid_of);
Johnson/Road/Rows/AttPortD.lean pays (D1) and (D2) for the attention's sumchecks in a world of its own. This file pays them at the merge's record G. D1_at is hid_of's like for any world with w1.
SPENT OF THE LIBRARY (theorems that this file's proofs call themselves; each speaks of plain records and pure functions alone): Cb.ldPartVars_degs (Cb/Part/LdPartVarsProofs.lean) ·
Cb.Pv.Lay.WeightsL.inc_sum (Cb/Pv/Lay/Weights.lean) · OnBytes.Tie.Pv.Lay.Proved.merge_target_start (OnBytes/Tie/Pv/Lay/MergeTarget.lean) · OnBytes.PscRun.value_public (OnBytes/Tie/Pv/Psc/PscForm.lean) ·
OnBytes.Tie.Pv.place_slotNo, slotNo_pIx (OnBytes/Tie/Pv/SeamRun.lean) · the fields of OnBytes.Model.Reading (OnBytes/Model/HideLaws.lean).
AND BY THE FIVE FILES BENEATH, WHOSE HEADS NAME ONLY THE MAIN ONES. Caller.lean: Alg.DegLE.add, const, const_mul, mono, mul, mul_const, sub, sum (Alg/Poly.lean), and the record's own field WeightsL.deg. Tie.lean: the fields of Reading. AtLay.lean:
OnBytes.Road.unitOK_of_layout (Johnson/Road/FormsKeysWLay.lean), the fields of OnBytes.Road.UnitOK. Prog.lean: Alg.bits_num, sum_num (Alg/Mle.lean) · OnBytes.Road.eqTab_value (Johnson/Road/FormsKeysEq.lean) ·
eqN_low_bits, foldl_mul_range, gamOf_size, shape_of_claim, table_at, table_size, toArray_getD, wsDigits_length, wsDigits_value, wsDot_value, wsEpsT_value, wsGamma_eq, wsOuter_getD, wsOuter_size
(Johnson/Road/FormsKeysFac.lean) · eqN_eqB, merge_sum, pending_gamma, wsEq1_value (Johnson/Road/FormsKeysMerge.lean) · le_two_pow_ceilLog2 (Johnson/Road/FormsKeysPlace.lean) · the fields of UnitOK and Reading.
Limits: that the numbers are a plan's is not said. That a run's ledger meets world_at's two premises is not shown here. The coefficients' readings (hr) are a premise. On hiding nothing.

-/
import Johnson.Top.H0.K11Caller.Tie
import Cb.Pv.Lay.OwnParts
import OnBytes.Tie.Pv.Lay.MergeTarget
import OnBytes.Tie.Pv.Psc.PscForm
import OnBytes.Tie.Pv.SeamRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K11Caller
open OnBytes
open OnBytes.Model (Reading World Fork Aff WsClaim wsForkStart)
open OnBytes.Tie.Pv (slotP slotNo place_slotNo slotNo_pIx)
open Cb Cb.Pv.Lay Finset

theorem slotP_bounds {E : Type} : ∀ (l : List (PFmt E)) (s : ℕ) (q : PIdx l), s ≤ slotP l s q ∧ slotP l s q < s + 1 + (l.map PFmt.n).sum
  | [], s, _ => by simp [slotP]
  | [f], s, Sum.inl t => by
    have := t.isLt
    simp only [slotP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | [f], s, Sum.inr _ => by
    simp only [slotP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | f :: f' :: l, s, Sum.inl t => by
    have := t.isLt
    simp only [slotP, List.map_cons, List.sum_cons]
    omega
  | f :: f' :: l, s, Sum.inr i => by
    have h := slotP_bounds (f' :: l) (s + f.n) i
    simp only [slotP, List.map_cons, List.sum_cons] at h ⊢
    omega

theorem fmt_sum (E : Type) [Field E] [Fintype E] (k : ℕ) : (((ldPartFmt E k fun _ => 2) ++ [pDummy E 1]).map PFmt.n).sum = 2 * k + 1 := by
  have h : ((ldPartFmt E k fun _ => 2) ++ [pDummy E 1]).map PFmt.n = List.replicate k 2 ++ [1] := by
    rw [List.map_append, ldPartVars_degs E]
    simp [List.ofFn_const]
    rfl
  rw [h]
  simp
  omega

/-- **The numbers of the slots at a place.** -/
structure Nums (P : Place) where
  /-- the number of the sub-proof's slots; of the entries of the index-mask message -/
  ns : ℕ
  ni : ℕ
  /-- the sumcheck's first slot -/
  first : ℕ
  /-- the slot of each claim's value -/
  sv : Fin P.n → ℕ
  /-- the entry of the index-mask message that masks the end value -/
  c : ℕ
  hsv : ∀ a, sv a < ns
  room : first + 2 * P.lay.lk + 2 ≤ ns
  hc : c < ni

/-- What the merge reads of the carried record: the claims and the ledger. -/
structure MergeIn (n : ℕ) where
  cl : Fin n → WsClaim
  F : Fork

section
variable {E' : Type} [Field E'] [Fintype E'] (ρ : Reading E')

/-- **The letters out of the numbers of the slots.** Rd stays a letter. -/
noncomputable def Letters.atSlots (P : Place) (N : Nums P) (Rd : MergeIn P.n → (P.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → E') → Prop) : Letters E' P where
  Jm := Fin N.ns ⊕ Fin N.ni
  St := MergeIn P.n
  rd := fun st => ⟨fun a => facsOf ρ (st.cl a), fun a => ρ.val (st.F.mf.getD (N.sv a) zeroE), fun a => ρ.val (st.F.vp.getD (N.sv a) zeroE)⟩
  nm := fun a => .inl ⟨N.sv a, N.hsv a⟩
  wAt := fun q => .inl ⟨slotP _ N.first q, by
    have h := (slotP_bounds _ N.first q).2
    rw [fmt_sum] at h
    have := N.room
    omega⟩
  cAt := .inr ⟨N.c, N.hc⟩
  Rd := Rd

variable {P : Place} (N : Nums P) (Rd : MergeIn P.n → (P.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → E') → Prop)

/-- The sub-proof's mask row, out of the entries. -/
def maskOf (m : P.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → E') (j : ℕ) : E' := if h : j < N.ns then m (.inr (.inl ⟨j, h⟩)) else 0

/-- The slots of the claims' values as the program's array. -/
def Nums.svA : Array ℕ := Array.ofFn N.sv

/-- The record at these letters. -/
noncomputable abbrev GS : WeightsL E' := G P (Letters.atSlots ρ P N Rd)

omit [Fintype E'] in
/-- The start form's value in a world, over the claims. -/
theorem start_value (W : World E') (rho : Array E) :
    (wsForkStart N.svA rho).value ρ W = ∑ a : Fin P.n, ρ.val (rho.getD a.val zeroE) * W.slot (N.sv a) := by
  rw [OnBytes.Tie.Pv.Lay.Proved.merge_target_start ρ W N.svA rho]
  have hs : N.svA.size = P.n := by simp [Nums.svA]
  rw [hs, ← Fin.sum_univ_eq_sum_range (fun i => ρ.val (rho.getD i zeroE) * W.slot (N.svA.getD i 0))]
  refine sum_congr rfl fun a _ => ?_
  have e : N.svA.getD a.val 0 = N.sv a := by simp [Nums.svA, Array.getD, a.isLt]
  rw [e]

theorem start_ents (sv : Array ℕ) (rho : Array E) : (wsForkStart sv rho).ents = #[] := by
  unfold wsForkStart
  rw [← Array.foldl_toList]
  have H : ∀ (l : List (ℕ × E)) (s : Aff), s.ents = #[] → (l.foldl (fun s y => Aff.addMul s (Aff.slot y.1) y.2) s).ents = #[] := by
    intro l
    induction l with
    | nil => exact fun s h => h
    | cons y l ih => exact fun s h => ih _ (by simp [Aff.addMul, Aff.slot, h])
  exact H _ _ rfl

/-- **The record's target is the ledger's public target, read.** -/
theorem tg_at (st : MergeIn P.n) (b : E') (rho : Array E) (T : E) (h : st.F.publicPart (wsForkStart N.svA rho) = some T)
    (hr : ∀ a : Fin P.n, ρ.val (rho.getD a.val zeroE) = b ^ (a : ℕ)) :
    (GS ρ N Rd).L.tg (st, b) = ρ.val T := by
  have h1 := OnBytes.PscRun.value_public ρ st.F _ T h (start_ents _ _) (fun _ => 0) (fun _ _ _ => 0)
  rw [start_value] at h1
  simp only [mul_zero, List.map_const', List.sum_replicate, smul_zero, sub_zero] at h1
  rw [← h1]
  show ∑ a : Fin P.n, b ^ (a : ℕ) * ρ.val (st.F.vp.getD (N.sv a) zeroE) = _
  refine sum_congr rfl fun a _ => ?_
  rw [hr a]
  simp [Fork.worldOf]

/-- Two arrays of n members, paired, as a list over Fin n. -/
theorem zip_ofFn {α β : Type} [Inhabited α] (a : Array α) (b : Array β) (d : β) (n : ℕ) (ha : a.size = n) (hb : b.size = n) :
    (a.zip b).toList = List.ofFn fun i : Fin n => (a.getD i.val default, b.getD i.val d) := by
  apply List.ext_getElem
  · simp [ha, hb]
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    simp [Array.getD, ha, hb]

/-- The two conditions on a world. -/
structure Fits2 (st : MergeIn P.n) (m : P.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → E') (W : World E') : Prop where
  /-- under each of the sumcheck's own slots lies its mask entry -/
  w1 : ∀ j, N.first ≤ j → j < N.first + 2 * P.lay.lk + 2 → W.slot j = maskOf N m j
  /-- under the slot of a claim's value lies what was shown less the factor times the mask entry -/
  w2 : ∀ a, W.slot (N.sv a) = ρ.val (st.F.vp.getD (N.sv a) zeroE) - ρ.val (st.F.mf.getD (N.sv a) zeroE) * maskOf N m (N.sv a)

/-- **(D1) at these letters.** -/
theorem D1_at (x : MergeIn P.n × E') (m : P.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → E') (W : World E') (F : Fits2 ρ N x.1 m W) :
    (GS ρ N Rd).L.toSum.T.par.W x m = OnBytes.Road.Hd.place W.slot ((GS ρ N Rd).L.toSum.T.par.vars x) N.first := by
  funext i
  rw [place_slotNo, slotNo_pIx]
  obtain ⟨h1, h2⟩ := slotP_bounds _ N.first (pIx (GS ρ N Rd).L.toSum.T.par.fmt ((GS ρ N Rd).L.toSum.T.par.dat x) i)
  have h3 : slotP _ N.first (pIx (GS ρ N Rd).L.toSum.T.par.fmt ((GS ρ N Rd).L.toSum.T.par.dat x) i) < N.first + 2 * P.lay.lk + 2 := by
    have e := fmt_sum E' P.lay.lk
    have h2' : slotP _ N.first (pIx (GS ρ N Rd).L.toSum.T.par.fmt ((GS ρ N Rd).L.toSum.T.par.dat x) i) <
        N.first + 1 + (((ldPartFmt E' P.lay.lk fun _ => 2) ++ [pDummy E' 1]).map PFmt.n).sum := h2
    rw [e] at h2'
    omega
  rw [F.w1 _ h1 h3]
  unfold maskOf
  rw [dif_pos (by have := N.room; omega)]
  rfl

/-- **(D2) at these letters.** -/
theorem D2_at (x : MergeIn P.n × E') (m : P.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → E') (W : World E') (F : Fits2 ρ N x.1 m W)
    (rho : Array E) (T : E) (h : x.1.F.publicPart (wsForkStart N.svA rho) = some T)
    (hr : ∀ a : Fin P.n, ρ.val (rho.getD a.val zeroE) = x.2 ^ (a : ℕ)) :
    (GS ρ N Rd).L.toSum.T.par.inc x m = ρ.val T - (wsForkStart N.svA rho).value ρ W := by
  rw [← tg_at ρ N Rd x.1 x.2 rho T h hr, start_value]
  show ∑ j, (GS ρ N Rd).L.inc x j * m j = _
  rw [(GS ρ N Rd).inc_sum x m]
  show _ = ∑ a : Fin P.n, x.2 ^ (a : ℕ) * ρ.val (x.1.F.vp.getD (N.sv a) zeroE) - _
  rw [← Finset.sum_sub_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [hr a, F.w2 a]
  have e : maskOf N m (N.sv a) = m (.inr (.inl ⟨N.sv a, N.hsv a⟩)) := by
    unfold maskOf
    rw [dif_pos (N.hsv a)]
  rw [e]
  show x.2 ^ (a : ℕ) * (m (.inr (.inl ⟨N.sv a, N.hsv a⟩)) * ρ.val (x.1.F.mf.getD (N.sv a) zeroE)) = _
  ring

omit [Fintype E'] in
/-- **The world of a ledger is such a world**, if the ledger Fl holds 0 and -1 under the sumcheck's own slots, and under the claims' slots what the state's ledger holds. -/
theorem world_at (st : MergeIn P.n) (m : P.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → E') (Fl : Fork) (entry : ℕ → ℕ → ℕ → E')
    (own : ∀ j, N.first ≤ j → j < N.first + 2 * P.lay.lk + 2 → Fl.vp.getD j zeroE = zeroE ∧ Fl.mf.getD j zeroE = subE zeroE oneE)
    (kept : ∀ a, Fl.vp.getD (N.sv a) zeroE = st.F.vp.getD (N.sv a) zeroE ∧ Fl.mf.getD (N.sv a) zeroE = st.F.mf.getD (N.sv a) zeroE) :
    Fits2 ρ N st m (Fl.worldOf ρ (maskOf N m) entry) where
  w1 := fun j h1 h2 => by
    obtain ⟨a, b⟩ := own j h1 h2
    show ρ.val (Fl.vp.getD j zeroE) - ρ.val (Fl.mf.getD j zeroE) * maskOf N m j = _
    rw [a, b, ρ.sub, ρ.zero, ρ.one]
    ring
  w2 := fun a => by
    obtain ⟨h1, h2⟩ := kept a
    show ρ.val (Fl.vp.getD (N.sv a) zeroE) - ρ.val (Fl.mf.getD (N.sv a) zeroE) * maskOf N m (N.sv a) = _
    rw [h1, h2]

end

end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.tg_at
#print axioms VerifiableInference.Desc.First.K11Caller.D1_at
#print axioms VerifiableInference.Desc.First.K11Caller.D2_at
#print axioms VerifiableInference.Desc.First.K11Caller.world_at
#print axioms VerifiableInference.Desc.First.K11Caller.zip_ofFn
