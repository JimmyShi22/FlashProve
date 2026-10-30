-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/PortZ.lean: the out-of-domain sample of a shape of the programs as a sample map of the
library, for one answer.

Definitions, statements and proofs. In Johnson/Pack/Port.lean the sample map of an oracle message is
a parameter. Here it is defined, after the block SEND of the verifier that is written after the
programs (OnBytes/Iop/Send.lean: `Send.cube`, `Send.pad`, `Send.front`, `Send.form`), for a shape
with one answer. The entries of a message stand on the corners of one cube; an entry that is no pad
has the weight eq(corner, z); the pad has a factor other than 0 times its basis element. That is the
library's row with a pad (`Sample.pad`, Cb/Gen/OodDecPad.lean).
Main names:
  `k1`, `k2`, `B1`, `B2`, `bitsZ`: the row bits, the tables' index bits and the cube's bits.
  `idxZ`: the corner of an entry: row + 2^(row bits) place inside its table, and the top bit for the
    mask table if there is a main table too. `idxZ_lt`, `idxZ_inj`: these numbers are below 2^bitsZ
    and different.
  `eachZ`, `padP`, `padNo`, `wZ`: the pad: the last place of the last mask row; without mask rows
    the last place of the last main row, or its last three places if the main rows are over the base
    field, with the weights 1, x, x² (`Cb.Gl.padW`).
  `portZ`: the sample map. `portZ_S`: it has one answer.
  `CaseE`, `portZ_ok`: if the shape has a mask row or main rows over the extension field, `portZ` is
    a zero-evader on all vectors (`Sample.OK`).
  `portOmZ`, `port_johnZ`: the oracle message with that sample map; it is below the Johnson radius
    (`OMsg.John`) from conditions on numbers alone.
Limits: one answer. That these numbers are those of `Send.cube` and `Send.pad` is stated in
Johnson/Pack/PortTie.lean; that the coefficients are those of `Send.form` is not stated in this file
(on `Send.form`'s side OnBytes/Slice/BlkSend.lean has `coefAt_form_one` and `tableW_eq_eqW`). Where
the row is too short for its pad `Send.pad` gives nothing, and `portZ` is defined all the same
(`PadFits`, Johnson/Pack/PortF.lean, is the condition). The case of no mask row and main rows over
the base field: Johnson/Pack/PortF.lean. The seed that the messages of one sending share:
Johnson/Pack/PortS.lean. Nothing on the honest prover or on hiding.
-/
import Johnson.Pack.Port
import Cb.Gl.GlSenders
import Cb.Gen.OodDecPadProofs
import Cb.Gen.OodDecSendProofs
import OnBytes.Slice.Corners
import OnBytes.Iop.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Cb.Ood Iop IOR Prob OnBytes.Slice

section
variable (cs : OnBytes.Codes) (s : OnBytes.OracleShape)

/-- The row bits and the index bits of the two tables. -/
def k1 : ℕ := OnBytes.ceilLog2 s.mainRows
def k2 : ℕ := OnBytes.ceilLog2 s.maskRows
def B1 : ℕ := k1 s + OnBytes.ceilLog2 (pMain cs s).ell
def B2 : ℕ := k2 s + OnBytes.ceilLog2 (pMask cs s).ell

/-- The cube's bits. -/
def bitsZ : ℕ :=
  if 0 < s.mainRows ∧ 0 < s.maskRows then max (B1 cs s) (B2 cs s) + 1
  else (if 0 < s.mainRows then B1 cs s else 0) + (if 0 < s.maskRows then B2 cs s else 0)

/-- The corner of an entry, as a number. -/
def idxZ : (portCode cs s).J → ℕ
  | .inl x => x.1.val + 2 ^ k1 s * x.2.val
  | .inr x => x.1.val + 2 ^ k2 s * x.2.val +
      (if 0 < s.mainRows then 2 ^ max (B1 cs s) (B2 cs s) else 0)

theorem tab_lt {R L i c : ℕ} (hi : i < R) (hc : c < L) :
    i + 2 ^ OnBytes.ceilLog2 R * c < 2 ^ (OnBytes.ceilLog2 R + OnBytes.ceilLog2 L) := by
  have h1 : i < 2 ^ OnBytes.ceilLog2 R := lt_of_lt_of_le hi (le_two_pow_ceilLog2 R)
  have h2 : c + 1 ≤ 2 ^ OnBytes.ceilLog2 L := le_trans hc (le_two_pow_ceilLog2 L)
  calc i + 2 ^ OnBytes.ceilLog2 R * c < 2 ^ OnBytes.ceilLog2 R + 2 ^ OnBytes.ceilLog2 R * c := by
        omega
    _ = 2 ^ OnBytes.ceilLog2 R * (c + 1) := by ring
    _ ≤ 2 ^ OnBytes.ceilLog2 R * 2 ^ OnBytes.ceilLog2 L := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (OnBytes.ceilLog2 R + OnBytes.ceilLog2 L) := (pow_add 2 _ _).symm

theorem main_lt (x : Fin s.mainRows × Fin (pMain cs s).ell) :
    x.1.val + 2 ^ k1 s * x.2.val < 2 ^ B1 cs s := tab_lt x.1.isLt x.2.isLt

theorem mask_lt (x : Fin s.maskRows × Fin (pMask cs s).ell) :
    x.1.val + 2 ^ k2 s * x.2.val < 2 ^ B2 cs s := tab_lt x.1.isLt x.2.isLt

theorem idxZ_lt (j : (portCode cs s).J) : idxZ cs s j < 2 ^ bitsZ cs s := by
  rcases j with x | x
  · have h0 : 0 < s.mainRows := lt_of_le_of_lt (Nat.zero_le _) x.1.isLt
    refine lt_of_lt_of_le (main_lt cs s x) (Nat.pow_le_pow_right (by decide) ?_)
    unfold bitsZ
    by_cases h2 : 0 < s.maskRows
    · rw [if_pos ⟨h0, h2⟩]
      exact le_trans (le_max_left _ _) (Nat.le_succ _)
    · rw [if_neg (fun h => h2 h.2), if_pos h0, if_neg h2]
      exact Nat.le_refl _
  · have h2 : 0 < s.maskRows := lt_of_le_of_lt (Nat.zero_le _) x.1.isLt
    have hb := mask_lt cs s x
    show x.1.val + 2 ^ k2 s * x.2.val +
      (if 0 < s.mainRows then 2 ^ max (B1 cs s) (B2 cs s) else 0) < 2 ^ bitsZ cs s
    unfold bitsZ
    by_cases h0 : 0 < s.mainRows
    · rw [if_pos h0, if_pos ⟨h0, h2⟩, pow_succ]
      have hm : 2 ^ B2 cs s ≤ 2 ^ max (B1 cs s) (B2 cs s) :=
        Nat.pow_le_pow_right (by decide) (le_max_right _ _)
      omega
    · rw [if_neg h0, if_neg (fun h => h0 h.1), if_neg h0, if_pos h2]
      simpa using hb

theorem idxZ_inj : Function.Injective (idxZ cs s) := by
  intro j j' h
  rcases j with x | x <;> rcases j' with y | y
  · have hx : x.1.val < 2 ^ k1 s := lt_of_lt_of_le x.1.isLt (le_two_pow_ceilLog2 _)
    have hy : y.1.val < 2 ^ k1 s := lt_of_lt_of_le y.1.isLt (le_two_pow_ceilLog2 _)
    obtain ⟨a, b⟩ := idx_inj (k1 s) hx hy h
    exact congrArg Sum.inl (Prod.ext (Fin.ext a) (Fin.ext b))
  · exfalso
    have h0 : 0 < s.mainRows := lt_of_le_of_lt (Nat.zero_le _) x.1.isLt
    have hb := main_lt cs s x
    have hm : 2 ^ B1 cs s ≤ 2 ^ max (B1 cs s) (B2 cs s) :=
      Nat.pow_le_pow_right (by decide) (le_max_left _ _)
    have h' : x.1.val + 2 ^ k1 s * x.2.val = y.1.val + 2 ^ k2 s * y.2.val +
        (if 0 < s.mainRows then 2 ^ max (B1 cs s) (B2 cs s) else 0) := h
    rw [if_pos h0] at h'
    omega
  · exfalso
    have h0 : 0 < s.mainRows := lt_of_le_of_lt (Nat.zero_le _) y.1.isLt
    have hb := main_lt cs s y
    have hm : 2 ^ B1 cs s ≤ 2 ^ max (B1 cs s) (B2 cs s) :=
      Nat.pow_le_pow_right (by decide) (le_max_left _ _)
    have h' : x.1.val + 2 ^ k2 s * x.2.val +
        (if 0 < s.mainRows then 2 ^ max (B1 cs s) (B2 cs s) else 0) =
          y.1.val + 2 ^ k1 s * y.2.val := h
    rw [if_pos h0] at h'
    omega
  · have hx : x.1.val < 2 ^ k2 s := lt_of_lt_of_le x.1.isLt (le_two_pow_ceilLog2 _)
    have hy : y.1.val < 2 ^ k2 s := lt_of_lt_of_le y.1.isLt (le_two_pow_ceilLog2 _)
    obtain ⟨a, b⟩ := idx_inj (k2 s) hx hy (Nat.add_right_cancel h)
    exact congrArg Sum.inr (Prod.ext (Fin.ext a) (Fin.ext b))

/-- How many places the pad of one answer has in a main row. -/
def eachZ : ℕ := if s.mainDeg = 3 then 1 else 3

/-- Is an entry a place of the pad. -/
def padP : (portCode cs s).J → Prop
  | .inl x => s.maskRows = 0 ∧ x.1.val + 1 = s.mainRows ∧ (pMain cs s).ell ≤ x.2.val + eachZ s
  | .inr x => x.1.val + 1 = s.maskRows ∧ x.2.val + 1 = (pMask cs s).ell

instance : DecidablePred (padP cs s) := fun j => by
  rcases j with x | x <;> unfold padP <;> infer_instance

/-- The number of a pad's place, from the first on. -/
def padNo : (portCode cs s).J → ℕ
  | .inl x => x.2.val + eachZ s - (pMain cs s).ell
  | .inr _ => 0

/-- Its weight: 1, x, x². -/
def wZ (j : {j // padP cs s j}) : GE :=
  Cb.Gl.padW ⟨padNo cs s j.1 % 3, Nat.mod_lt _ (by decide)⟩

/-- The entries: those that are no pad, and the pad. -/
def sigmaZ : (portCode cs s).J ≃ {j // ¬ padP cs s j} ⊕ {j // padP cs s j} :=
  (Equiv.sumCompl (padP cs s)).symm.trans (Equiv.sumComm _ _)

/-- The sample map. -/
@[reducible] noncomputable def portZ : Sample GE (portCode cs s).J :=
  (Sample.pad GE (Fin (bitsZ cs s)) {j // ¬ padP cs s j} {j // padP cs s j} GEˣ
    (fun j t => (idxZ cs s j.1).testBit t.val) (wZ cs s) Units.val).comap (sigmaZ cs s)

theorem portZ_S : Fintype.card (portZ cs s).S = 1 := Fintype.card_unit

theorem plc_inj : Function.Injective
    fun (j : {j // ¬ padP cs s j}) (t : Fin (bitsZ cs s)) => (idxZ cs s j.1).testBit t.val :=
  fun j j' h => Subtype.ext (idxZ_inj cs s
    (testBit_inj _ (idxZ_lt cs s j.1) (idxZ_lt cs s j'.1) fun t => congrFun h t))

/-- The shape has a mask row, or its main rows are over the extension field: the pad is one place
in a row over the extension field. -/
def CaseE : Prop := 0 < s.maskRows ∨ s.mainDeg = 3

theorem pad_sub (h : CaseE s) : Subsingleton {j // padP cs s j} := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have he : s.maskRows = 0 → eachZ s = 1 := fun z => by
    rcases h with h | h
    · omega
    · unfold eachZ
      rw [if_pos h]
  rcases a with x | x <;> rcases b with y | y
  · have e := he ha.1
    have h1 := ha.2.1
    have h2 := hb.2.1
    have h3 := ha.2.2
    have h4 := hb.2.2
    have h5 : x.2.val < (pMain cs s).ell := x.2.isLt
    have h6 : y.2.val < (pMain cs s).ell := y.2.isLt
    exact congrArg Sum.inl (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  · exfalso
    have hy : y.1.val < s.maskRows := y.1.isLt
    have hz := ha.1
    omega
  · exfalso
    have hx : x.1.val < s.maskRows := x.1.isLt
    have hz := hb.1
    omega
  · exact congrArg Sum.inr (Prod.ext (Fin.ext (by have := ha.1; have := hb.1; omega))
      (Fin.ext (by have := ha.2; have := hb.2; omega)))

theorem wZ_one (h : CaseE s) (j : {j // padP cs s j}) : wZ cs s j = 1 := by
  have hn : padNo cs s j.1 = 0 := by
    obtain ⟨j, hj⟩ := j
    rcases j with x | x
    · have e : eachZ s = 1 := by
        rcases h with h | h
        · have := hj.1
          omega
        · unfold eachZ
          rw [if_pos h]
      have h3 := hj.2.2
      have h5 : x.2.val < (pMain cs s).ell := x.2.isLt
      show x.2.val + eachZ s - (pMain cs s).ell = 0
      omega
    · rfl
  unfold wZ
  simp only [hn]
  rfl

theorem padVal_inj (h : CaseE s) : Function.Injective (padVal (F := GE) (wZ cs s)) := by
  haveI := pad_sub cs s h
  intro c c' e
  funext i
  have hs : ∀ d : {j // padP cs s j} → GE, padVal (F := GE) (wZ cs s) d = d i := fun d => by
    unfold padVal
    rw [Fintype.sum_subsingleton _ i, wZ_one cs s h, one_mul]
    rfl
  rw [← hs c, ← hs c', e]

/-- Under `CaseE` the sample map is a zero-evader on all vectors. -/
theorem portZ_ok (h : CaseE s) : (portZ cs s).OK := by
  have hon := Cb.ood_okOn_comap GE _ _ _ (sigmaZ cs s) (PadInF GE)
    (Cb.ood_okOn_pad GE GE (Fin (bitsZ cs s)) {j // ¬ padP cs s j} {j // padP cs s j} GEˣ _
      (wZ cs s) Units.val (plc_inj cs s) (fun _ _ e => Units.ext e) (padVal_inj cs s h))
  exact fun v hv => hon v (fun i => ⟨_, rfl⟩) hv

/-- The oracle message with that sample map and the order 0. -/
noncomputable def portOmZ (e : ℕ) : OMsg GE := portOm cs s e (portZ cs s) fun _ => 0

theorem port_johnZ (e d L : ℕ) (g : PBase cs s d)
    (hJ : InJohnson (Fintype.card (Fin (2 ^ aOf cs s))) d e)
    (hL : L = listMax (Fintype.card (Fin (2 ^ aOf cs s))) d e) (h : CaseE s) :
    (portOmZ cs s e).John d L :=
  port_john cs s e _ _ d L g hJ hL (portZ_ok cs s h)

end
end Johnson.Pack

#print axioms Johnson.Pack.idxZ_lt
#print axioms Johnson.Pack.idxZ_inj
#print axioms Johnson.Pack.portZ
#print axioms Johnson.Pack.portZ_ok
#print axioms Johnson.Pack.port_johnZ
