-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/NormBridge/BridgeWorld.lean: THE PER-POSITION BRIDGE OF A NORM, FLOOR B: FROM THE
VERIFIER's
WORLD AT THE NORM's POINT TO EVERY POSITION. Over plain records alone (Model.Aff, Model.Psc, World,
Reading,
lists, elements) and lemmas on them; NO ROUTINE IN A CONTEXT (Blk, Ctx, Chan, SubM, LinkM) is
reached from a
statement or a proof. Definitions, statements and proofs.

THE SETTING (OnBytes/Model/HideLaws.lean). A reading rho takes the program's elements to a field K.
A world W
gives every hidden value (slot) and every entry of a read a value in K. Aff.value is a form's value
there.

FIXED FIRST: c : Data K (BridgeCore.lean: sizes, constants, limbs, digits), lPd, and M : Masks K
(the mask
entries beneath the two sumchecks: hiding coefficients and the end values' masks).
THE RUN's LETTERS, under "for all": R : Run (elements, lists, slots' numbers, two sumchecks as
heard, the
caller's forms) and the world W. THE ROUNDS' ORDER is BridgeCore.lean's (1 to 8).

THE PREMISES, IN FIVE NAMED GROUPS, and who pays each:
  Run.Shapes     sizes of the points; the squares' point is (rho, lPd times h, P); record and rounds
  of each
                 sumcheck fit each other. PAYER: whoever takes the hearing text apart (public
                 facts).
  Run.Consts     what the caller's own forms and end terms are worth BY ALGEBRA: eps, two; the
  squares' start
                 form; the two end terms on what was shown; 1 - h = h. PAYER: the kind's caller; no
                 chance.
  Run.Ledger     the world is the ledger's: hidden = shown - factor * mask, at the slots of the two
  sumchecks.
                 PAYER: the ledger's law.
  Run.FormsZero  EVERY ONE OF THE 5 + 21 NI FORMS IS WORTH 0 IN W. PAYER: the link's one equation
  (its batching).
  Run.ReadsTrue  reads_are_true: the three reads' forms are worth the committed cells' extensions:
  the 99
                 digits at P; the streams' batch at the squares' end point; the 99 digits at the
                 products' end
                 point.
                 PAYER: the reads' row (K8's files); and words_are_committed for "c stands first in
                 time".
NO BAD DRAW: BridgeCore.lean's four (BadP, BadG, BadI, BadO) and, for each sumcheck, Heard1.Clean
(EqSum.lean: pscBadE at most 1, pscBad at most 2 a round). WHAT THE SUMCHECKS' BAD SETS READ, by
their
arguments: the squares': the point zsS (rounds 1, 4), c and gam (round 3), M, the start form's
public part,
and Run.cvS: a formula in Wt (round 2), gam and the point; then mu; then eps and the rounds in
front. The
products': P (round 1), c, om (round 7), M, the start form's public part, and the one hidden scalar
under
the slot sCl (sent in round 8 in front of eps). OF THE WORLD the bad sets read the slots of Wt, Pt
and sCl
alone: no entry of a read, which is sent behind all these draws.

  bridge_world: THE LAW: the five groups, no bad draw: then c.Holds: every identity at every
  position.
  rows_at_position: and then, at EVERY world that holds one position's digits, sums and products,
  all 17 of
    the part's own forms (OnBytes/Desc/First/P6/NormRow.lean: carries, lines) are worth 0: the
    premises of
    row_says (OnBytes/Desc/First/P6/NormRowLaw.lean) at that position's own world.
  yes_to_all: at data that do not hold, a run in which every form is worth 0, without a bad draw,
  FAILS
    reads_are_true. It is the law's bare contrapositive: no check of
    its own; a verifier that
    says yes to all is caught where FormsZero is paid.

ALSO TAKEN: products_sound (through EqSum.lean);
NormRowLaw.lean carries_value,
lines_value, a_value, b_value, Rlo_value, Rhi_value, idnP_congr. COPIED from its proofs of row_says
and
row_honest: the steps idnP_of_forms and forms_of_idnP.
NOT CLAIMED. Any of the five groups. A DEBT THAT NO GROUP NAMES: Good
and Clean read W.slot at
the 9 NI slots of the sums, the 7 NI of the products and at sCl; Ledger ties the two sumchecks'
slots alone: WHOEVER
COUNTS owes "slot = shown - 1 * mask" there, or these bad sets do not stand in front of their draws.
The order
"c and M before P" is named by no premise: c and M must be terms of the committed words, never of R
or W. That a bad element of K has just one drawn word above it (words below
the prime; Reading.gl one-to-one there). Time: the order of the letters alone. Four limbs. The
integers.
Probabilities. Hiding.
-/
import OnBytes.Desc.First.NormBridge.BridgeTables
import OnBytes.Desc.First.NormBridge.EqSum
import OnBytes.Desc.First.NormBridge.IdnDigits
import OnBytes.Desc.First.P6.NormRowLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D6.Bridge
open Finset
open OnBytes OnBytes.Model
open Blocks (ext eqN nat ofList)
open Inst.Model (NormPar)
open Inst.Model.Ledger (idnP prods sa sb Rlo Rhi)
open OnBytes.Desc.First.P1 (Term sumTerms)
open OnBytes.Desc.First.P6 (Row carries lines dv)

variable {K : Type} [Field K]

/-! ## 0. Two steps out of NormRowLaw.lean's proofs -/

/-- All 17 forms worth 0: the identities with letters hold at the forms' values. -/
theorem idnP_of_forms (ρ : Reading K) (W : World K) (D Wf P : ℕ → Aff) (np : NormPar) (eps : E)
    (two : Aff) (heps : ρ.val eps = (np.eps : K)) (htwo : two.value ρ W = 2 ^ (np.M + 1))
    (hc : ∀ f ∈ carries (Row.ofDigits D) D Wf, f.value ρ W = 0)
    (hl : ∀ f ∈ lines (Row.ofDigits D) P eps two, f.value ρ W = 0) (k : ℕ) :
    idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) k = 0 := by
  by_cases h9 : k < 9
  · have h := OnBytes.Desc.First.P6.carries_value ρ W D Wf P np
    have hm : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) k ∈
        (carries (Row.ofDigits D) D Wf).map (·.value ρ W) := by
      rw [h]
      exact List.mem_map.mpr ⟨k, List.mem_range.mpr h9, rfl⟩
    obtain ⟨f, hf, hv⟩ := List.mem_map.mp hm
    rw [← hv]
    exact hc f hf
  · by_cases h17 : 17 ≤ k
    · exact Inst.Model.Ledger.idnP_of_le np _ _ _ h17
    · have h := OnBytes.Desc.First.P6.lines_value ρ W D Wf P np eps two heps htwo
      obtain ⟨j, rfl⟩ : ∃ j, k = 9 + j := ⟨k - 9, by omega⟩
      have hm : idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) (9 + j) ∈
          (lines (Row.ofDigits D) P eps two).map (·.value ρ W) := by
        rw [h]
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩
      obtain ⟨f, hf, hv⟩ := List.mem_map.mp hm
      rw [← hv]
      exact hl f hf

/-- The identities with letters hold at the forms' values: all 17 forms are worth 0. -/
theorem forms_of_idnP (ρ : Reading K) (W : World K) (D Wf P : ℕ → Aff) (np : NormPar) (eps : E)
    (two : Aff) (heps : ρ.val eps = (np.eps : K)) (htwo : two.value ρ W = 2 ^ (np.M + 1))
    (hz : ∀ k, idnP np (dv ρ W Wf) (dv ρ W D) (dv ρ W P) k = 0) :
    (∀ f ∈ carries (Row.ofDigits D) D Wf, f.value ρ W = 0) ∧
      ∀ f ∈ lines (Row.ofDigits D) P eps two, f.value ρ W = 0 := by
  constructor
  · intro f hf
    have hm : f.value ρ W ∈ (carries (Row.ofDigits D) D Wf).map (·.value ρ W) :=
      List.mem_map_of_mem hf
    rw [OnBytes.Desc.First.P6.carries_value ρ W D Wf P np] at hm
    obtain ⟨s, _, hs⟩ := List.mem_map.mp hm
    rw [← hs]
    exact hz s
  · intro f hf
    have hm : f.value ρ W ∈ (lines (Row.ofDigits D) P eps two).map (·.value ρ W) :=
      List.mem_map_of_mem hf
    rw [OnBytes.Desc.First.P6.lines_value ρ W D Wf P np eps two heps htwo] at hm
    obtain ⟨s, _, hs⟩ := List.mem_map.mp hm
    rw [← hs]
    exact hz (9 + s)

/-! ## 1. What stands first beside the data; the run's letters -/

/-- The mask entries beneath the two sumchecks. -/
structure Masks (K : Type) where
  /-- the squares' hiding coefficients -/
  hS : ℕ → K
  /-- the masks of its two end values -/
  mS : ℕ → K
  /-- the products' hiding coefficients -/
  hP : ℕ → K
  /-- the masks of its 4 NI end values -/
  mP : ℕ → K

/-- The letters of a run. -/
structure Run where
  /-- round 1: the point over the positions -/
  PE : List E
  /-- round 2: the first slot of the 9 NI sums -/
  sW : ℕ
  /-- round 3 -/
  gam : E
  /-- rounds 1 and 4: the squares' point: rho, then lPd times the half, then P -/
  zsS : List E
  /-- the program's inverse of 2 -/
  half : E
  /-- round 5: the squares' sumcheck as heard -/
  S : Heard1
  /-- its two end values' slots are sL and sL + 1 -/
  sL : ℕ
  /-- what was shown in them -/
  shS : ℕ → E
  /-- the caller's form for the streams' batch at the squares' end point, through its read -/
  XS : Aff
  /-- round 6: the first slot of the 7 NI products -/
  sPv : ℕ
  /-- round 7 -/
  om : E
  /-- round 8: the slot of the hidden batched sum -/
  sCl : ℕ
  /-- round 8: the products' sumcheck as heard -/
  Pr : Heard1
  /-- the first of its 4 NI end values' slots -/
  sE : ℕ
  /-- what was shown in them -/
  shP : ℕ → E
  /-- the caller's form for digit n of norm i through the read at P: D i n -/
  D : ℕ → ℕ → Aff
  /-- the same through the read at the products' end point -/
  D' : ℕ → ℕ → Aff
  /-- norm i's constant under the root, and 2^(M + 1), as the caller lays them -/
  eps : ℕ → E
  two : ℕ → Aff

namespace Run
variable (R : Run) (ρ : Reading K) (c : Data K) (lPd : ℕ) (M : Masks K) (W : World K)

/-- The point over the positions, read; as a function on numbers and as a tuple. -/
def pk : ℕ → K := ofList (R.PE.map ρ.val)
def P : Fin c.lt → K := fun v => R.pk ρ v

/-- The squares' point, read; its first lNI coordinates. -/
def aS : ℕ → K := ofList (R.zsS.map ρ.val)
def rho : Fin c.lNI → K := fun v => R.aS ρ v

/-- The hidden sums and the hidden products. -/
def Wt : ℕ → K := fun j => W.slot (R.sW + j)
def Pt : ℕ → K := fun m => W.slot (R.sPv + m)

/-- What the squares' start form is worth: a function of the hidden sums (round 2), gam (round 3)
and the
squares' point (rounds 1, 4). -/
def cvS : K := ρ.val R.half ^ lPd * ∑ i ∈ range c.NI,
  eqN c.lNI 0 (R.aS ρ) i * ∑ s ∈ range 9, ρ.val R.gam ^ s * R.Wt W (9 * i + s)

/-- The two sumchecks' end points, read. -/
def rS : ℕ → K := ofList (R.S.r ρ)
def rP : ℕ → K := ofList (R.Pr.r ρ)

/-- Public facts on sizes and on how record and rounds fit. -/
structure Shapes : Prop where
  lenP : R.PE.length = c.lt
  lenS : R.zsS.length = c.lNI + lPd + c.lt
  mid : ∀ t < lPd, R.aS ρ (c.lNI + t) = ρ.val R.half
  last : ∀ t < c.lt, R.aS ρ (c.lNI + lPd + t) = R.pk ρ t
  sq : R.S.Shape R.zsS
  pr : R.Pr.Shape R.PE

/-- What the caller's forms and end terms are worth by algebra. -/
structure Consts : Prop where
  half : 1 - ρ.val R.half = ρ.val R.half
  eps : ∀ i < c.NI, ρ.val (R.eps i) = ((c.np i).eps : K)
  two : ∀ i < c.NI, (R.two i).value ρ W = 2 ^ ((c.np i).M + 1)
  startS : R.S.p.start.value ρ W = R.cvS ρ c lPd W
  startP : R.Pr.p.start.value ρ W = W.slot R.sCl
  endS : ρ.val R.S.S0 = ρ.val (R.shS 0) * ρ.val (R.shS 1)
  endP : ρ.val R.Pr.S0 = sumTerms (prTerms c.NI (ρ.val R.om)) fun e => ρ.val (R.shP e)

/-- The world is the ledger's, at the two sumchecks' slots. -/
structure Ledger : Prop where
  hidS : ∀ i, i < OnBytes.Psc.hidingEntries (eqWs R.zsS ++ [wY]) →
    W.slot (R.S.p.first + i) = M.hS i
  hidP : ∀ i, i < OnBytes.Psc.hidingEntries (eqWs R.PE ++ [wY]) →
    W.slot (R.Pr.p.first + i) = M.hP i
  shownS : ∀ e < 2, ρ.val (R.shS e) = W.slot (R.sL + e) + R.S.beta ρ * M.mS e
  shownP : ∀ e < 4 * c.NI, ρ.val (R.shP e) = W.slot (R.sE + e) + R.Pr.beta ρ * M.mP e

/-- Every one of the 5 + 21 NI forms is worth 0 in the world. -/
structure FormsZero : Prop where
  /-- the squares' sumcheck's own form -/
  rowS : (R.S.p.rowForm R.S.S0 {}).value ρ W = 0
  /-- its two end values are equal -/
  endsS : (Aff.slot R.sL - Aff.slot (R.sL + 1)).value ρ W = 0
  /-- the first is the streams' batch -/
  endS : (Aff.slot R.sL - R.XS).value ρ W = 0
  /-- the products' claimed sum is the batch of the 7 NI products -/
  batchP : W.slot R.sCl - ∑ m ∈ range (7 * c.NI), ρ.val R.om ^ m * R.Pt W m = 0
  /-- the products' sumcheck's own form -/
  rowP : (R.Pr.p.rowForm R.Pr.S0 {}).value ρ W = 0
  /-- its end values are the rows' four fields -/
  endA : ∀ i < c.NI, (Aff.slot (R.sE + (4 * i + 0)) - (Row.ofDigits (R.D' i)).a).value ρ W = 0
  endB : ∀ i < c.NI, (Aff.slot (R.sE + (4 * i + 1)) - (Row.ofDigits (R.D' i)).b).value ρ W = 0
  endLo : ∀ i < c.NI, (Aff.slot (R.sE + (4 * i + 2)) - (Row.ofDigits (R.D' i)).Rlo).value ρ W = 0
  endHi : ∀ i < c.NI, (Aff.slot (R.sE + (4 * i + 3)) - (Row.ofDigits (R.D' i)).Rhi).value ρ W = 0
  /-- the nine carries and the eight lines of every norm, at the read under P -/
  carries : ∀ i < c.NI, ∀ f ∈ OnBytes.Desc.First.P6.carries (Row.ofDigits (R.D i)) (R.D i)
    (fun s => Aff.slot (R.sW + (9 * i + s))), f.value ρ W = 0
  lines : ∀ i < c.NI, ∀ f ∈ OnBytes.Desc.First.P6.lines (Row.ofDigits (R.D i))
    (fun n => Aff.slot (R.sPv + (7 * i + n))) (R.eps i) (R.two i), f.value ρ W = 0

/-- **reads_are_true**: the three reads are worth the committed cells' extensions. -/
structure ReadsTrue : Prop where
  atP : ∀ i < c.NI, ∀ n < 99, (R.D i n).value ρ W = c.digAt (nat (R.P ρ c)) i n
  atS : R.XS.value ρ W = ext (c.lNI + lPd + c.lt) (c.sqTab lPd (ρ.val R.gam)) (R.rS ρ)
  atR : ∀ i < c.NI, ∀ n < 99, (R.D' i n).value ρ W = c.digAt (R.rP ρ) i n

/-- No element of either sumcheck was bad. -/
structure Clean : Prop where
  sq : R.S.Clean ρ R.zsS (fun _ => c.sqTab lPd (ρ.val R.gam)) M.mS [(1, 0, 1)] M.hS
    (ρ.val R.S.p.target) (R.cvS ρ c lPd W)
  pr : R.Pr.Clean ρ R.PE c.field M.mP (prTerms c.NI (ρ.val R.om)) M.hP
    (ρ.val R.Pr.p.target) (W.slot R.sCl)

/-- None of the four draws outside the sumchecks was bad. -/
structure Good : Prop where
  p : ¬ c.BadP (R.P ρ c)
  g : ¬ c.BadG (nat (R.P ρ c)) (R.Wt W) (ρ.val R.gam)
  i : ¬ c.BadI (nat (R.P ρ c)) (R.Wt W) (ρ.val R.gam) (R.rho ρ c)
  o : ¬ c.BadO (nat (R.P ρ c)) (R.Pt W) (ρ.val R.om)

end Run

/-! ## 2. The three premises of floor A, paid -/

section
variable (R : Run) (ρ : Reading K) (c : Data K) (lPd : ℕ) (M : Masks K) (W : World K)

theorem natP_eq {t : ℕ} (ht : t < c.lt) : nat (R.P ρ c) t = R.pk ρ t := nat_apply c.lt (R.pk ρ) ht

theorem natRho_eq {t : ℕ} (ht : t < c.lNI) : nat (R.rho ρ c) t = R.aS ρ t :=
  nat_apply c.lNI (R.aS ρ) ht

/-- The linear claims. -/
theorem lines_of_run (hk : R.Consts ρ c lPd W) (hz : R.FormsZero ρ c W)
    (hr : R.ReadsTrue ρ c lPd W) : c.Lines (nat (R.P ρ c)) (R.Wt W) (R.Pt W) := by
  intro i hi k _
  have h := idnP_of_forms ρ W (R.D i) (fun s => Aff.slot (R.sW + (9 * i + s)))
    (fun n => Aff.slot (R.sPv + (7 * i + n))) (c.np i) (R.eps i) (R.two i) (hk.eps i hi)
    (hk.two i hi) (hz.carries i hi) (hz.lines i hi) k
  have eD := idnP_congr_D (c.np i) (dv ρ W fun s => Aff.slot (R.sW + (9 * i + s)))
    (dv ρ W fun n => Aff.slot (R.sPv + (7 * i + n))) (D := dv ρ W (R.D i))
    (D' := c.digAt (nat (R.P ρ c)) i) (fun n hn => hr.atP i hi n hn) k
  have eW : dv ρ W (fun s => Aff.slot (R.sW + (9 * i + s))) = fun s => R.Wt W (9 * i + s) :=
    funext fun s => Aff.value_slot ρ W _
  have eP : dv ρ W (fun n => Aff.slot (R.sPv + (7 * i + n))) = fun n => R.Pt W (7 * i + n) :=
    funext fun n => Aff.value_slot ρ W _
  rw [eD, eW, eP] at h
  exact h

/-- The squares' sumcheck's conclusion. -/
theorem squares_of_run (hd : c.d ≤ 2 ^ lPd) (hN : c.NI ≤ 2 ^ c.lNI) (hs : R.Shapes ρ c lPd)
    (hk : R.Consts ρ c lPd W) (hl : R.Ledger ρ c M W) (hz : R.FormsZero ρ c W)
    (hr : R.ReadsTrue ρ c lPd W) (hc : R.Clean ρ c lPd M W) :
    c.Squares (nat (R.P ρ c)) (R.Wt W) (ρ.val R.gam) (nat (R.rho ρ c)) := by
  -- the two hidden end values are the table's extension
  have v0 : W.slot R.sL = ext (c.lNI + lPd + c.lt) (c.sqTab lPd (ρ.val R.gam)) (R.rS ρ) := by
    have h := hz.endS
    rw [Aff.value_sub, Aff.value_slot, hr.atS] at h
    exact sub_eq_zero.mp h
  have v1 : W.slot (R.sL + 1) = ext (c.lNI + lPd + c.lt) (c.sqTab lPd (ρ.val R.gam)) (R.rS ρ) := by
    have h := hz.endsS
    rw [Aff.value_sub, Aff.value_slot, Aff.value_slot] at h
    rw [← sub_eq_zero.mp h]
    exact v0
  have hS0 : ρ.val R.S.S0 = sumTerms [((1 : K), 0, 1)] fun e =>
      ext (c.lNI + lPd + c.lt) (c.sqTab lPd (ρ.val R.gam)) (R.rS ρ) + R.S.beta ρ * M.mS e := by
    have s0 := hl.shownS 0 (by omega)
    have s1 := hl.shownS 1 (by omega)
    rw [Nat.add_zero, v0] at s0
    rw [v1] at s1
    rw [hk.endS, s0, s1]
    simp [OnBytes.Desc.First.P1.sumTerms]
  have hlaw := psc_law ρ R.zsS (fun _ => c.sqTab lPd (ρ.val R.gam)) M.mS [((1 : K), 0, 1)] M.hS W
    R.S (fun e => ext (c.lNI + lPd + c.lt) (c.sqTab lPd (ρ.val R.gam)) (R.rS ρ) +
      R.S.beta ρ * M.mS e) hs.sq hl.hidS hz.rowS hS0 (fun e => by rw [hs.lenS]; rfl)
    (by rw [hk.startS]; exact hc.sq)
  rw [hs.lenS] at hlaw
  have hsum : (fun X => sumTerms [((1 : K), 0, 1)] fun _ => c.sqTab lPd (ρ.val R.gam) X) =
      fun X => c.sqTab lPd (ρ.val R.gam) X * c.sqTab lPd (ρ.val R.gam) X := by
    funext X
    simp [OnBytes.Desc.First.P1.sumTerms]
  rw [hsum] at hlaw
  have hext := c.ext_sqTab lPd hd hN (ρ.val R.gam) (ρ.val R.half) hk.half (R.aS ρ) hs.mid
  have hh0 : ρ.val R.half ^ lPd ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have := hk.half
    rw [h0] at this
    simp at this
  have hcancel := mul_left_cancel₀ hh0 ((hk.startS.symm.trans hlaw).trans hext)
  -- to the letters of floor A
  unfold Data.Squares
  have eL : ∀ i, eqN c.lNI 0 (nat (R.rho ρ c)) i = eqN c.lNI 0 (R.aS ρ) i := fun i =>
    eqN_congr_pt c.lNI 0 (fun t ht => by rw [Nat.zero_add]; exact natRho_eq R ρ c ht) i
  have eR : ∀ i, ext c.lt (fun t => ∑ j ∈ range c.d,
        (∑ l ∈ range 5, ρ.val R.gam ^ l * c.limb i l j t) ^ 2) (nat (R.P ρ c)) =
      c.sqZ (ρ.val R.gam) (fun t => R.aS ρ (c.lNI + lPd + t)) i := fun i =>
    ext_congr_pt c.lt _ fun t ht => by rw [natP_eq R ρ c ht, hs.last t ht]
  simp only [eL, eR]
  exact hcancel

/-- A hidden end value of the products' sumcheck is its table's extension. -/
theorem hidden_field (hz : R.FormsZero ρ c W) (hr : R.ReadsTrue ρ c lPd W) (i : ℕ) (hi : i < c.NI)
    (q : ℕ) (hq : q < 4) :
    W.slot (R.sE + (4 * i + q)) = ext c.lt (c.field (4 * i + q)) (R.rP ρ) := by
  have eD : ∀ n < 99, dv ρ W (R.D' i) n = c.digAt (R.rP ρ) i n := fun n hn => hr.atR i hi n hn
  have hc : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · have h := hz.endA i hi
    rw [Aff.value_sub, Aff.value_slot, OnBytes.Desc.First.P6.a_value ρ W, sa_congr eD] at h
    rw [c.ext_field0]
    exact sub_eq_zero.mp h
  · have h := hz.endB i hi
    rw [Aff.value_sub, Aff.value_slot, OnBytes.Desc.First.P6.b_value ρ W, sb_congr eD] at h
    rw [c.ext_field1]
    exact sub_eq_zero.mp h
  · have h := hz.endLo i hi
    rw [Aff.value_sub, Aff.value_slot, OnBytes.Desc.First.P6.Rlo_value ρ W, Rlo_congr eD] at h
    rw [c.ext_field2]
    exact sub_eq_zero.mp h
  · have h := hz.endHi i hi
    rw [Aff.value_sub, Aff.value_slot, OnBytes.Desc.First.P6.Rhi_value ρ W, Rhi_congr eD] at h
    rw [c.ext_field3]
    exact sub_eq_zero.mp h

/-- The products' sumcheck's conclusion. -/
theorem products_of_run (hs : R.Shapes ρ c lPd) (hk : R.Consts ρ c lPd W) (hl : R.Ledger ρ c M W)
    (hz : R.FormsZero ρ c W) (hr : R.ReadsTrue ρ c lPd W) (hc : R.Clean ρ c lPd M W) :
    c.Products (nat (R.P ρ c)) (R.Pt W) (ρ.val R.om) := by
  have hshown : ∀ i < c.NI, ∀ q < 4, ρ.val (R.shP (4 * i + q)) =
      ext c.lt (c.field (4 * i + q)) (R.rP ρ) + R.Pr.beta ρ * M.mP (4 * i + q) := by
    intro i hi q hq
    rw [hl.shownP (4 * i + q) (by omega), hidden_field R ρ c lPd W hz hr i hi q hq]
  have hS0 : ρ.val R.Pr.S0 = sumTerms (prTerms c.NI (ρ.val R.om)) fun e =>
      ext c.lt (c.field e) (R.rP ρ) + R.Pr.beta ρ * M.mP e := by
    rw [hk.endP, sumTerms_pr, sumTerms_pr]
    refine sum_congr rfl fun m hm => ?_
    have hm' : m / 7 < c.NI := by
      have := mem_range.mp hm
      omega
    rw [hshown (m / 7) hm' _ (pairA_lt _), hshown (m / 7) hm' _ (pairB_lt _)]
  have hlaw := psc_law ρ R.PE c.field M.mP (prTerms c.NI (ρ.val R.om)) M.hP W R.Pr
    (fun e => ext c.lt (c.field e) (R.rP ρ) + R.Pr.beta ρ * M.mP e) hs.pr hl.hidP hz.rowP hS0
    (fun e => by rw [hs.lenP]; rfl) (by rw [hk.startP]; exact hc.pr)
  rw [hs.lenP] at hlaw
  unfold Data.Products
  rw [← sub_eq_zero.mp hz.batchP, ← hk.startP, hlaw]
  have e1 : (fun X => sumTerms (prTerms c.NI (ρ.val R.om)) fun i => c.field i X) =
      fun t => ∑ m ∈ range (7 * c.NI), ρ.val R.om ^ m * c.prodR (m / 7) (m % 7) t :=
    funext fun t => sumTerms_field c (ρ.val R.om) t
  rw [e1]
  exact ext_congr_pt c.lt _ fun t ht => (natP_eq R ρ c ht).symm

/-! ## 3. The law -/

/-- **THE PER-POSITION BRIDGE, FLOOR B.** The data and the masks stand first. For every run and
every
world: if the shapes fit, the caller's algebra is as said, the world is the ledger's, EVERY FORM IS
WORTH 0, THE READS ARE TRUE, and no drawn element was bad, then every identity of every norm holds
at
every position. -/
theorem bridge_world (hd : c.d ≤ 2 ^ lPd) (hN : c.NI ≤ 2 ^ c.lNI) (hs : R.Shapes ρ c lPd)
    (hk : R.Consts ρ c lPd W) (hl : R.Ledger ρ c M W) (hz : R.FormsZero ρ c W)
    (hr : R.ReadsTrue ρ c lPd W) (hc : R.Clean ρ c lPd M W) (hg : R.Good ρ c W) : c.Holds :=
  bridge c (R.P ρ c) (R.Wt W) (ρ.val R.gam) (R.rho ρ c) (R.Pt W) (ρ.val R.om)
    (lines_of_run R ρ c lPd W hk hz hr) (squares_of_run R ρ c lPd M W hd hN hs hk hl hz hr hc)
    (products_of_run R ρ c lPd M W hs hk hl hz hr hc) hg.p hg.g hg.i hg.o

/-- **THE CHECK: A WORLD THAT SAYS YES TO ALL.** At data that do not hold, a run in which every form
is
worth 0, without a bad draw, fails reads_are_true. -/
theorem yes_to_all (hd : c.d ≤ 2 ^ lPd) (hN : c.NI ≤ 2 ^ c.lNI) (hfalse : ¬ c.Holds)
    (hs : R.Shapes ρ c lPd) (hk : R.Consts ρ c lPd W) (hl : R.Ledger ρ c M W)
    (hz : R.FormsZero ρ c W) (hc : R.Clean ρ c lPd M W) (hg : R.Good ρ c W) :
    ¬ R.ReadsTrue ρ c lPd W :=
  fun hr => hfalse (bridge_world R ρ c lPd M W hd hN hs hk hl hz hr hc hg)

end

/-! ## 4. At each position's own world -/

/-- **Where row_says (NormRowLaw.lean) begins.** If the data hold, then at every world that holds
the digits, the
sums and the products of ONE position of one norm, all 17 of the part's forms are worth 0, and the
seven forms P are worth the products of the row's fields. -/
theorem rows_at_position (ρ : Reading K) (c : Data K) (h : c.Holds) (i : ℕ) (hi : i < c.NI) (t : ℕ)
    (ht : t < 2 ^ c.lt) (Wp : World K) (D Wf P : ℕ → Aff) (eps : E) (two : Aff)
    (heps : ρ.val eps = ((c.np i).eps : K)) (htwo : two.value ρ Wp = 2 ^ ((c.np i).M + 1))
    (hD : ∀ n < 99, (D n).value ρ Wp = c.dig i n t) (hW : ∀ s < 9, (Wf s).value ρ Wp = c.sumW i s t)
    (hP : ∀ n, n < 7 → (P n).value ρ Wp = c.prodR i n t) :
    (∀ f ∈ carries (Row.ofDigits D) D Wf, f.value ρ Wp = 0) ∧
      (∀ f ∈ lines (Row.ofDigits D) P eps two, f.value ρ Wp = 0) ∧
      ∀ n, n < 7 → (P n).value ρ Wp = prods (dv ρ Wp D) n := by
  have eD : ∀ n < 99, dv ρ Wp D n = (fun n => c.dig i n t) n := hD
  have hP' : ∀ n, n < 7 → (P n).value ρ Wp = prods (dv ρ Wp D) n := by
    intro n hn
    rw [hP n hn, prods_congr eD]
    rfl
  have hz : ∀ k, idnP (c.np i) (dv ρ Wp Wf) (dv ρ Wp D) (dv ρ Wp P) k = 0 := by
    intro k
    rw [idnP_congr_pv (c.np i) _ _ k (pv' := prods (dv ρ Wp D)) fun n hn => hP' n hn,
      prods_congr eD, idnP_congr_D (c.np i) _ _ eD k,
      idnP_congr (c.np i) _ _ k (Ws' := fun s => c.sumW i s t) (fun s hs => hW s hs),
      ← Inst.Model.Ledger.idn_eq_idnP]
    exact holds_all c h i hi k t ht
  obtain ⟨h1, h2⟩ := forms_of_idnP ρ Wp D Wf P (c.np i) eps two heps htwo hz
  exact ⟨h1, h2, hP'⟩

end D6.Bridge

#print axioms D6.Bridge.bridge_world
#print axioms D6.Bridge.yes_to_all
#print axioms D6.Bridge.rows_at_position
