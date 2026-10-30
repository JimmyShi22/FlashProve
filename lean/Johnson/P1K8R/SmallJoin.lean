-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SmallJoin.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: A
PAYMENT BENEATH THE KIND'S FROZEN CONDITION: THE FIELD `small` OF `K8LeftT` AT THE CLOSED CONSTANT,
CUT DOWN TO ONE SENTENCE ON THE LAYOUT. NO SOUNDNESS.

The smallness test's own law ends in `TieAt`: there are integers below 2^18 in absolute value whose
packing the table of cells shows (Johnson/Desc/First/K8/LawItems.lean). The table of joints' item
"small" at the closed constant says the like of the symbols that the witness holds at the plan's
seats (`Cb.Pv.Tail.Base`), with the model's clause "small". That the first gives the second is a
field of the kind's condition. Another file writes the item out (`constr_small_iff`,
Johnson/Desc/First/K8/SmallAtNine.lean) and cuts the field down under a sentence that asks, among
others, that the plan's sizes ARE the state's part's. These sizes read the part's number of draws
and its number of tables too, which `Base` never reads. Here the field is had from less:
  `beta_at`, `rad_at`: the sizes' bound and radix are `2 ^ OnBytes.Model.lbz` and
    `OnBytes.Model.radb`: THE SAME CONSTANTS, BY NAME, AS IN `TieOf`.
  `base_at_plan`: **the tie at a part tl gives `Base` of the symbols read at seats, AT THE SIZES OF
    ANOTHER PART tlP**, where the two have one number of matrices and one list of matrices, and the
    seats show the table's cells.
  `ShowsAt`: that sentence, at the constant, a link, a state and a witness.
  `h_is_seat`: the constant's reader of a witness IS `P5J.hidAtSeat` at the plan's sizes and the
    seats as a function of the label: by the make.
  `small_at_const`: **under the head, at every link l ≤ 24: `ShowsAt` and `TieAt` at `cellsAt` give
    `(mgAtAll h).constr l .small`.** The model's clause holds by the make of the integers (they are
    read by unpacking): it is true of every witness: THE WEIGHT LIES IN `Base`.
Limits. `ShowsAt` is a premise here. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.Desc.First.K8.SmallAtNine
import Johnson.P5J.RowsAtMg
import Johnson.P5J.MgAtAll
import Johnson.P1K8R.SmallHead

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open Cb.Pv.Tail (Size Syms Base baseAt_of_packs)
open OnBytes.Tie.Pv.Tail (sizeOf_uniq)
open _root_.Meaning (symAt smallM_mgOf attSmall_maOf)
open VerifiableInference.Desc (Chain Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

/-- **The sizes' bound is the tie's, by name.** -/
theorem beta_at (X : Verify.Public) (k : ℕ) : (Meaning.sizesOf X k).beta = 2 ^ OnBytes.Model.lbz :=
  rfl

/-- So is their radix. -/
theorem rad_at (X : Verify.Public) (k : ℕ) : (Meaning.sizesOf X k).rad = OnBytes.Model.radb := rfl

theorem beta_pos (X : Verify.Public) : ∀ k < 25, (0 : ℤ) < ((Meaning.sizesOf X k).beta : ℤ) := by
  intro k _
  rw [beta_at]
  decide

theorem beta_le (X : Verify.Public) :
    ∀ k < 25, 2 * ((Meaning.sizesOf X k).beta : ℤ) ≤ 2 ^ 18 := by
  intro k _
  rw [beta_at]
  decide

/-- **The tie at tl gives `Base` at the sizes of tlP.** -/
theorem base_at_plan {tl tlP : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (eN : tl.NM = tlP.NM)
    (eM : tl.mats = tlP.mats) (st : Fin (Tie.Pv.Tail.sizeOf tlP).size.NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (msg : _root_.Meaning.Msgs)
    (hy : ∀ (μ : Fin (Tie.Pv.Tail.sizeOf tlP).size.NM) (r c : ℕ),
      r < Alg.symRows ((Tie.Pv.Tail.sizeOf tlP).size.m μ) → c < (Tie.Pv.Tail.sizeOf tlP).size.k μ →
      msg (st μ r c).1 false (st μ r c).2.1 (st μ r c).2.2 = A (tl.gtTree.getD μ 0) r c)
    (h : TieOf tl A) : Base (symAt (Tie.Pv.Tail.sizeOf tlP).size st msg) := by
  obtain ⟨a, h1, h2, -⟩ := h
  rw [eN, eM] at h1 h2
  exact ⟨fun μ c i => a μ.val i.val c.val,
    baseAt_of_packs (K := Cb.Gl.E) (s := (Tie.Pv.Tail.sizeOf tlP).size) Cb.Gl.p (sizeOf_uniq tlP)
      (y := symAt (Tie.Pv.Tail.sizeOf tlP).size st msg) (fun μ c i => h1 μ μ.2 c c.2 i i.2)
      fun μ c i' => (hy μ i' c i'.2 c.2).trans (h2 μ μ.2 c c.2 i' i'.2)⟩

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- The seats at which the constant reads a witness. -/
abbrev seatC (Zp : ProofFile.Pub) :=
  Meaning.seatBy (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp)
    (Meaning.sizesOf (P5J.At.X Zp))

/-- **The sentence on the layout**, at link l, a state and a witness: the state's part has the
plan's number and list of matrices, and the seats' entries, as segment l reads them, are the table's
cells at the part's symbol arrays. -/
def ShowsAt (Zp : ProofFile.Pub) (cF : Chain S Cl) (lay : ByteArray) (l : ℕ) (a : ProofFile.InstPub × S)
    (w : Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT) : Prop :=
  ∀ tl, a.2.tl? = some tl → tl.NM = (Meaning.tlAt (P5J.At.X Zp) l).NM ∧
    tl.mats = (Meaning.tlAt (P5J.At.X Zp) l).mats ∧
    ∀ (μ : Fin (Meaning.sizesOf (P5J.At.X Zp) l).NM) (r c : ℕ),
      r < Alg.symRows ((Meaning.sizesOf (P5J.At.X Zp) l).m μ) →
      c < (Meaning.sizesOf (P5J.At.X Zp) l).k μ →
      readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp lay) (P5J.At.N Zp cF) l w
          (seatC Zp l μ r c).1 false (seatC Zp l μ r c).2.1 (seatC Zp l μ r c).2.2 =
        cellsAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp lay) (P5J.At.N Zp cF) l a w
          (tl.gtTree.getD μ 0) r c

/-- **The constant's reader of a witness is `hidAtSeat`**, by the make. -/
theorem h_is_seat (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) :
    h.𝔇.H = P5J.hidAtSeat (P5J.At.X Zp) (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay)
      (P5J.At.N Zp cF) (Meaning.sizesOf (P5J.At.X Zp)) (seatC Zp) P5J.tokVOf h.𝔇.H.req
      h.𝔇.H.dec h.plan.hN h.plan.hG := rfl

/-- **THE FIELD "small" AT THE CLOSED CONSTANT, from one sentence on the layout.** -/
theorem small_at_const (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l ≤ 24)
    (z : ProofFile.InstPub) (st : S) (y : Strs)
    (w : Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)
    (hL : ShowsAt Zp cF Z.lay l (z, st) w)
    (hT : TieAt (cellsAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
      (z, st)) st w) :
    (mgAtAll h).constr l .small (z, st) y w := by
  have e24 : VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp) = 24 :=
    P5J.headLink_in_scope h.scope h.reads h.pubOne
  obtain ⟨tl, htl, ht⟩ := hT
  obtain ⟨eN, eM, hy⟩ := hL tl htl
  refine (constr_small_iff h.𝔇 mgBase l (z, st) y w).2 ⟨?_, ?_⟩
  · rw [h_is_seat h]
    exact base_at_plan eN eM (seatC Zp l) _ hy ht
  · intro M i _ _
    rw [e24]
    split
    · exact headSmall_at h i _ _ _
    · rw [h_is_seat h]
      split
      · exact smallM_mgOf _ (beta_pos _) (beta_le _) (P5J.At.X Zp).y (g := l / 2) (by omega)
      · exact attSmall_maOf _ (beta_pos _) (beta_le _) (P5J.At.X Zp) (g := l / 2) (by omega)

end P1K8T

#print axioms P1K8T.beta_at
#print axioms P1K8T.rad_at
#print axioms P1K8T.base_at_plan
#print axioms P1K8T.h_is_seat
#print axioms P1K8T.small_at_const
