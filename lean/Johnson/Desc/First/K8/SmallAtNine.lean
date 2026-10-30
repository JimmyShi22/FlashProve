-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/SmallAtNine.lean: THE FIELD "small" OF K8Fill AT THE COMPOSED
MEANING: from the smallness test's tie at the table of cells cellsAt to
(mgAll 𝔇 Mg).constr m .small. CUT DOWN, NOT PAID: to H's make, one sentence on the layout, and the
head's own part.

  constr_small_iff  what (mgAll 𝔇 Mg).constr m .small says, written out: 𝔇.H.base m w, and, at every
                    index that the decoded matrix holds, the model's clause "small" of segment m
  base_of_small     so the field, at whatever 𝔇, gives: the tie → 𝔇.H.base m w
  base_of_tie       **the tie gives Base of the symbols that the table of cells shows** (symsA,
                    Johnson/Meaning/PlanesTieK8Cells.lean), by baseAt_of_packs and sizeOf_uniq
  base_at_seat      the same of the symbols read at seats (symAt), where the sizes are the state's
                    plan's and the seats show the table's cells
  SeatShows         that sentence on the layout, at segment m, a state and a witness
  small_at_seat     **THE FIELD, AT 𝔇.H := P5J.hidAtSeat …**, at every segment below 24 that is not
                    the head's: under SeatShows; the model's clause by the make (smallM_mgOf,
                    attSmall_maOf)
  small_at_head     at the head's segment: under SeatShows and the head's own part "small"

Limits. 𝔇.H IS A FREE FIELD OF MgData: AT A FREE H NOTHING TIES base TO THE TIE: so the field is
stated at hidAtSeat. SeatShows IS A PREMISE: that the sizes s m are those of the state's plan, and
that the seats' entries, as segment m reads them, are cellsAt's cells at the plan's symbol arrays:
shown nowhere here; no member. 𝔇.headPart is a letter. Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAll
import Johnson.Meaning.PlanesTieK8Cells
import Johnson.Goal.Meaning.HidRiders

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8
open OnBytes OnBytes.Model
open Cb.Pv.Tail (Size Syms Base baseAt_of_packs)
open OnBytes.Tie.Pv.Tail (sizeOf_uniq)
open _root_.Meaning (symAt ownOf smallM_mgOf attSmall_maOf)
open _root_.Meaning.Reads (symsA)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.Sound (MgData mgAll mgAll_constr cellsAt CellsQ MsgT readAt SeatsNamed
  GroupsSeated oneDec)
open VerifiableInference.OnPublicFiles (headLink)

/-- **The tie gives Base of the symbols that the table of cells shows.** -/
theorem base_of_tie {tl : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (h : TieOf tl A) :
    Base (symsA tl A) := by
  obtain ⟨a, h1, h2, _⟩ := h
  exact ⟨fun μ c i => a μ.val i.val c.val,
    baseAt_of_packs (K := Cb.Gl.E) (s := (Tie.Pv.Tail.sizeOf tl).size) Cb.Gl.p (sizeOf_uniq tl)
      (y := symsA tl A) (fun μ c i => h1 μ μ.2 c c.2 i i.2) fun μ c i' => h2 μ μ.2 c c.2 i' i'.2⟩

/-- **Of the symbols read at seats**, where the sizes are the plan's and the seats show the table's
cells. -/
theorem base_at_seat {tl : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (σ : Size)
    (st : Fin σ.NM → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : _root_.Meaning.Msgs)
    (hσ : σ = (Tie.Pv.Tail.sizeOf tl).size)
    (hy : ∀ (μ : Fin σ.NM) (r c : ℕ), r < Alg.symRows (σ.m μ) → c < σ.k μ →
      msg (st μ r c).1 false (st μ r c).2.1 (st μ r c).2.2 = A (tl.gtTree.getD μ 0) r c)
    (h : TieOf tl A) : Base (symAt σ st msg) := by
  subst hσ
  have e : symAt (Tie.Pv.Tail.sizeOf tl).size st msg = symsA tl A := by
    funext μ r c
    exact hy μ r c r.2 c.2
  rw [e]
  exact base_of_tie h

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **What the part "small" says at the composed meaning**, written out. -/
theorem constr_small_iff (m : ℕ) (a : P × S) (y : Strs) (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).constr m .small a y w ↔
      𝔇.H.base m w ∧ ∀ M (i : Sound.IdxQ), 𝔇.decT y.cell a = some M →
        VerifiableInference.OnPublicFiles.Flat.Holds M i →
        if m = headLink X then 𝔇.headPart .small i a y w
        else if m % 2 = 0 then
          P5J.partG X i (𝔇.put (𝔇.H.req a) (𝔇.H.hid w).tok).val (𝔇.H.hid w).MG (m / 2) .small
        else P5J.partA (OnBytes.Road.Hd.shapeA X (m / 2)) ((𝔇.H.hid w).MA (m / 2)) .small := by
  rw [mgAll_constr]
  unfold P5J.constrQAt
  rw [if_neg (show ¬ ((.small : P5J.TPart) = .lookDigits) by decide)]
  exact ⟨fun h => ⟨h.1 rfl, h.2⟩, fun h => ⟨fun _ => h.1, h.2⟩⟩

/-- **So the field gives base**, at whatever 𝔇. -/
theorem base_of_small (m : ℕ)
    (F : ∀ z s y w, TieAt (cellsAt 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m (z, s)) s w →
      (mgAll 𝔇 Mg).constr m .small (z, s) y w) (z : P) (s : S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT)
    (h : TieAt (cellsAt 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m (z, s)) s w) : 𝔇.H.base m w :=
  ((constr_small_iff 𝔇 Mg m (z, s) y w).1 (F z s y w h)).1

/-- **The sentence on the layout**, at segment m, a state and a witness: the sizes are those of the
state's plan, and the seats' entries, as segment m reads them, are the table's cells at the plan's
symbol arrays. -/
def SeatShows (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (m : ℕ) (a : P × S)
    (w : Wit (CellsQ rows cols) Tok MsgT) : Prop :=
  ∀ tl, a.2.tl? = some tl → s m = (Tie.Pv.Tail.sizeOf tl).size ∧
    ∀ (μ : Fin (s m).NM) (r c : ℕ), r < Alg.symRows ((s m).m μ) → c < (s m).k μ →
      readAt 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m w (seat m μ r c).1 false (seat m μ r c).2.1 (seat m μ r c).2.2 =
        cellsAt 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m a w (tl.gtTree.getD μ 0) r c

variable {s : ℕ → Size} {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ}
  {tokV : Tok → Fin Inst.Model.ppref.V} {req : P × S → P5J.TReq}
  {dec : P × S → Strs → Option (Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE)}
  {hN : SeatsNamed 𝔇.arr 𝔇.N s seat} {hG : GroupsSeated 𝔇.ms 𝔇.N}
  (hH : 𝔇.H = P5J.hidAtSeat X 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N s seat tokV req dec hN hG)
include hH

/-- base, at hidAtSeat, from the tie. -/
theorem base_at_nine (m : ℕ) (z : P) (st : S) (w : Wit (CellsQ rows cols) Tok MsgT)
    (hL : SeatShows 𝔇 s seat m (z, st) w)
    (h : TieAt (cellsAt 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m (z, st)) st w) : 𝔇.H.base m w := by
  obtain ⟨tl, htl, ht⟩ := h
  obtain ⟨hs, hy⟩ := hL tl htl
  rw [hH]
  exact base_at_seat (s m) (seat m) (readAt 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m w) hs hy ht

/-- **THE FIELD "small" AT THE COMPOSED MEANING, AT hidAtSeat**: at every segment below 24 that is
not the head's. -/
theorem small_at_seat (h0 : ∀ k < 25, (0 : ℤ) < ((s k).beta : ℤ))
    (h2 : ∀ k < 25, 2 * ((s k).beta : ℤ) ≤ 2 ^ 18) (m : ℕ) (hm : m < 24) (hd : m ≠ headLink X)
    (z : P) (st : S) (y : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (hL : SeatShows 𝔇 s seat m (z, st) w)
    (h : TieAt (cellsAt 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m (z, st)) st w) :
    (mgAll 𝔇 Mg).constr m .small (z, st) y w := by
  refine (constr_small_iff 𝔇 Mg m (z, st) y w).2 ⟨base_at_nine 𝔇 hH m z st w hL h, ?_⟩
  intro M i _ _
  rw [if_neg hd, hH]
  split
  · exact smallM_mgOf _ h0 h2 X.y (g := m / 2) (by omega)
  · exact attSmall_maOf _ h0 h2 X (g := m / 2) (by omega)

/-- **At the head's segment**: under the head's own part. -/
theorem small_at_head (z : P) (st : S) (y : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (hL : SeatShows 𝔇 s seat (headLink X) (z, st) w)
    (hHead : ∀ i, 𝔇.headPart .small i (z, st) y w)
    (h : TieAt (cellsAt 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N (headLink X) (z, st)) st w) :
    (mgAll 𝔇 Mg).constr (headLink X) .small (z, st) y w := by
  refine (constr_small_iff 𝔇 Mg _ (z, st) y w).2 ⟨base_at_nine 𝔇 hH _ z st w hL h, ?_⟩
  intro M i _ _
  rw [if_pos rfl]
  exact hHead i

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.base_of_tie
#print axioms VerifiableInference.Desc.First.K8.base_at_seat
#print axioms VerifiableInference.Desc.First.K8.constr_small_iff
#print axioms VerifiableInference.Desc.First.K8.base_of_small
#print axioms VerifiableInference.Desc.First.K8.base_at_nine
#print axioms VerifiableInference.Desc.First.K8.small_at_seat
#print axioms VerifiableInference.Desc.First.K8.small_at_head
