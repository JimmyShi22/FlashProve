-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/PinKeptBack.lean (kind K10): A PIN AT A KEPT MEMBER RIDES BACKWARD
ACROSS
K10's STEP, TO THE VALUE OF THE TABLE's EXTRACTOR. K10's extractor lays its group's seats BUT THE
KEPT
ONES (`laysSeats`, Johnson/Desc/First/Borders.lean); the items that K10 takes in ask a pin at the
kept
tenants too: there the pin in front comes from "pinKept" behind. Definitions, statements and proofs:
calls.

  `pin_back`: GENERAL: `PinAt` reads the state through the sample's reader alone, the strings
through
    the columns of the member's one tree, the witness through the member's number and seat. So: the
    reader answers alike at the two states; the strings stay below base; the member's tree lies
    below base; its number is none of mine's; its seat none of mine's or minePad's: THEN a pin at
    (b, y', w) gives the pin at (a, y, extAt .. mine minePad .. a y w).
  `keptApartB arr N links p`: A TEST WITH CODE ON THE PLAN: no kept seat has the number of a seat
that
    the sub-protocol at p lays. IT BEARS LOAD: two seats can have one number (the copies of one
    message); had a kept seat a laid seat's number, the extractor would overwrite the message at
    that number, and the sentence below would be false.
  `keptLowB N l base`: a test with code: every kept tenant's tree lies below base.
  `seat_not_laid`: by the table's own text: at a place of the kind K10 a kept seat is among neither
    the laid seats nor the seats whose pads alone are laid.
  `pin_kept_back`: **at a place p of the kind K10 of segment l, at the table's own `mineAt` and
    `minePadAt`: seatOf x ∈ N.keptOf l · the two tests · the reader answers alike · Stays base y y'
⊢
    PinAt .. x .. b y' w → PinAt .. x .. a y (extAt .. a y w).**
  `pin_kept_behind`: the same from `Behind F base y y'` (T2AtPiece.lean).
Limits. "The reader answers alike at the two states" is a premise: at the named reader, along K10's
step, it is `k10_smpNamed` (OracleAsksK10.lean), which this file does not import. The
two tests have run at no data. No soundness statement.

-/
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.Sound.ReadsTreeAt
import Johnson.Top.H0.Walk.StaysBehind
import Johnson.Desc.First.Close.Law.T2AtPiece

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers ModelPart laysSeats laysPads)
open Johnson.Desc.First.Walk.Tied (Stays stays_behind)
open _root_.Run (ckP)

variable (cs : OnBytes.Codes) {Xi A Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → A → Option Cells) (c₀ : Cells)

/-- **A pin rides backward to the extractor's value.** -/
theorem pin_back (mine minePad : List Mem) (cellsToo : Bool) (tokNew : Option Tok) (x : Mem)
    (a b : A) (y y' : Strs) (base : ℕ) (hsm : smp b x.1 x.2 = smp a x.1 x.2)
    (hst : Stays base y y') (hj : (seatOf x).1 < base)
    (hn : numOf arr x ∉ mine.map (numOf arr)) (hs : seatOf x ∉ (mine ++ minePad).map seatOf)
    (w : Wit Cells Tok MsgT)
    (h : PinAt G cs x.1.l x.1.seat (fun q => smp q x.1) arr x.2 b y' w) :
    PinAt G cs x.1.l x.1.seat (fun q => smp q x.1) arr x.2 a y
      (extAt cs G arr smp decT c₀ mine minePad cellsToo tokNew a y w) := by
  have h1 : PinAt G cs x.1.l x.1.seat (fun q => smp q x.1) arr x.2 b y w :=
    pinAt_col G cs x.1.l x.1.seat (fun q => smp q x.1) arr y' y x.2 b w
      (fun c => (hst.2 _ c hj).symm) h
  obtain ⟨zz, hz, hsh, hd⟩ := h1
  have h2 : PinAt G cs x.1.l x.1.seat (fun q => smp q x.1) arr x.2 a y w :=
    ⟨zz, hsm.symm.trans hz, hsh, hd⟩
  exact pin_congr cs G arr smp x.1 x.2 a y w _
    (extAt_other cs G arr smp decT c₀ mine minePad cellsToo tokNew a y w _ hn)
    (extAt_other_pad cs G arr smp decT c₀ mine minePad cellsToo tokNew a y w _ _ hs) h2

/-- A test with code on the plan: no kept seat has the number of a seat that is laid at p. -/
def keptApartB (N : Numbers) (links : List ModelPart) (p : Place) : Bool :=
  (N.keptOf (p.link.getD 0)).all fun t =>
    (laysSeats N links p).all fun u => arr t.1 t.2 != arr u.1 u.2

/-- A test with code: every kept tenant's tree lies below base. -/
def keptLowB (N : Numbers) (l base : ℕ) : Bool := (N.keptOf l).all fun t => decide (t.1 < base)

/-- At a place of the kind K10 a kept seat is not laid. -/
theorem seat_not_laid (N : Numbers) (links : List ModelPart) (p : Place) (hK : p.kind = .K10)
    (t : ℕ × ℕ) (ht : t ∈ N.keptOf (p.link.getD 0)) :
    t ∉ laysSeats N links p ∧ t ∉ laysPads N links p := by
  constructor
  · intro h
    unfold laysSeats at h
    split at h
    · cases h
    · rw [hK] at h
      have h2 := (List.mem_filter.1 h).2
      have h3 : (N.keptOf (p.link.getD 0)).contains t = true := List.contains_iff_mem.2 ht
      rw [h3] at h2
      cases h2
  · intro h
    unfold laysPads at h
    split at h
    · cases h
    · rw [hK] at h
      cases h

variable (ms : List Mem)

/-- **THE KEPT MEMBER's PIN, BACKWARD ACROSS THE STEP, AT THE TABLE's OWN EXTRACTOR.** -/
theorem pin_kept_back (N : Numbers) (links : List ModelPart) (p : Place) (hK : p.kind = .K10)
    (cellsToo : Bool) (tokNew : Option Tok) (x : Mem)
    (hx : seatOf x ∈ N.keptOf (p.link.getD 0)) (base : ℕ)
    (T1 : keptApartB arr N links p = true) (T2 : keptLowB N (p.link.getD 0) base = true)
    (a b : A) (y y' : Strs) (hsm : smp b x.1 x.2 = smp a x.1 x.2) (hst : Stays base y y')
    (w : Wit Cells Tok MsgT)
    (h : PinAt G cs x.1.l x.1.seat (fun q => smp q x.1) arr x.2 b y' w) :
    PinAt G cs x.1.l x.1.seat (fun q => smp q x.1) arr x.2 a y
      (extAt cs G arr smp decT c₀ (mineAt ms N links p) (minePadAt ms N links p) cellsToo tokNew
        a y w) := by
  obtain ⟨n1, n2⟩ := seat_not_laid N links p hK _ hx
  refine pin_back cs G arr smp decT c₀ _ _ cellsToo tokNew x a b y y' base hsm hst
    (of_decide_eq_true (List.all_eq_true.1 T2 _ hx)) ?_ ?_ w h
  · intro hm
    obtain ⟨x', hx', e⟩ := List.mem_map.1 hm
    have hs' : (laysSeats N links p).contains (x'.1.seat x'.2) = true :=
      (List.mem_filter.1 hx').2
    have h3 := List.all_eq_true.1 (List.all_eq_true.1 T1 _ hx) _ (List.contains_iff_mem.1 hs')
    exact absurd e.symm (by simpa [numOf, seatOf] using h3)
  · intro hm
    obtain ⟨x', hx', e⟩ := List.mem_map.1 hm
    rcases List.mem_append.1 hx' with hx' | hx'
    · have hs' : (laysSeats N links p).contains (x'.1.seat x'.2) = true :=
        (List.mem_filter.1 hx').2
      exact n1 (e ▸ List.contains_iff_mem.1 hs')
    · have hs' : (laysPads N links p).contains (x'.1.seat x'.2) = true :=
        (List.mem_filter.1 hx').2
      exact n2 (e ▸ List.contains_iff_mem.1 hs')

/-- The same, from the readings of strings in front of and behind a stage at that base. -/
theorem pin_kept_behind {F : Frame} (N : Numbers) (links : List ModelPart) (p : Place)
    (hK : p.kind = .K10) (cellsToo : Bool) (tokNew : Option Tok) (x : Mem)
    (hx : seatOf x ∈ N.keptOf (p.link.getD 0)) (base : ℕ)
    (T1 : keptApartB arr N links p = true) (T2 : keptLowB N (p.link.getD 0) base = true)
    (a b : A) (y y' : Strs) (hsm : smp b x.1 x.2 = smp a x.1 x.2) (hB : Behind F base y y')
    (w : Wit Cells Tok MsgT)
    (h : PinAt G cs x.1.l x.1.seat (fun q => smp q x.1) arr x.2 b y' w) :
    PinAt G cs x.1.l x.1.seat (fun q => smp q x.1) arr x.2 a y
      (extAt cs G arr smp decT c₀ (mineAt ms N links p) (minePadAt ms N links p) cellsToo tokNew
        a y w) := by
  obtain ⟨ds, u, τ, rfl, rfl⟩ := hB
  exact pin_kept_back cs G arr smp decT c₀ ms N links p hK cellsToo tokNew x hx base T1 T2 a b _ _
    hsm (stays_behind (ckP .two) F base ds u τ) w h

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.pin_back
#print axioms VerifiableInference.Desc.First.Close.seat_not_laid
#print axioms VerifiableInference.Desc.First.Close.pin_kept_back
#print axioms VerifiableInference.Desc.First.Close.pin_kept_behind
