-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SigRides.lean: THE FIELDS THAT MeaningSig.lean FILLS RIDE PAST A PIECE, SEAT BY
SEAT. Theorems, proved. No kind is named.

Why. A table's promise at the border behind a block asks "shown", "no collision" and "held" again at
every seat whose pin stays open. Past a block in front of which the seat's tree was sent these ride,
whatever the block's kind. The members' own riding is proved (`wordStays`, StringsStay.lean;
`pinStays`, MsgSig.lean; `rides`, SendLaw.lean: under `Fenced` and `SmpStays` of a whole list). Here
it is said of the table's items, at ONE seat (j, t), under what that seat alone asks.
  `shownJT_rides` (proved): j < p.base; the piece says yes from a to b: `shownJT` at (j, t) of the
    strings in front gives it of the strings behind. (And back: `shownJT_rides_iff`.)
  `noCollJT_rides` (proved): moreover the record behind holds, for each member of ms that sits at
    (j, t), the sample that the record in front holds: `noCollJT` rides.
  `pinJT_rides` (proved): under the same: `pinJT` rides, at every witness.
  `smpHeld_rides` (proved): the record behind has the statement and the book of the record in front:
    `smpHeld` is the same Bool.
Limits. j < p.base (the seat's tree was sent in front of the piece) and the samples' staying are
premises. Nothing is proved of any block. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Sound.SendLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  {C : CK} {Fr : Frame} {Cl W : Type}

theorem shownAt_ridesSig (p : Piece C Fr A Cl W) (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) (x : Mem) (hx : (x.1.seat x.2).1 < p.base) :
    ShownAt G cs x.1.l x.1.seat (strsOf Fr b.2) x.2 ↔
      ShownAt G cs x.1.l x.1.seat (strsOf Fr a.2) x.2 := by
  rw [out_behind p a b τ hb]
  unfold ShownAt
  rw [wordStays Xi G C Fr p.base p.ds a.2 τ (x.1.seat x.2).1 (x.1.seat x.2).2 hx]

theorem shownJT_rides_iff (p : Piece C Fr A Cl W) (ms : List Mem) (j t : ℕ) (hj : j < p.base)
    (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (hb : p.ior.red.out a τ = some b) :
    shownJT cs G ms j t (strsOf Fr b.2) ↔ shownJT cs G ms j t (strsOf Fr a.2) := by
  have key : ∀ x ∈ ms, SitsAt x j t →
      (ShownAt G cs x.1.l x.1.seat (strsOf Fr b.2) x.2 ↔
        ShownAt G cs x.1.l x.1.seat (strsOf Fr a.2) x.2) := by
    intro x _ hs
    refine shownAt_ridesSig cs G p a b τ hb x ?_
    have e : x.1.seat x.2 = (j, t) := hs
    rw [e]
    exact hj
  unfold shownJT
  exact ⟨fun h => ⟨h.1, fun x hx hs => (key x hx hs).1 (h.2 x hx hs)⟩,
    fun h => ⟨h.1, fun x hx hs => (key x hx hs).2 (h.2 x hx hs)⟩⟩

/-- **"shown" rides.** -/
theorem shownJT_rides (p : Piece C Fr A Cl W) (ms : List Mem) (j t : ℕ) (hj : j < p.base)
    (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (hb : p.ior.red.out a τ = some b)
    (h : shownJT cs G ms j t (strsOf Fr a.2)) : shownJT cs G ms j t (strsOf Fr b.2) :=
  (shownJT_rides_iff cs G p ms j t hj a b τ hb).2 h

/-- A member's pin and "no collision" past the piece, at that member alone. -/
theorem member_rides (p : Piece C Fr A Cl W) (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) (x : Mem) (hx : (x.1.seat x.2).1 < p.base)
    (hs : smp b.1 x.1 x.2 = smp a.1 x.1 x.2) :
    (∀ w : Wit Cells Tok MsgT,
      PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 b.1 (strsOf Fr b.2) w ↔
        PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a.1 (strsOf Fr a.2) w) ∧
      (CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 b.1 (strsOf Fr b.2) ↔
        CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a.1 (strsOf Fr a.2)) := by
  have hw := wordsStay G cs x.1.l x.1.seat C Fr p.base p.ds a.2 τ x.2 hx
  have hsh := shownAt_ridesSig cs G p a b τ hb x hx
  rw [out_behind p a b τ hb] at hsh ⊢
  unfold PinAt CfAt
  simp only [hs, hw, hsh]
  exact ⟨fun _ => trivial, trivial⟩

/-- **"no collision" rides.** -/
theorem noCollJT_rides (p : Piece C Fr A Cl W) (ms : List Mem) (j t : ℕ) (hj : j < p.base)
    (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (hb : p.ior.red.out a τ = some b)
    (hS : ∀ x ∈ ms, SitsAt x j t → smp b.1 x.1 x.2 = smp a.1 x.1 x.2)
    (h : noCollJT cs G smp ms j t a.1 (strsOf Fr a.2)) :
    noCollJT cs G smp ms j t b.1 (strsOf Fr b.2) := by
  intro x hx hs
  have e : x.1.seat x.2 = (j, t) := hs
  exact ((member_rides (Cells := Unit) (Tok := Unit) cs G (fun _ _ => 0) smp p a b τ hb x
    (by rw [e]; exact hj) (hS x hx hs)).2).2 (h x hx hs)

/-- **The pin rides**, at every witness. -/
theorem pinJT_rides (p : Piece C Fr A Cl W) (ms : List Mem) (j t : ℕ) (hj : j < p.base)
    (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (hb : p.ior.red.out a τ = some b)
    (hS : ∀ x ∈ ms, SitsAt x j t → smp b.1 x.1 x.2 = smp a.1 x.1 x.2)
    (w : Wit Cells Tok MsgT) :
    pinJT cs G arr smp ms j t b.1 (strsOf Fr b.2) w ↔
      pinJT cs G arr smp ms j t a.1 (strsOf Fr a.2) w := by
  have key : ∀ x ∈ ms, SitsAt x j t →
      (PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 b.1 (strsOf Fr b.2) w ↔
        PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a.1 (strsOf Fr a.2) w) := by
    intro x hx hs
    have e : x.1.seat x.2 = (j, t) := hs
    exact (member_rides cs G arr smp p a b τ hb x (by rw [e]; exact hj) (hS x hx hs)).1 w
  unfold pinJT
  exact ⟨fun h => ⟨h.1, fun x hx hs => (key x hx hs).1 (h.2 x hx hs)⟩,
    fun h => ⟨h.1, fun x hx hs => (key x hx hs).2 (h.2 x hx hs)⟩⟩

end

/-- **"held" rides**: it reads the statement and the book alone. -/
theorem smpHeld_rides (st st' : OnBytes.Statement) (book book' : OnBytes.TreeBook) (j t : ℕ)
    (h1 : st' = st) (h2 : book' = book) : smpHeld st' book' j t = smpHeld st book j t := by
  rw [h1, h2]

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.shownJT_rides
#print axioms VerifiableInference.Desc.Sound.noCollJT_rides
#print axioms VerifiableInference.Desc.Sound.pinJT_rides
