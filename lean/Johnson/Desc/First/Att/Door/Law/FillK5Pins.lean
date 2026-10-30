-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/FillK5Pins.lean: TOWARD A MEMBER: THE ORACLES' CLAUSES OVER THE KIND's LAY, AT THE LAYER meaningSig's OWN TERMS (Johnson/Desc/Sound/MeaningSig.lean: pinJT · noCollJT · shownJT; mgAll pays "Mg1.pin = pinJT …" and its like by rfl): K5Fill.strs ("shown and no collision ride") AND K5FillRel.pinI | ctxPin ("a pin rides back"), Johnson/Desc/First/Att/K05T2.lean | K05Riders.lean. By the five lemmas on "the same below a base" (Johnson/Desc/Sound/PinItemFill.lean), which can stand beside MeaningSig. Mathlib beneath.
-- UNDER TWO FACTS: hsmp: the layer's letter smp answers alike at the record in front of and behind the kind's lay (it reads the statement's oracles and the book: the lay leaves them): A FACT ON A LETTER: PAID BY WHOEVER FILLS smp · the tree lies below the base (j < base): seated_fenced (Johnson/Desc/Sound/PieceSeated.lean) has it for the sampled tenants of the open set.
import Johnson.Desc.First.Att.Door.Law.LayKeeps
import Johnson.Desc.Sound.PinItemFill
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Att.P (behind hear Heard SameBelow)

theorem sameBelow_symm {Fr : Frame} {base : Nat} {y y' : Fr.E.Str} (h : SameBelow Fr base y y') : SameBelow Fr base y' y :=
  ⟨h.1.symm, fun j x hj => (h.2 j x hj).symm⟩

section
variable (cs : OnBytes.Codes) {Xi Pp Cells Tok : Type} (G : FileDescription Xi) (arr : Nat → Nat → Nat)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List Mem)
  {Fr : Frame} {base : Nat} {y y' : Fr.E.Str}

/-- "Every leaf is shown" goes over, both ways, at a tree below the base. -/
theorem shownJT_below (hy : SameBelow Fr base y y') {j t : Nat} (hj : j < base)
    (h : shownJT cs G ms j t (strsOf Fr y')) : shownJT cs G ms j t (strsOf Fr y) :=
  ⟨h.1, fun x hx hs => shownAt_below G cs x.1.l x.1.seat Fr base y y' hy x.2 (by rw [hs]; exact hj) (h.2 x hx hs)⟩

/-- "No collision" goes over, where the sample is the same at the two records. -/
theorem noCollJT_below (hy : SameBelow Fr base y y') {j t : Nat} (hj : j < base) {a a' : Pp × S} (hs : smp a' = smp a)
    (h : noCollJT cs G smp ms j t a' (strsOf Fr y')) : noCollJT cs G smp ms j t a (strsOf Fr y) := by
  intro x hx hsit
  obtain ⟨z, hz, hsh, hc⟩ := h x hx hsit
  have hl : (x.1.seat x.2).1 < base := by rw [hsit]; exact hj
  refine ⟨z, by show smp a x.1 x.2 = some z; rw [← hs]; exact hz, shownAt_below G cs x.1.l x.1.seat Fr base y y' hy x.2 hl hsh, ?_⟩
  rw [← wordsOf_below G cs x.1.l x.1.seat Fr base y y' hy x.2 hl]
  exact hc

/-- A pin goes over, where the sample is the same at the two records. -/
theorem pinJT_below (hy : SameBelow Fr base y y') {j t : Nat} (hj : j < base) {a a' : Pp × S} (hs : smp a' = smp a)
    (w : Wit Cells Tok MsgT) (h : pinJT cs G arr smp ms j t a' (strsOf Fr y') w) : pinJT cs G arr smp ms j t a (strsOf Fr y) w := by
  refine ⟨h.1, fun x hx hsit => ?_⟩
  have hl : (x.1.seat x.2).1 < base := by rw [hsit]; exact hj
  have h1 := pinAt_below G cs x.1.l x.1.seat (fun z => smp z x.1) arr Fr base y y' hy x.2 hl a' w (h.2 x hx hsit)
  obtain ⟨z, hz, hsh, hd⟩ := h1
  exact ⟨z, by show smp a x.1 x.2 = some z; rw [← hs]; exact hz, hsh, hd⟩

end

section
variable {Pp Xi Cells Tok : Type} (d : K5Data) (Mg1 : Meaning Pp (Wit Cells Tok MsgT)) (π : Pp) (cs : OnBytes.Codes) (G : FileDescription Xi)
  (arr : Nat → Nat → Nat) (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List Mem)
  (hsmp : ∀ s a h Gk, s.here = .att a → smp (π, behind s a h Gk) = smp (π, s))
include hsmp

/-- **K5Fill.strs**, at one tenant below the base. -/
theorem at_strs (hshown : Mg1.shown = shownJT cs G ms) (hnc : Mg1.noColl = noCollJT cs G smp ms) {Fr : Frame} {base : Nat}
    {j t : Nat} (hj : j < base) (s : S) (a : AttOwn) (h : Heard) (Gk : Fork) (y y' : Fr.E.Str) (e : s.here = .att a)
    (hy : SameBelow Fr base y y') :
    (fillK5 d Mg1).shown j t (strsOf Fr y) ∧ (fillK5 d Mg1).noColl j t (π, s) (strsOf Fr y) →
      (fillK5 d Mg1).shown j t (strsOf Fr y') ∧ (fillK5 d Mg1).noColl j t (π, behind s a h Gk) (strsOf Fr y') := by
  show Mg1.shown j t _ ∧ Mg1.noColl j t _ _ → Mg1.shown j t _ ∧ Mg1.noColl j t _ _
  rw [hshown, hnc]
  rintro ⟨h1, h2⟩
  exact ⟨shownJT_below cs G ms (sameBelow_symm hy) hj h1,
    noCollJT_below cs G smp ms (sameBelow_symm hy) hj (hsmp s a h Gk e).symm h2⟩

/-- **K5FillRel.pinI | ctxPin**, at one tenant below the base: a pin rides back over the lay. -/
theorem at_pin_back (hpin : Mg1.pin = pinJT cs G arr smp ms) {Fr : Frame} {base : Nat} {j t : Nat} (hj : j < base) (s : S)
    (a : AttOwn) (h : Heard) (Gk : Fork) (y y' : Fr.E.Str) (w : Wit Cells Tok MsgT) (e : s.here = .att a)
    (hy : SameBelow Fr base y y') :
    (fillK5 d Mg1).pin j t (π, behind s a h Gk) (strsOf Fr y') w → (fillK5 d Mg1).pin j t (π, s) (strsOf Fr y) w := by
  show Mg1.pin j t _ _ w → Mg1.pin j t _ _ w
  rw [hpin]
  exact pinJT_below cs G arr smp ms hy hj (hsmp s a h Gk e) w

end

#print axioms sameBelow_symm
#print axioms shownJT_below
#print axioms noCollJT_below
#print axioms pinJT_below
#print axioms at_strs
#print axioms at_pin_back

end H2K5.Door
