-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/OwnAtTableR.lean: THE TABLE's WIDER DOOR TO A ROW's OWN LAW, WITH "REACHED" IN
HAND: the second form of `ownAtTableWide` (Johnson/Desc/Sound/BordersQ.lean), for whoever ends in
`SeatLawsR` (Johnson/Desc/Sound/TiedSeatR.lean). Kind-free.

Main names:
  `ownAtTableWideR`: from ANY law of the piece between a kind's own two conditions and relations,
    and the four implications of `ownAtTableWide`, EACH WITH ONE PREMISE MORE, Rch k a: the piece's
    own law between `onR … k` (the promise at border k and Rch k) and the promise at border k + 1.
    "A mark stays" and "decodes rides" are asked as before.
  `seatLawsR_of_seatLaws`: the first form of what a kind's files owe at a seat gives the second,
    for nothing: so a kind's files may be retyped place by place.

Why. A fact on the verifier's state that holds along the fold from the state at the start (the
codes, the open link's own numbers, the book's order) need not be carried as a public item past
every sub-protocol: it is taken from Rch where a law spends it.

Limits: rules over letters; Rch is a letter. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.Sound.TiedSeatR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

/-- **The wider door, second form.** -/
theorem ownAtTableWideR {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S)
    (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ) (q : Piece C Fr A Cl W)
    (o o' : A × Fr.E.Str → Prop) (R R' : A × Fr.E.Str → W → Prop) (h : q.GoodIn o o' R R')
    (ho : ∀ a, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none → o a)
    (ho' : ∀ a τ b, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → onQ N Mg links ps get (k + 1) b)
    (hR' : ∀ a τ b w, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R' b w)
    (hR : ∀ a τ b w, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R a (q.ext a τ w) → relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w))
    (hMark : ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
      (get b.1).2.failed ≠ none)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
      Mg.decodes (get b.1) (strsOf Fr b.2)) :
    q.Own (onR N Mg links ps get Rch k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (insQ links ps k) (outsQ links ps k) := by
  refine ownOfGoodInWide A Cl W Item C Fr q _ _ _ _ _ (fun a => (get a.1).2.failed ≠ none) o o' R
    R' h (fun a ha => ho a ha.1 ha.2) (fun a τ b ha => ho' a τ b ha.1 ha.2)
    (fun a τ b w ha => hR' a τ b w ha.1 ha.2) (fun a τ b w ha => hR a τ b w ha.1 ha.2) ?_
  intro a τ b ha hm hb
  refine ⟨⟨hDec a τ b hb ha.1.1, Or.inl (hMark a τ b hb hm)⟩, fun w hw => ?_⟩
  have hu : meansQ (Fr := Fr) N Mg get .unmarked b w :=
    hw .unmarked (List.mem_append_right _ (List.mem_singleton.2 rfl))
  exact hMark a τ b hb hm hu

/-- **The first form of a kind's files' four gives the second.** -/
theorem seatLawsR_of_seatLaws {Cl P W : Type} {C : CK} {Fr : Frame} {links : List ModelPart}
    {ps : List Place} {k : ℕ} {q : Piece C Fr (P × First.S) Cl W} {N : Numbers}
    {Mg : Meaning P W} (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) {Bst : Block First.S Cl}
    (H : SeatLaws links ps k q N Mg Bst) : SeatLawsR links ps k q N Mg Rch Bst :=
  ⟨fun B' hB z a ha => H.1 B' hB z a ha.1,
    fun B' hB z a τ b w i ha _ => H.2.1 B' hB z a τ b w i ha, H.2.2.1, H.2.2.2⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.ownAtTableWideR
#print axioms VerifiableInference.Desc.Sound.seatLawsR_of_seatLaws
