-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/PointCore.lean: THE CHANCE OF "LIN point", WITH NO KIND NAMED: a block at one
stretch whose written round reads as one typed draw of a point psi = (psi_lo, gamma); a vector V
that
the statement in front pins; a matrix and row weights that the statement in front fixes. In the form
of the rule of composition (Piece.GoodIn), by the bridge goodIn_of_count
(Johnson/Desc/K14/Law/Bridge.lean). The pattern is Johnson/Desc/K14/Law/FoldCore.lean's; the count
is
point_goodIn's (Johnson/Desc/K14/Law/PointGood.lean), which stands at the shared chain's own record.

EVERYTHING THAT READS A RECORD IS A LETTER. The lost points are of three sorts:
  the key's     BadKey a gamma: a letter ON THE STATEMENT IN FRONT (so it may read the stored
    table's
                record) and the point's high part: no more than ef points gamma (hkey).
  the point's   BadPt a psi: a letter: what the promise behind asks of the point itself: no more
                than en points (hpt). At BadPt := fun _ _ => False and en := 0 it is not there.
  the slot's    V is not the row weights applied to the matrix, and yet (Dot)'s equation holds at
                the point: no more than kCol |K| ^ (kCol - 1) points (dotTrueCatches).
THE EXTRACTOR IS A NAMED MAP lay OF THE STATEMENT IN FRONT AND THE WITNESS (it may lay what the
stored table decodes to).
  point_core    **the law.**
What is not claimed. PREMISES, each under the promise in front: hkey, hpt; two witnesses pinned by
one statement give the same vector V (hdetV); the written round reads as one typed draw, at errors
that fit; at a yes: off BadPt the promise behind holds; off BadKey every witness pinned behind
gives,
laid, a witness pinned in front at which (Dot)'s equation with the matrix itself holds at the point
drawn (G, fits, hread). All are letters: no member is shown here. A block that refuses all has
GoodIn
too. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.PointGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open Iop Prob OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run.PQ (CK)
open Iop.IOR (drawRound)

variable {K : Type} [Field K] {T Cl W : Type} {C : CK} {F : Frame}

open Classical in
/-- **The chance of "LIN point", with no kind named.** -/
theorem point_core [Fintype K] (pc : Piece C F T Cl W) (Rr kLo v : Nat)
    (lay : T × F.E.Str → W → W) (hext : ∀ a τ w, pc.ext a τ w = lay a w)
    (on on' : T × F.E.Str → Prop) (PinA PinB : T × F.E.Str → W → Prop)
    (BadKey : T × F.E.Str → (Fin v → K) → Prop)
    (BadPt : T × F.E.Str → (Fin (kLo + v) → K) → Prop)
    (g : T × F.E.Str → Nat → K) (Mat : T × F.E.Str → Nat → Nat → K)
    (V : T × F.E.Str → W → Nat → K) (ef en c : Nat)
    (hc : ef * Fintype.card K ^ kLo + (en + (kLo + v) * Fintype.card K ^ (kLo + v - 1)) ≤ c)
    (hkey : ∀ a, on a → cnt (BadKey a) ≤ ef) (hpt : ∀ a, on a → cnt (BadPt a) ≤ en)
    (hdetV : ∀ a w w', on a → PinA a w → PinA a w' → V a w = V a w')
    (G : T × F.E.Str → CarryS (uLT C pc.ds) [drawRound (Fin (kLo + v) → K)])
    (fits : ∀ a, (G a).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ a τ b, on a → pc.ior.red.out a τ = some b →
      ∃ psi, (G a).tr τ = some (((), ()), psi, ()) ∧ (¬ BadPt a psi → on' b) ∧
        (¬ BadKey a (gamOf kLo v psi) → ∀ w, PinB b w → PinA a (lay a w) ∧
          ∑ c ∈ Finset.range (2 ^ (kLo + v)), eqK (List.ofFn psi) c * V a (lay a w) c =
            ∑ y ∈ Finset.range Rr, g a y *
              ∑ c ∈ Finset.range (2 ^ (kLo + v)), eqK (List.ofFn psi) c * Mat a y c)) :
    pc.GoodIn on on'
      (fun a w => PinA a w ∧
        ∀ c < 2 ^ (kLo + v), V a w c = ∑ y ∈ Finset.range Rr, g a y * Mat a y c) PinB := by
  refine goodIn_of_count pc _ _ _ _ (Fin (kLo + v) → K) c G fits
    (fun a psi => BadKey a (gamOf kLo v psi) ∨ (BadPt a psi ∨
      ∃ w, PinA a w ∧ (¬ ∀ c < 2 ^ (kLo + v), V a w c = ∑ y ∈ Finset.range Rr, g a y * Mat a y c) ∧
        ∑ c ∈ Finset.range (2 ^ (kLo + v)), eqK (List.ofFn psi) c * V a w c =
          ∑ y ∈ Finset.range Rr, g a y *
            ∑ c ∈ Finset.range (2 ^ (kLo + v)), eqK (List.ofFn psi) c * Mat a y c)) ?_ ?_
  · intro a ha
    refine le_trans (cnt_or_le _ _) (le_trans (Nat.add_le_add ?_
      (le_trans (cnt_or_le _ _) (Nat.add_le_add (hpt a ha) ?_))) hc)
    · exact le_trans (cnt_high kLo v (BadKey a)) (Nat.mul_le_mul_right _ (hkey a ha))
    · by_cases hw0 : ∃ w0, PinA a w0 ∧
          ¬ ∀ c < 2 ^ (kLo + v), V a w0 c = ∑ y ∈ Finset.range Rr, g a y * Mat a y c
      · obtain ⟨w0, hp0, hn0⟩ := hw0
        have hgap : ∃ c < 2 ^ (kLo + v), V a w0 c ≠ ∑ y ∈ Finset.range Rr, g a y * Mat a y c := by
          push Not at hn0
          exact hn0
        refine le_trans (cnt_mono fun psi hq => ?_) (le_trans
          (le_of_eq (@cnt_eq_card_filter _ _ _ fun _ => Classical.propDecidable _))
          (dotTrueCatches Rr (kLo + v) (Mat a) (g a) (V a w0) hgap))
        obtain ⟨w, hp, _, hq⟩ := hq
        rw [hdetV a w0 w ha hp0 hp]
        exact hq
      · rw [cnt_false fun psi hq => hw0 (by obtain ⟨w, hp, hn, _⟩ := hq; exact ⟨w, hp, hn⟩)]
        exact Nat.zero_le _
  · intro a τ b ha hout
    obtain ⟨psi, htr, h1, h2⟩ := hread a τ b ha hout
    refine ⟨_, htr, fun hnl => ⟨h1 fun hb => hnl (Or.inr (Or.inl hb)), fun w hw => ?_⟩⟩
    obtain ⟨hpa, hdot⟩ := h2 (fun hb => hnl (Or.inl hb)) w hw
    rw [hext]
    refine ⟨hpa, ?_⟩
    by_contra hn
    exact hnl (Or.inr (Or.inr ⟨lay a w, hpa, hn, hdot⟩))

end Desc.K14.Law
