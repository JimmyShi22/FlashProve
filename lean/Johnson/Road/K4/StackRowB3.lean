-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackRowB3.lean: the record BFields (Johnson/Road/K4/StackRowB2.lean) of every pair
of the verifier's placed list of panels and the library's list, from the records that other files
have of these pairs.

Main names:
  `placed_off`: each placed panel begins where the library places its panel, if the bits agree
    pair by pair (placed_offP, Johnson/Road/K4/PlaceOff.lean, said of pairs).
  `bfields_of`: BFields of one pair, from EndFields (Johnson/Road/K4/EndFields.lean), the bits, the
    place, the verifier's passed test and the number of the first weight claim.
  `f2_and`: two relations on the same two lists, in one.
  `placed_bfields`: BFields of every pair.
Limits. Premises: EndFields and the bits of every pair; that stackEnd has returned on the placed
list; that the state's lookup point is the letter z of EndFields; v0Of: the numbers of the panels'
first weight claims, a letter with the premise that they are the verifier's. Identities on public
data: nothing on a world, on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.StackRowB2
import Johnson.Road.K4.EndFields
import Johnson.Road.K4.PanelsBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World)
open OnBytes.Model.Layer (SBlk Lay StackEnd stackEnd placePanels)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Pan pans offP)
open Cb.Pv.Lay.At (InnPar0 nP)

/-- Two relations on the same two lists, in one. -/
theorem f2_and {α β : Type} {R S : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → List.Forall₂ S l l' → List.Forall₂ (fun a b => R a b ∧ S a b) l l'
  | _, _, .nil, .nil => .nil
  | _, _, .cons h1 t1, .cons h2 t2 => .cons ⟨h1, h2⟩ (f2_and t1 t2)

/-- Each placed panel begins where the library places its panel. -/
theorem placed_off (D : Dim) (bl : Array SBlk)
    (h2 : List.Forall₂ (fun (b : SBlk) (pn : Pan) => b.w = pn.wid D) (placePanels bl).1.toList
      (pans D)) :
    List.Forall₂ (fun (b : SBlk) (pn : Pan) => b.off = offP D pn) (placePanels bl).1.toList
      (pans D) := by
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h2
  have hsz : bl.size = (pans D).length := by
    rw [← hlen, Array.length_toList, placePanels_size]
  have get : ∀ i (h : i < (placePanels bl).1.toList.length),
      (placePanels bl).1.toList.get ⟨i, h⟩ = (placePanels bl).1.getD i {} := by
    intro i h
    have h' : i < (placePanels bl).1.size := by simpa using h
    simp [Array.getD, h']
  have hw : ∀ j (h : j < (pans D).length), wOf bl j = ((pans D)[j]).wid D := by
    intro j h
    have h1 : j < (placePanels bl).1.toList.length := by rw [hlen]; exact h
    have e := hget j h1 h
    rw [get j h1, ((placePanels_apart bl).1 j (by rw [hsz]; exact h)).1] at e
    exact e
  refine List.forall₂_iff_get.mpr ⟨hlen, fun i k1 k2 => ?_⟩
  rw [get i k1]
  exact placed_offP D bl hsz hw k2

variable {K : Type} [Field K] [Fintype K] [scl : Scl] {ρ : Reading K} {P : InnPar0 K} {st : P.St}

/-- **BFields of one pair.** -/
theorem bfields_of {y : Lay} {sh : Array E} {z : ℕ → K} {b : SBlk} {pn : Pan}
    (En : EndFields ρ y sh P.D z b pn) (hz : st.z = z) (bw : b.w = pn.wid P.D)
    (bwy : b.wy = pn.wcol P.D) (off : b.off = offP P.D pn) {rs : Array E} {lam : ℕ}
    (ok : OnBytes.Model.eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) = true) {v0 : ℕ}
    (hv0 : pn.weight = true → b.v0 = some v0) : BFields P st ρ rs lam b pn v0 where
  bw := bw
  bwy := bwy
  off := by
    rw [off, bw]
    rfl
  ok := ok
  tri := En.tri
  v0s := hv0
  v0n := fun hw => ⟨En.v0n hw, by
    rw [En.virt]
    cases pn <;> first | rfl | exact absurd hw (by simp [Pan.weight])⟩
  ni := En.ni
  facV := fun h3 k hk i hi => by
    rw [En.virt] at hk
    cases pn with
    | D =>
      rw [En.dB rfl i hi, ← hz]
      rfl
    | Dr l => exact absurd h3 (by simp [Pan.three])
    | _ => exact absurd hk (by simp [virtOf])
  facN := fun h3 hk i _ => by
    rw [En.virt] at hk
    cases pn with
    | D => exact absurd hk (by simp [virtOf])
    | Dr l => exact absurd h3 (by simp [Pan.three])
    | _ => rfl

/-- **BFields of every pair of the placed list and the library's list.** -/
theorem placed_bfields {y : Lay} {sh : Array E} {z : ℕ → K} {bl : Array SBlk}
    (FE : List.Forall₂ (fun b pn => EndFields ρ y sh P.D z b pn) (placePanels bl).1.toList
      (pans P.D))
    (FW : List.Forall₂ (fun (b : SBlk) (pn : Pan) => b.w = pn.wid P.D ∧ b.wy = pn.wcol P.D)
      (placePanels bl).1.toList (pans P.D))
    (hz : st.z = z) {rs om H1 V : Array E} {lam : ℕ} {shA shB : E} {s' : StackEnd}
    (hst : stackEnd y (placePanels bl).1 rs lam om H1 V shA shB = some s') (v0Of : Pan → ℕ)
    (F0 : List.Forall₂ (fun (b : SBlk) (pn : Pan) => pn.weight = true → b.v0 = some (v0Of pn))
      (placePanels bl).1.toList (pans P.D)) :
    List.Forall₂ (fun b pn => BFields P st ρ rs lam b pn (v0Of pn)) (placePanels bl).1.toList
      (pans P.D) := by
  have FO := placed_off P.D bl (FW.imp fun _ _ k => k.1)
  refine (f2_mem_left (f2_and (f2_and FE FW) (f2_and FO F0))).imp fun b pn k => ?_
  obtain ⟨hm, ⟨En, bw, bwy⟩, off, hv0⟩ := k
  obtain ⟨s1, s2, hs⟩ := stackEnd_each hst b hm
  exact bfields_of En hz bw bwy off (stackEndOf_ok hs) hv0

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.placed_off
#print axioms OnBytes.Road.K4.bfields_of
#print axioms OnBytes.Road.K4.placed_bfields
