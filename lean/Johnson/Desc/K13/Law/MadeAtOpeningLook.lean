-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/MadeAtOpeningLook.lean: THREE MORE OF THE PUBLIC ITEMS THAT COME AT THE FIRST
SEGMENT's OPENING ARE MADE BY THE BLOCK: "the link is fresh" and "the look-up's condition in front
of its block", in the tests of the layer that lays them (`linkFreshC`, `lookInC`:
Johnson/Desc/First/Look/K3FillCode.lean; `k3OnIn`: K3Borders.lean). Statements
with their proofs. What the joined block leaves (other files' lemmas on the frame's step "link
0: opened", Johnson/Top/H0/Walk/): the open link has the number 0 and the plan's table of arrays;
the ledger is the fresh one; the link's own state is the plan's first; what the chain's state owes
of rows is as the sending left it.
  `madeSix`: the five items of which MadeAtOpening.lean and this file show the making.
  `openingZero_fresh`: the four facts behind a yes.
  `openingZero_linkFresh`: `linkFreshC d 0` holds behind, WHERE the plan's first state has heard
    nothing and the layer's table of arrays at 0 is the block's.
  `openingZero_lookIn`: `lookInC d 0 dg` holds behind, WHERE the layer has a place p for that
    look-up with a shape, the look-up on the calls; the fresh ledger's next number is p's first;
    p's scalars fit in the ledger's room; p's link is 0; the table of arrays as above. EACH OF
    THESE IS A NAMED PREMISE ON THE PLAN's VALUES. That nothing is heard at its seat and no row
    waits behind the block is shown (`openingZero_unheard`).
  `openingZero_live`, `openingZero_liveIs`: the look-ups' name "frame.liveIs" at segment 0
  (`liveIsC`)
    holds behind, where "in order" as our layer lays it holds behind at the same shape and layout.
What is not claimed. These premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.MadeAtOpening
import Johnson.Desc.First.Look.K3FillCode
import Johnson.Desc.K13.Law.FillK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar startFork)
open Johnson.Desc.First.Walk.Law (SizedAt openLayZero_ok openLayZero_tl)
open Johnson.Desc.First.Walk.Tied (openLayZero_eq)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (K3Data linkFreshC lookInC liveIsC placeAt)

/-- The five public items of which our files show that the sub-protocol makes them: the table's own
four and the look-ups' name "frame.liveIs" at segment 0. -/
def madeSix : List First.Pub := madeG ++ [.more (some 0) "frame.liveIs"]

section
variable {Cl : Type} {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
  {fvs : List Bool} {kCol : ℕ}

/-- **What the joined block leaves of the link.** -/
theorem openingZero_fresh {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    (∃ L, t.link? = some L ∧ L.link = 0 ∧ L.arrayOf = X.X.arrayOf) ∧
      t.fork? = some (startFork X.X X.ns) ∧ t.tl? = some X.tl₀ := by
  obtain ⟨s₁, g₁, _, h2⟩ := K1.openingZero_mid h
  obtain ⟨_, _, _, _, _, hl, hf, _⟩ := openLayZero_ok h2
  exact ⟨⟨_, hl, rfl, rfl⟩, hf, openLayZero_tl h2⟩

/-- Behind the block the look-up on the calls is not heard yet. -/
theorem openingZero_unheard {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    t.lookHeard? = none := by
  obtain ⟨s₁, g₁, _, h2⟩ := K1.openingZero_mid h
  obtain ⟨a, e⟩ := openLayZero_eq h2
  rw [e]
  rfl

/-- "The link is fresh" behind the block. -/
theorem openingZero_linkFresh {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (d : K3Data) (h0 : X.tl₀.heard = none) (ha : d.arrayOf.getD 0 #[] = X.X.arrayOf) :
    linkFreshC d 0 t = true := by
  obtain ⟨⟨L, hL, _, hA⟩, _, htl⟩ := openingZero_fresh h
  unfold linkFreshC
  rw [htl, hL]
  simp [h0, hA, ha]

/-- "The look-up's condition in front of its block" behind the block. -/
theorem openingZero_lookIn {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (d : K3Data) (dg : Bool) (p : First.Look.P) (sh : Forest.Shape)
    (hp : placeAt d.X 0 dg = some p) (hsh : p.shape = some sh) (hdig : p.digits = false)
    (hnext : (startFork X.X X.ns).next = p.first)
    (hroom : p.first + Forest.elems sh ≤ X.ns) (hlink : p.link = 0)
    (ha : d.arrayOf.getD 0 #[] = X.X.arrayOf) : lookInC d 0 dg t = true := by
  obtain ⟨⟨L, hL, hL0, hA⟩, hf, _⟩ := openingZero_fresh h
  have hheard : (Desc.K3.heardAt p.digits t).isNone = true := by
    unfold Desc.K3.heardAt
    rw [hdig, if_neg (by simp), openingZero_unheard h]
    rfl
  have hwait : First.Tape.RowsOwed.noneWaits t.rowsOwed = true := by
    rw [(K1.openingZero_rec h).2.2.2.1]
    rfl
  obtain ⟨F, hF, hs, hn, hfree⟩ := openingZero_sized h
  obtain rfl : F = startFork X.X X.ns := Option.some.inj (hF.symm.trans hf)
  have hfreeB : Desc.K3.freeB (startFork X.X X.ns) p.first (Forest.elems sh) = true := by
    unfold Desc.K3.freeB
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.not_eq_true']
    refine ⟨by rw [hn]; exact hroom, fun j hj => ?_⟩
    have hlt : p.first + j < (startFork X.X X.ns).gotF.size := by
      rw [hs.got, hn]
      omega
    have e := hfree (p.first + j)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt] at e ⊢
    exact e
  have hsized : Desc.K3.sizedB (startFork X.X X.ns) = true := by
    unfold Desc.K3.sizedB
    simp [hs.vp, hs.mf, hs.got]
  unfold lookInC
  rw [hp]
  simp only [Option.any_some, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold Desc.K3.k3OnIn
    rw [hsh]
    simp only [Bool.and_eq_true]
    refine ⟨⟨hheard, hwait⟩, ?_⟩
    rw [hf]
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨hnext, hsized⟩, hfreeB⟩
  · rw [hL]
    simp [hL0, hlink, hA, ha]

/-- Behind the block the live state of the calls is the walk's own. -/
theorem openingZero_live {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    t.live = t.check := by
  obtain ⟨s₁, g₁, _, h2⟩ := K1.openingZero_mid h
  obtain ⟨_, _, _, _, _, hl, _, hc, _⟩ := openLayZero_ok h2
  unfold S.live
  rw [hl, hc]

/-- "The live request's shape and its rows' layout are the plan's" behind the block, WHERE "in
order" as our layer lays it holds behind, at the layer's own shape and layout. -/
theorem openingZero_liveIs {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (d : K3Data) (cs : Codes) (hin : inOrderK13 cs d.shape d.layout t = true) :
    liveIsC d t = true := by
  unfold inOrderK13 at hin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
  unfold liveIsC
  rw [openingZero_live h]
  simp [hin.1.2, hin.2]

end

end VerifiableInference.Desc.K13.Law
