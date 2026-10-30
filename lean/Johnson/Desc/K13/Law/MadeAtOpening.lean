-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/MadeAtOpening.lean: TWO OF THE PUBLIC ITEMS THAT COME AT THE FIRST SEGMENT's
OPENING ARE MADE BY THE BLOCK: "a ledger is open, with its three arrays at its number of slots"
and "every slot from the next free number on is free, and the ledger has n slots", in the tests of
the layer that lays them (`First.ledgerB`, `First.freeAboveB`: Johnson/Desc/First/FillKeeper.lean).
Statements with their proofs.
Why. The table books these items at our row, because the flat list joins the frame's step "link 0:
opened" behind kind K1's sending. What that step lays is another file's lemma (`openedZeroGives`,
Johnson/Top/H0/Walk/FrameTiedRec.lean): the fresh ledger is sized, has the plan's number of slots,
and none of its slots is taken.
  `sized_ledgerB`, `sized_freeAboveB`: the two tests at any state with such a ledger.
  `openingZero_ledger`, `openingZero_freeAbove`: **behind a yes of the joined block.**
  `madeG_keeper`: so, at any filling with these two sentences, where the plan's number of slots of
    segment 0 is the block's: the two items hold behind a step.
What is not claimed. The other items that come at the block (the look-ups' window; the link is
fresh; the pile's room). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtTableFirst
import Johnson.Desc.First.FillKeeper

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open Johnson.Desc.First.Walk.Law (SizedAt)
open Johnson.Desc.First.Walk.Tied (openedZeroGives)
open VerifiableInference.Desc.First (S Pub Meaning ledgerB freeAboveB)

/-- A sized ledger passes the first test. -/
theorem sized_ledgerB {ns : ℕ} {t : S} (h : SizedAt ns t) : ledgerB t = true := by
  obtain ⟨F, hF, hs, _, _⟩ := h
  unfold ledgerB
  rw [hF]
  simp [hs.vp, hs.mf, hs.got]

/-- A sized ledger none of whose slots is taken passes the second. -/
theorem sized_freeAboveB {ns : ℕ} {t : S} (h : SizedAt ns t) : freeAboveB ns t = true := by
  obtain ⟨F, hF, hs, hn, hfree⟩ := h
  unfold freeAboveB
  rw [hF]
  simp only [Option.any_some, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.not_eq_true', beq_iff_eq]
  refine ⟨fun j hj => ?_, hn⟩
  have hlt : F.next + j < F.gotF.size := by
    rw [hs.got]
    omega
  have e := hfree (F.next + j)
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt] at e ⊢
  exact e

section
variable {Pp W Cl : Type} {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
  {fvs : List Bool} {kCol : ℕ}

/-- What the joined block leaves of the ledger. -/
theorem openingZero_sized {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    SizedAt X.ns t := by
  obtain ⟨s₁, g₁, _, h2⟩ := K1.openingZero_mid h
  exact (openedZeroGives X fvs kCol s₁ t h2).2.2.2.2.1

theorem openingZero_ledger {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    ledgerB t = true := sized_ledgerB (openingZero_sized h)

theorem openingZero_freeAbove {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    freeAboveB X.ns t = true := sized_freeAboveB (openingZero_sized h)

/-- **The two items hold behind a step**, at any filling with these sentences. -/
theorem madeG_keeper {Mg : Meaning Pp W} {nsOf : ℕ → Option ℕ}
    (hL : ∀ x, Mg.pub (.ledger 0) x = ledgerB x.2)
    (hA : ∀ x, Mg.pub (.freeAbove 0) x = (nsOf 0).any fun n => freeAboveB n x.2)
    (hns : nsOf 0 = some X.ns) (x x' : Pp × S) (h : StepG Cl q gp nm X fvs kCol x x') :
    Mg.pub (.ledger 0) x' = true ∧ Mg.pub (.freeAbove 0) x' = true := by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  refine ⟨by rw [hL]; exact openingZero_ledger hd, ?_⟩
  rw [hA, hns]
  exact openingZero_freeAbove hd

end

end VerifiableInference.Desc.K13.Law
