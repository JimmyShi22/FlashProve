-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SLotTwelve.lean: UNDER THE LIBRARY's HEAD (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean): THE LOT k5SLot (Honest/K5/Law/SLot5.lean) OF THE ATTENTION SEGMENTS' OWN
ROUNDS (kind K5: the label of that sub-protocol in the description) HAS ITS TWELVE ROWS AT THE
DESCRIPTION's OWN PUBLIC PART AND GROUND, WHERE THE THIRD TEST ON THE PUBLIC DATA SAYS YES AT EACH
GROUP. Statements with their proofs.

  filterMap_all  GENERAL: where the function yields at every member the list keeps its length
  KeysFitAll     the third test (Seat5.keysFit, Honest/K5/KeysFit.lean) says yes at each of the
                 twelve groups, at challenges that are all 0: a sentence on the letter keyOf: a
                 definition: a premise's form
  rows_twelve    **CONDITIONAL: the lot has twelve rows**

By seatAt_returns_at_head (Honest/K5/Law/SeatReturns.lean): under the head the third test's yes
gives the other two, and the maker of seats yields.

THE PREMISES THAT STAY, BY NAME. h: the head: A HYPOTHESIS · G is the ground that the description's
maker makes of the public part · KeysFitAll: SHOWN HERE AT NO keyOf: where a keyOf has wrong lengths
at a group it is false, and the lot has fewer rows, or none. It is a sentence on lengths alone;
whoever lays keyOf is meant to pay it: at the reader keyOfK3 it is paid under the head, at the
ground that the maker makes (keysFitAll_K3, Honest/K5/Law/SLotK3.lean, WHICH THIS FILE DOES NOT
IMPORT).

Limits. A count of rows: no distribution occurs. The library's full size alone. No property is
claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SLot5
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

/-- Where the function yields at every member the list keeps its length. -/
theorem filterMap_all {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, (f x).isSome = true) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | x :: l, h => by
    cases hx : f x with
    | none =>
      have h0 := h x List.mem_cons_self
      rw [hx] at h0
      cases h0
    | some y =>
      rw [List.filterMap_cons_some hx, List.length_cons, List.length_cons,
        filterMap_all f l fun z hz => h z (List.mem_cons_of_mem _ hz)]

/-- **The third test says yes at each of the twelve groups.** It is a definition: a premise's
form. -/
def KeysFitAll (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Zp : ProofFile.Pub)
    (G : Ground) (cF : Chain TS ProofFile.Cl) : Prop :=
  ∀ g, g < 12 → ∀ a, (P5J.At.X Zp).A[g]? = some a →
    (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true

/-- **THE LOT HAS TWELVE ROWS.** CONDITIONAL: see the head. -/
theorem rows_twelve {W₀ Rc Xi Tr X Pb : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    (hKey : KeysFitAll keyOf Zp G cF) :
    ((k5SLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells keyOf).rows Zp G).length =
      12 := by
  show ((H2K5.k5Places G).filterMap fun y =>
    (seatAtK keyOf Zp G y.1 y.2.1 y.2.2).map
      (r5 (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells)).length = 12
  rw [filterMap_all, H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG, List.length_map,
    List.length_range]
  intro y hy
  rw [H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG] at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  obtain ⟨_, a, -, Pl, -⟩ := k5_member h (List.mem_range.1 hg)
  show ((seatAtK keyOf Zp G (2 * g + 1) ("A" ++ toString g) g).map _).isSome = true
  rw [(seatAt_returns_at_head h (List.mem_range.1 hg) hG Pl.plan
    (hKey g (List.mem_range.1 hg) a Pl.plan)).2]
  rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.filterMap_all
#print axioms ProofFile.Honest.K5.rows_twelve
