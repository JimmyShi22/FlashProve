-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SLotK3.lean: UNDER THE LIBRARY's HEAD (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean): THE LOT k5SLot (Honest/K5/Law/SLot5.lean) OF THE ATTENTION SEGMENTS' OWN
ROUNDS (kind K5: the label of that sub-protocol in the description), WITH THE READER OF THE KEY
POINTS LAID AT THE LOOKUPS' OWN TEXT (keyOfK3, Honest/K5/Law/KeyOfK3.lean), HAS ITS TWELVE ROWS: NO
PREMISE ON A FREE LETTER STAYS. And two small statements beside. Statements with their proofs.

  ground_head    CONDITIONAL: under the head the description's maker yields a ground of the public
                 part: so the premise hG of k5_good_rows and rows_twelve has a payer by a term
  keysFitAll_K3  CONDITIONAL: KeysFitAll (Honest/K5/Law/SLotTwelve.lean) at keyOfK3: keysFit_K3
                 (Honest/K5/Law/KeysFitK3.lean) at each of the twelve groups
  rows_twelve_K3 **CONDITIONAL: at keyOfK3 the lot has twelve rows**: under the head and hG alone
  lot_twelve_head   CONDITIONAL: the two in one: under the head alone there is a ground that the
                 maker yields, and at it the lot has twelve rows
  k5_rows_noneSeen  CONDITIONAL: at the seated side of EVERY ROW OF THE LOT, whatever keyOf, no move
                 of a member reads anything of what has been seen (k5_members_noneSeen,
                 Honest/K5/Law/NoneSeen5.lean): no head is asked

THE PREMISE THAT STAYS, BY NAME. h: the head: A HYPOTHESIS of every statement that names it. (The
library has P5J.head_exists_at_name, Johnson/P5J/HeadExistsAtName.lean: a head is there under four
premises on the public files; no file of this folder calls it.)

Limits. A count of rows, a ground that is there, a sentence on what a move reads: no distribution
occurs. The library's full size alone. What Good says at these rows, and what not: see the heads of
Honest/K5/Law/GoodPaid.lean, GoodHead.lean and SLotRows.lean. What k5_rows_noneSeen shuts, and what
not: see the head of Honest/K5/Law/NoneSeen5.lean: one road, at this storey. KeysFitAll asks the key
points' lengths at challenges that are all 0; that at keyOfK3 they are the same at all challenges is
keyOfK3_sizes (Honest/K5/Law/KeyOfK3.lean), which is not called here. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SLotTwelve
import Johnson.Desc.ProofFile.Honest.K5.Law.SLotRows
import Johnson.Desc.ProofFile.Honest.K5.Law.NoneSeen5
import Johnson.Desc.ProofFile.Honest.K5.Law.KeysFitK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain)
open P5J (AtMgA TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head the description's maker yields a ground.** CONDITIONAL: the head. -/
theorem ground_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) :
    ∃ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G := by
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  exact ⟨Bs.G₀, O.blank⟩

/-- **The third test says yes at each of the twelve groups, at keyOfK3.** CONDITIONAL: the head; G
is the ground that the description's maker makes. -/
theorem keysFitAll_K3 (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : KeysFitAll keyOfK3 Zp G cF :=
  fun _ hg _ ha => keysFit_K3 h hg hG ha

/-- **AT keyOfK3 THE LOT HAS TWELVE ROWS.** CONDITIONAL: the head; hG. -/
theorem rows_twelve_K3 {W₀ Rc Xi Tr X Pb : Type} (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {G : Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells) :
    ((k5SLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells keyOfK3).rows Zp G).length =
      12 :=
  rows_twelve h hG cells (keysFitAll_K3 h hG)

/-- **Under the head alone: a ground is there, and at it the lot has twelve rows.** CONDITIONAL: the
head. -/
theorem lot_twelve_head {W₀ Rc Xi Tr X Pb : Type} (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (cells : Tr → Cells) :
    ∃ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G ∧
      ((k5SLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells keyOfK3).rows Zp
        G).length = 12 := by
  obtain ⟨G, hG⟩ := ground_head h
  exact ⟨G, hG, rows_twelve_K3 h hG cells⟩

end

/-- **At the seated side of every row of the lot no move of a member reads anything of what has been
seen.** CONDITIONAL: r is a row of the lot; σ₀ is the side that Side.seated makes at it. General in
the public part, the ground, the list of blocks and keyOf. WHERE THE LOT HAS NO ROW NOTHING IS
SAID. -/
theorem k5_rows_noneSeen {W₀ Rc Xi Tr X Pb S Cl : Type} {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)} {Zp : Pub} {G : Ground}
    {r : Row5 W₀ Rc Xi Tr X Pb} (hr : r ∈ (k5SLot cells keyOf).rows Zp G)
    {bs : List (Block S Cl)} {fs₀ : List (Fall S)}
    {σ₀ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated bs r.place r.row fs₀ = some σ₀) :
    ∀ u ∈ σ₀.members, u.part.readsNoneSeen := by
  obtain ⟨_, _, Y, _, rfl⟩ := row_of_lot hr
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 hσ
  exact k5_members_noneSeen (cells := cells) (Z := Y) rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.ground_head
#print axioms ProofFile.Honest.K5.keysFitAll_K3
#print axioms ProofFile.Honest.K5.rows_twelve_K3
#print axioms ProofFile.Honest.K5.lot_twelve_head
#print axioms ProofFile.Honest.K5.k5_rows_noneSeen
