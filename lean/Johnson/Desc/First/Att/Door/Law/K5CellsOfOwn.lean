-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5CellsOfOwn.lean: kind K5: PAYMENTS BENEATH THE KIND's FROZEN NAMED CONDITION (K5CondAt, K5LeftOfCond.lean; its fields pads := PadsAll h and cells := ∃ idx, K5CellsCond h a x₁ idx: K5RestCells.lean): WHAT THE FIELD cells OF K5Rest SPENDS OF "OFF THE PADS", AND FROM
WHAT THE CONDITION's FIELD pads FOLLOWS.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)


Main names:
  `K5CellsOwn h g a x₁ idx`: PER GROUP: tie · one · own · ownG. THE FOUR TEXTS ARE MADE BY PROGRAM OUT OF THE LOOKUP ARGUMENT's OWN LEDGER's LINES (Johnson/Desc/Sound/MgAt/K3Owed.lean: AttOwedR's tie · one · own; LayOwedR's own), SIGN FOR
    SIGN, under the one substitution Dm := h.𝔇 · X := At.X Zp · num := At.num Zp · tls := Meaning.tlAt (At.X Zp) · tl := a.seam.tl · x.link := x₁.link (ownG: 2 * g: the layers' place's link) · seatL := its notation's own text.
  `cellsOwn_all`: **K5Rest's field cells from ∃ idx, K5CellsOwn h g a x₁ idx ALONE**: one call of cells_any (K5CellsAny.lean): NO PadsAll. `rest_cellsOwn`: THE CHECK of its type against the field.
  `cellsCond_of_own`: the frozen condition's per-group field follows: K5CellsOwn h g a x₁ idx → K5CellsCond h a x₁ idx.
  `own_of_pads`: the frozen set gives the weaker: PadsAll h · K5CellsCond h a x₁ idx → K5CellsOwn h g a x₁ idx.
  `pads_of_own`: **"REST → CONDITION" FOR pads**: OwnNamed at every segment below 25 gives PadsAll h (above 24 the library's sizes have no matrix: sizesOf_beyond, Johnson/P5J/HidAtPlan.lean).
WHAT IT SAYS OF THE FROZEN CONDITION: pads asks "off the pads" at ALL 25 segments; the field cells spends it at the two segments 2 g + 1 and 2 g of each group: 24 segments: THE CLAUSE AT THE OUTPUT HEAD's SEGMENT 24 IS ASKED AND NOWHERE SPENT BY THIS KIND.
Is it empty here? K5CellsOwn AND pads_of_own's PREMISE ARE SHOWN AT NOTHING IN LEAN. idx stands under ∃ behind g: a letter of each segment.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5RestCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt sigListCalls CellsAre)
open VerifiableInference.OnPublicFiles (OneNumber OwnNamed)
open P5J (AtMgA mgAtAll TS)

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)

/-- **Per group: four fields of the lookup argument's own ledger.** -/
structure K5CellsOwn (g : ℕ) (a : Attention.Plan) (x₁ : Look.Place) (idx : ℕ → ℕ) : Prop where
  /-- test on the public parameters and the layout -/
  tie : _root_.Meaning.linkTieB (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp) idx x₁.link a.seam.tl = true
  /-- test on the list of rounds: a member's number is its label's; no pad's place -/
  one : OneNumber (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp) idx (_root_.Meaning.tlAt (P5J.At.X Zp)) x₁.link (fun j : Fin (sigListCalls h.𝔇.sent h.𝔇.rad3 x₁.link).length => h.𝔇.seat3 x₁.link false j.1) h.𝔇.arr id
  /-- test on the table's numbers: one tenant with that number; no pad's place -/
  own : OwnNamed (P5J.At.X Zp) h.𝔇.sent (P5J.At.num Zp) (_root_.Meaning.tlAt (P5J.At.X Zp)) x₁.link h.𝔇.arr h.𝔇.ms h.𝔇.N
  /-- the same at the group's own segment, which owns the borrowed array -/
  ownG : OwnNamed (P5J.At.X Zp) h.𝔇.sent (P5J.At.num Zp) (_root_.Meaning.tlAt (P5J.At.X Zp)) (2 * g) h.𝔇.arr h.𝔇.ms h.𝔇.N

/-- **K5Rest's field cells, from the four alone.** -/
theorem cellsOwn_all {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {x₁ : Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (C : ∃ idx, K5CellsOwn h g a x₁ idx) :
    ∀ w, h.𝔇.H.base (2 * g + 1) w →
      CellsAre x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad
        (msgsOf h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link) (seatAll h x₁) h.𝔇.arr w) (zofAll h g w) := by
  obtain ⟨idx, C⟩ := C
  exact cells_any h.scope h.reads h.pubOne h.𝔇.sent h.𝔇.arr h.𝔇.ms h.𝔇.N (P5J.At.num Zp) P5J.tokVOf _ _ h.plan.hN h.plan.hG hg ha hx
    h.𝔇.l3.rad idx (seatAll h x₁) C.tie C.one C.own C.ownG

/-- **THE CHECK** (of types: it takes a member and gives one back): Lean's own word that cellsOwn_all's statement is K5Rest's field cells at the closed letters. -/
theorem rest_cellsOwn {Fr : Frame} {Ld : VerifiableInference.Desc.K12.Door.Laid} {Ms : List OracleShape} {bs g : ℕ} {before : List (ℕ × ℕ)} {a : Attention.Plan}
    {x₁ : Look.Place} {pl : VerifiableInference.Desc.Place} {O : List Item} {Q : List Pub} {Lk : Link S Claim} {same : S → S → Bool}
    {blk : Block S Claim} {nm : String} (hg : g < 12) (ha : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (C : ∃ idx, K5CellsOwn h g a x₁ idx)
    (R : K5RestAll (Fr := Fr) h Ld Ms bs g before a x₁ pl O Q Lk same blk nm (zofAll h g)) :
    K5RestAll (Fr := Fr) h Ld Ms bs g before a x₁ pl O Q Lk same blk nm (zofAll h g) :=
  { R with cells := cellsOwn_all h hg ha hx C }

/-- The frozen condition's per-group field follows from the four. -/
theorem cellsCond_of_own {g : ℕ} {a : Attention.Plan} {x₁ : Look.Place} {idx : ℕ → ℕ} (C : K5CellsOwn h g a x₁ idx) :
    K5CellsCond h a x₁ idx := ⟨C.tie, C.one⟩

/-- The frozen set gives the four. -/
theorem own_of_pads (hO : PadsAll h) (g : ℕ) {a : Attention.Plan} {x₁ : Look.Place} {idx : ℕ → ℕ} (C : K5CellsCond h a x₁ idx) :
    K5CellsOwn h g a x₁ idx :=
  ⟨C.tie, C.one, ownNamed_of_places h.𝔇.sent h.𝔇.arr h.𝔇.ms h.𝔇.N (P5J.At.num Zp) h.plan.hN hO x₁.link,
    ownNamed_of_places h.𝔇.sent h.𝔇.arr h.𝔇.ms h.𝔇.N (P5J.At.num Zp) h.plan.hN hO (2 * g)⟩

/-- **The condition's field pads, from OwnNamed at the 25 segments.** -/
theorem pads_of_own
    (H : ∀ k, k < 25 → OwnNamed (P5J.At.X Zp) h.𝔇.sent (P5J.At.num Zp) (_root_.Meaning.tlAt (P5J.At.X Zp)) k h.𝔇.arr h.𝔇.ms h.𝔇.N) :
    PadsAll h := by
  intro k μ r c hr hc
  by_cases hk : k < 25
  · exact (H k hk μ.val r c μ.isLt hr hc).2
  · exact absurd (P5J.sizesOf_beyond (P5J.At.X Zp) k (by omega) ▸ μ.isLt : μ.val < 0) (Nat.not_lt_zero _)

end

end H2K5.Door

#print axioms H2K5.Door.cellsOwn_all
#print axioms H2K5.Door.rest_cellsOwn
#print axioms H2K5.Door.cellsCond_of_own
#print axioms H2K5.Door.own_of_pads
#print axioms H2K5.Door.pads_of_own
