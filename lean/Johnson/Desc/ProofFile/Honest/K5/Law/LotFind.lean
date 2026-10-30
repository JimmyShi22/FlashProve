-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotFind.lean: CONDITIONAL: WHAT THE HONEST SIDE OF THE LOT OF
THE KIND "an attention segment's own rounds" (K5) HOLDS AT THE KIND's PLACE OF GROUP g: the half at
what the maker of the place's public data yields there; no half where it yields nothing; and, under
the hypothesis on the public input, at the key points' reader `keyOfK3`: the half at the group's own
public data. Five small theorems: corollaries of `lot_find` and `halves_k5LotK`
(Honest/K5/Law/LotLaid.lean) at the lot `k5LotK` itself.

Why. A law that says which half the halves of several lots, laid one behind another, hold at a place
p asks of the lot L that is meant: (L.halves Z G).find? (fun x => x.place == p) = some g. `lot_find`
has that of the list `halvesBy mk cells G`, general in the maker mk. Here it stands in the asked
form.

Main names:
  `seatAtK_link`   what the maker `seatAtK` yields at a segment bears that segment's number
  `k5LotK_find`   **the maker yields Y at group g: then ((k5LotK cells keyOf).halves Zp G).find?
    (fun x => x.place == placeOf g) = some (k5Half cells Y)**
  `k5LotK_find_none`   it yields nothing: then that list holds no half at the place
  `k5LotK_find_head`   the third test's yes at the group, for "the maker yields": then the half is
    that at `seatOf keyOf Zp G cF g a` (by `seatAt_returns_at_head`, Law/SeatReturns.lean)
  `k5LotK_find_K3`   **at `keyOfK3` no test is left as a premise** (by `seatAt_returns_K3`,
    Law/KeysFitK3.lean: at `keyOfK3` the maker yields)

ALL BUT THE FIRST ARE CONDITIONAL on: the hypothesis h on the public input (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean); g is below 12; hG: G is the ground that the description's maker makes of
the public part. Beside these: `k5LotK_find`, `k5LotK_find_none`: what the maker does at the group;
`k5LotK_find_head`: a is the group's plan, and the third test's yes; `k5LotK_find_K3`: a is the
group's plan.
ON h. It is a hypothesis of every statement that names it. It can be met: at the full-size public
files as Ladder/Stored.lean spells them the head has a member with no premise (`headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean). This file does not call it. Here h is spent for the ground's
twelve attention segments and, in the last two, for the maker's tests.
Limits. LENGTHS ALONE: the maker's third test asks the key points' lengths, at challenges that are
all 0; that at `keyOfK3` they are the same at all challenges is `keyOfK3_sizes` (Law/KeyOfK3.lean),
which is not called here; and nothing here says that the value of `keyOfK3` is what the verifier's
state holds. The four statements under h speak at the library's full size (its twelve groups of
layers) and at the format's second hash function (OnBytes.secondHashFunction) alone: h is typed there. Nothing is said
of other lots. `lotLaid_first` (Law/LotLaid.lean) is the law of this folder on the halves of several
lots at the kind's places; it is not called here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotLaid
import Johnson.Desc.ProofFile.Honest.K5.Law.KeysFitK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

/-- What `seatAtK` yields at a segment bears that segment's number. CONDITIONAL: it yields. -/
theorem seatAtK_link {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)}
    {Zp : ProofFile.Pub} {G : Ground} (l : Nat) (nm : String) (j : Nat) (Y : Seat5)
    (hY : seatAtK keyOf Zp G l nm j = some Y) : Y.link = l :=
  seatAt_link l nm j Y (seatAtK_spec hY).1

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Tr X : Type}
include h

/-- **WHAT THE LOT's OWN LIST HOLDS AT THE KIND's PLACE OF GROUP g, WHERE THE MAKER YIELDS.**
CONDITIONAL: under the hypothesis h; g is below 12; hG: G is the ground that the description's maker
makes; hY: the maker of the place's public data yields Y at the group. -/
theorem k5LotK_find {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)) {Y : Seat5}
    (hY : seatAtK keyOf Zp G (2 * g + 1) ("A" ++ toString g) g = some Y) :
    ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) cells keyOf).halves Zp G).find?
      (fun q => q.place == placeOf g) = some (k5Half cells Y) := by
  rw [halves_k5LotK, lot_find h hg _ seatAtK_link hG cells, hY]
  rfl

/-- **Where the maker yields nothing, the lot's own list holds no half at the place.** CONDITIONAL:
as above, with hN for hY. -/
theorem k5LotK_find_none {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E))
    (hN : seatAtK keyOf Zp G (2 * g + 1) ("A" ++ toString g) g = none) :
    ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) cells keyOf).halves Zp G).find?
      (fun q => q.place == placeOf g) = none := by
  rw [halves_k5LotK, lot_find h hg _ seatAtK_link hG cells, hN]
  rfl

/-- **The same with the third test's yes for "the maker yields".** CONDITIONAL: under the hypothesis
h; g is below 12; hG; ha: a is the group's plan; hKey: the third test says yes at the group. -/
theorem k5LotK_find_head {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a)
    (hKey : (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true) :
    ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) cells keyOf).halves Zp G).find?
      (fun q => q.place == placeOf g) = some (k5Half cells (seatOf keyOf Zp G cF g a)) :=
  k5LotK_find h hg hG cells keyOf (seatAt_returns_at_head h hg hG ha hKey).2

/-- **AT keyOfK3 NO TEST IS LEFT AS A PREMISE.** CONDITIONAL: under the hypothesis h; g is below 12;
hG; ha: a is the group's plan. -/
theorem k5LotK_find_K3 {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) :
    ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) cells keyOfK3).halves Zp G).find?
      (fun q => q.place == placeOf g) = some (k5Half cells (seatOf keyOfK3 Zp G cF g a)) :=
  k5LotK_find h hg hG cells keyOfK3 (seatAt_returns_K3 h hg hG ha).2

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.seatAtK_link
#print axioms ProofFile.Honest.K5.k5LotK_find
#print axioms ProofFile.Honest.K5.k5LotK_find_none
#print axioms ProofFile.Honest.K5.k5LotK_find_head
#print axioms ProofFile.Honest.K5.k5LotK_find_K3
