-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/PubGOf.lean: CONDITIONAL. Four statements with their proofs.

What is here. On `k4PubG Zp g` (Lot/PubG.lean), the public data of the place of the feed-forward
layers' own rounds (sub-protocol K4) in group g as a term of the public part and g. WHEREVER IT
RETURNS A Qp, with no other hypothesis: `k4PubG_fields`: Qp's group is g, its link and segment 2 g,
its piece 3, its layers' data and plan those of the public part's own structure at g (of its seventh
field, the number of rounds in front, it says nothing); `k4PubG_place`: SO THE PLACE AT WHICH THE
BOOK OF COINS IS ASKED, `k4Place Qp`, IS GROUP g's; `k4PubG_places_apart`: TWO GROUPS ASK THE BOOK
AT TWO PLACES. `k4PubG_of`: WHERE THE MEMBER OF GROUP g IS LAID (`LaidK4`, Law/SeatedHead.lean) AND
`k4PubOf` RETURNS Qp AT ITS PARAMETERS (hQ), `k4PubG Zp g` (Lot/PubG.lean) IS THAT Qp. So a lot that
takes the group's number alone speaks at the member's own public data.

How. The first three by unfolding. `k4PubOf` unfolds to the same look-up in the public part's table,
at the name that `LaidK4` gives the parameters; five more fields of `LaidK4` give the other fields.

Not shown here. THAT IT RETURNS: under the head at the maker's return (`HeadAtReturn`) `k4PubG`
returns at each g below 12: `k4_member_and_public_data`, Law/ClosingLinePayers.lean. THAT TWO PLACES
HOLD NO COIN IN COMMON:
that hangs on the book's entries: nothing is shown. `LaidK4` holds the full size's numbers (twelve
groups; member number 28 g + 4): `k4PubG_of` speaks there alone. That the member is laid: `laid_at`
(Law/LaidAtGroup.lean) has it at each of the twelve groups under the library's hypothesis
`P5J.AtMgA` on the public files. That `k4PubOf` returns: `k4Pub_head` (Law/FrontCount.lean), under
the same. Neither is called here: `k4PubG_of` takes Lh and hQ, and nothing else. A program's walk
from import to import, which reads import lines alone and stops unopened at Johnson/Goal/,
ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 18 modules under Johnson/Goal/
and at 5 under Johnson/Bridge/: floors. A LAW, NOT A PART: no file that defines a part of the proof
file's description may import this one. Nothing on soundness, on completeness or on any other
property. No property is claimed.

  `k4PubG_fields`, `k4PubG_place`   what the term returns; the place is group g's
  `k4PubG_places_apart`   **two groups, two places**
  `k4PubG_of`   the term of (Zp, g) is the member's own public data
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedHead
import Johnson.Desc.ProofFile.Honest.K4.Lot.PubG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Chain Block Place)
open P5J (TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- CONDITIONAL on hp. **What the term returns, field by field**: by unfolding. -/
theorem k4PubG_fields {Zp : ProofFile.Pub} {g : ℕ} {Qp : K4Pub} (hp : Lot.k4PubG Zp g = some Qp) :
    Qp.P = (P5J.At.X Zp).layers ∧ (P5J.At.X Zp).G[g]? = some Qp.hp ∧ Qp.g = g ∧
      Qp.link = 2 * g ∧ Qp.piece = 3 ∧ Qp.seg = 2 * g := by
  unfold Lot.k4PubG at hp
  obtain ⟨hp0, h1, h2⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨r0, -, rfl⟩ := Option.map_eq_some_iff.1 h2
  exact ⟨rfl, h1, rfl, rfl, rfl, rfl⟩

/-- CONDITIONAL on hp. **The place at which the book is asked is group g's**: link 2 g, piece 3. -/
theorem k4PubG_place {Zp : ProofFile.Pub} {g : ℕ} {Qp : K4Pub} (hp : Lot.k4PubG Zp g = some Qp) :
    k4Place Qp = (⟨1, some (2 * g), 3, .K4⟩ : Place) := by
  obtain ⟨-, -, -, hl, hc, -⟩ := k4PubG_fields hp
  unfold k4Place
  rw [hl, hc]

/-- CONDITIONAL on hp, hp' and hne. **Two groups ask the book at two places.** -/
theorem k4PubG_places_apart {Zp : ProofFile.Pub} {g g' : ℕ} {Qp Qp' : K4Pub}
    (hp : Lot.k4PubG Zp g = some Qp) (hp' : Lot.k4PubG Zp g' = some Qp') (hne : g' ≠ g) :
    k4Place Qp' ≠ k4Place Qp := by
  rw [k4PubG_place hp, k4PubG_place hp']
  intro e
  have e2 : (some (2 * g') : Option ℕ) = some (2 * g) := congrArg Place.link e
  have e3 : 2 * g' = 2 * g := Option.some.inj e2
  omega

/-- CONDITIONAL on Lh and hQ. **The term of the public part and the group's number is the member's
own public data.** -/
theorem k4PubG_of {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) : Lot.k4PubG Zp g = some Qp := by
  unfold k4PubOf at hQ
  rw [Lh.name] at hQ
  have hQ' : (Zp.roundsBefore? (k4StepOf g)).map (fun r0 =>
      ({ P := x.2.P, hp := x.2.hp, g := x.2.g, link := x.2.link, piece := x.2.piece, r0 := r0,
         seg := 2 * x.2.g } : K4Pub)) = some Qp := hQ
  obtain ⟨r0, hr, rfl⟩ := Option.map_eq_some_iff.1 hQ'
  unfold Lot.k4PubG
  rw [Lh.hp, hr]
  show some (k4PubAtX (P5J.At.X Zp) x.2.hp g r0) = some _
  unfold k4PubAtX
  rw [Lh.P, Lh.grp, Lh.link, Lh.piece]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4PubG_fields
#print axioms ProofFile.Honest.K4.W.k4PubG_place
#print axioms ProofFile.Honest.K4.W.k4PubG_places_apart
#print axioms ProofFile.Honest.K4.W.k4PubG_of
