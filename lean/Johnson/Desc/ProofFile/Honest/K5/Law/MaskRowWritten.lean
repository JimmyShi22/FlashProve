-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MaskRowWritten.lean: NUMBERS OF A PUBLIC PLAN: what the public
premises of `covers_mask_switch_at_book` (MaskSwitchBook.lean in this folder) come to AT MESSAGE
NUMBER 3 OF THE SENDING OF A CODE SWITCH THAT LEADS INTO AN ATTENTION SEGMENT: first as closed facts
on the code switches' closed list of written places (`K2.Law.placesW`,
Johnson/Desc/ProofFile/Honest/K2/Law/PlacesWritten.lean) and on the written numbers of a group's own
rounds (`H2K5.Row.ownW`); then, CONDITIONAL, under the library's hypothesis h on the public input
(`P5J.AtMgA`), at the plan's own switches and at a group's stored plan. No run, no input, no book.
No definition; eight theorems.

Main names. Closed facts; Lean's kernel evaluates the first, second and fourth:
  `switches_written`: at each member of the written list whose link is odd and below 24: its place
    is ⟨1, its link, 1, K2⟩; its sending has five messages; message 3 has one mask row;
    `K2.maskBase` at 3 is 439; `K2.maskLength` at 3 is 8192.
  `one_switch_written`: at each g < 12 just one member of the list has the link 2 g + 1.
  `script_rows`: the stretch's stages do not read the field rows.
  `own_written`: at the eleven written numbers, whatever the field rows: the stages take 1072 slots,
    and the row has 13 parts.
Under h:
  `own_numbers_head`: at a group's stored plan a: `slotsOf (script a.own)` = 1072 and `(shapes
    a.own).length` = 13: by `own_head` (MarksSmall.lean in this folder).
  `places_under_head`: with hG (G is the maker's own ground): the plan's switches ARE the written
    list: by `K2.Law.places_at_head`, its opening taken out of h's field `laid.opened`.
  `switch_numbers_head`: so `switches_written`'s five clauses at every switch of the plan that leads
    into segment 2 g + 1, g < 12.
  `switch_there_head`: and such a switch is there.

What they are for. With n := 3, ν₅ := `Forest.elems a.fs` and cnt := `slotsOf (script a.own)`, the
premises hn (3 < 5), hl (3 ≠ 4), h1 and hN of `covers_mask_switch_at_book`, and the owner and the
base on the right side of its hT, follow from these by arithmetic. That `Forest.elems a.fs` = 1812
under h is a neighbour file's (`elems_head`, ForestAtHead.lean in this folder): not imported.

Limits. THAT MESSAGE 3 OF THAT SENDING IS THE MESSAGE THAT K5 KNOWS AS ITS MASK MESSAGE IS NOT SAID:
in `covers_mask_switch_at_book` two numbers stand side by side: n, a message of the switch's
sending, and kM, K5's own number of its mask message, which goes into the lot's number: NO EQUATION
BETWEEN n AND kM IS HAD, THERE OR HERE: here «3» is a choice: that among the sending's messages but
the last it is the only one with a mask row is not said here. Nothing is said of the book: hT's left
side is not touched. The closed facts are evaluations by Lean's kernel of terms of other houses' and
the library's making: they say what these terms come to, not that the terms are the right ones. The
file imports the code switch's PlacesWritten.lean and MaskCoin.lean and our LotsMask.lean and
MarksSmall.lean: these, and further files beneath them, lie in no seal. Through MarksSmall.lean it
stands above Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/
(lean/LIMITS.md, L15): a fact on import lines. At the earlier hash `OnBytes.secondHashFunction` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskCoin
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsMask
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Att.P (slotsOf script)
open P5J (AtMgA TS)

/-- **AT THE WRITTEN SWITCHES INTO THE ODD SEGMENTS BELOW 24**: the place, the number of messages,
and at message 3 the mask rows, where their entries begin, and how many they are. A closed fact. -/
theorem switches_written : ∀ p ∈ K2.Law.placesW, p.link % 2 = 1 → p.link < 24 →
    p.place = ⟨1, some p.link, 1, .K2⟩ ∧ (K2.switchSent p.sizes p.others).size = 5 ∧
      ((K2.switchSent p.sizes p.others).getD 3 default).shape.maskRows = 1 ∧
      K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
        (K2.switchFresh p.sizes p.others p.foldVars) 3 = 439 ∧
      K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) 3 = 8192 := by
  decide +kernel

/-- **Just one written switch leads into segment 2 g + 1**, g < 12. A closed fact. -/
theorem one_switch_written : ∀ g, g < 12 →
    (K2.Law.placesW.filter fun p => p.link == 2 * g + 1).length = 1 := by
  decide +kernel

/-- The stretch's stages do not read the field rows. -/
theorem script_rows (x : OnBytes.Params.AttentionRounds) (ρ : ℕ) :
    script { x with rows := ρ } = script x :=
  rfl

/-- **At the eleven written numbers: 1072 slots, 13 parts**, whatever the field rows. -/
theorem own_written (ρ : ℕ) : slotsOf (script { H2K5.Row.ownW with rows := ρ }) = 1072 ∧
    (H2K5.Honest.shapes { H2K5.Row.ownW with rows := ρ }).length = 13 := by
  unfold H2K5.Honest.shapes
  rw [script_rows]
  exact ⟨by decide +kernel, by decide +kernel⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head a group's own rounds take 1072 slots, in 13 parts.** CONDITIONAL: h; hg; ea:
the group's stored plan. -/
theorem own_numbers_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    slotsOf (script a.own) = 1072 ∧ (H2K5.Honest.shapes a.own).length = 13 := by
  obtain ⟨ρ, e⟩ : ∃ ρ, a.own = { H2K5.Row.ownW with rows := ρ } := ⟨_, own_head h hg ea⟩
  rw [e]
  exact own_written ρ

/-- **Under the head the plan's switches are the written list.** CONDITIONAL: h; hG: G is the
maker's own ground. -/
theorem places_under_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) : K2.switchPlaces Zp G = K2.Law.placesW := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have e : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  rw [← e]
  exact K2.Law.places_at_head h.toAtMg O

/-- **Under the head, at a switch of the plan that leads into segment 2 g + 1.** CONDITIONAL: h; hG;
hp: p is one of the plan's switches; hg; hl: its link. -/
theorem switch_numbers_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {p : K2.SwitchPlace}
    (hp : p ∈ K2.switchPlaces Zp G) {g : ℕ} (hg : g < 12) (hl : p.link = 2 * g + 1) :
    p.place = ⟨1, some (2 * g + 1), 1, .K2⟩ ∧ (K2.switchSent p.sizes p.others).size = 5 ∧
      ((K2.switchSent p.sizes p.others).getD 3 default).shape.maskRows = 1 ∧
      K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
        (K2.switchFresh p.sizes p.others p.foldVars) 3 = 439 ∧
      K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) 3 = 8192 := by
  rw [places_under_head h hG] at hp
  have H := switches_written p hp (by omega) (by omega)
  rw [hl] at H
  exact H

/-- **Under the head such a switch is there.** CONDITIONAL: h; hG; hg. -/
theorem switch_there_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {g : ℕ} (hg : g < 12) :
    ∃ p ∈ K2.switchPlaces Zp G, p.link = 2 * g + 1 := by
  have H := one_switch_written g hg
  cases hq : K2.Law.placesW.filter fun p => p.link == 2 * g + 1 with
  | nil =>
    rw [hq] at H
    cases H
  | cons p _ =>
    have hp : p ∈ K2.Law.placesW.filter fun p => p.link == 2 * g + 1 := by
      rw [hq]
      exact List.mem_cons_self
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hp
    exact ⟨p, by rw [places_under_head h hG]; exact h1, beq_iff_eq.1 h2⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.switches_written
#print axioms ProofFile.Honest.K5.one_switch_written
#print axioms ProofFile.Honest.K5.script_rows
#print axioms ProofFile.Honest.K5.own_written
#print axioms ProofFile.Honest.K5.own_numbers_head
#print axioms ProofFile.Honest.K5.places_under_head
#print axioms ProofFile.Honest.K5.switch_numbers_head
#print axioms ProofFile.Honest.K5.switch_there_head
