-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/AtOcEnd.lean: THE TIE AT "LIN point": ITS PREMISES ON THE SLOT's OWN CONDITION, AT THE CONDITION THAT IS MEANT: Oc := THE FIRST CHAIN's WHOLE PROMISE AT ITS LAST BORDER (ocEnd, Johnson/Desc/Sound/TieEnd.lean), at the first table's named filling mg1Joint (Johnson/Desc/Sound/JointFilling.lean).
Two definitions, five theorems. A joint build of K13's and K14's files.
Why. hW ("inside Oc, at a record without a mark, W sits as the plan says": seven public facts: WSits, Johnson/Desc/K13/Law/PointStepBack.lean) cannot be paid at that Oc without a public item of its own: an unmarked record with (Eval) laid over other codes would be inside it. So the public item "K13.wSits" comes through the first
table's door (Johnson/Desc/K13/Law/SitsDoor.lean: made at W's sending, kept at the seal, dropped by nobody; its makers' lemmas: SitsMade.lean, SeatMade.lean) and mg1Joint fills it by K13's two tests with code: wSitsB cs Pw && wSeatB wSeat.
  hW_at_ocEnd: AT THAT Oc, AT A RECORD WITHOUT A MARK, WHERE THE READER GIVES A RECORD D OF (Eval): WSits cs arr xW lay₀ stOf tabP p D. FROM: ONE TEST ON THE PROMISE's TABLE (h3: the item is among the public items at the last border) · THREE CONDITIONS ON THE FILLING's LETTERS, EACH BY THE MAKE OF A LETTER: hst (the statement
    that is read is the record's own) · hlay (the layout is the plan's) · hbook (THE WORDS' READER GOES FROM A NUMBER TO A TENANT BY THE RECORD's OWN BOOK, and reads the witness through the one accessor) · AND TWO EQUATIONS ON THE PLAN: hsh (W's member's shape is the linear claim's shape for W) · hseat (W's member's seat is wSeat).
  tabByBook · tabByBook_book · tabByBook_stays: SO THAT hbook IS NOT A PREMISE THAT NO FILLING MEETS: a reader that meets it, and the tie's own condition on the reader (it reads a witness's messages and pads alone), both by Lean.
  gLaid · gLaid_is: the like for the tie's condition hg on the row weights: a filling that meets it at every handed record.
  hOc_at_ocEnd: that Oc reads below lo: from one test with code on the first table's numbers (sampledBelow): mg1Joint leaves the three letters that are read as meaningSig lays them.
IS EACH PREMISE PAYABLE AT THE MEANT LETTERS? (asked before typing) h3: wSits_fit (Johnson/Desc/K13/Law/AtTableW.lean) says it by Lean at wSitsMore alone at both real lists; at a merged filling it is a test to run · hst | hlay: rfl at stOf := the record's statement, lay₀ := linLayW cs Pw.lin · hbook: tabByBook_book · hsh | hseat: two
equations between the plan's numbers: by evaluation at a plan: run by nobody here.

Limits. Unfoldings and ties. NO LAW OF A BLOCK: that a yes of W's sending MAKES the item and that the seal KEEPS it are lemmas of K13's files, under their own premises (three tests on the plan; one equation on the plan for the seat); they are not called here. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.JointFilling
import Johnson.Desc.Sound.ReadsBelowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Johnson.Pack (sigOf)
open VerifiableInference.Desc (Strs Wit FileDescription First.S)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound (OcReadsBelow MsgT Mem Sending CellsOf ocEnd ocEnd_pub ocEndReadsBelow
  lettersReadBelow_sig sampledBelow)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt EvalLaid laidOf laidOf_ok evalLaidB evalLaidB_iff wSitsItem wSitsMore
  wSitsB wSitsL wSeatB wSitsB_gives linAt)

variable {P₁ P₀ Xi Cells Tok : Type}

/-- A reader of the words' tables that goes from a message's number to its tenant by the record's own book. -/
def tabByBook (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (s : First.S) (w : Wit Cells Tok MsgT) (n : Nat) : MsgT :=
  match s.book.place[n]?, (s.st.oracles[n]?).map (·.shape) with
  | some x, some sh => w.tab cs sh (arr x.1 x.2) x.1 x.2
  | _, _ => fun _ _ _ => 0

/-- It meets the condition on the reader that hW_at_ocEnd asks. -/
theorem tabByBook_book (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (s : First.S) (w : Wit Cells Tok MsgT)
    (n j t : Nat) (sh : OracleShape) (h1 : s.book.place[n]? = some (j, t))
    (h2 : (s.st.oracles[n]?).map (·.shape) = some sh) :
    tabByBook cs arr s w n = w.tab cs sh (arr j t) j t := by
  unfold tabByBook
  rw [h1, h2]

/-- And the tie's own: it reads a witness's messages and pads alone. -/
theorem tabByBook_stays (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (s : First.S) (w w' : Wit Cells Tok MsgT)
    (hm : ∀ n, w'.msg n = w.msg n) (hp : ∀ j t, w'.pad j t = w.pad j t) :
    tabByBook cs arr s w' = tabByBook cs arr s w := by
  funext n
  unfold tabByBook
  split
  · funext mask row place
    unfold Wit.tab
    rw [hm, hp]
  · rfl

/-- The row weights, read off what the reader gives at the handed record; 0 where it gives nothing. -/
def gLaid (Pw : Where) (get : P₁ → P₀ × First.S) (p : P₁) (y : Nat) : GE :=
  ((laidOf Pw (get p).2).map fun D => (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum).getD 0

/-- It meets the tie's condition on the row weights, at every handed record. -/
theorem gLaid_is (Pw : Where) (get : P₁ → P₀ × First.S) (p : P₁) (D : EvalAt) (hD : laidOf Pw (get p).2 = some D)
    (y : Nat) : gLaid Pw get p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum := by
  unfold gLaid
  rw [hD]
  rfl

section
variable (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ : List Mem) (decT₁ : CellsOf → P₀ × First.S → Option Cells)
  (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
  (Pw : Where) (wSeat : Nat × Nat) (matC : Cells → Nat → Nat → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
  (get : P₁ → P₀ × First.S) (N₁ : Numbers) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)

/-- **hW, at the slot's own condition that is meant.** -/
theorem hW_at_ocEnd (xW : Mem) (lay₀ : VectorLay) (stOf : P₁ → Statement)
    (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT)
    (h3 : wSitsItem ∈ (pubSets (Mg₁.more.merge wSitsMore) links ps)[ps.length]?.getD [])
    (hst : ∀ p, stOf p = (get p).2.st) (hlay : lay₀ = linLayW cs Pw.lin)
    (hbook : ∀ p (w : Wit Cells Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) →
      ((get p).2.st.oracles[n]?).map (·.shape) = some sh → tabP p w n = w.tab cs sh (arr j t) j t)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1) (hseat : xW.1.seat xW.2 = wSeat) :
    ∀ p y D, ocEnd get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁) links ps p y →
      (get p).2.failed = none → laidOf Pw (get p).2 = some D → WSits cs arr xW lay₀ stOf tabP p D := by
  intro p y D h hm hD
  have hb := ocEnd_pub get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁) links ps p y h hm
    wSitsItem h3
  rw [pub_wSits, Bool.and_eq_true] at hb
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨D', hD', -, hst', hS⟩ := wSitsB_gives hb1
  rw [hD] at hD'
  obtain rfl := Option.some.inj hD'
  have hE : evalLaidB Pw (get p).2 = true := by
    unfold wSitsB wSitsL at hb1
    rw [List.all_cons, Bool.and_eq_true] at hb1
    exact hb1.1
  obtain ⟨D₂, hD₂, -, -, -, l, hl, hw, -, -⟩ := laidOf_ok ((evalLaidB_iff Pw _).1 hE)
  rw [hD] at hD₂
  obtain rfl := Option.some.inj hD₂
  have hplace : (get p).2.book.place[D.w]? = some (wSeat.1, wSeat.2) := by
    unfold wSeatB at hb2
    rw [hl] at hb2
    rw [hw]
    exact of_decide_eq_true (by simpa using hb2)
  have hshape : ((get p).2.st.oracles[D.w]?).map (·.shape) = some (xW.1.l.get xW.2).1 := by
    rw [← hst', ← hsh]
    exact hS.shape
  refine ⟨hst'.trans (hst p).symm, hS.codes, ?_, fun w => ?_, hS.lay.trans hlay.symm, hS.lengths, hsh ▸ hS.code⟩
  · rw [← hst'] at hshape
    obtain ⟨x, hx, hxs⟩ := Option.map_eq_some_iff.1 hshape
    exact ⟨x, hx, hxs⟩
  · rw [hseat]
    exact hbook p w D.w wSeat.1 wSeat.2 _ hplace hshape

/-- **hOc there**: the first chain's last promise, at mg1Joint, reads below lo. -/
theorem hOc_at_ocEnd (lo : Nat)
    (h : sampledBelow lo N₁ ((openSets links ps (start links))[ps.length]?.getD []) = true) :
    OcReadsBelow lo (ocEnd get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁) links ps) :=
  ocEndReadsBelow P₁ P₀ _ get lo N₁ _ links ps (lettersReadBelow_sig cs G arr smp₁ ms₁ decT₁ Mg₁ lo N₁ _ h)

end

end Desc.K14.Law

#print axioms Desc.K14.Law.tabByBook_book
#print axioms Desc.K14.Law.tabByBook_stays
#print axioms Desc.K14.Law.gLaid_is
#print axioms Desc.K14.Law.hW_at_ocEnd
#print axioms Desc.K14.Law.hOc_at_ocEnd
