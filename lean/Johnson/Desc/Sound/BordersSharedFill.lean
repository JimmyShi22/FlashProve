-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BordersSharedFill.lean: THE SHARED CHAIN's TABLE OF JOINTS: ITS LETTERS ON THE READING OF THE ORACLES, FILLED BY THE LIBRARY's OWN
NOTIONS, CALLED (as Johnson/Desc/Sound/BordersFill.lean does for the first chain's table); WHAT "two witnesses agree at a component" MEANS; and THE
TABLE's ONE EXTRACTOR. Definitions, one small lemma, one statement written as `def … : Prop`. (`ExtSSame` asks of arr just what its proof
spends, as a test with code, `apartAt`; `pin₁` is laid by one road alone; a witness has, beside a message's number, A PAD FOR EACH SEAT: `sameAt` asks the pads too, `extS` lays
the pads of the messages that it lays, `apartAt` asks that the seats are apart too).

The type of witnesses is `Wit Cells Tok MsgT` (Johnson/Desc/Msg.lean; Johnson/Desc/Sound/MsgSig.lean).
  `meaningSigS`: TWO LETTERS OF `MeaningS`: pin := `pinJT` at the chain's OWN record's reading of a sample (smp₂) · pinT := `pinWOf` at the decoder of the
    stored table with the record whose key lies in the chain's own record (decT₂). (`pin₁` IS NOT LAID HERE: it is the first chain's table's own `pin`, laid by
    `tiedMeaning`, Johnson/Desc/Sound/TieEnd.lean: one road.)
  `promSigS`: THREE LETTERS OF `PromMeaning`: noColl := `noCollJT` · shown := `shownJT` · held := `smpHeld` at the record's statement and book (by reading, not machine-checked): A FIELD FOR RUNS' SHEETS, in no clause of the promise.
  `sameAt`: TWO WITNESSES AGREE AT A COMPONENT (`Comp`): the cells: equal · a message's, W's, the index masks': equal at the number that arr gives its
    tenant, AND THE PADS AT THAT TENANT's SEAT ARE EQUAL. IT TIES THE TABLE's NAMES OF COMPONENTS TO THE TYPE OF WITNESSES. (No message of this chain is sent again: a component has one seat.)
  `laysAtS`: what the table says that block number k lays.  `mineS`: the members that sit at the tenants of the messages that it lays.
  `extS`: THE EXTRACTOR OF BLOCK NUMBER k: the one extractor (`extAt`, Johnson/Desc/Sound/World.lean) at these members, the cells too where the table
    says so, no token: A FUNCTION OF THE CHAIN's OWN RECORD, THE ORACLES THAT IT IS HANDED, AND THE WITNESS BEHIND: no transcript, no slot's own. Handed the
    acting part's value (`strsOfAct`) it reads the statement through the acting part alone BY MAKE.
  `extS_id` (proved): where the table lays nothing it is the identity.
  `numOfComp`, `seatOfComp`, `apartAt`: A TEST WITH CODE ON THE PLAN's NUMBERS: no message that block number k lays bears the component's number or sits at its seat.
  `ExtSSame` (A STATEMENT): at a component that the table does not lay at k, and that is apart there, what the extractor gives agrees with the witness behind: "the old
    part kept". (arr is not one-to-one on seats by design: a kept copy bears its original's number: so no more is asked than this.)
  THAT IT READS NO TREE OF A SLOT's OWN wants `NumbersS.sorted` (the shared messages sit in the chain's own trees): a premise of nothing here: a test on the plan's numbers beside `apartAt`.

STILL LETTERS, AND WHOSE: nearU · recRow · omU · row cls (K14's, K1's, K12's files: what a row of the record says of the messages) · claimM · ev · dot
(K13's | K14's) · unmarked1 (a definition where the first chain's record's type is at hand: Johnson/Desc/Sound/TieEnd.lean lays it) · tablePromise (the
library's condition on the stored table; from "decodes" by the row table_promise) · shape · nothingLeft (tests with code on the record). Beneath: cs, arr,
smp₂, ms, decT₂, the two readers: functions of the plan and of the record.

Limits. Those of BordersFill.lean: until smp has an honest filling every pin holds of nothing.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Shared.BordersShared
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.Shared

section
variable (cs : OnBytes.Codes) {Xi S₂ P₁ Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → S₂ → Option Cells)

/-- **Two letters of the items' meaning, filled.** -/
def meaningSigS (Mg : MeaningS S₂ P₁ (Wit Cells Tok MsgT)) : MeaningS S₂ P₁ (Wit Cells Tok MsgT) :=
  { Mg with
    pin := pinJT cs G arr smp₂ ms
    pinT := pinWOf decT₂ }

/-- **Three letters of the promise's meaning, filled.** stOf, bookOf: the record's statement and book. -/
def promSigS (stOf : S₂ → OnBytes.Statement) (bookOf : S₂ → OnBytes.TreeBook) (Pm : PromMeaning S₂) :
    PromMeaning S₂ :=
  { Pm with
    noColl := noCollJT cs G smp₂ ms
    shown := shownJT cs G ms
    held := fun j t s => smpHeld (stOf s) (bookOf s) j t }

end

/-- **Two witnesses agree at a component.** -/
def sameAt {Cells Tok : Type} (N : NumbersS) (arr : ℕ → ℕ → ℕ) :
    Comp → Wit Cells Tok MsgT → Wit Cells Tok MsgT → Prop
  | .cells, w, w' => w.cells = w'.cells
  | .msg m, w, w' =>
    w.msg (arr (N.tenant m).1 (N.tenant m).2) = w'.msg (arr (N.tenant m).1 (N.tenant m).2) ∧
      w.pad (N.tenant m).1 (N.tenant m).2 = w'.pad (N.tenant m).1 (N.tenant m).2
  | .w, w, w' => w.msg (arr N.w.1 N.w.2) = w'.msg (arr N.w.1 N.w.2) ∧ w.pad N.w.1 N.w.2 = w'.pad N.w.1 N.w.2
  | .index, w, w' =>
    w.msg (arr N.index.1 N.index.2) = w'.msg (arr N.index.1 N.index.2) ∧
      w.pad N.index.1 N.index.2 = w'.pad N.index.1 N.index.2

/-- What the table says that block number k lays. Behind the last block: nothing. -/
def laysAtS (split : Bool) (k : ℕ) : List Comp := ((sharedPlaces split)[k]?.map (laysOfS split)).getD []

/-- The members that sit at the tenants of the messages that block number k lays. -/
def mineS (N : NumbersS) (ms : List Mem) (split : Bool) (k : ℕ) : List Mem :=
  ms.filter fun x => (laysAtS split k).any fun c =>
    match c with
    | .msg m => decide (x.1.seat x.2 = N.tenant m)
    | _ => false

section
variable (cs : OnBytes.Codes) {Xi S₂ Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → S₂ → Option Cells) (c₀ : Cells)
  (N : NumbersS) (split : Bool)

/-- **The extractor of block number k.** s: the chain's own record in front of the block; y: the oracles that it is handed. -/
def extS (k : ℕ) (s : S₂) (y : Strs) (w : Wit Cells Tok MsgT) : Wit Cells Tok MsgT :=
  extAt cs G arr smp₂ decT₂ c₀ (mineS N ms split k) [] ((laysAtS split k).contains .cells) none s y w

/-- Where the table lays nothing the extractor is the identity. -/
theorem extS_id (k : ℕ) (h : laysAtS split k = []) (s : S₂) (y : Strs) (w : Wit Cells Tok MsgT) :
    extS cs G arr smp₂ ms decT₂ c₀ N split k s y w = w := by
  have h3 : mineS N ms split k = [] := by
    unfold mineS
    rw [h]
    exact List.filter_eq_nil_iff.2 fun _ _ => by simp
  unfold extS
  rw [h3, h]
  exact extAt_none cs G arr smp₂ decT₂ c₀ s y w

end

/-- The number that a component of the witness bears; the cells: none. -/
def numOfComp (N : NumbersS) (arr : ℕ → ℕ → ℕ) : Comp → Option ℕ
  | .cells => none
  | .msg m => some (arr (N.tenant m).1 (N.tenant m).2)
  | .w => some (arr N.w.1 N.w.2)
  | .index => some (arr N.index.1 N.index.2)

/-- The seat of a component of the witness; the cells: none. -/
def seatOfComp (N : NumbersS) : Comp → Option (ℕ × ℕ)
  | .cells => none
  | .msg m => some (N.tenant m)
  | .w => some N.w
  | .index => some N.index

/-- A TEST ON THE PLAN's NUMBERS: no message that block number k lays bears the component's number or sits at its seat. -/
def apartAt (N : NumbersS) (arr : ℕ → ℕ → ℕ) (split : Bool) (k : ℕ) (c : Comp) : Bool :=
  (laysAtS split k).all fun c' =>
    match c' with
    | .msg m' => numOfComp N arr c != some (arr (N.tenant m').1 (N.tenant m').2) &&
        seatOfComp N c != some (N.tenant m')
    | _ => true

/-- **The old part is kept.** -/
def ExtSSame : Prop :=
  ∀ (cs : OnBytes.Codes) (Xi S₂ Cells Tok : Type) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → S₂ → Option Cells) (c₀ : Cells)
    (N : NumbersS) (split : Bool),
    ∀ (k : ℕ) (c : Comp), c ∉ laysAtS split k → apartAt N arr split k c = true →
      ∀ (s : S₂) (y : Strs) (w : Wit Cells Tok MsgT),
      sameAt N arr c (extS cs G arr smp₂ ms decT₂ c₀ N split k s y w) w

/-- What the table lays, by evaluation, with a split: the cells at 1, o_u's message at 9, o_sp's at 10; else nothing. -/
example : (List.range 13).map (laysAtS true) =
    [[], [.cells], [], [], [], [], [], [], [], [.msg .oU], [.msg .oSp], [], []] := by decide
/-- Without a split: the cells at 1, o_u's message at 9; else nothing. -/
example : (List.range 12).map (laysAtS false) =
    [[], [.cells], [], [], [], [], [], [], [], [.msg .oU], [], []] := by decide
-- apartAt CAN FAIL: at numbers that give o_u's and o_omega's tenants one number
example : apartAt ⟨0, fun _ => (0, 0), (1, 0), (2, 0)⟩ (fun j _ => j) true 9 (.msg .oOmega) = false := by decide
example : apartAt ⟨0, fun _ => (0, 0), (1, 0), (2, 0)⟩ (fun j _ => j) true 9 .w = true := by decide

#check @ExtSSame

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.extS_id
