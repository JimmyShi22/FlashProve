-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Own.lean: THE OUTPUT HEAD's BLOCK's OWN LAW AT THE TABLE's FRAME: THE CALL
OF THE BRIDGE FROM A KIND's RULE OF BAD ELEMENTS (Johnson/Desc/Sound/RuleAtKit.lean:
OwnOfRuleAtKit; its proof ownOfRuleAtKit) AT K6: p.Own on on' means In Out, that is p.GoodIn: FOR A
STATEMENT IN FRONT, FIXED, the transcripts at which
the block says yes, the promise behind fails or a witness of what the block opens is no witness of
what it closes, ARE DOOMED WITHIN THE PIECE's ERRORS. STATED AND PROVED. HERE, AT LAST, THE ORDER IN
TIME STANDS IN THE STATEMENT (in GoodIn), AND (pin) IS A THEOREM,
NOT A PREMISE.
  compK6 w THE COMPONENTS THAT K6's RULE READS, OFF THE TABLE's OWN WITNESS (Wit): rd6 of the
      witness's tables THROUGH THE ONE ACCESSOR memTab, and of its cells of the stored table.
  decK6 a THE SAME rd6 of WHAT THE EARLIER MESSAGES DECODE TO AT THE STATEMENT a (by
      decAt: the library's decoder at the committed word in the statement's strings and the sample
      that the record holds; decT for the stored table): A DEFINITION, A FUNCTION OF THE STATEMENT
      IN FRONT ALONE.
  ReadsPinned THIS KIND's HALF OF (pin): rd6 reads the tables at the members ms alone, and there
      inside each message's ranges alone (a pin fixes nothing outside them).
  K6Item · meansK6 · InK6 · OutK6 three items: closed (K6In, and no mark) · opened (K6Out, and no
      mark) · pins (each member of ms is pinned: PinAt; the stored cells: pinWOf).
      The block closes {closed}, opens {opened}; pins stand on both sides (the row's context).
  pin_K6 at a witness that is pinned at a statement, compK6 w = decK6 a: by dec_of_pin
      | tab_of_pin and ReadsPinned.
  pins_back the pins ride back past the piece (by rides; the stored table's decoding by
      the premise DecTStays).
  k6Own        THE CALL.
A SILLY FILLING, WHICH NOTHING HERE SHUTS OUT: rd6 := a constant: ReadsPinned holds, compK6 w =
decK6 a for every w by rfl, and the law speaks of these fixed components and reads nothing of the
witness: true, and not what is wanted. SO "(pin) IS A THEOREM" HAS ITS CONTENT ONLY AT THE REAL rd6
(one that does read the messages), AND ONLY THERE IS THE
TIE OF K6In | K6Out TO THE WITNESS's CELLS MORE THAN A NAME.
WHAT IT DOES NOT SAY. **rd6 IS A LETTER**: from the tables of the messages to the cells and the mask
row: a message holds SYMBOLS, the cells are the integers whose packing the symbols are: that reading
is typed once, in other files (readAt · symAt · ownOf … 24, then Hd.cellsH over the
integers): not called here: this file neither fills rd6 nor proves ReadsPinned of it.
**ms IS A LETTER** (which members hold the head's matrices, the stream and the mask row: the
plan's map: made at no real plan). PREMISES ON THE PIECE, PAID BY NOBODY HERE: it holds below b6, b6
the block as it rides · no round is put behind · its extractor is the identity · Fenced (the
members' trees were sent in front of the piece's base: THE ORDER IN TIME, AS A TEST ON
THE PLAN's NUMBERS) · SmpStays · DecTStays (Law/RowPromise.lean's decide_record says which three
fields turn: that smp and decT read none of them is to be shown where they are filled) · every
round's logN ≤ 64 · ErrBears: the piece's errors bear, round by round, (elements drawn) · priceAt ·
(the kit's share). K6On IS THE PROMISE IN FRONT: it is not inside the table's
own promise yet (by reading): the blocks upstream owe it. The items are OURS, in our own words:
not
the table's Meaning (letters there): planes on neither side; Opened's runs against the table's one
run. K6Out is what later blocks' laws must give. NO MEMBER: no piece is shown to meet the premises;
none is called here. The bridge, the
frame and the pins are in other files. NO SOUNDNESS OF A PROTOCOL OR
A VERIFIER: one block's goodness under these premises.

-/
import Mathlib
import Johnson.Desc.Sound.RuleAtKitProofs
import Johnson.Desc.Sound.SendLaw
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Kinds.Law.K6Frame
import Johnson.Desc.Kinds.Law.RowPromise

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open TypedOracleCompiler.Run.PQ (rvSL)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Piece Frame relAt Sending Mem MsgT memTab decAt PinAt InMsg
    strsOf
  Fenced SmpStays pinWOf ErrBears kitK kitFs)

variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : Nat → Nat →
           Nat)
  (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (Nat → Option (Nat × List UInt64)) → S → Option Cells) (c₀ : Cells)
  (ms : List Mem) (rd6 : (Mem → MsgT) → Cells → Pinned) (Wp : OnBytes.Model.Verify.Public)

/-- **The components that K6's rule reads, off the table's own witness.** -/
def compK6 (w : Wit Cells Tok MsgT) : Pinned := rd6 (memTab cs arr w) w.cells

/-- **The same of what the earlier messages decode to at the statement.** -/
def decK6 (Fr : Frame) (a : S × Fr.E.Str) : Pinned :=
  rd6 (fun x => (decAt cs G smp x.1 x.2 a.1 (strsOf Fr a.2)).getD fun _ _ _ => 0)
    ((decT (strsOf Fr a.2).cell a.1).getD c₀)

/-- **This kind's half of (pin)**: rd6 reads the tables at the members ms alone, inside each
message's ranges alone. -/
def ReadsPinned : Prop :=
  ∀ (T T' : Mem → MsgT) (c : Cells),
    (∀ x ∈ ms, ∀ mask row place, InMsg cs (x.1.l.get x.2).1 mask row place →
      T x mask row place = T' x mask row place) → rd6 T c = rd6 T' c

/-- The items at K6's two borders. -/
inductive K6Item | closed | opened | pins

/-- What each item says of a statement and a witness. -/
def meansK6 (Fr : Frame) : K6Item → S × Fr.E.Str → Wit Cells Tok MsgT → Prop
  | .closed, a, w => K6In Wp a.1 (compK6 cs arr rd6 w) ∧ a.1.failed = none
  | .opened, b, w => K6Out Wp b.1 (compK6 cs arr rd6 w) ∧ b.1.failed = none
  | .pins, a, w => Sound.Pinned cs G arr smp ms a.1 (strsOf Fr a.2) w ∧
      pinWOf decT a.1 (strsOf Fr a.2) w

def InK6 : K6Item → Prop := fun i => i = .closed ∨ i = .pins
def OutK6 : K6Item → Prop := fun i => i = .opened ∨ i = .pins

/-- Where the piece says yes, the stored table decodes behind it as in front. -/
def DecTStays {C : _root_.Run.PQ.CK} {Fr : Frame} {Cl W : Type} (p : Piece C Fr S Cl W) : Prop :=
  ∀ a τ b, p.ior.red.out a τ = some b →
    decT (strsOf Fr b.2).cell b.1 = decT (strsOf Fr a.2).cell a.1

namespace Came

/-- **(pin), at one statement: A THEOREM.** -/
theorem pin_K6 (hloc : ReadsPinned cs ms rd6) (Fr : Frame) (a : S × Fr.E.Str)
    (w : Wit Cells Tok MsgT) (h : meansK6 cs G arr smp decT ms rd6 Wp Fr .pins a w) :
    compK6 cs arr rd6 w = decK6 cs G smp decT c₀ rd6 Fr a := by
  obtain ⟨hP, hW⟩ := h
  have hW' : decT (strsOf Fr a.2).cell a.1 = some w.cells := hW
  unfold compK6 decK6
  rw [hW', Option.getD_some]
  refine hloc _ _ _ fun x hx mask row place hin => ?_
  have hd := Sound.dec_of_pin cs G arr smp x.1 x.2 a.1 (strsOf Fr a.2) w (hP x hx)
  rw [hd, Option.getD_some]
  exact Sound.tab_of_pin cs G arr smp x.1 x.2 a.1 (strsOf Fr a.2) w _ hd (hP x hx) mask row place
      hin

/-- **The pins ride back past the piece.** -/
theorem pins_back {C : _root_.Run.PQ.CK} {Fr : Frame} {Cl : Type}
    (p : Piece C Fr S Cl (Wit Cells Tok MsgT)) (hF : Fenced p.base ms) (hS : SmpStays cs smp p ms)
    (hD : DecTStays decT p) (a b : S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) (w : Wit Cells Tok MsgT)
    (h : meansK6 cs G arr smp decT ms rd6 Wp Fr .pins b w) :
    meansK6 cs G arr smp decT ms rd6 Wp Fr .pins a w := by
  obtain ⟨hP, hW⟩ := h
  refine ⟨fun x hx => ((Sound.rides cs G arr smp p ms hF hS a b τ hb x hx).1 w).1 (hP x hx), ?_⟩
  have hW' : decT (strsOf Fr b.2).cell b.1 = some w.cells := hW
  show decT (strsOf Fr a.2).cell a.1 = some w.cells
  rw [← hD a τ b hb]
  exact hW'

include c₀ in
/-- **THE CALL: K6's OWN LAW AT THE TABLE's FRAME.** (c₀: any cells: what decK6 reads where the
stored table does not decode.) -/
theorem k6Own (fld : Fmt.Fld) (Fr : Frame)
    (p : Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)) (l : Nat) (b6 : Block S Unit)
    (hb6 : blockOf Wp l = some b6) (hpb : p.b = Sound.below b6) (hback : p.back = [])
    (hext : ∀ a τ w, p.ext a τ w = w) (hloc : ReadsPinned cs ms rd6) (hF : Fenced p.base ms)
    (hS : SmpStays cs smp p ms) (hD : DecTStays decT p)
    (hlog : ∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs p.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs p.ds) j)) (toRDs p.ds) 0 p.err) :
    p.Own (fun a => K6On Wp a.1) (fun b => K6After Wp b.1)
      (meansK6 cs G arr smp decT ms rd6 Wp Fr) InK6 OutK6 := by
  have hstep : ∀ a τ b, p.ior.red.out a τ = some b →
      ∃ cols n, Canonical (rvSL (_root_.Run.ckP fld) (toRDs p.ds) τ) ∧
        b6.step Fr.ft a.1 (rvSL (_root_.Run.ckP fld) (toRDs p.ds) τ) cols = .ok (b.1, n) := by
    intro a τ b hout
    obtain ⟨cols, n, hs⟩ := out_step p a b τ hout
    rw [hback, List.append_nil, hpb] at hs
    exact ⟨cols, n, below_step Fr.ft b6 a.1 _ cols b.1 n hs⟩
  refine Sound.ownOfRuleAtKit S Unit (Wit Cells Tok MsgT) K6Item Pinned fld Fr p _ _ _ _ _
    (compK6 cs arr rd6) (decK6 cs G smp decT c₀ rd6 Fr) (fun a d => ruleStep Wp a.1 d)
    (priceAt (parOf Wp.hS (workOf Wp))) ?_ hlog hErr ?_ ?_ ?_
  · intro a d g _
    exact ruleStep_length Wp a.1 d g
  · intro a τ b w _ hout hrel
    exact pin_K6 cs G arr smp decT c₀ ms rd6 Wp hloc Fr a w
      (pins_back cs G arr smp decT ms rd6 Wp p hF hS hD a b τ hout w (hrel .pins (Or.inr rfl)))
  · intro a τ b ha _ _ hout
    obtain ⟨cols, n, _, hs⟩ := hstep a τ b hout
    exact (rowPromise Wp l b6 hb6 Fr.ft a.1 _ cols b.1 n ha hs).1
  · intro a τ b w ha _ hnb hout hrel i hi
    obtain ⟨cols, n, hcan, hs⟩ := hstep a τ b hout
    rw [hext]
    rcases hi with rfl | rfl
    · exact ⟨rowStep Wp l b6 hb6 Fr.ft a.1 (compK6 cs arr rd6 w) _ cols b.1 n ha hnb hcan hs
        (hrel .opened (Or.inl rfl)).1, (unmarked_both Wp l b6 hb6 Fr.ft a.1 _ cols b.1 n hs).1⟩
    · exact pins_back cs G arr smp decT ms rd6 Wp p hF hS hD a b τ hout w (hrel .pins (Or.inr rfl))

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.pin_K6
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.pins_back
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6Own
