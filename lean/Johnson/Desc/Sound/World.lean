-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/World.lean: THE ONE MAP FROM A STATEMENT TO THE WITNESS: what the oracles'
strings decode to, with the samples and the record that the chain's record holds. Definitions, and
their first laws, proved.

Why. The top's statement on a proof file asks for ONE witness map, which reads the instance, the
record, the committed string and the transcript. In the rule of composition each piece has an
extractor (`Piece.ext`: the statement in front of the block, the stretch's transcript, the witness
behind ↦ the witness in front). THE FORM THAT IS MEANT, and that is still to be shown kind by kind:
no kind has an extractor of its own: a block either leaves the witness as it is, or lays components
of it, and what it lays is what the strings decode to (the token: what the record behind has heard).
  `Sending`, `Mem`: one sending's sampled members: their shapes with their radii, and their seats
    (tree, tenant).
  `toMsgT`, `InMsg`, `msgs_back`, `msgs_forth`: a member's typed message as a total function; inside
    the member's ranges it is the witness's table at the member's seat (`Wit.tab`, MsgSig.lean) just
    where the witness's typed message is that message.
  `decAt s i a`: WHAT MEMBER i OF THE SENDING s DECODES TO AT THE STATEMENT a: by the library's
    decoder with a sample (`OMsg.dec`), where the record holds the member's sample and every leaf is
    shown; else nothing.
  `pin_of_dec`, `tab_of_pin` (proved): a witness is pinned at a member that decodes (`PinAt`,
    MsgSig.lean) just where its table at the member's seat is, inside the ranges, what the member
    decodes to. `pin_congr` (proved): a pin reads the member's two components alone: the message of
    its number and the pad of its seat.
  `numOf`, `seatOf`, `memTab`: a member's number, its seat, the witness's table of it.
  `tabBy key ms a k`, `AgreeBy`, `tabBy_of` (proved): what the first of ms with the key k that
    decodes decodes to (the zero message if none does); where all of ms with one key that decode
    decode alike, it is what each decodes to. `msgAt`, `Agree`, `msgAt_of`: by number. `padAt`: by
    seat.
  `AgreeOff`, `msgAt_off` (proved): alike OUTSIDE THEIR PADS: what can hold of a message and its
    later copies, which are sent with other pads.
  `worldOf`, `pin_world` (proved): THE MAP at all members of all sendings: cells: what the stored
    table decodes to with the record (a letter: `decT`; a fixed value where it does not decode);
    tok: the token heard, off the record (a letter); msg: `msgAt`; pad: `padAt`.
  `extAt mine minePad cellsToo tokNew a w`: **THE EXTRACTOR OF EVERY ROW**: w, with the components
    of THE ROW's OWN MEMBERS set to what these decode to at the statement in front of the block: of
    mine (the seats whose pins it closes) the message and the pad; of minePad the pad alone. Not by
    the file's first member with that number: an older copy's seat may decode otherwise.
  `pin_ext`, `pin_ext_pad`, `extAt_other`, `extAt_other_pad`, `extAt_none` (proved): a member of the
    row's own that decodes is pinned at what the extractor gives (one of minePad: where the witness
    behind has its message outside the pad already); every other component is left; a row without
    members, cells and token leaves all.
  `pins_clash`, `pin_both` (proved): WHY EACH SEAT HAS A PAD OF ITS OWN: were the pad's places read
    off the message's number, a message and a copy that part there could not both be pinned at one
    witness; as it is they can.
  `dec_of_pin`, `tabAlike`, `ext_of_pinned` (proved): THE CARRYING: two witnesses that read alike at
    a member are pinned alike there; and where a member of minePad is pinned at a witness w', the
    extractor's value reads there as w' does: so a law may be proved at pads from elsewhere.
  `restWorld`: a piece's `Rest` (Tiles.lean) at that extractor.
  HOW IT IS TO BE THE TOP's WITNESS MAP (a plan: no equation is typed yet): the rows' extractors in
  a row (`IOR.extSeq`) take the first statement (the instance's record, the committed string, empty
  trees), the whole transcript and a fixed last witness to a `Wit`; its `cells` are the top's
  witness.
Limits. `decT`, `tokOf`, `smp` are letters. A message without a sample is no member: no component is
laid for it, and no boundary's relation speaks of it (WordsLaw.lean: WHO IS NO MEMBER). A pin fixes
a message INSIDE THE MEMBER's RANGES ALONE (rows below its rows, places below its length): outside
them `toMsgT` lays 0 and `PinAt` compares nothing. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MsgSig
import Johnson.Desc.Sound.Tiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)

/-- One sending's sampled members: shapes with radii, and seats (tree through the file, tenant). -/
structure Sending where
  l : List (OnBytes.OracleShape × ℕ)
  seat : Fin l.length → ℕ × ℕ

section
variable (cs : OnBytes.Codes)

/-- A member's typed message as a total function: mask row or main row, row, place; 0 outside. -/
def toMsgT (l : List (OnBytes.OracleShape × ℕ)) (i : Fin l.length)
    (m : ((sigOf cs l).om i).Msg) : MsgT := fun mask row place =>
  if mask then
    if h : row < (l.get i).1.maskRows ∧ place < (pMask cs (l.get i).1).ell then
      m (.inr (⟨row, h.1⟩, ⟨place, h.2⟩)) else 0
  else
    if h : row < (l.get i).1.mainRows ∧ place < (pMain cs (l.get i).1).ell then
      m (.inl (⟨row, h.1⟩, ⟨place, h.2⟩)) else 0

/-- Inside a message's ranges: rows below its rows, places below its length. -/
def InMsg (s : OnBytes.OracleShape) (mask : Bool) (row place : ℕ) : Prop :=
  if mask = true then row < s.maskRows ∧ place < (pMask cs s).ell
  else row < s.mainRows ∧ place < (pMain cs s).ell

/-- And back: where the witness's table at the member's seat is that function inside the ranges. -/
theorem msgs_back {Cells Tok : Type} (l : List (OnBytes.OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT) (i : Fin l.length)
    (m : ((sigOf cs l).om i).Msg)
    (h : ∀ mask row place, InMsg cs (l.get i).1 mask row place →
      w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 mask row place =
        toMsgT cs l i m mask row place) :
    msgsOf cs l seat arr w i = m := by
  funext j
  rcases j with q | q
  · show w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 false q.1.val
      q.2.val = m (.inl q)
    rw [h false q.1.val q.2.val (by
      unfold InMsg
      rw [if_neg (by decide)]
      exact ⟨q.1.isLt, q.2.isLt⟩)]
    unfold toMsgT
    rw [if_neg (by decide), dif_pos ⟨q.1.isLt, q.2.isLt⟩]
  · show w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 true q.1.val
      q.2.val = m (.inr q)
    rw [h true q.1.val q.2.val (by
      unfold InMsg
      rw [if_pos rfl]
      exact ⟨q.1.isLt, q.2.isLt⟩)]
    unfold toMsgT
    rw [if_pos rfl, dif_pos ⟨q.1.isLt, q.2.isLt⟩]

/-- And forth: inside the ranges the witness's table at the member's seat is its typed message. -/
theorem msgs_forth {Cells Tok : Type} (l : List (OnBytes.OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT) (i : Fin l.length)
    (mask : Bool) (row place : ℕ) (hin : InMsg cs (l.get i).1 mask row place) :
    w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 mask row place =
      toMsgT cs l i (msgsOf cs l seat arr w i) mask row place := by
  cases mask
  · unfold InMsg at hin
    rw [if_neg (by decide)] at hin
    have e : toMsgT cs l i (msgsOf cs l seat arr w i) false row place =
        msgsOf cs l seat arr w i (.inl (⟨row, hin.1⟩, ⟨place, hin.2⟩)) := by
      unfold toMsgT
      rw [if_neg (by decide), dif_pos hin]
    exact e.symm
  · unfold InMsg at hin
    rw [if_pos rfl] at hin
    have e : toMsgT cs l i (msgsOf cs l seat arr w i) true row place =
        msgsOf cs l seat arr w i (.inr (⟨row, hin.1⟩, ⟨place, hin.2⟩)) := by
      unfold toMsgT
      rw [if_pos rfl, dif_pos hin]
    exact e.symm

variable {Xi : Type} (G : FileDescription Xi) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

open Classical in
/-- **What member i of the sending s decodes to at the statement (a, y).** -/
def decAt (s : Sending) (i : Fin s.l.length) (a : A) (y : Strs) : Option MsgT :=
  (smp a s i).bind fun z =>
    if ShownAt G cs s.l s.seat y i then
      (((sigOf cs s.l).om i).dec (wordsOf G cs s.l s.seat y i) z).map (toMsgT cs s.l i)
    else none

/-- A witness whose table at the member's seat is, inside the ranges, what the member decodes to is
pinned there. -/
theorem pin_of_dec (s : Sending) (i : Fin s.l.length) (a : A) (y : Strs) (w : Wit Cells Tok MsgT)
    (m : MsgT) (hd : decAt cs G smp s i a y = some m)
    (hw : ∀ mask row place, InMsg cs (s.l.get i).1 mask row place →
      w.tab cs (s.l.get i).1 (arr (s.seat i).1 (s.seat i).2) (s.seat i).1 (s.seat i).2 mask row
        place = m mask row place) :
    PinAt G cs s.l s.seat (fun x => smp x s) arr i a y w := by
  unfold decAt at hd
  obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 hd
  by_cases hs : ShownAt G cs s.l s.seat y i
  · rw [if_pos hs] at h
    obtain ⟨m₀, hm, e⟩ := Option.map_eq_some_iff.1 h
    subst e
    exact ⟨z, hz, hs, by rw [hm, msgs_back cs s.l s.seat arr w i m₀ hw]⟩
  · rw [if_neg hs] at h
    cases h

/-- And the other way: at a pinned witness the table at the member's seat is, inside the ranges,
what the member decodes to. -/
theorem tab_of_pin (s : Sending) (i : Fin s.l.length) (a : A) (y : Strs) (w : Wit Cells Tok MsgT)
    (m : MsgT) (hd : decAt cs G smp s i a y = some m)
    (hp : PinAt G cs s.l s.seat (fun x => smp x s) arr i a y w) (mask : Bool) (row place : ℕ)
    (hin : InMsg cs (s.l.get i).1 mask row place) :
    w.tab cs (s.l.get i).1 (arr (s.seat i).1 (s.seat i).2) (s.seat i).1 (s.seat i).2 mask row
      place = m mask row place := by
  obtain ⟨z, hz, hs, hm⟩ := hp
  have hz' : smp a s i = some z := hz
  unfold decAt at hd
  rw [hz', Option.bind_some, if_pos hs, hm] at hd
  have e : toMsgT cs s.l i (msgsOf cs s.l s.seat arr w i) = m := Option.some.inj hd
  rw [← e]
  exact msgs_forth cs s.l s.seat arr w i mask row place hin

/-- A pin reads of the witness the member's two components alone. -/
theorem pin_congr (s : Sending) (i : Fin s.l.length) (a : A) (y : Strs)
    (w w' : Wit Cells Tok MsgT)
    (e1 : w'.msg (arr (s.seat i).1 (s.seat i).2) = w.msg (arr (s.seat i).1 (s.seat i).2))
    (e2 : w'.pad (s.seat i).1 (s.seat i).2 = w.pad (s.seat i).1 (s.seat i).2)
    (h : PinAt G cs s.l s.seat (fun x => smp x s) arr i a y w) :
    PinAt G cs s.l s.seat (fun x => smp x s) arr i a y w' := by
  obtain ⟨z, hz, hs, hm⟩ := h
  have e : msgsOf cs s.l s.seat arr w' i = msgsOf cs s.l s.seat arr w i := by
    funext j
    rcases j with q | q
    · show w'.tab cs (s.l.get i).1 (arr (s.seat i).1 (s.seat i).2) (s.seat i).1 (s.seat i).2 false
        q.1.val q.2.val = w.tab cs (s.l.get i).1 (arr (s.seat i).1 (s.seat i).2) (s.seat i).1
          (s.seat i).2 false q.1.val q.2.val
      unfold Wit.tab
      rw [e1, e2]
    · show w'.tab cs (s.l.get i).1 (arr (s.seat i).1 (s.seat i).2) (s.seat i).1 (s.seat i).2 true
        q.1.val q.2.val = w.tab cs (s.l.get i).1 (arr (s.seat i).1 (s.seat i).2) (s.seat i).1
          (s.seat i).2 true q.1.val q.2.val
      unfold Wit.tab
      rw [e1, e2]
  exact ⟨z, hz, hs, by rw [e]; exact hm⟩

/-- A member of a sending. -/
abbrev Mem : Type := Σ s : Sending, Fin s.l.length

/-- All members of all sendings, in order. -/
def membersOf (sends : List Sending) : List Mem :=
  sends.flatMap fun s => (List.finRange s.l.length).map fun i => ⟨s, i⟩

/-- A member's number in the witness. -/
def numOf (x : Mem) : ℕ := arr (x.1.seat x.2).1 (x.1.seat x.2).2

/-- A member's seat: tree through the file, tenant. -/
def seatOf (x : Mem) : ℕ × ℕ := x.1.seat x.2

/-- **The witness's table of a member**: the one accessor (`Wit.tab`, MsgSig.lean) at the member's
own shape, number and seat. -/
def memTab (w : Wit Cells Tok MsgT) (x : Mem) : MsgT :=
  w.tab cs (x.1.l.get x.2).1 (numOf arr x) (x.1.seat x.2).1 (x.1.seat x.2).2

section
variable {κ : Type} [DecidableEq κ] (key : Mem → κ)

/-- What the first of the members ms with the key k that decodes decodes to at the statement (a, y);
the zero message if none does. -/
def tabBy (ms : List Mem) (a : A) (y : Strs) (k : κ) : MsgT :=
  (ms.findSome? fun x =>
    if key x = k then decAt cs G smp x.1 x.2 a y else none).getD fun _ _ _ => 0

/-- All of the members ms with one key that decode decode alike. -/
def AgreeBy (ms : List Mem) (a : A) (y : Strs) (k : κ) : Prop :=
  ∀ x ∈ ms, ∀ x' ∈ ms, key x = k → key x' = k →
    ∀ m m', decAt cs G smp x.1 x.2 a y = some m → decAt cs G smp x'.1 x'.2 a y = some m' → m = m'

/-- The first with the key that decodes is one of them with the key that decodes. -/
theorem tabBy_some (ms : List Mem) (a : A) (y : Strs) (x : Mem) (hx : x ∈ ms) (m : MsgT)
    (hd : decAt cs G smp x.1 x.2 a y = some m) :
    ∃ x₀ ∈ ms, key x₀ = key x ∧
      decAt cs G smp x₀.1 x₀.2 a y = some (tabBy cs G smp key ms a y (key x)) := by
  unfold tabBy
  cases hf : ms.findSome? fun x' =>
      if key x' = key x then decAt cs G smp x'.1 x'.2 a y else none with
  | none =>
    have t := List.findSome?_eq_none_iff.1 hf x hx
    rw [if_pos rfl, hd] at t
    cases t
  | some m₀ =>
    obtain ⟨x₀, h₀, e₀⟩ := List.exists_of_findSome?_eq_some hf
    by_cases hn : key x₀ = key x
    · rw [if_pos hn] at e₀
      exact ⟨x₀, h₀, hn, e₀⟩
    · rw [if_neg hn] at e₀
      cases e₀

theorem tabBy_of (ms : List Mem) (a : A) (y : Strs) (x : Mem) (hx : x ∈ ms) (m : MsgT)
    (hd : decAt cs G smp x.1 x.2 a y = some m) (hA : AgreeBy cs G smp key ms a y (key x)) :
    tabBy cs G smp key ms a y (key x) = m := by
  obtain ⟨x₀, h₀, hn, e₀⟩ := tabBy_some cs G smp key ms a y x hx m hd
  exact hA x₀ h₀ x hx hn rfl _ m e₀ hd

end

/-- **The message number n at the statement (a, y), by the members ms**: what the first of them with
that number that decodes decodes to; the zero message if none does. -/
def msgAt (ms : List Mem) (a : A) (y : Strs) (n : ℕ) : MsgT :=
  tabBy cs G smp (numOf arr) ms a y n

/-- **The table of which tenant t of tree j's pad is read**: what the first of the members ms that
sits there and decodes decodes to. -/
def padAt (ms : List Mem) (a : A) (y : Strs) (j t : ℕ) : MsgT :=
  tabBy cs G smp seatOf ms a y (j, t)

/-- All of the members ms with one number that decode decode alike, THE PAD's PLACES TOO: meant for
a row's own members, of which no two have one number. OF A MESSAGE AND ITS LATER COPY IT IS FALSE AT
AN HONEST RUN: see `AgreeOff`. -/
def Agree (ms : List Mem) (a : A) (y : Strs) (n : ℕ) : Prop :=
  AgreeBy cs G smp (numOf arr) ms a y n

theorem msgAt_of (ms : List Mem) (a : A) (y : Strs) (x : Mem) (hx : x ∈ ms) (m : MsgT)
    (hd : decAt cs G smp x.1 x.2 a y = some m) (hA : Agree cs G arr smp ms a y (numOf arr x)) :
    msgAt cs G arr smp ms a y (numOf arr x) = m :=
  tabBy_of cs G smp (numOf arr) ms a y x hx m hd hA

/-- **All of the members ms with one number that decode decode alike OUTSIDE THEIR PADS.** Taken
both ways it asks them to be alike at every place that is not the pad's place of BOTH: so it can be
met at an honest run only where the copies of a message have their pads at one place and one range:
a test on the plan (seats with one number have one shape in the numbers that `padB` and `InMsg`
read). -/
def AgreeOff (ms : List Mem) (a : A) (y : Strs) (n : ℕ) : Prop :=
  ∀ x ∈ ms, ∀ x' ∈ ms, numOf arr x = n → numOf arr x' = n →
    ∀ m m', decAt cs G smp x.1 x.2 a y = some m → decAt cs G smp x'.1 x'.2 a y = some m' →
      ∀ mask row place, padB cs (x.1.l.get x.2).1 mask row place = false →
        m mask row place = m' mask row place

theorem msgAt_off (ms : List Mem) (a : A) (y : Strs) (x : Mem) (hx : x ∈ ms) (m : MsgT)
    (hd : decAt cs G smp x.1 x.2 a y = some m) (hA : AgreeOff cs G arr smp ms a y (numOf arr x))
    (mask : Bool) (row place : ℕ) (hp : padB cs (x.1.l.get x.2).1 mask row place = false) :
    msgAt cs G arr smp ms a y (numOf arr x) mask row place = m mask row place := by
  obtain ⟨x₀, h₀, hn, e₀⟩ := tabBy_some cs G smp (numOf arr) ms a y x hx m hd
  exact (hA x hx x₀ h₀ rfl hn m _ hd e₀ mask row place hp).symm

variable (decT : (ℕ → Option (ℕ × List UInt64)) → A → Option Cells) (c₀ : Cells) (tokOf : A → Tok)

/-- **THE MAP: the world of a statement.** decT: what the stored table decodes to, with the record
that the chain's record holds. -/
def worldOf (sends : List Sending) (a : A) (y : Strs) : Wit Cells Tok MsgT :=
  ⟨(decT y.cell a).getD c₀, tokOf a, msgAt cs G arr smp (membersOf sends) a y,
    padAt cs G smp (membersOf sends) a y⟩

/-- Where the members with its number agree outside their pads, and those at its seat agree, a
member that decodes is pinned at the world. -/
theorem pin_world (sends : List Sending) (a : A) (y : Strs) (x : Mem) (hx : x ∈ membersOf sends)
    (m : MsgT) (hd : decAt cs G smp x.1 x.2 a y = some m)
    (hA : AgreeOff cs G arr smp (membersOf sends) a y (numOf arr x))
    (hS : AgreeBy cs G smp seatOf (membersOf sends) a y (seatOf x)) :
    PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y
      (worldOf cs G arr smp decT c₀ tokOf sends a y) := by
  refine pin_of_dec cs G arr smp x.1 x.2 a y _ m hd ?_
  intro mask row place _
  show (if padB cs (x.1.l.get x.2).1 mask row place = true then
      padAt cs G smp (membersOf sends) a y (x.1.seat x.2).1 (x.1.seat x.2).2 mask row place
    else msgAt cs G arr smp (membersOf sends) a y (numOf arr x) mask row place) = m mask row place
  have h2 : padAt cs G smp (membersOf sends) a y (x.1.seat x.2).1 (x.1.seat x.2).2 = m :=
    tabBy_of cs G smp seatOf (membersOf sends) a y x hx m hd hS
  by_cases hp : padB cs (x.1.l.get x.2).1 mask row place = true
  · rw [if_pos hp, h2]
  · rw [if_neg hp]
    exact msgAt_off cs G arr smp (membersOf sends) a y x hx m hd hA mask row place
      (Bool.eq_false_iff.2 hp)

/-- **THE EXTRACTOR OF EVERY ROW**: the witness behind the block, with the components that the row
lays set to what THE ROW's OWN MEMBERS decode to at the statement in front of the block. mine: the
seats whose pins it closes: their messages' numbers AND their seats' pads are laid (the whole
decoded table at both: of the first only the places outside the pad are ever read, of the second
only the pad's). minePad: the seats of which it lays THE PAD ALONE (an older copy of a message that
is sent again: the message's number stays the later copy's row's to lay). cellsToo: the cells as
well; tokNew: the token, where the row lays it (it is in no oracle: the caller reads it off the
record that the block puts out). -/
def extAt (mine minePad : List Mem) (cellsToo : Bool) (tokNew : Option Tok) (a : A) (y : Strs)
    (w : Wit Cells Tok MsgT) : Wit Cells Tok MsgT :=
  ⟨if cellsToo then (decT y.cell a).getD c₀ else w.cells, tokNew.getD w.tok,
    fun n => if n ∈ mine.map (numOf arr) then msgAt cs G arr smp mine a y n else w.msg n,
    fun j t => if (j, t) ∈ (mine ++ minePad).map seatOf then
      padAt cs G smp (mine ++ minePad) a y j t else w.pad j t⟩

/-- A row that lays nothing leaves the witness as it is. -/
theorem extAt_none (a : A) (y : Strs) (w : Wit Cells Tok MsgT) :
    extAt cs G arr smp decT c₀ [] [] false none a y w = w := by
  unfold extAt
  simp

/-- **A member of the row's own that decodes is pinned at what the row's extractor gives**, where
the row's own members with its number agree, and those at its seat (so always where no two of them
have one number or one seat). -/
theorem pin_ext (mine minePad : List Mem) (cellsToo : Bool) (tokNew : Option Tok) (a : A)
    (y : Strs) (w : Wit Cells Tok MsgT) (x : Mem) (hx : x ∈ mine) (m : MsgT)
    (hd : decAt cs G smp x.1 x.2 a y = some m) (hA : Agree cs G arr smp mine a y (numOf arr x))
    (hS : AgreeBy cs G smp seatOf (mine ++ minePad) a y (seatOf x)) :
    PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y
      (extAt cs G arr smp decT c₀ mine minePad cellsToo tokNew a y w) := by
  refine pin_of_dec cs G arr smp x.1 x.2 a y _ m hd ?_
  intro mask row place _
  show (if padB cs (x.1.l.get x.2).1 mask row place = true then
      (if ((x.1.seat x.2).1, (x.1.seat x.2).2) ∈ (mine ++ minePad).map seatOf then
        padAt cs G smp (mine ++ minePad) a y (x.1.seat x.2).1 (x.1.seat x.2).2
      else w.pad (x.1.seat x.2).1 (x.1.seat x.2).2) mask row place
    else (if numOf arr x ∈ mine.map (numOf arr) then msgAt cs G arr smp mine a y (numOf arr x)
      else w.msg (numOf arr x)) mask row place) = m mask row place
  have h1 : ((x.1.seat x.2).1, (x.1.seat x.2).2) ∈ (mine ++ minePad).map seatOf :=
    List.mem_map.2 ⟨x, List.mem_append_left _ hx, rfl⟩
  have h2 : padAt cs G smp (mine ++ minePad) a y (x.1.seat x.2).1 (x.1.seat x.2).2 = m :=
    tabBy_of cs G smp seatOf (mine ++ minePad) a y x (List.mem_append_left _ hx) m hd hS
  rw [if_pos h1, if_pos (List.mem_map.2 ⟨x, hx, rfl⟩), h2,
    msgAt_of cs G arr smp mine a y x hx m hd hA]
  split <;> rfl

/-- **A member of which the row lays the pad alone**, that decodes, is pinned at what the row's
extractor gives, WHERE THE WITNESS BEHIND HAS ITS MESSAGE OUTSIDE THE PAD ALREADY (inside the
member's ranges), and the row does not lay that number. -/
theorem pin_ext_pad (mine minePad : List Mem) (cellsToo : Bool) (tokNew : Option Tok) (a : A)
    (y : Strs) (w : Wit Cells Tok MsgT) (x : Mem) (hx : x ∈ minePad) (m : MsgT)
    (hd : decAt cs G smp x.1 x.2 a y = some m)
    (hS : AgreeBy cs G smp seatOf (mine ++ minePad) a y (seatOf x))
    (hn : numOf arr x ∉ mine.map (numOf arr))
    (hoff : ∀ mask row place, InMsg cs (x.1.l.get x.2).1 mask row place →
      padB cs (x.1.l.get x.2).1 mask row place = false →
        w.msg (numOf arr x) mask row place = m mask row place) :
    PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y
      (extAt cs G arr smp decT c₀ mine minePad cellsToo tokNew a y w) := by
  refine pin_of_dec cs G arr smp x.1 x.2 a y _ m hd ?_
  intro mask row place hin
  show (if padB cs (x.1.l.get x.2).1 mask row place = true then
      (if ((x.1.seat x.2).1, (x.1.seat x.2).2) ∈ (mine ++ minePad).map seatOf then
        padAt cs G smp (mine ++ minePad) a y (x.1.seat x.2).1 (x.1.seat x.2).2
      else w.pad (x.1.seat x.2).1 (x.1.seat x.2).2) mask row place
    else (if numOf arr x ∈ mine.map (numOf arr) then msgAt cs G arr smp mine a y (numOf arr x)
      else w.msg (numOf arr x)) mask row place) = m mask row place
  have h1 : ((x.1.seat x.2).1, (x.1.seat x.2).2) ∈ (mine ++ minePad).map seatOf :=
    List.mem_map.2 ⟨x, List.mem_append_right _ hx, rfl⟩
  have h2 : padAt cs G smp (mine ++ minePad) a y (x.1.seat x.2).1 (x.1.seat x.2).2 = m :=
    tabBy_of cs G smp seatOf (mine ++ minePad) a y x (List.mem_append_right _ hx) m hd hS
  rw [if_pos h1, if_neg hn, h2]
  by_cases hp : padB cs (x.1.l.get x.2).1 mask row place = true
  · rw [if_pos hp]
  · rw [if_neg hp]
    exact hoff mask row place hin (Bool.eq_false_iff.2 hp)

/-- A message whose number is none of the row's own members' is left as it is. -/
theorem extAt_other (mine minePad : List Mem) (cellsToo : Bool) (tokNew : Option Tok) (a : A)
    (y : Strs) (w : Wit Cells Tok MsgT) (n : ℕ) (h : n ∉ mine.map (numOf arr)) :
    (extAt cs G arr smp decT c₀ mine minePad cellsToo tokNew a y w).msg n = w.msg n := by
  show (if n ∈ mine.map (numOf arr) then _ else _) = _
  rw [if_neg h]

/-- A pad at a seat that is none of the row's is left as it is. -/
theorem extAt_other_pad (mine minePad : List Mem) (cellsToo : Bool) (tokNew : Option Tok) (a : A)
    (y : Strs) (w : Wit Cells Tok MsgT) (j t : ℕ) (h : (j, t) ∉ (mine ++ minePad).map seatOf) :
    (extAt cs G arr smp decT c₀ mine minePad cellsToo tokNew a y w).pad j t = w.pad j t := by
  show (if (j, t) ∈ (mine ++ minePad).map seatOf then _ else _) = _
  rw [if_neg h]

/-- **THE FAULT THAT THE SEATS' PADS CURE, SAID IN LEAN**: at a witness that reads the pad's places
off the message's number too (its pads at the two seats ARE its message), two members with one
number that decode to tables which part at a place inside both ranges cannot both be pinned. (A
message and its later copy part at the pad.) -/
theorem pins_clash (x x' : Mem) (a : A) (y : Strs) (w : Wit Cells Tok MsgT)
    (hn : numOf arr x = numOf arr x')
    (hp : w.pad (x.1.seat x.2).1 (x.1.seat x.2).2 = w.msg (numOf arr x))
    (hp' : w.pad (x'.1.seat x'.2).1 (x'.1.seat x'.2).2 = w.msg (numOf arr x')) (m m' : MsgT)
    (hd : decAt cs G smp x.1 x.2 a y = some m) (hd' : decAt cs G smp x'.1 x'.2 a y = some m')
    (mask : Bool) (row place : ℕ) (hin : InMsg cs (x.1.l.get x.2).1 mask row place)
    (hin' : InMsg cs (x'.1.l.get x'.2).1 mask row place)
    (hne : m mask row place ≠ m' mask row place) :
    ¬ (PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w ∧
      PinAt G cs x'.1.l x'.1.seat (fun z => smp z x'.1) arr x'.2 a y w) := by
  rintro ⟨p, p'⟩
  have t := tab_of_pin cs G arr smp x.1 x.2 a y w m hd p mask row place hin
  have t' := tab_of_pin cs G arr smp x'.1 x'.2 a y w m' hd' p' mask row place hin'
  have u : w.tab cs (x.1.l.get x.2).1 (numOf arr x) (x.1.seat x.2).1 (x.1.seat x.2).2 mask row
      place = w.msg (numOf arr x) mask row place := by
    unfold Wit.tab
    rw [hp]
    split <;> rfl
  have u' : w.tab cs (x'.1.l.get x'.2).1 (numOf arr x') (x'.1.seat x'.2).1 (x'.1.seat x'.2).2 mask
      row place = w.msg (numOf arr x') mask row place := by
    unfold Wit.tab
    rw [hp']
    split <;> rfl
  have k : w.msg (numOf arr x) mask row place = w.msg (numOf arr x') mask row place := by rw [hn]
  exact hne (t.symm.trans (u.trans (k.trans (u'.symm.trans t'))))

/-- **THE CURE, AT ONE WITNESS**: x and x' sit at two seats (they may have one number: a message and
its later copy). x' is pinned at w; x decodes to m, and outside x's pad, inside x's ranges, m is
w's message of x's number. THEN BOTH ARE PINNED AT w WITH x's PAD LAID. -/
theorem pin_both (x x' : Mem) (a : A) (y : Strs) (w : Wit Cells Tok MsgT)
    (hs : seatOf x ≠ seatOf x') (m : MsgT) (hd : decAt cs G smp x.1 x.2 a y = some m)
    (hoff : ∀ mask row place, InMsg cs (x.1.l.get x.2).1 mask row place →
      padB cs (x.1.l.get x.2).1 mask row place = false →
        w.msg (numOf arr x) mask row place = m mask row place)
    (p' : PinAt G cs x'.1.l x'.1.seat (fun z => smp z x'.1) arr x'.2 a y w) :
    PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y
        (extAt cs G arr smp decT c₀ [] [x] false none a y w) ∧
      PinAt G cs x'.1.l x'.1.seat (fun z => smp z x'.1) arr x'.2 a y
        (extAt cs G arr smp decT c₀ [] [x] false none a y w) := by
  have hA : AgreeBy cs G smp seatOf ([] ++ [x]) a y (seatOf x) := by
    intro u hu u' hu' _ _ k k' e e'
    have e1 : u = x := List.mem_singleton.1 hu
    have e2 : u' = x := List.mem_singleton.1 hu'
    rw [e1] at e
    rw [e2] at e'
    exact Option.some.inj (e.symm.trans e')
  have hq : ((x'.1.seat x'.2).1, (x'.1.seat x'.2).2) ∉ ([] ++ [x]).map seatOf := by
    intro h
    obtain ⟨u, hu, e⟩ := List.mem_map.1 h
    have e1 : u = x := List.mem_singleton.1 hu
    rw [e1] at e
    exact hs e
  exact ⟨pin_ext_pad cs G arr smp decT c₀ [] [x] false none a y w x (List.mem_singleton.2 rfl) m hd
      hA (List.not_mem_nil) hoff,
    pin_congr cs G arr smp x'.1 x'.2 a y w _
      (extAt_other cs G arr smp decT c₀ [] [x] false none a y w _ (List.not_mem_nil))
      (extAt_other_pad cs G arr smp decT c₀ [] [x] false none a y w _ _ hq) p'⟩

/-- No two of ms at one seat: so those at one seat that decode decode alike. -/
theorem agreeSeat_of_seats (ms : List Mem) (h : (ms.map seatOf).Nodup) (a : A) (y : Strs)
    (k : ℕ × ℕ) : AgreeBy cs G smp seatOf ms a y k := by
  intro x hx x' hx' e e' m m' hm hm'
  have ex : x = x' := List.inj_on_of_nodup_map h hx hx' (e.trans e'.symm)
  subst ex
  exact Option.some.inj (hm.symm.trans hm')

/-- A member that is pinned decodes: to the witness's typed message. -/
theorem dec_of_pin (s : Sending) (i : Fin s.l.length) (a : A) (y : Strs) (w : Wit Cells Tok MsgT)
    (hp : PinAt G cs s.l s.seat (fun x => smp x s) arr i a y w) :
    decAt cs G smp s i a y = some (toMsgT cs s.l i (msgsOf cs s.l s.seat arr w i)) := by
  obtain ⟨z, hz, hs, hm⟩ := hp
  have hz' : smp a s i = some z := hz
  unfold decAt
  rw [hz', Option.bind_some, if_pos hs, hm]
  rfl

/-- **Two witnesses that read alike through the accessor at a member, inside its ranges, are pinned
alike there.** -/
theorem tabAlike (x : Mem) (a : A) (y : Strs) (w w' : Wit Cells Tok MsgT)
    (h : ∀ mask row place, InMsg cs (x.1.l.get x.2).1 mask row place →
      memTab cs arr w' x mask row place = memTab cs arr w x mask row place)
    (p : PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w) :
    PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w' := by
  obtain ⟨z, hz, hs, hm⟩ := p
  have e : msgsOf cs x.1.l x.1.seat arr w' x.2 = msgsOf cs x.1.l x.1.seat arr w x.2 :=
    msgs_back cs x.1.l x.1.seat arr w' x.2 _ fun mask row place hin =>
      (h mask row place hin).trans (msgs_forth cs x.1.l x.1.seat arr w x.2 mask row place hin)
  exact ⟨z, hz, hs, by rw [e]; exact hm⟩

/-- **THE CARRYING**: a law may be proved at a witness w' that has the pads from elsewhere. If a
member x of which the row lays the pad alone IS PINNED at (a, y, w'), then what the row's extractor
gives, at any w that has w' 's message of x's number, reads at x, inside x's ranges, as w' does. -/
theorem ext_of_pinned (minePad : List Mem) (hN : (minePad.map seatOf).Nodup) (x : Mem)
    (hx : x ∈ minePad) (a : A) (y : Strs) (w w' : Wit Cells Tok MsgT)
    (hp : PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w')
    (hw : w.msg (numOf arr x) = w'.msg (numOf arr x)) (mask : Bool) (row place : ℕ)
    (hin : InMsg cs (x.1.l.get x.2).1 mask row place) :
    memTab cs arr (extAt cs G arr smp decT c₀ [] minePad false none a y w) x mask row place =
      memTab cs arr w' x mask row place := by
  have hd := dec_of_pin cs G arr smp x.1 x.2 a y w' hp
  have t := tab_of_pin cs G arr smp x.1 x.2 a y w' _ hd hp mask row place hin
  have h1 : ((x.1.seat x.2).1, (x.1.seat x.2).2) ∈ ([] ++ minePad).map seatOf :=
    List.mem_map.2 ⟨x, hx, rfl⟩
  have h2 := tabBy_of cs G smp seatOf ([] ++ minePad) a y x hx _ hd
    (agreeSeat_of_seats cs G smp minePad hN a y (seatOf x))
  have h2' : padAt cs G smp ([] ++ minePad) a y (x.1.seat x.2).1 (x.1.seat x.2).2 =
      toMsgT cs x.1.l x.2 (msgsOf cs x.1.l x.1.seat arr w' x.2) := h2
  have hn : numOf arr x ∉ ([] : List Mem).map (numOf arr) := List.not_mem_nil
  show (if padB cs (x.1.l.get x.2).1 mask row place = true then
      (if ((x.1.seat x.2).1, (x.1.seat x.2).2) ∈ ([] ++ minePad).map seatOf then
        padAt cs G smp ([] ++ minePad) a y (x.1.seat x.2).1 (x.1.seat x.2).2
      else w.pad (x.1.seat x.2).1 (x.1.seat x.2).2) mask row place
    else (if numOf arr x ∈ ([] : List Mem).map (numOf arr) then
        msgAt cs G arr smp [] a y (numOf arr x)
      else w.msg (numOf arr x)) mask row place) = memTab cs arr w' x mask row place
  rw [if_pos h1, if_neg hn, h2', hw]
  by_cases hpd : padB cs (x.1.l.get x.2).1 mask row place = true
  · rw [if_pos hpd]
    exact t.symm
  · rw [if_neg hpd]
    show _ = (if padB cs (x.1.l.get x.2).1 mask row place = true then
      w'.pad (x.1.seat x.2).1 (x.1.seat x.2).2 mask row place
      else w'.msg (numOf arr x) mask row place)
    rw [if_neg hpd]

/-- **What a piece holds beside its block and its stretch, at that extractor** (`Rest`, Tiles.lean).
out: what the block puts out at a statement and a transcript; tokToo: the row lays the token, off
the record behind. -/
def restWorld {C : CK} (mine minePad : List Mem) (Fr : Frame) (ds : List RDT)
    (cellsToo tokToo : Bool) (out : A × Fr.E.Str → Iop.Tr (uLT C ds) → Option A)
    (err : Iop.Err (uLT C ds)) : Rest C Fr A (Wit Cells Tok MsgT) ds :=
  ⟨fun a τ w => extAt cs G arr smp decT c₀ mine minePad cellsToo
    (if tokToo then (out a τ).map tokOf else none) a.1 (strsOf Fr a.2) w, err⟩

end

end VerifiableInference.Desc.Sound
