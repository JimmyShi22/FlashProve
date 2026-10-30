-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4Pins.lean: THE PINNED PART AT K4's ROW OF THE TABLE OF JOINTS, FILLED: a type of
tuples of decoded messages, its reader off a witness, its reader off a statement, AND THE LINES pin,
decRides AND ctxRides OF `K4Lines` (Johnson/Road/K4/CloseAtTable.lean) PROVED AT THAT FILLING, at a
meaning whose six letters on the reading of the oracles are the library's own (`meaningSig`,
Johnson/Desc/Sound/BordersFill.lean), UNDER THE PREMISES `FencedB`, `RecRides`, `SmallRides`.
Definitions, small lemmas and theorems. CALLED, NOT WRITTEN ANEW: what a member decodes to at a
statement (`decAt`, `dec_of_pin`, `toMsgT`: Johnson/Desc/Sound/World.lean); that the stored table, a
word, "every leaf is shown" and the table's pin are the same at two statements with `SameRead`
(`cell_same`, `wordsOf_same`, `shownAt_iff`, `pin_iff`: Johnson/Road/K4/SameReadSig.lean).
No draw, no count.

  `pinSeats N m`: the seats (tree, tenant) that the row's two pins of messages name: those of
    segment m's moment 0, and the index masks' message's.
  `memAt ms x`: the first member of ms that sits at the seat x (as `seatTab`, BordersFill.lean,
    finds it).
  `PinM Cells`: THE TUPLE: BY SEAT a table (mask row or main row, row, place ↦ a field element),
    and the cells of the stored table, or nothing.
  `cutTab`: a member's table off a witness, CUT TO THE MEMBER's RANGES: the witness's typed message
    (`msgsOf`, Johnson/Desc/Sound/MsgSig.lean: through the one accessor) as a total function, 0
    outside the ranges: so no place that a pin does not fix is in the tuple.
  `partOf`: off a witness: at a seat of `pinSeats` `cutTab` of the member that `memAt` finds; the
    zero table where it finds none and at every other seat; the witness's cells.
  `decOf`: off a statement: at a seat of `pinSeats` what the member that `memAt` finds decodes to
    (`decAt`: the library's decoder with a sample, `OMsg.dec`, at the member's word and at the
    sample that the record holds, where every leaf is shown); the zero table where there is no
    member, where it does not decode, and at every other seat; what the stored table decodes to
    (decT).
  `FencedB`: a test on the plan's numbers: every tree of `pinSeats` has a number below base.
  `RecRides`: smp and decT read the same at two records with `Rest`
    (Johnson/Desc/First/K4/ReadsAtS.lean). `SmallRides`: the item constr m small
    goes back from y to x wherever `SameRead base x y` (Johnson/Road/K4/RidesBack.lean).
  **`pin_line`**: the four items that the row reads give `partOf … w = decOf … b`. NO PREMISE.
  **`dec_line`**: `SameRead base x y → decOf … y = decOf … x`, from `FencedB` and `RecRides`.
  **`ctx_line`**: `SameRead base x y →` the four items at (y, w) give them at (x, w), from
    `FencedB`, `RecRides` and `SmallRides`.
  `K4Six`: the lines forms, wo, idn, planes, keys, rider of `K4Lines`, as CloseAtTable.lean has them
    (a program holds the six against it at each pack).
  `k4Lines_of_six`: `K4Lines` at that filling from `K4Six` and these premises.
  `recRides_of_fields`: `RecRides` holds of readers of the record's fields st and book alone.
  `sample_smpOf`: its line sample at smp := `smpOf forms ans` (Johnson/Desc/Sound/Seed.lean), if
    forms and ans read the same at two records with `Rest`.

OBJECT: the meaning `meaningSig cs G arr smp ms decT Mg`, Mg any; the witnesses are the library's
`Wit Cells Tok MsgT`. USER: Johnson/Road/K4/K4PinsRead.lean (the value's readers of a tuple) ·
Johnson/Road/K4/K4PinsOwn.lean (`k4Lines_of_six`, laid into `RefSeat.k4_own_refS`). LETTERS, filled
by nobody: the codes cs, the description G, arr, smp, the members ms, decT, the rest of the meaning
Mg, the numbers N, the public part Zt, m, base.

Limits. K04_law IS NOT PROVED BY THIS. WHAT STAYS A PREMISE, AND WHO COULD PAY IT:
 · `FencedB N m base = true`: a test on the plan's numbers; it has itself run at no plan. From the
   table's own tests, or from a line of `K4Keeps`: Johnson/Road/K4/K4PinsFence.lean.
 · `RecRides`: whoever fills smp and decT: readers of the record's fields st and book alone have it
   (`recRides_of_fields`). The filling of smp that Johnson/Desc/Sound/Seed.lean means (`smpOf`)
   reads the record through two further letters (the record's sample rows and their targets): it
   has the line sample if these two read the same at two records with `Rest` (`sample_smpOf`).
 · `SmallRides`: whoever fills the item constr m small: a sentence on the witness alone has it.
   The one filling of that item that we know written (the table's authors' `constrQ`) is none: it
   reads the stored table's decoder too: it has the line if that decoder reads of a statement what
   `SameRead` keeps (by reading; not typed). `meaningSig` lays the promise "the stored table
   decodes" by decT OVER whatever Mg has: that `constrQ`'s decoder is decT's is owed by whoever lays
   the two fillings together: else the table has two decoders, tied by nothing.
 · in `k4Lines_of_six` every line of `K4Six`: whoever fills the six items.
`pin_line` SAYS THAT THE TWO READERS AGREE WHERE THE FOUR ITEMS HOLD: it does not say that the items
hold anywhere, nor that what the decoder gives is the one candidate (that is the promise "no
collision", not read here). AT A SEAT WHERE NO MEMBER OF ms SITS BOTH READERS GIVE THE ZERO TABLE,
IN SILENCE (the pin itself is false there: `pinJT` asks a member at the seat). WHERE TWO MEMBERS OF
ms SIT AT ONE SEAT the first alone is read. Whether the messages that K4's value reads (the matrices
behind the committed symbols, the mask row, the index masks) sit at `pinSeats` is a fact on the plan
that is not shown here. `SeatFits` AT ms (Johnson/Desc/Sound/MsgSig.lean: the members fit the
description's trees: leaves, rows, words) IS ASKED NOWHERE HERE, nor by `pinJT`: K4's own law spends
nothing of it, but "what the COMMITTED words decode to" hangs on it.
-/
import Johnson.Road.K4.CloseAtTable
import Johnson.Road.K4.SameReadSig
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Desc.First.K4 (Par Rest formsBack seatS)
open VerifiableInference.Desc (FileDescription Wit Strs)
open VerifiableInference.Desc.First (S Item Meaning Numbers)
open VerifiableInference.Desc.Sound (Frame Sending Mem MsgT seatOf PinAt msgsOf toMsgT decAt
  dec_of_pin pinJT meaningSig meansQ strsOf smpOf SeedIs)
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)
open Inst.Model (Scl)

/-! ## 1 The six lines of `K4Lines` that stay -/

/-- **The lines forms, wo, idn, planes, keys, rider of `K4Lines`**, as CloseAtTable.lean has
them. -/
structure K4Six {P W M : Type} {Fr : Frame} [scl : Scl] (N : Numbers) (Mg : Meaning P W) (Zt : P)
    (m : ℕ) (QK : Plan4K M S) (part : W → M) (p : Par)
    (Lt : VerifiableInference.Desc.Plain.K04.Letters S W Fr) (onB : S × Fr.E.Str → Prop) :
    Prop where
  /-- formsT m 3 "own", at a statement that meets the filling's promise behind and onB, and bears
  no mark -/
  forms : ∀ b w, Lt.on' b → onB b → b.1.failed = none →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.formsT m 3 "own") b w →
    FormsT seatS (QK.semOf part p.hp.tl) (frontRun p) formsBack b.1 w
  /-- wo m, likewise -/
  wo : ∀ b w, Lt.on' b → onB b → b.1.failed = none →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.wo m) b w → Lt.wo b w
  /-- constr m idn, with ctx in hand, as in the three lines that follow -/
  idn : ∀ a w, Lt.on a → Lt.ctx a w → Lt.idn a w →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.constr m .idn) a w
  /-- worth m 2 "planes" -/
  planes : ∀ a w, Lt.on a → Lt.ctx a w → Lt.worthPlanes a w →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.worth m 2 "planes") a w
  /-- worth m 2 "keys" -/
  keys : ∀ a w, Lt.on a → Lt.ctx a w → Lt.worthKeys a w →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.worth m 2 "keys") a w
  /-- worth m 2 "rider" -/
  rider : ∀ a w, Lt.on a → Lt.ctx a w → Lt.worthRider a w →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.worth m 2 "rider") a w

/-! ## 2 The filling -/

/-- The seats that the row's two pins of messages name. -/
def pinSeats (N : Numbers) (m : ℕ) : List (ℕ × ℕ) := N.sent m 0 ++ [N.index]

/-- The first member of ms that sits at a seat. -/
def memAt (ms : List Mem) (x : ℕ × ℕ) : Option Mem := ms.find? fun y => decide (seatOf y = x)

theorem memAt_some {ms : List Mem} {x : ℕ × ℕ} {u : Mem} (h : memAt ms x = some u) :
    u ∈ ms ∧ seatOf u = x := by
  have h' : ms.find? (fun y => decide (seatOf y = x)) = some u := h
  have h2 := List.find?_some h'
  exact ⟨List.mem_of_find?_eq_some h', of_decide_eq_true h2⟩

/-- **The tuple**: by seat a table; the stored table's cells, or nothing. -/
abbrev PinM (Cells : Type) : Type := (ℕ × ℕ → MsgT) × Option Cells

/-- A test on the plan's numbers: every tree of these seats has a number below base. -/
def FencedB (N : Numbers) (m base : ℕ) : Bool :=
  (pinSeats N m).all fun x => decide (x.1 < base)

theorem fenced_lt {N : Numbers} {m base : ℕ} (h : FencedB N m base = true) {t : ℕ × ℕ}
    (ht : t ∈ pinSeats N m) : t.1 < base :=
  of_decide_eq_true (List.all_eq_true.1 h _ ht)

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
  (N : Numbers) (Zt : P) (m : ℕ) {Fr : Frame}

/-- A member's table off a witness, cut to the member's ranges. -/
def cutTab (w : Wit Cells Tok MsgT) (u : Mem) : MsgT :=
  toMsgT cs u.1.l u.2 (msgsOf cs u.1.l u.1.seat arr w u.2)

/-- **The pinned part, off a witness.** -/
def partOf (w : Wit Cells Tok MsgT) : PinM Cells :=
  (fun x => if x ∈ pinSeats N m then ((memAt ms x).map (cutTab cs arr w)).getD fun _ _ _ => 0
    else fun _ _ _ => 0,
    some w.cells)

/-- **The pinned part, off a statement.** -/
def decOf (b : S × Fr.E.Str) : PinM Cells :=
  (fun x => if x ∈ pinSeats N m then
      ((memAt ms x).bind fun u => decAt cs G smp u.1 u.2 (Zt, b.1) (strsOf Fr b.2)).getD
        fun _ _ _ => 0
    else fun _ _ _ => 0,
    decT (strsOf Fr b.2).cell (Zt, b.1))

theorem partOf_at (w : Wit Cells Tok MsgT) {x : ℕ × ℕ} (hx : x ∈ pinSeats N m) {u : Mem}
    (hu : memAt ms x = some u) : (partOf cs arr ms N m w).1 x = cutTab cs arr w u := by
  show (if x ∈ pinSeats N m then ((memAt ms x).map (cutTab cs arr w)).getD fun _ _ _ => 0
    else fun _ _ _ => 0) = _
  rw [if_pos hx, hu, Option.map_some, Option.getD_some]

theorem decOf_at (b : S × Fr.E.Str) {x : ℕ × ℕ} (hx : x ∈ pinSeats N m) {u : Mem}
    (hu : memAt ms x = some u) :
    (decOf cs G smp ms decT N Zt m b).1 x =
      (decAt cs G smp u.1 u.2 (Zt, b.1) (strsOf Fr b.2)).getD fun _ _ _ => 0 := by
  show (if x ∈ pinSeats N m then
      ((memAt ms x).bind fun u => decAt cs G smp u.1 u.2 (Zt, b.1) (strsOf Fr b.2)).getD
        fun _ _ _ => 0
    else fun _ _ _ => 0) = _
  rw [if_pos hx, hu, Option.bind_some]

theorem partOf_none (w : Wit Cells Tok MsgT) {x : ℕ × ℕ}
    (hx : x ∉ pinSeats N m ∨ memAt ms x = none) :
    (partOf cs arr ms N m w).1 x = fun _ _ _ => 0 := by
  show (if x ∈ pinSeats N m then ((memAt ms x).map (cutTab cs arr w)).getD fun _ _ _ => 0
    else fun _ _ _ => 0) = _
  rcases hx with hx | hx
  · rw [if_neg hx]
  · rw [hx]
    split <;> rfl

theorem decOf_none (b : S × Fr.E.Str) {x : ℕ × ℕ}
    (hx : x ∉ pinSeats N m ∨ memAt ms x = none) :
    (decOf cs G smp ms decT N Zt m b).1 x = fun _ _ _ => 0 := by
  show (if x ∈ pinSeats N m then
      ((memAt ms x).bind fun u => decAt cs G smp u.1 u.2 (Zt, b.1) (strsOf Fr b.2)).getD
        fun _ _ _ => 0
    else fun _ _ _ => 0) = _
  rcases hx with hx | hx
  · rw [if_neg hx]
  · rw [hx]
    split <;> rfl

variable (Mg : Meaning P (Wit Cells Tok MsgT))

/-- The row's two pins of messages pin every member of ms that sits at a seat of `pinSeats`. -/
theorem pinAt_of_ctx (b : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (h : tableCtx0 N (meaningSig cs G arr smp ms decT Mg) Zt m b w) {u : Mem} (hu : u ∈ ms)
    (hs : seatOf u ∈ pinSeats N m) :
    PinAt G cs u.1.l u.1.seat (fun z => smp z u.1) arr u.2 (Zt, b.1) (strsOf Fr b.2) w := by
  have h1 : ∀ t ∈ N.sent m 0, pinJT cs G arr smp ms t.1 t.2 (Zt, b.1) (strsOf Fr b.2) w := h.1
  have h4 : pinJT cs G arr smp ms N.index.1 N.index.2 (Zt, b.1) (strsOf Fr b.2) w := h.2.2.2
  rcases List.mem_append.1 hs with ht | ht
  · exact (h1 _ ht).2 u hu rfl
  · have e : u.1.seat u.2 = N.index := List.mem_singleton.1 ht
    exact h4.2 u hu e

/-- **THE LINE pin**: the four items that K4's row reads and leaves open give: the pinned part off
the witness is the pinned part off the statement. No premise. -/
theorem pin_line (b : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (h : tableCtx0 N (meaningSig cs G arr smp ms decT Mg) Zt m b w) :
    partOf cs arr ms N m w = decOf cs G smp ms decT N Zt m b := by
  refine Prod.ext (funext fun x => ?_) ?_
  · by_cases hx : x ∈ pinSeats N m
    · cases hu : memAt ms x with
      | none =>
        rw [partOf_none cs arr ms N m w (Or.inr hu),
          decOf_none cs G smp ms decT N Zt m b (Or.inr hu)]
      | some u =>
        have hm := memAt_some hu
        have hp := pinAt_of_ctx cs G arr smp ms decT N Zt m Mg b w h hm.1
          (by rw [hm.2]; exact hx)
        rw [partOf_at cs arr ms N m w hx hu, decOf_at cs G smp ms decT N Zt m b hx hu,
          dec_of_pin cs G arr smp u.1 u.2 _ _ w hp, Option.getD_some, cutTab]
    · rw [partOf_none cs arr ms N m w (Or.inl hx),
        decOf_none cs G smp ms decT N Zt m b (Or.inl hx)]
  · have h2 : decT (strsOf Fr b.2).cell (Zt, b.1) = some w.cells := h.2.1
    exact h2.symm

/-! ## 3 The premises, and the two lines on riding -/

/-- **The two letters that read the record read the same at two records with `Rest`**: the
samples' reader; the stored table's decoder. -/
structure RecRides : Prop where
  sample : ∀ s s' : S, Rest s s' → ∀ sd i, smp (Zt, s') sd i = smp (Zt, s) sd i
  table : ∀ (s s' : S) (c : ℕ → Option (ℕ × List UInt64)), Rest s s' →
    decT c (Zt, s') = decT c (Zt, s)

/-- Readers of the record's fields st and book alone have it. -/
theorem recRides_of_fields
    (h1 : ∀ s s' : S, s'.st = s.st → s'.book = s.book → smp (Zt, s') = smp (Zt, s))
    (h2 : ∀ (s s' : S) c, s'.st = s.st → s'.book = s.book → decT c (Zt, s') = decT c (Zt, s)) :
    RecRides cs smp decT Zt :=
  ⟨fun s s' r sd i => by rw [h1 s s' r.st r.book], fun s s' c r => h2 s s' c r.st r.book⟩

/-- The line sample at the samples' reader that is made of the record's sample rows and their
targets, if these two read the same at two records with `Rest`. -/
theorem sample_smpOf
    (forms : P × S → (s : Sending) → (i : Fin s.l.length) →
      Option (((sigOf cs s.l).om i).Z.S → ((sigOf cs s.l).om i).C.J → Cb.Gl.E))
    (ans : P × S → (s : Sending) → (i : Fin s.l.length) →
      Option (((sigOf cs s.l).om i).Z.S → Cb.Gl.E))
    (h1 : ∀ s s' : S, Rest s s' → forms (Zt, s') = forms (Zt, s))
    (h2 : ∀ s s' : S, Rest s s' → ans (Zt, s') = ans (Zt, s)) (s s' : S) (r : Rest s s')
    (sd : Sending) (i : Fin sd.l.length) :
    smpOf cs forms ans (Zt, s') sd i = smpOf cs forms ans (Zt, s) sd i := by
  unfold smpOf SeedIs
  rw [h1 s s' r, h2 s s' r]

/-- **The item constr m small goes back** from y to x wherever `SameRead base x y`. -/
def SmallRides (Fr : Frame) (base : ℕ) : Prop :=
  ∀ (x y : S × Fr.E.Str) (w : Wit Cells Tok MsgT), SameRead base x y →
    Mg.constr m .small (Zt, y.1) (strsOf Fr y.2) w → Mg.constr m .small (Zt, x.1) (strsOf Fr x.2) w

variable {base : ℕ} (hF : FencedB N m base = true) (R : RecRides cs smp decT Zt)
include hF R

/-- Under `FencedB` and `RecRides`: what a member that sits at `pinSeats` decodes to is the same at
x and y, where `SameRead base x y`. -/
theorem decAt_same {x y : S × Fr.E.Str} (h : SameRead base x y) {u : Mem}
    (hs : seatOf u ∈ pinSeats N m) :
    decAt cs G smp u.1 u.2 (Zt, y.1) (strsOf Fr y.2) =
      decAt cs G smp u.1 u.2 (Zt, x.1) (strsOf Fr x.2) := by
  unfold decAt
  rw [R.sample x.1 y.1 h.rest u.1 u.2, wordsOf_same G cs u.1.l u.1.seat h u.2 (fenced_lt hF hs),
    propext (shownAt_iff G cs u.1.l u.1.seat h u.2 (fenced_lt hF hs))]

/-- **THE LINE decRides**: from `FencedB` and `RecRides`: the pinned part off the statement reads
of a statement only what `SameRead` keeps. -/
theorem dec_line (x y : S × Fr.E.Str) (h : SameRead base x y) :
    decOf cs G smp ms decT N Zt m y = decOf cs G smp ms decT N Zt m x := by
  refine Prod.ext (funext fun t => ?_) ?_
  · by_cases ht : t ∈ pinSeats N m
    · cases hu : memAt ms t with
      | none =>
        rw [decOf_none cs G smp ms decT N Zt m y (Or.inr hu),
          decOf_none cs G smp ms decT N Zt m x (Or.inr hu)]
      | some u =>
        have hm := memAt_some hu
        rw [decOf_at cs G smp ms decT N Zt m y ht hu, decOf_at cs G smp ms decT N Zt m x ht hu,
          decAt_same cs G smp decT N Zt m hF R h (by rw [hm.2]; exact ht)]
    · rw [decOf_none cs G smp ms decT N Zt m y (Or.inl ht),
        decOf_none cs G smp ms decT N Zt m x (Or.inl ht)]
  · show decT (strsOf Fr y.2).cell (Zt, y.1) = decT (strsOf Fr x.2).cell (Zt, x.1)
    rw [cell_same h, R.table x.1 y.1 _ h.rest]

/-- **THE LINE ctxRides**: from `FencedB`, `RecRides` and `SmallRides`: the four items go back
from y to x wherever `SameRead base x y`. -/
theorem ctx_line (hS : SmallRides Zt m Mg Fr base) (x y : S × Fr.E.Str)
    (w : Wit Cells Tok MsgT) (h : SameRead base x y)
    (c : tableCtx0 N (meaningSig cs G arr smp ms decT Mg) Zt m y w) :
    tableCtx0 N (meaningSig cs G arr smp ms decT Mg) Zt m x w := by
  have h1 : ∀ t ∈ N.sent m 0, pinJT cs G arr smp ms t.1 t.2 (Zt, y.1) (strsOf Fr y.2) w := c.1
  have h2 : decT (strsOf Fr y.2).cell (Zt, y.1) = some w.cells := c.2.1
  have h3 : Mg.constr m .small (Zt, y.1) (strsOf Fr y.2) w := c.2.2.1
  have h4 : pinJT cs G arr smp ms N.index.1 N.index.2 (Zt, y.1) (strsOf Fr y.2) w := c.2.2.2
  rw [cell_same h, R.table x.1 y.1 _ h.rest] at h2
  have g1 : ∀ t ∈ N.sent m 0, pinJT cs G arr smp ms t.1 t.2 (Zt, x.1) (strsOf Fr x.2) w :=
    fun t ht => (pin_iff G cs smp arr ms Zt h (R.sample x.1 y.1 h.rest)
      (fenced_lt hF (List.mem_append_left _ ht)) t.2 w).1 (h1 t ht)
  have g4 : pinJT cs G arr smp ms N.index.1 N.index.2 (Zt, x.1) (strsOf Fr x.2) w :=
    (pin_iff G cs smp arr ms Zt h (R.sample x.1 y.1 h.rest)
      (fenced_lt hF (List.mem_append_right _ (List.mem_singleton.2 rfl))) N.index.2 w).1 h4
  exact ⟨g1, h2, hS x y w h h3, g4⟩

omit hF R

/-! ## 4 `K4Lines` at the filling -/

variable [scl : Scl]

/-- **`K4Lines` at the filling**, from `K4Six`, `FencedB`, `RecRides` and `SmallRides`. -/
theorem k4Lines_of_six (QK : Plan4K (PinM Cells) S) (p : Par)
    (Lt : VerifiableInference.Desc.Plain.K04.Letters S (Wit Cells Tok MsgT) Fr)
    (hF : FencedB N m base = true) (R : RecRides cs smp decT Zt)
    (hS : SmallRides Zt m Mg Fr base) (onB : S × Fr.E.Str → Prop)
    (X6 : K4Six N (meaningSig cs G arr smp ms decT Mg) Zt m QK (partOf cs arr ms N m) p Lt onB) :
    K4Lines N (meaningSig cs G arr smp ms decT Mg) Zt m QK (partOf cs arr ms N m) p Lt
      (decOf cs G smp ms decT N Zt m) base onB where
  forms := X6.forms
  wo := X6.wo
  pin := pin_line cs G arr smp ms decT N Zt m Mg
  idn := X6.idn
  planes := X6.planes
  keys := X6.keys
  rider := X6.rider
  ctxRides := fun x y w _ h c => ctx_line cs G arr smp ms decT N Zt m Mg hF R hS x y w h c
  decRides := fun x y _ h => dec_line cs G smp ms decT N Zt m hF R x y h

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pin_line
#print axioms OnBytes.Road.K4.dec_line
#print axioms OnBytes.Road.K4.ctx_line
#print axioms OnBytes.Road.K4.k4Lines_of_six
#print axioms OnBytes.Road.K4.recRides_of_fields
#print axioms OnBytes.Road.K4.sample_smpOf
