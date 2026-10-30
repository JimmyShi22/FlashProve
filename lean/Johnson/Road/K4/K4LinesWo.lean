-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4LinesWo.lean: THE LINE wo OF `K4Lines` (CloseAtTable.lean), AT A MEANING WHOSE
ITEM wo AND PUBLIC ITEM hasRow SAY WHAT THEIR OWNER's LAYER LAYS, WHERE wo m IS OPEN AT THE BORDER
BEHIND AND QK's SEAT IS seatS, UNDER ONE LINE ON THE TABLE's PROMISE AND NAMED TIES, THOSE THAT READ
THE VERIFIER's STATE FENCED. EXCHANGED, NOT PAID. The line's core `k4_wo_core` names
none of the law's letters; the pile's reader takes the public part and the
verifier's state, the tie of the mask entry is asked at a name of the plan, and no layer's
definition is named. Definitions, statements and proofs: a joining; no new argument.

OBJECT: the line: for every statement b and witness w: if b meets the filling's promise behind, the
table's promise behind K4's block, and bears no mark, and the table's item wo m holds at b and w,
then the law's letter wo holds: at every o (the Lean structure `Own`: what K4's hearing holds) that
the seat finds in b: `Plan4K.WoRow par o (part w)`. USER: `k4_wo_of_means` and `k04_own_later`
(Johnson/Road/K4/K04LawOf.lean).

  `hasRow_of_onQ`: at an unmarked statement inside the table's promise at a border at which the item
    wo m is open, the public item hasRow m is true: the promise's Bool `pubHeld` asks every public
    item that is tied to an open item (`pubOfItems`: wo m ↦ hasRow m): `bools_of_onQ`
    (K4PromiseBehind.lean).
  `woOpenB`, `woOpenB_full`, `wo_open_full`: at the driver's written lists the item wo (2 g) is open
    at border 28 g + 5, for every g < 12: by the kernel (`decide +kernel`).
  `WoTies lay nR kC QK part par`: FOUR TIES THAT READ NO STATE OF THE VERIFIER, as one Lean
    structure: layIs: the layer's layout is the plan's · rows, cols: the pile's witness has that
    layout's numbers of rows and column bits · zero: the value's cells are 0 from row nR on.
  `k4Lines_wo_at`: THE LINE, in the words of `K4Lines`' field wo, at the letters `QK.lettersOf …`
    with QK's seat that of the first chain's verifier's state, at onB := `onQ … (k + 1)`: from hopen
    (wo m is open at border k + 1), eH (the meaning's public item hasRow m IS the frame's Bool at
    lay, n, lin), eW (its item wo m GIVES: every row that the frame's reader gives at the verifier's
    state holds, in the pile's sense, of `rw a w`: an implication, so it is met by the owner's layer
    in a form whose reader reads the witness alone, and in a form whose
    reader takes the verifier's state), `WoTies`, hname (at an unmarked statement inside the table's
    promise behind: the index masks' message's number is im₀, and the entry that its ledger hands
    out next is v), and hmat, hmask: TWO TIES ASKED INSIDE THE FENCE ALONE: the pile's reader's
    matrix there is the value's cells; its mask entry at the name ⟨im₀, v⟩ is the value's message at
    c7; that the row bears that name follows from hname by `row_tie`: `Plan4K.woRow_of_holds`
    (WoAtFill.lean).

Limits. K04_law IS NOT PROVED BY THIS. ONE LINE OF `K4Lines`' NINE, OF THE 28 THAT THE ROAD TO THE
TABLE ASKS, AND IT IS NOT MET. hopen IS A PREMISE OF `k4Lines_wo_at`: `wo_open_full` pays it at the
driver's written lists alone, at k = 28 g + 4 and m = 2 g; at other lists, or at a k and an m that
nothing ties to one g, nobody pays it. `WoTies`, hmat AND hmask ARE PREMISES, WHOLE: layIs, rows,
cols are equations on the plan's numbers, meant so, as reported; zero, hmat and
hmask tie two readers of one witness, the pile's and the value's: THE PILE's READER IS A LETTER
HERE; as reported the meant term reads the witness through the state's own book; WHETHER THE
THREE CAN HOLD TOGETHER AT THE MEANT READERS IS NOT SHOWN; hname IS A PREMISE, AND NO ONE CLAUSE
OF THE TABLE's PROMISE GIVES IT:
the name that the row bears is the entry that b's OWN ledger of the index masks'
message hands out next; the value's c7 is a letter fixed in front of «for all b»; where nothing in
the promise pins that entry, two statements inside the promise can part in it. SO THIS LINE IS
EXCHANGED, NOT PAID, HERE. `Rec.nextEntryIs` (Rec/NextEntry.lean) concludes hname from five premises
on the meaning's public items, shown at no term, and two tests (NextEntryStatement.lean's Limits);
the message's number is the public item indexIs's. eH
and eW are premises here; `k4_wo_of_means` (Johnson/Road/K4/K04LawOf.lean) takes them from the
fields hasRow and wo of `K4Means`. The line is
spent behind a yes of K4's block, where the table's promise behind must first be SHOWN: that hasRow
m holds there is owed by K4's own row and is typed by nobody. `woOpenB_full` raises maxRecDepth to
1,000,000 for its one `decide +kernel`. The number of claims n and the shape lin enter `WoRow` under
its own «there are»: no tie is owed on them. BESIDE THE ENTRY, hmask's payer must show that the
fence pins the book's place of the index masks' message and that the entry lies within the table.
Nothing on soundness.
-/
import Johnson.Road.K4.CloseAtTable
import Johnson.Road.K4.WoAtFill
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers start openSets pubOfItems
  pubHeld flatPlacesOf)
open VerifiableInference.Desc.K13.Law (lowBits)
open VerifiableInference.Desc.Sound (Frame onQ meansQ strsOf linksFull)
open Johnson.Desc.First.Walk.Law (hasRow leftOf)
open VerifiableInference.Desc.First.MergeLaw (row_tie)
open Inst.Model (Scl)

section
variable {P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {Z : P} {links : List ModelPart}
  {ps : List VerifiableInference.Desc.Place} {j m : ℕ}

/-- **Inside the table's promise at a border at which wo m is open, hasRow m is true**, at an
unmarked statement. -/
theorem hasRow_of_onQ {b : S × Fr.E.Str} (hb : onQ N Mg links ps (fun s => (Z, s)) j b)
    (hu : b.1.failed = none)
    (hopen : Item.wo m ∈ (openSets links ps (start links))[j]?.getD []) :
    Mg.pub (.hasRow m) (Z, b.1) = true := by
  obtain ⟨_, hp, _⟩ := bools_of_onQ N Mg Z hb hu
  unfold pubHeld at hp
  refine List.all_eq_true.1 hp _ (List.mem_append_right _ ?_)
  unfold pubOfItems
  exact List.mem_flatMap.2 ⟨_, hopen, by simp⟩

end

/-- The test: at the written lists wo (2 g) is open at border 28 g + 5. -/
def woOpenB : Bool :=
  (List.range 12).all fun g =>
    decide (Item.wo (2 * g) ∈
      (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[28 * g + 4 + 1]?.getD
        [])

set_option maxRecDepth 1000000 in
theorem woOpenB_full : woOpenB = true := by decide +kernel

/-- **At the written lists the item wo (2 g) is open behind K4's block of group g.** -/
theorem wo_open_full (g : ℕ) (hg : g < 12) :
    Item.wo (2 * g) ∈
      (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[28 * g + 4 + 1]?.getD
        [] :=
  of_decide_eq_true (List.all_eq_true.1 woOpenB_full g (List.mem_range.2 hg))

variable [scl : Scl] {M : Type}

/-- **Four ties that read no state of the verifier**: the layer's layout is the plan's; the pile's
witness has its numbers of rows and column bits; the value's cells are 0 from row nR on. -/
structure WoTies {W : Type} (lay : WsLay) (nR kC : ℕ) (QK : Plan4K M S) (part : W → M)
    (par : Par) : Prop where
  layIs : lay = par.P.wsLay
  rows : nR = lay.m0
  cols : kC = lay.lk
  zero : ∀ w j, nR ≤ j → ∀ C, QK.toL.plan.full.Wn (QK.toL.plan.full.msg (part w)) j C = 0

/-- **The core of the line wo**: at a meaning whose public item hasRow m is the frame's Bool (eH)
and whose item wo m says that the row which the frame's reader gives holds, in the pile's sense, of
the pile's reader's witness (eW), where wo m is open at the border behind (hopen): at an unmarked
statement b inside the table's promise behind, and a witness w that meets the item wo m: for what
K4's hearing holds in b, o: `WoRow par o (part w)`. Under `WoTies`; under hname: A LINE ON THE
TABLE's PROMISE ALONE: there the index masks' message's number is im₀ and the entry that its ledger
hands out next is v: TWO NUMBERS FIXED IN FRONT OF «for all b»; and under hmat, hmask: two ties of
the pile's reader to the value, asked INSIDE THE FENCE, hmask AT THE ONE NAME ⟨im₀, v⟩. IT NAMES
NONE OF THE LAW's LETTERS: so it serves the first group and the later ones. hname IS A PREMISE:
EXCHANGED, NOT PAID, HERE: see Limits. -/
theorem k4_wo_core {P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {Z : P}
    {links : List ModelPart} {ps : List VerifiableInference.Desc.Place} {k m : ℕ} (QK : Plan4K M S)
    {part : W → M} {par : Par} {lay : WsLay} {n : ℕ} {lin : Params.LinShape} {nR kC : ℕ}
    {rw : P × S → W → VerifiableInference.Desc.K13.Law.Wit Cb.Gl.E nR kC}
    (hopen : Item.wo m ∈ (openSets links ps (start links))[k + 1]?.getD [])
    (eH : ∀ a : P × S, Mg.pub (.hasRow m) a = hasRow lay n lin a.2)
    (eW : ∀ (a : P × S) y w, Mg.wo m a y w →
      ∀ r, Johnson.Desc.First.Walk.Law.rowAt lay n lin a.2 = some r →
        VerifiableInference.Desc.K13.Law.Holds Reading.gl (rw a w) r)
    (T : WoTies lay nR kC QK part par)
    (hmat : ∀ (b : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (Z, s)) (k + 1) b →
      b.1.failed = none → ∀ (i : Fin nR) (C : ℕ), C < 2 ^ kC →
        (rw (Z, b.1) w).mat i (lowBits kC C) =
          QK.toL.plan.full.Wn (QK.toL.plan.full.msg (part w)) i C)
    {im₀ v : ℕ}
    (hname : ∀ b : S × Fr.E.Str, onQ N Mg links ps (fun s => (Z, s)) (k + 1) b →
      b.1.failed = none → b.1.out.indexMasks = im₀ ∧
        ∀ l c l', Johnson.Desc.First.Walk.Law.ledgerAt b.1 = some l →
          VerifiableInference.Desc.First.Pend.takeEntry l = some (c, l') → c = v)
    (hmask : ∀ (b : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (Z, s)) (k + 1) b →
      b.1.failed = none →
      (rw (Z, b.1) w).mask ⟨im₀, v⟩ = QK.toL.plan.full.msg (part w) QK.toL.plan.full.c7) :
    ∀ (b : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (Z, s)) (k + 1) b → b.1.failed = none →
      meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.wo m) b w →
      ∀ o, seatS.own b.1 = some o → QK.WoRow par o (part w) := by
  intro b w hb hu hm o ho
  obtain ⟨e1, e2, e3, hz⟩ := T
  subst e1
  have hh : hasRow par.P.wsLay n lin b.1 = true := by
    rw [← eH (Z, b.1)]
    exact hasRow_of_onQ hb hu hopen
  have hw : Mg.wo m (Z, b.1) (strsOf Fr b.2) w := hm
  refine QK.woRow_of_holds (rw (Z, b.1) w) ho hh (eW _ _ _ hw) e3 e2 (hz w) (hmat b w hb hu) ?_
  intro r hr t ht
  obtain ⟨_, wp, l, c, l', _, _, c3, c4, c5, _⟩ := row_tie (left := leftOf) hr
  obtain ⟨n1, n2⟩ := hname b hb hu
  rw [c5] at ht
  have e : t = (⟨b.1.out.indexMasks, c⟩, wp.beta) := by simpa using ht
  rw [e, n1, n2 l c l' c3 c4]
  exact hmask b w hb hu

/-- **The line wo of `K4Lines`**, where QK's seat is that of the first chain's verifier's state
(hL): `k4_wo_core` at the later groups' letters. The same premises; the same cautions. -/
theorem k4Lines_wo_at {P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {Z : P}
    {links : List ModelPart} {ps : List VerifiableInference.Desc.Place} {k m : ℕ} (QK : Plan4K M S)
    (hL : QK.L = seatS) {part : W → M} {par : Par} {first : ℕ} {h3 : Forest.Shape}
    {Q3 : Fork → Prop} {on0 on' : S × Fr.E.Str → Prop} {ctx0 : S × Fr.E.Str → W → Prop}
    {dec : S × Fr.E.Str → M} {lay : WsLay} {n : ℕ} {lin : Params.LinShape} {nR kC : ℕ}
    {rw : P × S → W → VerifiableInference.Desc.K13.Law.Wit Cb.Gl.E nR kC}
    (hopen : Item.wo m ∈ (openSets links ps (start links))[k + 1]?.getD [])
    (eH : ∀ a : P × S, Mg.pub (.hasRow m) a = hasRow lay n lin a.2)
    (eW : ∀ (a : P × S) y w, Mg.wo m a y w →
      ∀ r, Johnson.Desc.First.Walk.Law.rowAt lay n lin a.2 = some r →
        VerifiableInference.Desc.K13.Law.Holds Reading.gl (rw a w) r)
    (T : WoTies lay nR kC QK part par)
    (hmat : ∀ (b : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (Z, s)) (k + 1) b →
      b.1.failed = none → ∀ (i : Fin nR) (C : ℕ), C < 2 ^ kC →
        (rw (Z, b.1) w).mat i (lowBits kC C) =
          QK.toL.plan.full.Wn (QK.toL.plan.full.msg (part w)) i C)
    {im₀ v : ℕ}
    (hname : ∀ b : S × Fr.E.Str, onQ N Mg links ps (fun s => (Z, s)) (k + 1) b →
      b.1.failed = none → b.1.out.indexMasks = im₀ ∧
        ∀ l c l', Johnson.Desc.First.Walk.Law.ledgerAt b.1 = some l →
          VerifiableInference.Desc.First.Pend.takeEntry l = some (c, l') → c = v)
    (hmask : ∀ (b : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (Z, s)) (k + 1) b →
      b.1.failed = none →
      (rw (Z, b.1) w).mask ⟨im₀, v⟩ = QK.toL.plan.full.msg (part w) QK.toL.plan.full.c7) :
    ∀ b w, (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).on' b →
      onQ N Mg links ps (fun s => (Z, s)) (k + 1) b → b.1.failed = none →
      meansQ (Fr := Fr) N Mg (fun s => (Z, s)) (.wo m) b w →
      (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).wo b w := by
  intro b w _ hb hu hm o ho
  rw [hL] at ho
  exact k4_wo_core QK hopen eH eW T hmat hname hmask b w hb hu hm o ho

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hasRow_of_onQ
#print axioms OnBytes.Road.K4.woOpenB_full
#print axioms OnBytes.Road.K4.wo_open_full
#print axioms OnBytes.Road.K4.k4_wo_core
#print axioms OnBytes.Road.K4.k4Lines_wo_at
