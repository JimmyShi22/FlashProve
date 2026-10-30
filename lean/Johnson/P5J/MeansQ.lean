-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- The proof of `sound_of_verify_at` uses this file. THE TABLE OF JOINTS' UPPER STOREY: the parts
-- of the segments' relations AS DEFINITIONS, from the integer model's own clauses (those of
-- Goal/Meaning/Row.lean and of its hid), and THE TIE AT THE
-- CHAIN's FIRST BORDER AS A THEOREM. readAt and its four companions stand in
-- lean/Johnson/Desc/Sound/ReadAt.lean. hidAtSeat CANNOT BE FORMED WITHOUT THE TWO PUBLIC
-- CONDITIONS THAT BAR A SILENT ZERO: THEY ARE ARGUMENTS OF IT. hid READS A
-- MESSAGE THROUGH THE ONE ACCESSOR, AT THE SEAT OF THE SEGMENT's OWN GROUP's COPY: `readAt`.
-- The part "small" says that the committed symbols are a packing of small integers:
-- `HidAt.base`.
/-
P5J/MeansQ.lean.

What is said. `HidAt`: how a witness of the table is read as what the prover hides: `hid`; the
request's public part `req`; what the stored word decodes to `dec`; with one law that hid's make has
to give: `seams` (the three seams of the model's relation). `hidAtOf`: hid BUILT by the model's
`hidOf` from the witness's token and each segment's own committed arrays as integers (`own`:
a letter there); `seams` proved by its three theorems. `hidAtSeat`: `own` off the table's own
witness:
`ownAt` | `hidAt` (HidSeat.lean): hid's letters left are meant as public functions of the plan.
`partG`, `partA`: the parts of a group of layers' and of an attention sub-proof's share. `constrQ`:
the table's letter `Meaning.constr`, filled: AT EVERY INDEX THAT THE DECODED MATRIX HOLDS, as
`firstMeans` asks it. `firstAt`: `firstMeans` at what the witness hides, read at a statement of the
chain. `meansOfStart`, `tieStartQ`: UNDER THE NAMED PREMISE `HeadCuts`: IF EVERY ITEM THAT IS OPEN
AT THE CHAIN's START HOLDS, `firstAt`
HOLDS: `TieStart` IS A THEOREM. `firstChainMeansQ`: so the kinds' own laws and the riding at the
table give what every rule for a file asks of the first chain, AT DATA WHOSE FIELD R₀ IS
`firstMeans` (`first_iff`: other files' field "first", an "if and only if", under two equations
on the letters).

Which clause stands in which part (segment 2 g: group g of layers; 2 g + 1: its attention; 24: the
head): MeansG.small → small · norm, emb → idn · hot → rider · key → lookCalls · MeansA.small → small
· key → lookCalls · own1, own2 → idn · ridden → rider. IN NO PART: the three seams (by hid's make,
under "one component of the witness for all copies of a kept message"). No part of the model's
relation: lookDigits (the table's own inner item).

Limits. (1) partG, partA and `Seams` CALL other files' named notions: no clause is written anew.
(2) THE HEAD's ONE CLAUSE "plain" IS NOT CUT: its four parts are a letter `headPart`, and that
together they give the head's half in plain integers is A NAMED PREMISE HERE (`HeadCuts`); under the
head and one row of the entry tests it is `head_cuts_of_guard`
(Johnson/Desc/Kinds/Law/HeadCutsFive.lean): a record `HeadParts` has the four parts field by field
(idnSums, idnRows · lookCalls
· rider · small, smallS), a theorem `head_means` leads from them to its own two sentences in plain
integers, under two premises that follow from no part (a test on the record's tables; a bound on the
weights), and a further step of theirs leads from these to `SaysHead`: NOT CALLED HERE; the letter
is filled with that record's fields, and `HeadCuts` proved there under premises, in
Johnson/Desc/Kinds/Law/HeadCutsK6.lean (`headPartK6`, `headCuts_k6`). (3) `digitsPart` is a letter:
the smallness test's files' text. (4) The full size
alone (25 segments), as Meaning/Row.lean. (5) THE TIE HOLDS AT EVERY hid, A CONSTANT ONE TOO (the
parts are the model's clauses AT hid w: the tie is by unfolding). WHAT A SILLY hid BREAKS IS THE
PREMISE `EachOwn`: a closer must then prove the model's clause at the constant from items that speak
of
the committed messages: out of reach at a request that the constant does not fit: NOT SHOWN BY A
MEMBER. What ties hid to the oracles are the pins, through the layout: not typed here (`At.H`,
Johnson/P5J/LettersAt.lean; `hidAtList`, Johnson/P5J/HidAtList.lean): IN THIS FILE THE ROW's WEIGHT
STANDS ON THE LETTER hid. (6) Here the description D and the public part X are separate letters: no
theorem of this file ties D's plan to X's shapes. Of the description onlineDescription it is shown in part,
in the goals' scope, the files read and the two makers returning, at the hash function secondHashFunction: its
lots are made at a record that is what publicOf returns, and its list of 25 links carries that
record's plans (IM.ground_public, IM.ground_gets, Johnson/IMR/PureJoin.lean); the blocks of several
kinds are seated at those plans (Johnson/IMR/K*Seat.lean, e.g. IM.k5_of at Hd.shapeA X g). That
descPure's description is the one whose data are the D of these theorems is not shown in this file;
under the library's head it is two fields of `LaidAt` (`value`, `data`: Johnson/P5J/LaidOpens.lean).
(7) ps is free: the row is meant at the index of the full size's chain
(`flatPlaces true fullLinks true`), which fits the real chain by a run (P5J/FitFull.lean). (8) `put`
IS A BINDER: MEANT AS `OnBytes.Flat.putReq` (the request with a token put in, if that is well
formed; else the request as it is: so before the window's end, where a well-formed request has the
reply 0, every part is read at the reply 0, whatever the token): `tieStartP` IS THE TIE AT IT. The
head's part lookCallsHeard is meant through the same `put`, at the reply that the record has heard:
then the reply's block's own law is a rewriting there too.
-/
import Johnson.Goal.Meaning.HidSeat
import Johnson.Desc.Sound.FirstMeans
import Johnson.Desc.Sound.ReadAt

set_option autoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open Inst.Model.AttSeg (Raw Idn idnVal keyVec lut lutSet castT)
open VerifiableInference.OnPublicFiles.Flat (Holds GE Req)
open VerifiableInference.Desc (Strs Place)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)
open VerifiableInference.Desc.Sound (readAt SeatsNamed GroupsSeated)
open Meaning

/-- The table's parts (the program `verify-on-bytes` has a type of that name too). -/
abbrev TPart : Type := VerifiableInference.Desc.First.Part

/-- The request's public part. -/
abbrev TReq : Type := VerifiableInference.OnPublicFiles.Flat.Req

/-- The first chain's state. -/
abbrev TS : Type := VerifiableInference.Desc.First.S

/-- The three seams of the model's relation, of what the prover hides: the model's own names. -/
structure Seams (X : Model.Verify.Public) (h : Hid) : Prop where
  layers : ∀ g, LaySeam X.y h.MG g
  attention : ∀ g, AttSeam X.y (Hd.shapeA X g) (h.MG g) (h.MA g)
  head : HeadSeam X.y (h.MG 11) h.Xl

/-- **How a witness of the table is read.** -/
structure HidAt (X : Model.Verify.Public) (P W : Type) (rows cols : ℕ) where
  hid : W → Hid
  req : P × TS → TReq
  dec : P × TS → Strs → Option (Fin rows → Fin cols → GE)
  /-- segment k's committed symbols, as the witness holds them, ARE the packing of small integers.
  WHERE hid READS ITS INTEGERS BY UNPACKING ("the small integers whose packing the symbols are, else
  0") THE MODEL's CLAUSE "small" IS TRUE OF EVERY WITNESS, and where a column packs nothing small
  hid has 0 there, whatever is committed: a law on the MESSAGES (the symbols; the tables of reads)
  says something of hid's integers ONLY UNDER THIS: so it is what the part "small" says, what the
  smallness test's row closes, and what the rows in front of that test read -/
  base : ℕ → W → Prop
  /-- by hid's make: one component of the witness for all copies of a kept message -/
  seams : ∀ w, Seams X (hid w)

/-- **hid IS BUILT**: from the witness's token and, for each segment, its OWN committed arrays as
integers (`own`: a letter: the lift of the committed symbols along the layout), by the model's
own make `hidOf`: THE FIELD `seams` IS PROVED BY ITS THREE THEOREMS, for every `own`. THE SEAMS ARE
THEREBY MOVED, NOT PROVED (its own caution): a kind's law speaks of what ITS segment's
messages hold; where a segment only reads an array, `hidOf` takes the owner's: that reader and owner
read one array is not shown here. -/
def hidAtOf (X : Model.Verify.Public) {P W : Type} {rows cols : ℕ} (tok : W → Fin ppref.V)
    (own : W → ℕ → Mats ℤ) (base : ℕ → W → Prop) (req : P × TS → TReq)
    (dec : P × TS → Strs → Option (Fin rows → Fin cols → GE)) : HidAt X P W rows cols where
  hid := fun w => hidOf X (tok w) (own w)
  req := req
  dec := dec
  base := base
  seams := fun w => ⟨laySeam_hidOf X (tok w) (own w), attSeam_hidOf X (tok w) (own w),
    headSeam_hidOf X (tok w) (own w)⟩

/-- **hid OFF THE TABLE's OWN WITNESS**: `own` is no letter: it is the model's own
`ownOf`: segment k's own arrays are the small integers whose packing its committed symbols are, and
the symbols are the witness's entries at the seats named, READ AS SEGMENT k READS THEM (`readAt`).
LETTERS, MEANT AS PUBLIC FUNCTIONS OF THE PLAN (nothing here ties them to it): s k: the sizes
of segment k's signature; seat k μ r c: for row of symbols r and column c of its matrix μ: the
number of the message that holds it, its main row and its place (NO SHIFT: the release lays an array
block by block); tokV: the token as a number below the vocabulary's size; cs, arr, ms, N: the
table's own. AND req, dec, as before. TWO SEGMENTS' READINGS OF ONE MESSAGE ARE ONE OUTSIDE THE
PADS, BY THE ACCESSOR's MAKE, AND PART AT A PAD's PLACE: that reader's and owner's array are one
wants a public test more: no place that is named at a seam lies at a pad's place: NOT TYPED
HERE. THE TWO LAST ARGUMENTS ARE READ BY NOTHING IN THE BODY: THEY STAND THERE SO THAT hid CANNOT BE
FORMED AT LETTERS AT WHICH A READING FALLS TO THE ZERO MESSAGE IN SILENCE: whatever is said at
`hidAtSeat` bears them as premises BY TYPE. -/
noncomputable def hidAtSeat (X : Model.Verify.Public) {P Cells Tok : Type} {rows cols : ℕ}
    (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List VerifiableInference.Desc.Sound.Mem)
    (N : Numbers) (s : ℕ → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (tokV : Tok → Fin ppref.V) (req : P × TS → TReq)
    (dec : P × TS → Strs → Option (Fin rows → Fin cols → GE)) (_ : SeatsNamed arr N s seat)
    (_ : GroupsSeated ms N) :
    HidAt X P (VerifiableInference.Desc.Wit Cells Tok VerifiableInference.Desc.Sound.MsgT) rows
      cols :=
  hidAtOf X (fun w => tokV w.tok)
    (fun w => ownOf s fun k => symAt (s k) (seat k) (readAt cs arr ms N k w))
    (fun k w => Cb.Pv.Tail.Base (symAt (s k) (seat k) (readAt cs arr ms N k w))) req dec

/-- Segment k's list is `ownAt` (HidSeat.lean) at the messages as segment k reads them. -/
theorem hidAtSeat_own (s : ℕ → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (msgF : ℕ → Msgs) (k : ℕ) :
    (ownOf s fun k => symAt (s k) (seat k) (msgF k)) k = ownAt s seat (msgF k) k := rfl

/-- The parts of a group of layers' share. -/
def partG (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) (MG : ℕ → Mats ℤ) (g : ℕ) :
    TPart → Prop
  | .small => SmallM X.y (MG g)
  | .idn => NormField (layerShape X.P) X.layers.sc X.y g (MG g) i.mat x ∧
      EmbField (layerShape X.P) X.layers.sc X.y g (MG g) i.mat x
  | .rider => HotField (layerShape X.P) X.layers.sc X.y g (MG g) i.mat x
  | .lookCalls => KeyField (layerShape X.P) X.layers.sc X.y g (MG g) i.mat
  | _ => True

/-- The parts of an attention sub-proof's share: the model's own names. -/
def partA (S : Attention.Shape) (Za : Zs) : TPart → Prop
  | .small => AttSmall S Za
  | .lookCalls => AttKey S Za
  | .idn => AttOwn1 S Za ∧ AttOwn2 S Za
  | .rider => AttRidden S Za
  | _ => True

/-- The four parts that are open at the chain's start. -/
def parts4 : List TPart := [.idn, .lookCalls, .rider, .small]

theorem shareG {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {MG : ℕ → Mats ℤ}
    {g : ℕ} (h : ∀ p ∈ parts4, partG X i x MG g p)
    (hs : LaySeam X.y MG g) : MeansG X i x MG g :=
  ⟨h .small (by decide), (h .idn (by decide)).1, h .rider (by decide), (h .idn (by decide)).2,
    h .lookCalls (by decide), hs⟩

theorem shareA {y : Lay} {S : Attention.Shape} {Mg : Mats ℤ} {Za : Zs}
    (h : ∀ p ∈ parts4, partA S Za p)
    (hs : AttSeam y S Mg Za) : MeansA y S Mg Za :=
  ⟨h .small (by decide), h .lookCalls (by decide), (h .idn (by decide)).1,
    (h .idn (by decide)).2, h .rider (by decide), hs⟩

section
variable {X : Model.Verify.Public} {P W : Type} {rows cols : ℕ}

/-- **The table's letter `Meaning.constr`, filled**: at every index that the decoded matrix holds.
"Every digit lies in the digits' table" is no clause of the model's relation: the smallness test
opens it and leans on it: A LETTER WITH A NAME (`digitsPart`), NEVER "true". -/
def constrQ (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (k : ℕ) (p : TPart) (a : P × TS) (y : Strs)
    (w : W) : Prop :=
  if p = .lookDigits then digitsPart k a y w
  else (p = .small → H.base k w) ∧ ∀ M (i : Cm.Idx), H.dec a y = some M → Holds M i →
    if k = 24 then headPart p i a y w
    else if k % 2 = 0 then partG X i (put (H.req a) (H.hid w).tok).val (H.hid w).MG (k / 2) p
    else partA (Hd.shapeA X (k / 2)) ((H.hid w).MA (k / 2)) p

/-- **The part "small" gives `base`**: so it is false at every witness at which `base` fails. THAT
THERE IS SUCH A WITNESS IS NOT SHOWN HERE. -/
theorem constrQ_small_base (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (k : ℕ) (a : P × TS) (y : Strs) (w : W)
    (h : constrQ put H headPart digitsPart k .small a y w) : H.base k w := by
  unfold constrQ at h
  rw [if_neg (show ¬ ((.small : TPart) = .lookDigits) by decide)] at h
  exact h.1 rfl

/-- A meaning of the items with that letter filled; the promise "the stored table decodes" by THE
SAME decoder. -/
def meaningQ (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (Mg : Meaning P W) : Meaning P W :=
  { Mg with
    constr := constrQ put H headPart digitsPart
    decodes := fun a y => (H.dec a y).isSome = true }

/-- **`constrQ` WITH THE HEAD's SEGMENT A LETTER** hd (`constrQ` has the full size's 24 written in it: at
the small chain, five segments, the head is 4). -/
def constrQAt (hd : ℕ) (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (k : ℕ) (p : TPart) (a : P × TS) (y : Strs)
    (w : W) : Prop :=
  if p = .lookDigits then digitsPart k a y w
  else (p = .small → H.base k w) ∧ ∀ M (i : Cm.Idx), H.dec a y = some M → Holds M i →
    if k = hd then headPart p i a y w
    else if k % 2 = 0 then partG X i (put (H.req a) (H.hid w).tok).val (H.hid w).MG (k / 2) p
    else partA (Hd.shapeA X (k / 2)) ((H.hid w).MA (k / 2)) p

/-- `meaningQ` with the head's segment a letter. -/
def meaningQAt (hd : ℕ) (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (Mg : Meaning P W) : Meaning P W :=
  { Mg with
    constr := constrQAt hd put H headPart digitsPart
    decodes := fun a y => (H.dec a y).isSome = true }

/-- At 24 they are the full size's. -/
theorem constrQAt_full (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) :
    constrQAt 24 put H headPart digitsPart = constrQ put H headPart digitsPart := rfl

theorem meaningQAt_full (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (Mg : Meaning P W) :
    meaningQAt 24 put H headPart digitsPart Mg = meaningQ put H headPart digitsPart Mg := rfl

/-- THE NAMED PREMISE AT THE HEAD: its four parts together give the head's half in plain integers,
at the index's own output matrix. -/
def HeadCuts (pp : ScalesAndPolicy) (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop) : Prop :=
  ∀ i a y w, (∀ p ∈ parts4, headPart p i a y w) →
    HeadPlain pp i (put (H.req a) (H.hid w).tok).val (H.hid w).Xl

end

/-- The segments' sorts at the full size. -/
def fullLinks : List ModelPart :=
  (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++ [.head]

theorem constr_mem (k : ℕ) (hk : k < 25) (p : TPart) (hp : p ∈ parts4) :
    Item.constr k p ∈ start fullLinks := by
  have h : ∀ k ∈ List.range 25, ∀ p ∈ parts4, Item.constr k p ∈ start fullLinks := by decide
  exact h k (List.mem_range.2 hk) p hp

theorem ne_digits (p : TPart) (hp : p ∈ parts4) : p ≠ .lookDigits := by
  revert p
  decide

/-- **THE TIE AT THE CHAIN's FIRST BORDER**, of a record, the oracles and a witness. -/
theorem meansOfStart {X : Model.Verify.Public} {P W : Type} {rows cols : ℕ} (pp : ScalesAndPolicy)
    (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (hc : HeadCuts pp put H headPart) (N : Numbers)
    (Mg : Meaning P W) (a : P × TS) (y : Strs) (w : W)
    (h : ∀ i ∈ start fullLinks, i.holds N (meaningQ put H headPart digitsPart Mg) a y w) :
    firstMeans X pp put (H.dec a y) (H.req a) (H.hid w) := by
  intro M i hM hi
  have hk : ∀ k, k < 25 → ∀ p ∈ parts4,
      if k = 24 then headPart p i a y w
      else if k % 2 = 0 then partG X i (put (H.req a) (H.hid w).tok).val (H.hid w).MG (k / 2) p
      else partA (Hd.shapeA X (k / 2)) ((H.hid w).MA (k / 2)) p := by
    intro k hk p hp
    have h0 : constrQ put H headPart digitsPart k p a y w := h (.constr k p) (constr_mem k hk p hp)
    unfold constrQ at h0
    rw [if_neg (ne_digits p hp)] at h0
    exact h0.2 M i hM hi
  refine means_iff_from.2 fun k _ hk25 => ?_
  unfold Share
  by_cases h24 : k = 24
  · rw [if_pos h24]
    refine ⟨(H.seams w).head, hc i a y w fun p hp => ?_⟩
    have := hk 24 (by omega) p hp
    rwa [if_pos rfl] at this
  · rw [if_neg h24]
    by_cases he : k % 2 = 0
    · rw [if_pos he]
      refine shareG (fun p hp => ?_) ((H.seams w).layers (k / 2))
      have := hk k hk25 p hp
      rwa [if_neg h24, if_pos he] at this
    · rw [if_neg he]
      refine shareA (fun p hp => ?_) ((H.seams w).attention (k / 2))
      have := hk k hk25 p hp
      rwa [if_neg h24, if_neg he] at this

section
open VerifiableInference.Desc.Sound OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (oneExternalString)

variable {C : CK} {D : WholeD} {all : List LeftT} {Y P S₁ S₂ S₃ X₁ X₂ Cl W : Type}
  {X : Model.Verify.Public} {rows cols : ℕ}

/-- **The first relation**: `firstMeans` at what the witness hides; the request's public part and
what the stored word decodes to are read off a statement of the chain. -/
def firstAt (pp : ScalesAndPolicy) (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols) (ft : ℕ)
    (get : S₁ → P × TS) (a : S₁ × (EAll D all).Str) (w : W) : Prop :=
  firstMeans X pp put (H.dec (get a.1) (strsOf (frameAt D all D.key₁ ft) a.2)) (H.req (get a.1))
    (H.hid w)

/-- **`TieStart` IS A THEOREM at the filled meaning**, at the full size's list of segments. -/
theorem tieStartQ (pp : ScalesAndPolicy) (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (hc : HeadCuts pp put H headPart) (N : Numbers)
    (Mg : Meaning P W) (ft : ℕ) (ps : List Place) (get : S₁ → P × TS) :
    TieStart (D := D) (all := all) ft N (meaningQ put H headPart digitsPart Mg) fullLinks ps get
      (firstAt pp put H ft get) := by
  intro a w _ hR
  exact meansOfStart pp put H headPart digitsPart hc N Mg _ _ w fun i hi => hR i hi

/-- **THE TIE AS IT IS MEANT: at put := `putReq`** (the request with the token put in, if that is
well formed; else the request as it is): there the model's lemmas on the reply apply. -/
theorem tieStartP (pp : ScalesAndPolicy) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop)
    (hc : HeadCuts pp OnBytes.Flat.putReq H headPart) (N : Numbers) (Mg : Meaning P W) (ft : ℕ)
    (ps : List Place) (get : S₁ → P × TS) :
    TieStart (D := D) (all := all) ft N
      (meaningQ OnBytes.Flat.putReq H headPart digitsPart Mg) fullLinks ps get
      (firstAt pp OnBytes.Flat.putReq H ft get) :=
  tieStartQ pp OnBytes.Flat.putReq H headPart digitsPart hc N Mg ft ps get

/-- **THE ROW AT THE INTEGER MODEL's OWN RELATION.** -/
theorem firstChainMeansQ (pp : ScalesAndPolicy) (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (hc : HeadCuts pp put H headPart) (N : Numbers)
    (Mg : Meaning P W) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (ps : List Place)
    (get : S₁ → P × TS) (Q : Places D all S₁ S₂ S₃ W)
    (ho : EachOwn
      (onQ (Fr := frameAt D all D.key₁ T.ft₁) N (meaningQ put H headPart digitsPart Mg) fullLinks ps
        get)
      (meansQ N (meaningQ put H headPart digitsPart Mg) get) (insQ fullLinks ps)
      (outsQ fullLinks ps) (· ∈ start fullLinks) 0 (T.p₁ :: T.l₁)) :
    EachGoodIn
      (placesM T.ft₁ N (meaningQ put H headPart digitsPart Mg) fullLinks ps get
        (firstAt pp put H T.ft₁ get) Q).on₁
      (placesM T.ft₁ N (meaningQ put H headPart digitsPart Mg) fullLinks ps get
        (firstAt pp put H T.ft₁ get) Q).R₁ 0 (T.p₁ :: T.l₁) :=
  firstChainMeans C D all Y P S₁ S₂ S₃ X₁ X₂ Cl W T N _ fullLinks ps get _ Q ho
    (tieStartQ pp put H headPart digitsPart hc N Mg T.ft₁ ps get)

/-- **THE DATA's FIELD R₀ IS `firstMeans`**: other files' field "first", under two equations on
the letters: what `dec` and `req` read off the chain's first record are the decoder's value and the
request's public part. -/
theorem first_iff {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) (pp : ScalesAndPolicy)
    (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols) (N : Numbers) (Mg : Meaning P W)
    (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (links : List ModelPart) (ps : List Place)
    (get : S₁ → P × TS) (Q : Places D all S₁ S₂ S₃ W) (okF : Y → TF → Bool)
    (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃) (x : Y) (y : (oneExternalString (2 ^ D.a) SgX).Str) (w : W)
    (d : Option (Fin rows → Fin cols → GE)) (p : TReq)
    (hd : H.dec (get (T.in₁ x)) (strsOf (frameAt D all D.key₁ T.ft₁) (y, fun _ => [])) = d)
    (hp : H.req (get (T.in₁ x)) = p) :
    (T.snd tF tJ t3 (placesM T.ft₁ N Mg links ps get (firstAt pp put H T.ft₁ get) Q) okF okJ ok3 h₁
      h₂ h₃).R₀ (x, y) w ↔ firstMeans X pp put d p (H.hid w) := by
  rw [← hd, ← hp]
  exact Iff.rfl

end

end P5J

#print axioms P5J.hidAtSeat_own
#print axioms P5J.constrQ_small_base
#print axioms P5J.constrQAt_full
#print axioms P5J.meaningQAt_full
#print axioms P5J.shareG
#print axioms P5J.shareA
#print axioms P5J.constr_mem
#print axioms P5J.meansOfStart
#print axioms P5J.tieStartQ
#print axioms P5J.tieStartP
#print axioms P5J.firstChainMeansQ
#print axioms P5J.first_iff
