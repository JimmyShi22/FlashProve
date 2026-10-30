-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/FillSent.lean: A LAYER OF THE FILLING OF THE TABLE OF JOINTS' MEANING: TWO PUBLIC
ITEMS THROUGH THE DOOR (`Pub.more`, Johnson/Desc/First/Borders.lean), each with its test on the
record, its rows, and what its yes gives. Small; no Mathlib. A file BESIDE the table: it turns
nothing of it. After the pattern of Johnson/Desc/First/FillKeeper.lean.

Why. The table's sentences on a run's forms (Johnson/Desc/Sound/FormsQ.lean) read the witness
through THE RECORD's OWN frame and ledger: which oracle message holds an array
(`ReqFrame.whereIs`), which holds the mask row, how many own rows an array has in the ledger. A
caller's law reads the same cells through THE PLAN. Whoever exchanges the one for the other wants
"the record's reader is the plan's term". By a search over the table and the layers of its filling
that lay at hand, no clause of the promise speaks of the five fields of the open link's frame that
`whereIs` reads, nor of the ledger's arrays.

What is said.
  `SentData`: THE PLAN's SIDE, by segment, as letters: born (of each kept target of the switch into
    the segment's group: as what it was first sent) · own (the numbers, in the statement, of the
    segment's own messages of its first sending) · kept (the numbers of the kept messages as they
    are in the segment) · trees (the look of the ledger's arrays).
  `sentDataOf shape base trees`: born, own and kept AS TERMS OFF THE REQUEST's SHAPE AND THE PLAN's
    NUMBER OF MESSAGES IN FRONT OF THE SEGMENT's FIRST SENDING: BY A READING of `ReqFrame.first`
    (OnBytes/Iop/Req.lean) and `switchVerify` (OnBytes/Iop/Cs.lean): in the first segment the own
    messages come first; in a later one the carrying message, then the kept ones, then the own.
  `sentIsB d m` ("frame.sentIs"): a link is open; its own frame's next call is "a later moment or
    the closing"; its link's number is m; its group number m has the plan's born; its own and
    keptBefore are the plan's.
  `treeLook`, `treesAreB d m` ("ledger.treesAre"): a ledger is open, and its arrays' rows, columns
    and, of each virtual row, first column and number of weights are the plan's.
  `whereIsP`, `maskP`: THE PLAN's TERMS for `ReqFrame.whereIs` and for the number of the message
    with the segment's mask row.
  **`whereIs_of_sentIs`**, `link_of_sentIs`, **`maskAt_of_sentIs`** (this one under "the frame's
    shape is the given one" too), `trees_of_treesAre`: WHAT THE TWO TESTS GIVE.
  `sentMore`: THE ROWS: both MADE at piece 1 + o of the segment (the block that sends the first
    sending and opens the link), ASKED at 3 + o (the caller) and at 4 + o (the second sending),
    DROPPED at 4 + o; o: the shift of the segment's sort. WHY SO SHORT A SPAN: own grows at each
    sending, and a public item's meaning sees the record and no border.
  `pubSent`, `fillSent`: the layer's half with code; the layer. `fillSent_pub`, `_more`,
    `_sentIs`, `_treesAre` (by the make); `fillSent_else`: what it leaves.
  `sentFit_small`, `sentFit_full`, `sentFit_control`: the table's test `pubFit` at this filling
    alone, at two written lists of segments; with the maker's row struck it says false.

OBJECT: no block's text: the carried record's readers `S.link?` and `S.fork?`. USER: none yet;
meant: Johnson/Road/K4/Rec/. LETTERS, filled by nobody: every field of `SentData`.

Limits. NEITHER TEST HAS RUN AT ANY RECORD. THAT AN HONEST RECORD MEETS THEM AT THE BORDERS AT WHICH
THE ROWS HOLD THEM OPEN IS BY A READING OF `ReqFrame.first` (OnBytes/Iop/Req.lean) ALONE. NOBODY HAS
SAID "I MAKE IT" OR "I KEEP IT". At wrong letters the promise holds of marked records alone, in
silence. K04_law, the law of K4's block itself, IS NOT PROVED BY THIS. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.FillSent
open OnBytes OnBytes.Model

/-- What is read of an array of the ledger: its rows, its columns; of each virtual row the first
column and the number of weights. -/
abbrev TreeLook : Type := Nat × Nat × List (Nat × Nat)

/-- An array's look. -/
def treeLook (X : HTree) : TreeLook := (X.R, X.K, X.rows.toList.map fun r => (r.L0, r.L.size))

/-- **The plan's side**, by segment. -/
structure SentData where
  /-- of each kept target of the switch into the segment's group: as what it was first sent -/
  born : Nat → Array (Nat × Nat)
  /-- the numbers, in the statement, of the segment's own messages of its first sending -/
  own : Nat → Array Nat
  /-- the numbers of the kept messages of earlier segments as they are in this one -/
  kept : Nat → Array Nat
  /-- the look of the arrays of the segment's ledger -/
  trees : Nat → List TreeLook

/-- **born, own and kept off the request's shape.** base m: how many oracle messages are sent in
front of segment m's first sending. BY A READING; it has run nowhere. -/
def sentDataOf (shape : Params.ReqShape) (base : Nat → Nat) (trees : Nat → List TreeLook) :
    SentData where
  born m := ((reqGroups shape).getD m {}).born
  own m :=
    let n0 := (((shape.link[m]?.map (·.messages)).getD []).filter fun x => x.moment == 0).length
    let off := if m == 0 then 0 else 1 + ((reqGroups shape).getD m {}).born.size
    (Array.range n0).map (· + (base m + off))
  kept m :=
    if m == 0 then #[]
    else (Array.range ((reqGroups shape).getD m {}).born.size).map (· + (base m + 1))
  trees := trees

/-- "frame.sentIs". -/
def sentIsB (d : SentData) (m : Nat) (s : S) : Bool :=
  s.link?.any fun L =>
    decide (L.check.frame.next = .laterOrClose) && decide (L.check.frame.link = m) &&
      decide ((L.check.frame.groups.getD m {}).born = d.born m) &&
      decide (L.check.frame.own = d.own m) && decide (L.check.frame.keptBefore = d.kept m)

/-- "ledger.treesAre". -/
def treesAreB (d : SentData) (m : Nat) (s : S) : Bool :=
  s.fork?.any fun G => decide (G.trees.toList.map treeLook = d.trees m)

/-! ## The plan's terms -/

/-- The plan's term for `ReqFrame.whereIs` in segment m, in front of its second sending. -/
def whereIsP (d : SentData) (m born message : Nat) : Option Nat :=
  if born == m then (d.own m)[message]?
  else ((d.born m).idxOf? (born, message)).bind fun i => (d.kept m)[i]?

/-- The plan's term for the number of the message that holds segment m's mask row. -/
def maskP (shape : Params.ReqShape) (d : SentData) (m : Nat) : Option Nat :=
  (((shape.link[m]?.map (·.messages)).getD []).findIdx? fun x =>
    x.shape.maskRows != 0).bind fun i => whereIsP d m m i

/-! ## What the two tests give -/

section
variable {d : SentData} {m : Nat} {s : S} {L : LinkCtx}

/-- The five equations. -/
theorem five_of_sentIs (hL : s.link? = some L) (h : sentIsB d m s = true) :
    L.check.frame.next = .laterOrClose ∧ L.check.frame.link = m ∧
      (L.check.frame.groups.getD m {}).born = d.born m ∧ L.check.frame.own = d.own m ∧
      L.check.frame.keptBefore = d.kept m := by
  unfold sentIsB at h
  rw [hL] at h
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem link_of_sentIs (hL : s.link? = some L) (h : sentIsB d m s = true) :
    L.check.frame.link = m := (five_of_sentIs hL h).2.1

/-- **The open link's frame finds a message where the plan's term does.** -/
theorem whereIs_of_sentIs (hL : s.link? = some L) (h : sentIsB d m s = true)
    (born message : Nat) :
    L.check.frame.whereIs born message = whereIsP d m born message := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := five_of_sentIs hL h
  have e : (ReqNext.laterOrClose != ReqNext.laterOrClose) = false := by decide
  unfold ReqFrame.whereIs whereIsP
  rw [h1, h2, h3, h4, h5, e]
  first | rfl | simp

/-- **The message with the mask row**, where the frame's shape is the given one. The left side is
the text of `K9.maskAt` (Johnson/Desc/First/Batch/FormsIn.lean), written out. -/
theorem maskAt_of_sentIs {shape : Params.ReqShape} (hL : s.link? = some L)
    (h : sentIsB d m s = true) (hs : L.check.frame.shape = shape) :
    ((((L.check.frame.shape.link[L.check.frame.link]?.map (·.messages)).getD []).findIdx? fun x =>
      x.shape.maskRows != 0).bind fun i => L.check.frame.whereIs L.check.frame.link i) =
      maskP shape d m := by
  unfold maskP
  rw [hs, link_of_sentIs hL h]
  congr 1
  funext i
  exact whereIs_of_sentIs hL h m i

/-- The ledger's arrays have the plan's look. -/
theorem trees_of_treesAre {G : Fork} (hG : s.fork? = some G) (h : treesAreB d m s = true) :
    G.trees.toList.map treeLook = d.trees m := by
  unfold treesAreB at h
  rw [hG] at h
  simpa only [Option.any_some, decide_eq_true_eq] using h

end

/-! ## The rows -/

def sentName (m : Nat) : MoreName := (some m, "frame.sentIs")
def treesName (m : Nat) : MoreName := (some m, "ledger.treesAre")

/-- **The door's filling.** -/
def sentMore : More where
  rows links p :=
    match p.link with
    | some m =>
      match links[m]? with
      | none => {}
      | some sub =>
        let o := shift sub
        if p.piece == 1 + o then { makes := [sentName m, treesName m] }
        else if p.piece == 3 + o then { asks := [sentName m, treesName m] }
        else if p.piece == 4 + o then
          { asks := [sentName m, treesName m], drops := [sentName m, treesName m] }
        else {}
    | none => {}

/-! ## The layer -/

/-- Is the item one of this layer's? -/
def sentItem : Pub → Bool
  | .more (some _) name => name == "frame.sentIs" || name == "ledger.treesAre"
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. -/
def pubSent {P : Type} (d : SentData) (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .more (some m) name =>
      if name == "frame.sentIs" then sentIsB d m a.2
      else if name == "ledger.treesAre" then treesAreB d m a.2
      else f (.more (some m) name) a
    | q => f q a

/-- **The layer.** -/
def fillSent {P W : Type} (d : SentData) (Mg : Meaning P W) : Meaning P W :=
  { Mg with pub := pubSent d Mg.pub, more := Mg.more.merge sentMore }

section
variable {P W : Type} (d : SentData) (Mg : Meaning P W)

theorem fillSent_pub : (fillSent d Mg).pub = pubSent d Mg.pub := rfl

theorem fillSent_more : (fillSent d Mg).more = Mg.more.merge sentMore := rfl

theorem fillSent_sentIs (m : Nat) (a : P × S) :
    (fillSent d Mg).pub (moreItem (sentName m)) a = sentIsB d m a.2 := rfl

theorem fillSent_treesAre (m : Nat) (a : P × S) :
    (fillSent d Mg).pub (moreItem (treesName m)) a = treesAreB d m a.2 := rfl

/-- Every other item is handed on. -/
theorem fillSent_else (q : Pub) (h : sentItem q = false) (a : P × S) :
    (fillSent d Mg).pub q a = Mg.pub q a := by
  show pubSent d Mg.pub q a = Mg.pub q a
  unfold pubSent
  split
  · rename_i m name
    simp only [sentItem, Bool.or_eq_false_iff] at h
    rw [if_neg (by simp [h.1]), if_neg (by simp [h.2])]
  · rfl

end

/-! ## The table's test at this filling alone -/

/-- Two written lists of segments. -/
def segsSmall : List ModelPart := [.layers, .attention, .layers, .attention, .head]
def segsFull : List ModelPart :=
  (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++ [.head]

set_option maxRecDepth 100000 in
theorem sentFit_small : pubFit sentMore segsSmall (flatPlacesOf segsSmall true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sentFit_full : pubFit sentMore segsFull (flatPlacesOf segsFull true) = true := by
  decide +kernel

/-- The filling with the maker's row struck. -/
def sentMoreNoMaker : More where
  rows links p := { sentMore.rows links p with makes := [] }

set_option maxRecDepth 100000 in
/-- **A control**: without a maker the test rings. -/
theorem sentFit_control :
    pubFit sentMoreNoMaker segsSmall (flatPlacesOf segsSmall true) = false := by
  decide +kernel

end VerifiableInference.Desc.First.FillSent

#print axioms VerifiableInference.Desc.First.FillSent.whereIs_of_sentIs
#print axioms VerifiableInference.Desc.First.FillSent.maskAt_of_sentIs
#print axioms VerifiableInference.Desc.First.FillSent.trees_of_treesAre
#print axioms VerifiableInference.Desc.First.FillSent.fillSent_else
#print axioms VerifiableInference.Desc.First.FillSent.sentFit_small
#print axioms VerifiableInference.Desc.First.FillSent.sentFit_full
#print axioms VerifiableInference.Desc.First.FillSent.sentFit_control
