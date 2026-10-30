-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/BorderShapes/LKFU/Shape23.lean: Definitions with code; no theorem. THE BOOK-KEEPING AT THE EIGHTEEN BORDERS OF A KEY FILE's (AND, BY ITS LETTERS, A PROOF FILE's) TWO LATER CHAINS: for the table of joints' promise («a Bool on
the state»): shape₂ S k : Desc.K14.St → named clauses (k = 0 … 12: border k lies in front of block k of the shared chain's blocksInOrder list, 12 behind the last) · shape₃ S n g t k : Third.S₃ → named clauses (k = 0 … 4; n g t: the messages, groups
and trees that the first chain's end hands over: LETTERS: the last chain's own book-keeping is said RELATIVE to them).
IT BEARS ONE FORM ALONE, asked as its first clause: masks go ahead · G_u and Omega differ in code (a shared split) · W and Omega do not (no own split): the form of both stored sets.
WHAT A CLAUSE READS: counts, numbers, flags: how many messages, groups, trees; who is a member of which group; how many rows of which kind lie open; who is sampled, spent as a mask, whose ledger is shut. NO VALUE OF THE FIELD.
Written after a look at the small stored key file's eighteen states, in the shape's own numbers (stages · answers · columns): so the full size is a test of the formulas.
Nothing on soundness.
-/
import Johnson.Desc.K14.Text
import Johnson.Desc.Sound.BookOrder
import Johnson.Desc.Third.State

set_option autoImplicit false

namespace LKFU.Shape23
open OnBytes OnBytes.Params

abbrev Cls : Type := List (String × Bool)

def formOk (S : LinShape) : Bool := S.masksAhead && S.sharedSplitNeeded && !S.ownSplitNeeded

def plainRows (G : Group) : Nat := (G.rows.toList.filter (·.kind == .plain)).length
def genRows (G : Group) : Nat := (G.rows.toList.filter (·.kind == .generator)).length

/-- Group g: its members; its open rows, plain and generator; whether its test has begun. -/
def grpIs (st : Statement) (g : Nat) (members : List Nat) (plain gen : Nat) (inRun : Bool) : Bool :=
  match st.groups[g]? with
  | some G => G.members.toList == members && plainRows G == plain && genRows G == gen && G.rows.size == plain + gen && G.inRun == inRun
  | none => false

/-- Message o: sampled with so many sample rows; or without a sample, spent as a mask or not. -/
def msgIs (st : Statement) (o : Nat) (samples : Option Nat) (spent : Bool) : Bool :=
  match st.oracles[o]?, samples with
  | some x, some a => x.sampled && x.sampleRows.size == a && !x.spentAsMask
  | some x, none => !x.sampled && x.sampleRows.isEmpty && x.spentAsMask == spent
  | none, _ => false

/-- What a proximity test of s stages leaves behind it, from message m₀, group g₀ on: for each later stage a sampled target alone in a group whose test has begun, and a spent mask. -/
def towerIs (st : Statement) (m₀ g₀ s a : Nat) : Bool :=
  (List.range (s - 1)).all fun j =>
    msgIs st (m₀ + 2 * j) (some a) false && msgIs st (m₀ + 2 * j + 1) none true && grpIs st (g₀ + j) [m₀ + 2 * j] 0 0 true

/-- **The shared chain's thirteen borders.** a: the answers to a sample. -/
def shape₂ (S : LinShape) (a k : Nat) (d : Desc.K14.St) : Cls :=
  let st := d.st
  let l := d.loc
  let rec_ := S.fold.index.answers
  let t := S.fold.columns
  let sU := S.testU.length
  let sO := S.testOmega.length
  let msgs := if k ≤ 2 then 0 else if k ≤ 5 then 2 else if k ≤ 9 then 4 else if k == 10 then 4 + 2 * (sU - 1) else 4 + 2 * (sU - 1) + 1 + 2 * (sO - 1)
  let grps := if k ≤ 1 then 0 else if k ≤ 9 then 2 else if k == 10 then 2 + (sU - 1) else 2 + (sU - 1) + (sO - 1)
  let trees := if k ≤ 2 then 0 else if k ≤ 5 then 1 else if k ≤ 9 then 3 else if k == 10 then 3 + (sU - 1) else 3 + (sU - 1) + 1 + (sO - 1)
  [("the form that this page bears", formOk S),
   ("so many messages", st.oracles.size == msgs), ("so many groups", st.groups.size == grps),
   ("so many trees, each received as a root", d.book.trees.size == trees && d.roots == trees), ("statement and book are in step", st.oracles.size == d.book.place.size),
   ("the shared point is drawn, or not yet", l.psiSh.length == (if k ≤ 1 then 0 else S.kCol)),
   ("the two groups' numbers", if k ≤ 1 then l.gU == noId && l.gOmega == noId else l.gU == 0 && l.gOmega == 1),
   ("o_u's number and its test's first mask's", if k ≤ 2 then l.oU.oracle == noId && l.firstMask.isNone else l.oU.oracle == 0 && l.firstMask == some 1),
   ("o_u is sampled; the mask is not, and is spent by the test alone", k ≤ 2 || (msgIs st 0 (some a) false && msgIs st 1 none (decide (10 ≤ k)))),
   ("Omega's and the split's numbers", if k ≤ 5 then l.oOmega == noId && l.oSp == noId else l.oOmega == 2 && l.oSp == 3),
   ("Omega and the split are sampled", k ≤ 5 || (msgIs st 2 (some a) false && msgIs st 3 (some a) false)),
   ("the last point is drawn, or not yet", l.zFd.length == (if k ≤ 7 then 0 else S.kRow)),
   ("G_u: members, open rows, begun", k ≤ 1 ||
     grpIs st 0 (if k ≤ 3 then [] else if k ≤ 6 then [0] else [0, 3])
       (if k ≤ 3 then 0 else if k ≤ 8 then rec_ else if k == 9 then rec_ + 1 else 0) (if k ≤ 4 then 0 else if k ≤ 9 then t else 0) (decide (10 ≤ k))),
   ("G_omega: members, open rows, begun", k ≤ 1 ||
     grpIs st 1 (if k ≤ 6 then [] else [2, 3]) (if k ≤ 8 then 0 else if k ≤ 10 then 1 else 0) 0 (decide (11 ≤ k))),
   ("the split's ledger: an entry is taken at SPLIT; shut by the first test that reads it", k ≤ 5 ||
     match (st.oracles[3]?).bind (·.ledger), (st.oracles[3]?).map (·.shape) with
     | some L, some sh => L.closed == decide (10 ≤ k) &&
         L.left + (if k ≤ 8 then 0 else 1) == Send.freeMaskEntries sh.maskRows (st.codes.mask.getD sh.maskCode default).ell sh.answers
     | _, _ => false),
   ("behind the test on G_u: its later stages' messages and groups", k ≤ 9 || towerIs st 4 2 sU a),
   ("behind the test on G_omega: its own mask, spent; its later stages'", k ≤ 10 ||
     (msgIs st (4 + 2 * (sU - 1)) none true && towerIs st (4 + 2 * (sU - 1) + 1) (2 + (sU - 1)) sO a)),
   ("the book is in order: as many roots as trees; the tree at the place z bears the number z (the key file's chair's ruling 17; LAID LAST, so that the elder clauses keep their places)", VerifiableInference.Desc.Sound.bookStepB 0 d.book d.roots)]

/-- **The last chain's five borders.** n g t: the messages, groups and trees at the first chain's end; w, own, mask: W's, the own group's and the own test's first mask's numbers there. idx: the claim's masks' messages, members of the own group in front of W. -/
def shape₃ (S : LinShape) (a n g t : Nat) (idx : List Nat) (k : Nat) (s : VerifiableInference.Desc.Third.S₃) : Cls :=
  let st := s.st
  let l := s.loc
  let sW := S.testOwn.length
  let w := n - 2
  let own := g - 1
  [("the form that this page bears", formOk S),
   ("so many messages", st.oracles.size == n + (if k == 0 then 0 else 1) + (if k ≤ 2 then 0 else 2 * (sW - 1))),
   ("so many groups", st.groups.size == g + (if k ≤ 2 then 0 else sW - 1)),
   ("so many trees: the first chain's, Omega's, the own test's", s.book.trees.size == t + (if k == 0 then 0 else 1) + (if k ≤ 2 then 0 else sW - 1)),
   ("so many roots received on this chain", s.roots == (if k ≤ 2 then 0 else sW - 1)),
   ("W is the last message but one of the first chain's, the mask the last, the own group the last group", l.w == w && l.mask == some (n - 1) && l.own == own),
   ("the first own tree's number", l.firstTree == t + 1),
   ("the border lies until the first block has taken it", l.border.isSome == (k == 0)),
   ("Omega's number here", l.omega == (if k == 0 then noId else n)),
   ("W is sampled; the mask is not, and is spent by the test alone", msgIs st w (some a) false && msgIs st (n - 1) none (decide (3 ≤ k))),
   ("Omega is sampled as it was", k == 0 || msgIs st n (some a) false),
   ("the own group: members, open rows, begun",
     grpIs st own (idx ++ [w] ++ (if k == 0 then [] else [n])) (if k == 0 then 1 else if k ≤ 2 then 2 else 0) 0 (decide (3 ≤ k))),
   ("behind the own test: its later stages' messages and groups", k ≤ 2 || towerIs st (n + 1) g sW a)]

def ok (c : Cls) : Bool := c.all (·.2)
def failing (c : Cls) : List String := (c.filter (!·.2)).map (·.1)

end LKFU.Shape23
