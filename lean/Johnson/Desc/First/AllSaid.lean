-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/AllSaid.lean: who answers for what a public item says beside its test with code
(`Meaning.pubP`, Johnson/Desc/First/Borders.lean)? The twin of `allFilled`
(Johnson/Desc/First/AllFilled.lean) for that field. Definitions with code, four theorems. No
Mathlib. The table answers at the thirteen names that leave the list of extra
public tests too.

Why. The field's default is "True at every item": a sentence that no part lays is then granted in
silence. Here stands one written table: for each constructor and each name
of the list of extra public tests: the part that lays a sentence, or the part whose test with code
is taken to say all ("no sentence is meant"). The names in it are this table's reading alone:
they are not the named parts' own word.
The closed meaning beneath (Johnson/Desc/Sound/MgBase.lean) says "False" at every item that
the table leaves out: the promise is then false wherever such an item is open.
  `saysNone q`: the part to which the table gives "no sentence is meant" at q. By the constructor
    and the name alone: it reads no parameter: so the closed meaning beneath can be laid by it.
  `whoSays q`: that part; or, at left and leftOn, the lookups' part, which lays a sentence; or, at
    hasRow, the part of the pending claim on the weights, which lays "True" itself.
  `allSaidBy f M links ps`, `unsaidBy`: every public item that the promise asks at a border has an
    answer of f; for printing: where not. `allSaid`, `unsaid`: at f := whoSays.
  `allSaid_mem`: the test's acceptance, border by border and item by item.
  `whoSays_of_whoFills`: the table leaves out no item whose test with code a part claims: where
    `whoFills` names a part, `whoSays` names one: at every structure of parameters.
  `saysNone_of_leaves`: at every name that leaves the list of extra public tests (`leavesName`,
    Johnson/Desc/First/SmallDoor.lean) the table has an answer. These thirteen lines matter at a
    wider meaning alone, at which such names are open: at the composed meaning they are open
    at no border. They are this table's reading alone (at the four of the pending claim on the
    weights' part: a reading of that part's own files).
  `allSaid_of_allFilled`: so `allFilled`'s acceptance gives `allSaid`'s: `allSaid` is no independent
    test: it cannot reject where `allFilled` accepts. What this file adds is the written table and
    the "False" beneath it.

Limits. The promise asks `pubP` at the open public items alone; `allSaid` walks these and the items
tied to open items (`askedAt`): more than is needed. That "no sentence is meant" is right at an item
is no theorem: a law that wants more of an item than its test with code must get a sentence laid.
Whether any law takes `pubP` at an item of `saysNone` as a premise is not shown here. `request`
has no answer. Nothing on soundness.

-/
import Johnson.Desc.First.AllFilled
import Johnson.Desc.First.SmallDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K13 (k13ItemC)
open VerifiableInference.Desc.First.FillK4 (k4Item)
open VerifiableInference.Desc.Kinds.Head (k6k7Item)
open VerifiableInference.Desc.First.Look (k3Item)
open VerifiableInference.Desc.First.FillP1 (p1Item)
open H2K5.Door (k5Item)
open VerifiableInference.Desc.First.FillSent (sentItem sent1Item)
open VerifiableInference.Desc.First.FillBare (leftItem)

/-- **The part to which this file's table gives "no sentence is meant" at the item.** -/
def saysNone : Pub → Option String
  | .ledger _ => some "the table's own"
  | .freeAbove _ => some "the table's own"
  | .unheard => some "the table's own"
  | .tokenSmall => some "the head's"
  | .look _ => some "the segment's caller's"
  | .callerIn _ => some "the segment's caller's"
  | .lookIn _ _ => some "the lookups'"
  | .lookOut _ _ => some "the lookups'"
  | .linkFresh _ => some "the lookups'"
  | .noneSent => some "the index's and the last sub-protocols'"
  | .indexIs => some "the index's and the last sub-protocols'"
  | .indexThere => some "the index's and the last sub-protocols'"
  | .frontOk => some "the index's and the last sub-protocols'"
  | .evalLaid => some "the index's and the last sub-protocols'"
  | .formsIn _ _ _ => some "the claims on linear forms'"
  | .formsInT _ _ _ => some "the claims on linear forms'"
  | .totalIn _ => some "the claims on linear forms'"
  | .more none name =>
    if name == "K13.wSits" then some "the index's and the last sub-protocols'"
    else if name == "K12.bookInOrder" || name == "K12.seatsCarried" || name == "K12.bookFits" ||
        name == "K12.msgShapes" || name == "K13.weightsOk" then
      some "the proximity test's names' (leaves the list)"
    else if name == "K13.pileMasks" || name == "K13.pileWithin" || name == "K13.oneRow" then
      some "the index's and the last sub-protocols' (leaves the list)"
    else none
  | .more (some _) name =>
    if name == "frame.sentIs" || name == "ledger.treesAre" || name == "frame.sentIs1" then
      some "what has been sent"
    else if name == "K4.rowsBare" || name == "K4.lookLeft" then some "the feed-forward caller's"
    else if name == "K5.readsThere" || name == "K5.okAt" || name == "K5.liveReq" ||
        name == "K5.plain" then some "the attention caller's"
    else if name == "frame.liveIs" then some "the lookups' (leaves the list)"
    else if name == "pile.room" || name == "K8.lay7" || name == "K8.onThird" ||
        name == "K8.funsThird" then some "the pending claim on the weights' (leaves the list)"
    else none
  | _ => none

/-- **Who answers for what the item says beside its test with code.** -/
def whoSays : Pub → Option String
  | .left _ => some "the lookups': a sentence"
  | .leftOn _ => some "the lookups': a sentence"
  | .hasRow _ => some "the pending claim on the weights'"
  | q => saysNone q

/-- For printing: where f has no answer at an asked item. -/
def unsaidBy (f : Pub → Option String) (M : More) (links : List ModelPart) (ps : List Place) :
    List (Nat × Pub) :=
  (askedAt M links ps).zipIdx.flatMap fun x =>
    (x.1.filter fun q => (f q).isNone).map fun q => (x.2, q)

/-- Every asked public item has an answer of f. -/
def allSaidBy (f : Pub → Option String) (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (askedAt M links ps).all fun Q => Q.all fun q => (f q).isSome

def unsaid (M : More) (links : List ModelPart) (ps : List Place) : List (Nat × Pub) :=
  unsaidBy whoSays M links ps

/-- **At every asked public item somebody answers for its sentence.** -/
def allSaid (M : More) (links : List ModelPart) (ps : List Place) : Bool := allSaidBy whoSays M links ps

theorem allSaid_mem (M : More) (links : List ModelPart) (ps : List Place)
    (h : allSaid M links ps = true) (Q : List Pub) (hQ : Q ∈ askedAt M links ps) (q : Pub)
    (hq : q ∈ Q) : (whoSays q).isSome = true :=
  List.all_eq_true.1 (List.all_eq_true.1 h Q hQ) q hq

/-- **The table leaves out no item whose test with code a part claims.** -/
theorem whoSays_of_whoFills (D : PubData) (q : Pub) (h : (whoFills D q).isSome = true) :
    (whoSays q).isSome = true := by
  cases q with
  | request =>
    simp [whoFills, formsItem, k13ItemC, k3Item, k6k7Item, k4Item, p1Item, k5Item, sentItem,
      sent1Item, leftItem, keeperItem] at h
  | more sg name =>
    cases sg with
    | none =>
      by_cases e : (name == "K13.wSits") = true
      · simp [whoSays, saysNone, e]
      · simp [whoFills, formsItem, k13ItemC, k3Item, k6k7Item, k4Item, p1Item, k5Item, sentItem,
          sent1Item, leftItem, keeperItem, e] at h
    | some m =>
      by_cases e1 : (name == "frame.sentIs" || name == "ledger.treesAre" ||
          name == "frame.sentIs1") = true
      · simp [whoSays, saysNone, e1]
      · by_cases e2 : (name == "K4.rowsBare" || name == "K4.lookLeft") = true
        · simp [whoSays, saysNone, e1, e2]
        · by_cases e3 : (name == "K5.readsThere" || name == "K5.okAt" || name == "K5.liveReq" ||
              name == "K5.plain") = true
          · simp [whoSays, saysNone, e1, e2, e3]
          · exfalso
            simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at e1 e2 e3
            simp [whoFills, formsItem, k13ItemC, k3Item, k6k7Item, k4Item, p1Item, k5Item,
              sentItem, sent1Item, leftItem, keeperItem, e1, e2, e3] at h
  | _ => rfl

/-- **Every name that leaves the list of extra public tests has an answer in the table.** -/
theorem saysNone_of_leaves (n : MoreName) (h : leavesName n = true) :
    (saysNone (moreItem n)).isSome = true := by
  obtain ⟨sg, name⟩ := n
  cases sg with
  | none =>
    simp only [leavesName, List.contains_cons, List.contains_nil, Bool.or_false,
      Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h | h | h | h | h | h | h <;> subst h <;> rfl
  | some m =>
    simp only [leavesName, List.contains_cons, List.contains_nil, Bool.or_false,
      Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h | h | h | h <;> subst h <;> rfl

theorem allSaid_of_allFilled (D : PubData) (M : More) (links : List ModelPart) (ps : List Place)
    (h : allFilled D M links ps = true) : allSaid M links ps = true := by
  unfold allSaid allSaidBy
  refine List.all_eq_true.2 fun Q hQ => List.all_eq_true.2 fun q hq => ?_
  exact whoSays_of_whoFills D q (allFilled_mem D M links ps h Q hQ q hq)

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.allSaid_mem
#print axioms VerifiableInference.Desc.First.whoSays_of_whoFills
#print axioms VerifiableInference.Desc.First.saysNone_of_leaves
#print axioms VerifiableInference.Desc.First.allSaid_of_allFilled
