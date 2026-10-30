-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Shape/Facts.lean: the shared chain's shape (Johnson/Desc/K14/Shape/Lin.lean): THE
ONE TEST ON THE SHAPE at the border in front of each of the linear claim's eight sub-protocols, and
behind the last (the border b stands in front of the chain's sub-protocol number b, counted from 0).
Definitions with code, and the laws that say what the facts' half says of a state, at 1 to 8.

The test has two halves. stateB: the facts on a state under which the sub-protocol's step returns
(Johnson/Desc/K14/Honest/Returns.lean: Facts), but for the key's entries; up to "(rec_gamma)" with:
the key's sizes fit. kindsB: which constraints lie on the two groups, by kind and in their order. At
9 it says of what stands behind "SPLIT": the two groups with their members AS SETS, the three
sampled messages, o_omega's tree, o_sp's ledger with one entry taken, both points' lengths, and what
lies on the groups. THAT IS LESS THAN THE NEXT SUB-PROTOCOL's FRONT ASKS
(Johnson/Desc/K12/Front.lean: frontL): its clauses on the members' order, the marks kept, the groups
that a member knows, the number of sample constraints, the first mask's message and the members'
trees read fields that no conjunct here reads; and its clause on the members' pads asks that the
public pad can be made, where the conjunct here compares with the empty list if it cannot. What
stands behind "SPLIT" is given whole, as a term with code, in Johnson/Desc/K14/Shape/End.lean.

IT IS SUFFICIENT, NOT NECESSARY, AND NOT BY ITSELF: Johnson/Desc/K14/Shape/Run.lean says with what.
No lemma shows a conjunct needed. By a reading of the sub-protocols' guards
(Johnson/Desc/K14/Text.lean), which no law says: idle for the sub-protocol's own return, and kept
for handing on, among them: at "LIN zeta" the whole test; the key's sizes at 1 and 2; o_u's facts at
5 and 6; «o_omega is not o_u» at 6 and 7; «statement and book are in step» at 1, 3, 4 and from 6 on;
o_omega's group and «the two groups differ» at 2 to 5; o_omega's tree at 7 and 8; kindsB throughout.
No conjunct reads the count of roots, the first mask's number, a group's marks kept or its members'
order, a message's groups, its number of sample constraints or whether it is spent, a ledger other
than o_sp's, or of a tree anything but o_omega's parts. Nothing ties this test to the library's own
book-keeping at these borders (Johnson/Desc/K14/Law/ShapesSend.lean: shapeK). That it gives the
guards of the ground's own functions on shapes, under PlanFacts, the two sendings' test on the plan
and Eight P, and at the two sendings the sending's own guards in their stead:
Johnson/Desc/K14/Shape/Comp.lean.

Main names:
  groupB, msgB, carriedB, hasUB, aloneB, hasOmB, ledB, hasOB   the facts of
                      Johnson/Desc/K14/Honest/YesFacts.lean and YesBorders.lean as tests on the
                      shape; groupB_iff, msgB_iff, carriedB_iff, hasUB_iff, aloneB_eq, hasOB_iff:
                      each says its fact
  kindsAt, kindsU, kindsO, kindsB   what lies on the two groups
  stateB, stateB_iff  **the facts' half**: at a state's shape it holds exactly where Facts holds at
                      the state's own key (4 to 8); AT 1 TO 3: exactly where Facts holds there and
                      the key's sizes fit
  factsB, factsB_iff  **the one test**

WHAT THE SHAPE DOES NOT HOLD, THOUGH A LATER SUB-PROTOCOL OF THE CHAIN ASKS IT. The front of a
proximity test asks of ALL constraints that lie open on its group that each could be laid now
(Johnson/Desc/Ground/Ask.lean: openClaimsE). In front of the batching the test asks of these and of
the members' sample constraints that they can be combined (Johnson/Desc/K12/JoinGuarded.lean: combOk).
Sh2 does not hold that. For the first a mark stands beside the shape
(Johnson/Desc/Ground/Shape/Claims.lean; along the eight: Johnson/Desc/K14/Shape/Mark.lean).

What is not claimed. Nothing on soundness, on completeness or on hiding.
-/
import Johnson.Desc.K14.Shape.Pieces
import Johnson.Desc.K14.Honest.Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Shape
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Own (aloneIn keyFits)
open Desc.K14.Honest (GroupIs MsgIs Carried HasU HasO Facts)

/-! ## The facts as tests on the shape -/

/-- GroupIs, on the shape. -/
def groupB (h : StSh) (g code maskCode : Nat) (ms : List Nat) : Bool :=
  match h.groups[g]? with
  | some G => G.code == code && G.maskCode == maskCode && !G.inRun &&
      G.members.all (ms.contains ·) && ms.all (G.members.contains ·)
  | none => false

/-- The test says GroupIs. -/
theorem groupB_iff (T : Statement) (g code maskCode : Nat) (ms : List Nat) :
    groupB (stSh T) g code maskCode ms = true ↔ GroupIs T g code maskCode ms := by
  unfold groupB GroupIs
  rw [grp_get]
  cases hG : T.groups[g]? with
  | none => simp
  | some G =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left', Bool.and_eq_true, beq_iff_eq,
      Bool.not_eq_true', List.all_eq_true, List.contains_iff_mem, and_assoc]
    show (G.code = code ∧ G.maskCode = maskCode ∧ G.inRun = false ∧
      (∀ x ∈ G.members.toList, x ∈ ms) ∧ ∀ x ∈ ms, x ∈ G.members.toList) ↔ _
    simp only [Array.mem_toList_iff]
    exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, fun o => ⟨d o, e o⟩⟩,
      fun ⟨a, b, c, d⟩ => ⟨a, b, c, fun o => (d o).1, fun o => (d o).2⟩⟩

/-- MsgIs, on the shape. As in MsgIs, where the public pad cannot be made the message's pad is
compared with the empty list (getD []). -/
def msgB (h : StSh) (o : Nat) (s : OracleShape) : Bool :=
  match h.oracles[o]? with
  | some x => decide (x.shape = s) && x.sampled &&
      decide (x.pad = ((Send.pad h.codes s).getD []).map fun p => (p.part, p.index))
  | none => false

/-- The test says MsgIs. -/
theorem msgB_iff (T : Statement) (o : Nat) (s : OracleShape) :
    msgB (stSh T) o s = true ↔ MsgIs T o s := by
  unfold msgB MsgIs
  rw [orc_get]
  cases hx : T.oracles[o]? with
  | none => simp
  | some x =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left', Bool.and_eq_true,
      decide_eq_true_eq, and_assoc]
    rfl

/-- Carried, on the shape. Its clause on the key is left out: at the state's own key it says
nothing. -/
def carriedB (P : P14) (a : Sh2) (mU mO : List Nat) : Bool :=
  decide (a.core.st.codes = P.codes) && a.core.st.oracles.length == a.core.book.place.length &&
    a.lin.psi == P.par.S.kCol && a.lin.gU != a.lin.gOmega &&
    groupB a.core.st a.lin.gU P.par.S.fold.u.code P.par.S.sharedMaskCode mU &&
    groupB a.core.st a.lin.gOmega P.par.S.omega.code P.par.S.sharedMaskCode mO

/-- The test says Carried, at the state's own key. -/
theorem carriedB_iff (P : P14) (d : St) (mU mO : List Nat) :
    carriedB P (sh2 d) mU mO = true ↔ Carried P.par P.codes d.loc.key d mU mO := by
  unfold carriedB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, and_assoc]
  show (d.st.codes = P.codes ∧ (stSh d.st).oracles.length = (bookSh d.book).place.length ∧
    d.loc.psiSh.length = P.par.S.kCol ∧ d.loc.gU ≠ d.loc.gOmega ∧
    groupB (stSh d.st) d.loc.gU _ _ mU = true ∧ groupB (stSh d.st) d.loc.gOmega _ _ mO = true) ↔ _
  rw [groupB_iff, groupB_iff, orc_size, place_size]
  exact ⟨fun ⟨a, b, c, e, f, g⟩ => ⟨a, b, rfl, c, e, f, g⟩,
    fun h => ⟨h.codes, h.step, h.psi, h.two, h.gU, h.gO⟩⟩

/-- HasU, on the shape. -/
def hasUB (P : P14) (a : Sh2) : Bool :=
  decide (a.lin.lay = vectorLay a.core.st.codes P.par.S.fold.u P.par.S.fold.rowsHigh) &&
    msgB a.core.st a.lin.oU P.par.S.fold.u

/-- The test says HasU. -/
theorem hasUB_iff (P : P14) (d : St) : hasUB P (sh2 d) = true ↔ HasU P.par d := by
  unfold hasUB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  show (d.loc.oU.lay = vectorLay d.st.codes _ _ ∧ msgB (stSh d.st) d.loc.oU.oracle _ = true) ↔ _
  rw [msgB_iff]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun h => ⟨h.lay, h.u⟩⟩

/-- The message o has a tree to itself, on the shape. -/
def aloneB (b : BookSh) (o : Nat) : Bool :=
  match (b.place[o]?).bind fun p => b.trees[p.1]? with
  | some t => t.parts == [o]
  | none => false

/-- It is the library's test on the book. -/
theorem aloneB_eq (B : TreeBook) (o : Nat) : aloneB (bookSh B) o = aloneIn B o := by
  unfold aloneB aloneIn
  rw [place_get]
  cases hp : B.place[o]? with
  | none => rfl
  | some p =>
    simp only [Option.bind_some, tree_get]
    cases B.trees[p.1]? with
    | none => rfl
    | some t =>
      show (t.parts.toList == [o]) = (t.parts == #[o])
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact ⟨fun h => Array.ext' h, fun h => by rw [h]⟩

/-- HasO but for o_sp's ledger, on the shape. -/
def hasOmB (P : P14) (a : Sh2) : Bool :=
  msgB a.core.st a.lin.oOmega P.par.S.omega && msgB a.core.st a.lin.oSp P.par.S.sharedSplit &&
    a.lin.oOmega != a.lin.oSp && a.lin.oSp != a.lin.oU && a.lin.oOmega != a.lin.oU &&
    aloneB a.core.book a.lin.oOmega

/-- o_sp's ledger is l, if the message is there. -/
def ledB (a : Sh2) (l : Option Ledger) : Bool :=
  match a.core.st.oracles[a.lin.oSp]? with
  | some x => decide (x.ledger = l)
  | none => true

/-- HasO, on the shape. -/
def hasOB (P : P14) (a : Sh2) : Bool :=
  hasOmB P a && ledB a (Slice.freshLedger a.core.st.codes P.par.S.sharedSplit)

/-- The test says HasO. -/
theorem hasOB_iff (P : P14) (d : St) : hasOB P (sh2 d) = true ↔ HasO P.par d := by
  unfold hasOB hasOmB ledB
  simp only [Bool.and_eq_true, bne_iff_ne, and_assoc]
  show (msgB (stSh d.st) d.loc.oOmega _ = true ∧ msgB (stSh d.st) d.loc.oSp _ = true ∧
    d.loc.oOmega ≠ d.loc.oSp ∧ d.loc.oSp ≠ d.loc.oU.oracle ∧ d.loc.oOmega ≠ d.loc.oU.oracle ∧
    aloneB (bookSh d.book) d.loc.oOmega = true ∧
    (match (stSh d.st).oracles[d.loc.oSp]? with
      | some x => decide (x.ledger = Slice.freshLedger d.st.codes P.par.S.sharedSplit)
      | none => true) = true) ↔ _
  rw [msgB_iff, msgB_iff, aloneB_eq, orc_get]
  have hl : ((match (d.st.oracles[d.loc.oSp]?).map orcSh with
      | some x => decide (x.ledger = Slice.freshLedger d.st.codes P.par.S.sharedSplit)
      | none => true) = true) ↔ ∀ x, d.st.oracles[d.loc.oSp]? = some x →
        x.ledger = Slice.freshLedger d.st.codes P.par.S.sharedSplit := by
    cases d.st.oracles[d.loc.oSp]? with
    | none => simp
    | some x => simp [orcSh]
  rw [hl]
  exact ⟨fun ⟨a, b, e, f, g, h, c⟩ => ⟨a, b, c, e, f, g, h⟩,
    fun h => ⟨h.omega, h.sp, h.apart, h.apartU, h.apartOU, h.alone, h.ledger⟩⟩

/-! ## What lies on the two groups -/

/-- The kinds of the constraints on the group g, in their order; none where the group is not
there. -/
def kindsAt (c : CoreSh) (g : Nat) : List RowKind := ((c.st.groups[g]?).map (·.kinds)).getD []

/-- **What lies on o_u's group at the border b**: from 4 on a plain constraint for each OOD seed of
the key, in the plan's number (index.answers); from 5 on one of the kind generator for each sampled
location; from 9 on one plain constraint more. -/
def kindsU (P : P14) (b : Nat) : List RowKind :=
  (if 4 ≤ b then List.replicate P.par.S.fold.index.answers .plain else []) ++
    (if 5 ≤ b then List.replicate P.par.S.fold.columns .generator else []) ++
    if 9 ≤ b then [.plain] else []

/-- **What lies on o_omega's group at the border b**: from 9 on one plain constraint. -/
def kindsO (b : Nat) : List RowKind := if 9 ≤ b then [.plain] else []

/-- The two groups hold just these. -/
def kindsB (P : P14) (b : Nat) (a : Sh2) : Bool :=
  decide (kindsAt a.core a.lin.gU = kindsU P b) && decide (kindsAt a.core a.lin.gOmega = kindsO b)

/-! ## The one test at each border -/

/-- The facts of Johnson/Desc/K14/Honest/Returns.lean but for the key's entries, as a test on the
shape; up to 3 with: the key's sizes fit; at 9: what stands behind "SPLIT": one entry of o_sp is
taken. At 0 and from 10 on it is true: it says nothing there. -/
def stateB (P : P14) : Nat → Sh2 → Bool
  | 1, a => decide (a.core.st.codes = P.codes) &&
      a.core.st.oracles.length == a.core.book.place.length && keyB a.lin P.par.S.fold.index
  | 2, a => carriedB P a [] [] && keyB a.lin P.par.S.fold.index
  | 3, a => carriedB P a [] [] && hasUB P a && keyB a.lin P.par.S.fold.index
  | 4, a => carriedB P a [a.lin.oU] [] && hasUB P a
  | 5, a => carriedB P a [a.lin.oU] [] && hasUB P a
  | 6, a => carriedB P a [a.lin.oU] [] && hasUB P a && hasOB P a
  | 7, a => carriedB P a [a.lin.oU, a.lin.oSp] [a.lin.oOmega, a.lin.oSp] && hasUB P a && hasOB P a
  | 8, a => carriedB P a [a.lin.oU, a.lin.oSp] [a.lin.oOmega, a.lin.oSp] && hasUB P a &&
      hasOB P a && a.lin.zFd == P.par.S.kRow
  | 9, a => carriedB P a [a.lin.oU, a.lin.oSp] [a.lin.oOmega, a.lin.oSp] && hasUB P a &&
      hasOmB P a &&
      ledB a ((Slice.freshLedger a.core.st.codes P.par.S.sharedSplit).map ledNext) &&
      a.lin.zFd == P.par.S.kRow
  | _, _ => true

/-- **THE ONE TEST ON THE SHAPE AT THE BORDER b** (in front of the sub-protocol number b; 9: behind
"SPLIT"): the facts, and from 2 on what lies on the two groups. At 0 it is true: it says nothing
there. FROM 10 ON IT IS THE TEST ON THE KINDS AT 9. By reading, no law: no state behind the chain's
sub-protocol number 9 passes it (the beginning of a proximity test takes the constraints off the
group). No law here names the test there. -/
def factsB (P : P14) (b : Nat) (a : Sh2) : Bool :=
  stateB P b a && (decide (b < 2) || kindsB P b a)

/-- **The test says the facts**, at the state's own key: at 4 to 8 it holds exactly where Facts
holds; at 1 to 3 exactly where Facts holds and the key's sizes fit (keyFits). -/
theorem stateB_iff (P : P14) (d : St) :
    (stateB P 1 (sh2 d) = true ↔
      Facts P d.loc.key 1 d ∧ keyFits d.loc.key P.par.S.fold.index = true) ∧
    (stateB P 2 (sh2 d) = true ↔
      Facts P d.loc.key 2 d ∧ keyFits d.loc.key P.par.S.fold.index = true) ∧
    (stateB P 3 (sh2 d) = true ↔
      Facts P d.loc.key 3 d ∧ keyFits d.loc.key P.par.S.fold.index = true) ∧
    (stateB P 4 (sh2 d) = true ↔ Facts P d.loc.key 4 d) ∧
    (stateB P 5 (sh2 d) = true ↔ Facts P d.loc.key 5 d) ∧
    (stateB P 6 (sh2 d) = true ↔ Facts P d.loc.key 6 d) ∧
    (stateB P 7 (sh2 d) = true ↔ Facts P d.loc.key 7 d) ∧
    (stateB P 8 (sh2 d) = true ↔ Facts P d.loc.key 8 d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (decide (d.st.codes = P.codes) &&
      (stSh d.st).oracles.length == (bookSh d.book).place.length && keyB (linSh d.loc) _) = true ↔
      (d.st.codes = P.codes ∧ d.st.oracles.size = d.book.place.size ∧ d.loc.key = d.loc.key) ∧ _
    rw [orc_size, place_size, keyB_eq]
    simp
  · show (carriedB P (sh2 d) [] [] && keyB (linSh d.loc) _) = true ↔
      Carried P.par P.codes d.loc.key d [] [] ∧ _
    rw [Bool.and_eq_true, carriedB_iff, keyB_eq]
  · show (carriedB P (sh2 d) [] [] && hasUB P (sh2 d) && keyB (linSh d.loc) _) = true ↔
      (Carried P.par P.codes d.loc.key d [] [] ∧ HasU P.par d) ∧ _
    rw [Bool.and_eq_true, Bool.and_eq_true, carriedB_iff, hasUB_iff, keyB_eq]
  · show (carriedB P (sh2 d) [d.loc.oU.oracle] [] && hasUB P (sh2 d)) = true ↔
      Carried P.par P.codes d.loc.key d [d.loc.oU.oracle] [] ∧ HasU P.par d
    rw [Bool.and_eq_true, carriedB_iff, hasUB_iff]
  · show (carriedB P (sh2 d) [d.loc.oU.oracle] [] && hasUB P (sh2 d)) = true ↔
      Carried P.par P.codes d.loc.key d [d.loc.oU.oracle] [] ∧ HasU P.par d
    rw [Bool.and_eq_true, carriedB_iff, hasUB_iff]
  · show (carriedB P (sh2 d) [d.loc.oU.oracle] [] && hasUB P (sh2 d) && hasOB P (sh2 d)) = true ↔
      Carried P.par P.codes d.loc.key d [d.loc.oU.oracle] [] ∧ HasU P.par d ∧ HasO P.par d
    rw [Bool.and_eq_true, Bool.and_eq_true, carriedB_iff, hasUB_iff, hasOB_iff, and_assoc]
  · show (carriedB P (sh2 d) [d.loc.oU.oracle, d.loc.oSp] [d.loc.oOmega, d.loc.oSp] &&
      hasUB P (sh2 d) && hasOB P (sh2 d)) = true ↔
      Carried P.par P.codes d.loc.key d [d.loc.oU.oracle, d.loc.oSp] [d.loc.oOmega, d.loc.oSp] ∧
        HasU P.par d ∧ HasO P.par d
    rw [Bool.and_eq_true, Bool.and_eq_true, carriedB_iff, hasUB_iff, hasOB_iff, and_assoc]
  · show (carriedB P (sh2 d) [d.loc.oU.oracle, d.loc.oSp] [d.loc.oOmega, d.loc.oSp] &&
      hasUB P (sh2 d) && hasOB P (sh2 d) && d.loc.zFd.length == P.par.S.kRow) = true ↔
      Carried P.par P.codes d.loc.key d [d.loc.oU.oracle, d.loc.oSp] [d.loc.oOmega, d.loc.oSp] ∧
        HasU P.par d ∧ HasO P.par d ∧ d.loc.zFd.length = P.par.S.kRow
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, carriedB_iff, hasUB_iff, hasOB_iff,
      beq_iff_eq, and_assoc, and_assoc]

/-- The test's two halves. -/
theorem factsB_iff (P : P14) (b : Nat) (a : Sh2) :
    factsB P b a = true ↔ stateB P b a = true ∧ (2 ≤ b → kindsB P b a = true) := by
  unfold factsB
  rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨x, y⟩ => ⟨x, fun h => y.resolve_left (by omega)⟩,
    fun ⟨x, y⟩ => ⟨x, (Nat.lt_or_ge b 2).imp id y⟩⟩

end Desc.K14.Shape

#print axioms Desc.K14.Shape.groupB_iff
#print axioms Desc.K14.Shape.msgB_iff
#print axioms Desc.K14.Shape.carriedB_iff
#print axioms Desc.K14.Shape.hasUB_iff
#print axioms Desc.K14.Shape.aloneB_eq
#print axioms Desc.K14.Shape.hasOB_iff
#print axioms Desc.K14.Shape.stateB_iff
#print axioms Desc.K14.Shape.factsB_iff
