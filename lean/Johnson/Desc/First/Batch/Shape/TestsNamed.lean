-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/TestsNamed.lean: THE LINK's TESTS BEHIND THE ADDING (the text that
ProofFile.k9Tests lays, Johnson/Desc/ProofFile/Lot/K9.lean: the segment's part is there; K9.free-slot; the
sort's own counts), CUT INTO ONE NAMED TEST ON THE SHAPE OF THE CHAIN's STATE AND ONE NAMED TEST ON
VALUES. General laws; nothing is evaluated.

  `testsText w`: the text, at the numbers w that K9.testsWhere gives of the public record.
    `k9Tests_is`: ProofFile.k9Tests Z l is that text at testsWhere Z.p.X l 0.
  **`gTw w`**: THE TEST ON THE SHAPE: a ledger and the smallness test's structure are there · as
    many claims were added as the plan counts · at the head's link: the matrix was drawn once, and
    the lookup has run · the list of tables is closed, and table by table it has the shape of the
    list that was closed.
  **`vTw w`**: THE TEST ON VALUES: K9.free-slot (of the filled slots just the merge's has the
    coefficient 0) · the tables' weights are those of the list that was closed, entry by entry.
  **`tests_iff`**: THE CUT, BOTH WAYS: the text accepts just where gTw accepts at the state's shape
    and vTw at the state. `tests_named`: from the two to the text. `tests_back`: from the text to
    the two (it has no caller).
  `closed_iff`, `tablesHeld_iff`, `counts_iff`: the parts of the cut.

Limits. TWO NAMES HERE HIDE OLDER ONES OF OTHER MEANINGS: testsText is the lot's text (ProofFile.k9Tests),
not K9.testsText (Johnson/Desc/First/Batch/Tests.lean), which also runs the weights and returns a
ledger; freeB is K9.free-slot at a state, not First.Shape.freeB ("n slots are there and free", on a
ledger's shape). vTw means what is said above only beside gTw (see phiSame). In gTw the two tests
"is there" are idle: countsSh fails where either is missing. Of w's third part filled alone is read.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Lot.K9
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.First.Batch.Shape.DoorCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape

/-- The text. -/
def testsText (w : SegSort × Nat × TWhere) (s : S) : Except String Unit := do
  let part ← there "K9.in-a-segment" (tAtS.get? s)
  freeSlot w.2.2.filled part.merge part.F
  countsHold (countsAt w.1 w.2.1) s

theorem k9Tests_is (Z : ProofFile.Pub) (l : Nat) :
    ProofFile.k9Tests Z l = (testsWhere Z.p.X l 0).map testsText := rfl

/-! ## 1 The list of tables -/

/-- The tables' weights are those of the list that was closed, at the places below the list's own
size: that the two lists are as long is tablesSh's, on the other side of the cut. -/
def phiSame (s : S) : Bool :=
  match s.tl?, s.funs? with
  | some tl, some funs =>
    (List.range funs.size).all fun i => (funs.getD i {}).phi == (tl.funs.getD i {}).phi
  | _, _ => false

/-- The list is closed and has the closed list's shape. -/
def tablesSh (a : ChainSh) : Bool :=
  match a.tl, a.tables with
  | some t, some fs => t.funClosed && fs == t.funs
  | _, _ => false

theorem getD_sh (a : Array HFun) (i : Nat) (h : i < a.size) :
    (a.toList.map funSh)[i]? = some (funSh (a.getD i {})) := by
  rw [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem h]
  simp [Array.getD, h]

theorem closed_iff (tl : HTailF2) (funs : Array HFun) :
    closedList tl funs = true ↔
      (tl.funClosed = true ∧ funs.toList.map funSh = tl.funs.toList.map funSh) ∧
        ((List.range funs.size).all fun i =>
          (funs.getD i {}).phi == (tl.funs.getD i {}).phi) = true := by
  unfold closedList
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, fun i hi => ?_⟩
    · refine List.ext_getElem? fun i => ?_
      by_cases hi : i < funs.size
      · rw [getD_sh funs i hi, getD_sh tl.funs i (h2 ▸ hi)]
        have := h3 i hi
        unfold sameTable at this
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := this
        unfold funSh
        rw [a1, a2, a3, a4, a5]
      · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi),
          List.getElem?_eq_none (by simpa [← h2] using Nat.le_of_not_lt hi)]
    · have := h3 i hi
      unfold sameTable at this
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact this.2
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hs : funs.size = tl.funs.size := by
      have := congrArg List.length h2
      simpa using this
    refine ⟨⟨h1, hs⟩, fun i hi => ?_⟩
    have e := congrArg (fun l => l[i]?) h2
    simp only at e
    rw [getD_sh funs i hi, getD_sh tl.funs i (hs ▸ hi)] at e
    have e' := Option.some.inj e
    unfold funSh at e'
    injection e' with a1 a2 _ a3 a4
    unfold sameTable
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, h3 i hi⟩

theorem tablesHeld_iff (s : S) :
    tablesHeld s = true ↔ tablesSh (chainSh s) = true ∧ phiSame s = true := by
  unfold tablesHeld phiSame tablesSh
  have e1 : (chainSh s).tl = s.tl?.map tailSh := rfl
  have e2 : (chainSh s).tables = s.funs?.map fun a => a.toList.map funSh := rfl
  rw [e1, e2]
  cases s.tl? with
  | none => simp
  | some tl =>
    cases s.funs? with
    | none => simp
    | some funs =>
      show closedList tl funs = true ↔
        (tl.funClosed && (funs.toList.map funSh == tl.funs.toList.map funSh)) = true ∧ _
      rw [closed_iff, Bool.and_eq_true, beq_iff_eq]

/-! ## 2 The two named tests -/

/-- The sort's own counts, on the shape; the tables' weights are left to vTw. -/
def countsSh (k : SegSort) (nLin : Nat) (a : ChainSh) : Bool :=
  (a.led.map (·.claims == nLin)).getD false &&
    (match k with
     | .head =>
       (a.tl.map (·.foldDrawn == 1)).getD false && (a.tl.map (·.heard.isSome)).getD false
     | _ => true) && tablesSh a

/-- **THE TEST ON THE SHAPE.** -/
def gTw (w : SegSort × Nat × TWhere) (a : ChainSh) : Bool :=
  a.led.isSome && a.tl.isSome && countsSh w.1 w.2.1 a

/-- K9.free-slot, as a Bool at the state. -/
def freeB (n : Nat) (s : S) : Bool :=
  match s.fork? with
  | some F => (List.range n).all fun j => isZeroE (F.LS.getD j zeroE) == (mergeOf s == some j)
  | none => false

/-- **THE TEST ON VALUES.** -/
def vTw (w : SegSort × Nat × TWhere) (s : S) : Bool := freeB w.2.2.filled s && phiSame s

theorem counts_cons (c : String × (S → Bool)) (l : List (String × (S → Bool))) (s : S) :
    countsHold (c :: l) s = .ok () ↔ c.2 s = true ∧ countsHold l s = .ok () := by
  show (need c.1 (c.2 s) >>= fun _ => countsHold l s) = .ok () ↔ _
  rw [ans_bind]
  simp only [need_ok, exists_const]

theorem counts_nil (s : S) : countsHold ([] : List (String × (S → Bool))) s = .ok () := rfl

/-- The sort's own counts at a state whose ledger and structure are there. -/
theorem counts_iff (k : SegSort) (nLin : Nat) (s : S) (F : Fork) (tl : HTailF2)
    (hF : s.fork? = some F) (hl : s.tl? = some tl) :
    countsHold (countsAt k nLin) s = .ok () ↔
      (F.nClaim == nLin) = true ∧
        (match k with
         | .head => (tl.foldDrawn == 1) = true ∧ tl.heard.isSome = true
         | _ => True) ∧ tablesHeld s = true := by
  have c1 : claimsCounted nLin s = (F.nClaim == nLin) := by
    unfold claimsCounted
    rw [hF]
    rfl
  cases k with
  | layers =>
    show countsHold [("K9.claims-counted", claimsCounted nLin), ("K9.tables-held", tablesHeld)] s =
      .ok () ↔ _
    rw [counts_cons, counts_cons]
    dsimp only
    rw [c1]
    exact ⟨fun h => ⟨h.1, trivial, h.2.1⟩, fun h => ⟨h.1, h.2.2, counts_nil s⟩⟩
  | attention =>
    show countsHold [("K9.claims-counted", claimsCounted nLin), ("K9.tables-held", tablesHeld)] s =
      .ok () ↔ _
    rw [counts_cons, counts_cons]
    dsimp only
    rw [c1]
    exact ⟨fun h => ⟨h.1, trivial, h.2.1⟩, fun h => ⟨h.1, h.2.2, counts_nil s⟩⟩
  | head =>
    show countsHold [("K9.claims-counted", claimsCounted nLin),
      ("K9.matrix-drawn-once", fun s => (s.tl?.map (·.foldDrawn == 1)).getD false),
      ("K9.two-lookups", fun s => (s.tl?.map (1 + ·.groupsRun == 2)).getD false),
      ("K9.tables-held", tablesHeld)] s = .ok () ↔ _
    rw [counts_cons, counts_cons, counts_cons, counts_cons]
    dsimp only
    rw [c1]
    simp only [hl, Option.map_some, Option.getD_some]
    have e : (1 + tl.groupsRun == 2) = true ↔ tl.heard.isSome = true := by
      unfold HTailF2.groupsRun
      cases tl.heard.isSome <;> simp
    rw [e]
    exact ⟨fun h => ⟨h.1, ⟨h.2.1, h.2.2.1⟩, h.2.2.2.1⟩,
      fun h => ⟨h.1, h.2.1.1, h.2.1.2, h.2.2, counts_nil s⟩⟩

/-- **THE CUT, BOTH WAYS.** -/
theorem tests_iff (w : SegSort × Nat × TWhere) (s : S) :
    testsText w s = .ok () ↔ gTw w (chainSh s) = true ∧ vTw w s = true := by
  obtain ⟨k, nLin, p⟩ := w
  unfold testsText gTw vTw countsSh freeB
  have e1 : (chainSh s).tl = s.tl?.map tailSh := rfl
  have e3 : (chainSh s).led = s.fork?.map ledSh := rfl
  have hT := tablesHeld_iff s
  rw [e1, e3]
  cases hF : s.fork? with
  | none =>
    have : tAtS.get? s = none := by
      show (s.fork?.bind fun F => s.tl?.bind fun tl => _) = none
      rw [hF]
      rfl
    rw [this]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h.1)⟩
  | some F =>
    cases hl : s.tl? with
    | none =>
      have : tAtS.get? s = none := by
        show (s.fork?.bind fun F => s.tl?.bind fun tl => _) = none
        rw [hF, hl]
        rfl
      rw [this]
      exact ⟨(fun h => nomatch h), (fun h => nomatch h.1)⟩
    | some tl =>
      have : tAtS.get? s = some { merge := mergeOf s, tl := tl, F := F } := by
        show (s.fork?.bind fun F => s.tl?.bind fun tl => _) = _
        rw [hF, hl]
        rfl
      rw [this]
      show (freeSlot p.filled (mergeOf s) F >>= fun _ => countsHold (countsAt k nLin) s) =
        .ok () ↔ _
      rw [ans_bind]
      unfold freeSlot
      simp only [need_ok, exists_const]
      rw [counts_iff k nLin s F tl hF hl, hT]
      cases k <;>
        simp only [Option.map_some, Option.getD_some, Option.isSome_some, Bool.and_eq_true,
          Bool.true_and, Bool.and_true, true_and] <;>
        constructor <;> intro h
      · exact ⟨⟨h.2.1, h.2.2.1⟩, h.1, h.2.2.2⟩
      · exact ⟨h.2.1, h.1.1, h.1.2, h.2.2⟩
      · exact ⟨⟨h.2.1, h.2.2.1⟩, h.1, h.2.2.2⟩
      · exact ⟨h.2.1, h.1.1, h.1.2, h.2.2⟩
      · refine ⟨⟨⟨h.2.1, h.2.2.1.1, ?_⟩, h.2.2.2.1⟩, h.1, h.2.2.2.2⟩
        show (tl.heard.map heardAll).isSome = true
        rw [Option.isSome_map]
        exact h.2.2.1.2
      · refine ⟨h.2.1, h.1.1.1, ⟨h.1.1.2.1, ?_⟩, h.1.2, h.2.2⟩
        have := h.1.1.2.2
        have e : (tl.heard.map heardAll).isSome = true := this
        rw [Option.isSome_map] at e
        exact e

theorem tests_named (w : SegSort × Nat × TWhere) (s : S) (hg : gTw w (chainSh s) = true)
    (hv : vTw w s = true) : testsText w s = .ok () := (tests_iff w s).2 ⟨hg, hv⟩

theorem tests_back (w : SegSort × Nat × TWhere) (s : S) (h : testsText w s = .ok ()) :
    gTw w (chainSh s) = true ∧ vTw w s = true := (tests_iff w s).1 h

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.closed_iff
#print axioms VerifiableInference.Desc.K9.Shape.tablesHeld_iff
#print axioms VerifiableInference.Desc.K9.Shape.tests_iff
#print axioms VerifiableInference.Desc.K9.Shape.testsText
#print axioms VerifiableInference.Desc.K9.Shape.k9Tests_is
#print axioms VerifiableInference.Desc.K9.Shape.phiSame
#print axioms VerifiableInference.Desc.K9.Shape.tablesSh
#print axioms VerifiableInference.Desc.K9.Shape.getD_sh
#print axioms VerifiableInference.Desc.K9.Shape.countsSh
#print axioms VerifiableInference.Desc.K9.Shape.gTw
#print axioms VerifiableInference.Desc.K9.Shape.freeB
#print axioms VerifiableInference.Desc.K9.Shape.vTw
#print axioms VerifiableInference.Desc.K9.Shape.counts_cons
#print axioms VerifiableInference.Desc.K9.Shape.counts_nil
#print axioms VerifiableInference.Desc.K9.Shape.counts_iff
#print axioms VerifiableInference.Desc.K9.Shape.tests_named
#print axioms VerifiableInference.Desc.K9.Shape.tests_back
