-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormBatLaws.lean: THE FORM's HALF AT THE BATCHING: the batching's part in the
kind's block (guardedProximityTestParts.bat, Johnson/Desc/K12/JoinGuarded.lean) RETURNS ok, AND WHAT IT RETURNS IS batT
(Johnson/Prover/Link/FormFirst.lean): from the test on a view's format (roundsFit), one test
on the plan (batCut) and two records of premises on the record in front (TestFront, BatOwes).

Main names.
  batEntry_of, heard_bat   "BAT" is heard.
  layoutOf_own    the description's own layout of a group is the one of
  Johnson/Desc/Means/Layout.lean. combOk_of_order guard (c) from a statement in order.
  bat_yes         the batching's plain text (bat, Johnson/Desc/First/Close/Closing.lean) returns ok.
  bat5_yes        THE STATEMENT.
  group_batT      the frame's own question behind the batching: "the group is the first stage's".
  batCut_of_nums  the plan: at every place the first declared round passes batCut and counts N.rows.

Limits. TestFront and BatOwes are premises. GUARD (g) STANDS WHOLE AMONG THEM, at the record behind.
That the batching returns a row is the library's begin_inOrder (Johnson/Desc/Means/Order.lean). No
value that is sent or drawn is read, but for the equalities of elements that Own.formFits asks at a
written-out variable (its pair is (1, 1)): DenseRow, a premise through TestFront, holds them
(FormRow.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormBat
import Johnson.Prover.Link.FormFoldLaws
import Johnson.Prover.Link.FormFoldPlan
import Johnson.Desc.Own.LayoutAgree
import Johnson.Desc.Own.BatchAgree
import Johnson.Desc.Means.TestsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.First.Close

theorem batEntry_of {e : Fmt.Entry} (h : batEntry e = true) :
    (e.name == "BAT") = true ∧ e.drawNZ = 0 ∧ e.count = 1 ∧ e.msg = 0 ∧ e.roots = 0 ∧
      e.answers = 0 ∧ e.poss = 0 ∧ e.trits = 0 ∧ e.drawE = 1 := by
  unfold batEntry at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨beq_iff_eq.2 h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- **"BAT" is heard.** -/
theorem heard_bat (d : Fmt.DeclaredRound) (r : Fmt.RoundView) (he : batEntry d.entry = true)
    (hf : roundsFit [d] [r] = true) : heard "BAT" 0 d.entry r 0 = .ok ([], drawnOf r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := batEntry_of he
  unfold roundsFit at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, _⟩, _⟩, _⟩, _⟩ := hf
  have hv : r.vals = [] := by
    have e : d.items.filter (· != .root) = [] := by
      show (d.entry.cut).filter (· != .root) = []
      unfold Fmt.Entry.cut
      rw [h4, h5, h6]
      rfl
    rw [e] at f1
    exact List.map_eq_nil_iff.1 f1
  obtain ⟨x, hx⟩ : ∃ x, r.drawn.elems = [x] := List.length_eq_one_iff.1 (f2.trans h9)
  have g3 : r.drawn.poss.length = 0 := f3.trans h7
  have g4 : r.drawn.trits.length = 0 := f4.trans h8
  unfold heard
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, hv, g3, g4, hx]
  simp only [First.Close.need, got, beq_self_eq_true, Bool.and_self, Nat.mul_zero, Nat.add_zero,
    List.length_nil, List.length_cons, List.mapM_nil]
  show (Except.ok ([], E.ofTriple x) : Except String (List E × E)) = _
  unfold drawnOf
  rw [hx]
  rfl

/-- The description's own layout of a group is the one of Johnson/Desc/Means/Layout.lean. -/
theorem layoutOf_own {S : Statement} {g : Nat} {G : Group} (h : S.groups[g]? = some G) :
    Own.layoutOf S G = layoutOf S G :=
  Option.some.inj ((Own.layout_of_group h).symm.trans (layout_eq S g G h))

theorem layoutEqB_self (a : GroupLayout) : layoutEqB a a = true := by
  unfold layoutEqB
  simp

/-- **Guard (c) from a statement in order.** -/
theorem combOk_of_order (t : T12) (G : Group) (hG : t.st.groups[t.g]? = some G)
    (h : InOrder t.st) : combOk t = true := by
  have hE := extends_begun t.st t.g G
  have hG' := begun_group t.st t.g G hG
  have hOk := h.groups t.g G hG
  have hOk' : GroupOk (begun t.st t.g G) { G with inRun := true, rows := #[] } :=
    hOk.extends hE rfl rfl rfl rfl
  have hL' : (begun t.st t.g G).layout t.g = some (layoutOf t.st G) := by
    rw [layout_eq _ t.g _ hG',
      layoutOf_extends (G' := { G with inRun := true, rows := #[] }) hE hOk rfl rfl rfl rfl]
  unfold combOk
  rw [hG, layout_eq t.st t.g G hG]
  show combineAt (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩ = true
  unfold combineAt combineFrameAt combineRowsAt
  rw [hG', hL']
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨groupOkB_of hOk', layoutEqB_self _⟩, ?_⟩
  have hall : ∀ r ∈ (runRows t.st G).toList,
      rowInB (begun t.st t.g G) { G with inRun := true, rows := #[] } r = true :=
    fun r hr => rowInB_of (RowIn.extends (G := G) hE (fun _ c => c) (h.runRows t.g G hG r hr))
  rw [List.filter_eq_self.2 hall, Array.length_toList]

/-- **The batching's plain text returns ok.** -/
theorem bat_yes (S : Statement) (g : Nat) (G : Group) (d : Fmt.DeclaredRound) (r : Fmt.RoundView)
    (row : GroupRow) (hG : S.groups[g]? = some G) (hOk : GroupOk S G) (hr : G.inRun = false)
    (hm : 0 < G.members.size) (he : batEntry d.entry = true) (hf : roundsFit [d] [r] = true)
    (hn : d.entry.rows = (runRows S G).size)
    (hc : Bat.combine (begun S g G) g ⟨layoutOf S G, runRows S G⟩ (drawnOf r) = some row) :
    bat S g d.entry r = .ok (row, layoutOf S G, begun S g G) := by
  have hb : Ground.ok (Ground.beginRunL S g) = true := by
    unfold Ground.ok Ground.beginRunL
    rw [hG]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Option.isSome_some,
      Ground.has, Option.map_some, Option.getD_some, hr, Bool.not_false, true_and,
      Bool.not_eq_true', Array.all_eq_true_iff_forall_mem, decide_eq_true_eq]
    exact ⟨by
      rw [Array.isEmpty_eq_false_iff]
      exact fun e => by rw [e] at hm; exact absurd hm (by simp),
      fun o ho => hOk.there o (Array.mem_toList_iff.2 ho)⟩
  have hp : Ground.beginRunP (onSt S) g =
      some (⟨layoutOf S G, runRows S G⟩, { onSt S with st := begun S g G }) := by
    have hb' : Ground.ok (Ground.beginRunL (onSt S).st g) = true := hb
    unfold Ground.beginRunP
    rw [if_pos hb']
    show (do
      let G ← S.groups[g]?
      some (⟨Own.layoutOf S G, runRows S G⟩, { onSt S with st := begun S g G }) :
        Option (RunInput × _root_.Desc.Plain.DState Unit)) = _
    rw [hG]
    show some ((⟨Own.layoutOf S G, runRows S G⟩ : RunInput), { onSt S with st := begun S g G }) = _
    rw [layoutOf_own hG]
  unfold bat
  rw [named_ok hb, hp, heard_bat d r he hf]
  show (do
    First.Close.need "K10.rows" (d.entry.rows == (runRows S G).size)
    let row ← got "K10.combine"
      (Own.batch (begun S g G) g ⟨layoutOf S G, runRows S G⟩ (drawnOf r))
    pure (row, layoutOf S G, begun S g G) :
      Except String (GroupRow × GroupLayout × Statement)) = _
  rw [hn, ← Own.batch_agrees, hc]
  simp only [First.Close.need, beq_self_eq_true, if_true]
  rfl

/-! ## The part in the kind's block -/

/-- At a statement in order the batching returns a row: begin_inOrder, read at the ring
with one element: of its conclusion the row's being there alone is taken. -/
theorem combine_some {S : Statement} (h : InOrder S) (g : Nat) (G : Group) (x : E)
    (hG : S.groups[g]? = some G) :
    ∃ row, Bat.combine (begun S g G) g ⟨layoutOf S G, runRows S G⟩ x = some row := by
  have ρ : Model.Reading PUnit :=
    ⟨fun _ => PUnit.unit, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨_, row, hr, _⟩ := begin_inOrder ρ h g G x hG
  exact ⟨row, hr⟩

section Part
variable {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {G : Group} {i n : Nat × Nat} {id : Nat}

/-- **The part of Johnson/Desc/K12/Join.lean says yes, and the record behind is batT.** -/
theorem batJ_yes (H : TestFront p cur nxt t G i n id) (d : Fmt.DeclaredRound)
    (B : BatOwes p [d] t G) (hc : batCut [d] = true) (r : Fmt.RoundView)
    (hf : roundsFit [d] [r] = true) (row : GroupRow)
    (hr : Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩ (drawnOf r) =
      some row) :
    (batJ p [d]).decide t [r] [] = .ok (batT t G row) := by
  have he : batEntry d.entry = true := by
    unfold batCut at hc
    simp only [Bool.and_eq_true] at hc
    exact hc.1.1
  obtain ⟨j, hj, _⟩ := H.main
  have hb := bat_yes t.st t.g G d r row H.group (H.order.groups t.g G H.group) B.idle
    (Nat.lt_of_le_of_lt (Nat.zero_le j) hj) he hf (B.count d List.mem_cons_self) hr
  obtain ⟨rest, hi⟩ : ∃ rest, p.idx = i :: rest := by
    have h0 := H.idx0
    cases hp : p.idx with
    | nil => rw [hp] at h0; cases h0
    | cons a l =>
      rw [hp] at h0
      cases h0
      exact ⟨l, rfl⟩
  have hE : H2K.batE t.g (lay p [d] none t [r] []) =
      .ok ((row, layoutOf t.st G),
        { lay p [d] none t [r] [] with
          d := { (lay p [d] none t [r] []).d with st := begun t.st t.g G }
          entries := [], rounds := [], last := some d.entry, asked := true }) := by
    unfold H2K.batE
    show (do
      H2K.need "bat (o1): a count of rows is owed" (lay p [d] none t [r] []).owed.isNone
      let x ← (First.Close.bat t.st t.g d.entry r).mapError ("bat: " ++ ·)
      pure ((x.1, x.2.1),
        { lay p [d] none t [r] [] with
          d := { (lay p [d] none t [r] []).d with st := x.2.2 }
          entries := [], rounds := [], last := some d.entry, asked := true }) :
        Except String ((GroupRow × GroupLayout) × H2K.PS)) = _
    rw [hb]
    rfl
  have hx : (((begun t.st t.g G).groups[t.g]?).any fun G => G.code == i.1 && G.maskCode == i.2) =
      true := by
    rw [begun_group t.st t.g G H.group]
    show (G.code == i.1 && G.maskCode == i.2) = true
    rw [H.code, H.maskCode]
    simp
  simp only [batJ, B.pass, hi]
  rw [B.codes, hE]
  show (do
    VerifiableInference.Desc.need "(w): the record's codes are not the stages'" true
    VerifiableInference.Desc.need "(x): the group's two codes are not the first stage's"
      (((begun t.st t.g G).groups[t.g]?).any fun G => G.code == i.1 && G.maskCode == i.2)
    back t
      { lay p [d] none t [r] [] with
        d := { (lay p [d] none t [r] []).d with st := begun t.st t.g G }
        entries := [], rounds := [], last := some d.entry, asked := true }
      (.claim row (layoutOf t.st G)) (if p.early then t.mask else none) :
      Except String T12) = _
  rw [hx, B.early]
  unfold back
  show (do
    VerifiableInference.Desc.need "(w): the record's codes are not the stages'" true
    VerifiableInference.Desc.need "(x): the group's two codes are not the first stage's" true
    VerifiableInference.Desc.need "(v): a round, an entry or a column is left over"
      (([] : List Fmt.RoundView).isEmpty && ([] : List Fmt.Entry).isEmpty && (keyed p [d] []).isEmpty)
    pure { t with
      st := begun t.st t.g G, book := t.book, roots := t.roots
      pass := .claim row (layoutOf t.st G), mask := t.mask } : Except String T12) = _
  rw [keyed_nil]
  rfl

/-- **THE BATCHING's PART OF guardedProximityTestParts SAYS YES, AND THE RECORD BEHIND IS batT**, at the row that
Bat.combine returns. rs: its round as the view has it. -/
theorem bat5_yes (H : TestFront p cur nxt t G i n id) (cut : List Fmt.DeclaredRound)
    (B : BatOwes p cut t G) (hc : batCut cut = true) (rs : List Fmt.RoundView)
    (hf : roundsFit cut rs = true) :
    ∃ row, Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rs.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row ∧
      (guardedProximityTestParts.bat p cut).decide t (rs.map noDigest) [] = .ok (batT t G row) := by
  obtain ⟨d, rfl⟩ : ∃ d, cut = [d] := by
    cases cut with
    | nil => cases hc
    | cons d l =>
      cases l with
      | nil => exact ⟨d, rfl⟩
      | cons _ _ => cases hc
  obtain ⟨r, rfl⟩ : ∃ r, rs = [r] :=
    List.length_eq_one_iff.1 (H2K.Sw.roundsFit_length _ _ hf).symm
  have hf' : roundsFit [d] [noDigest r] = true :=
    (H2K.Onto.roundsFit_noDigest [d] [r]).trans hf
  obtain ⟨row, hr⟩ := combine_some H.order t.g G (drawnOf (noDigest r)) H.group
  refine ⟨row, hr, ?_⟩
  have hk : row.kept = #[] := H2K.Pin.combine_noKept0 _ _ _ _ _ hr fun j => H.noKept j
  have hnk : noKept (batT t G row) = true := by
    unfold noKept
    show (row.kept.isEmpty &&
      (List.range G.members.size).all fun j => !(G.kept.getD j false)) = true
    rw [hk, Bool.and_eq_true, List.all_eq_true]
    exact ⟨rfl, fun j _ => by rw [H.noKept j]; rfl⟩
  show (do
    VerifiableInference.Desc.need "(z): a drawn position is out of its round's range"
      (inRange [d] [noDigest r])
    VerifiableInference.Desc.need
      "(c): the group is not in order, or a batched row lies outside its members' tables"
      (combOk t)
    let t' ← (batJ p [d]).decide t [noDigest r] []
    VerifiableInference.Desc.need
      "(k): behind the batching the claim has a kept form, or the group a kept member" (noKept t')
    VerifiableInference.Desc.need
      "(g): the group's trees in the record are not those that the place's numbers declare"
      (H2K.First.gpOk p t' && H2K.First.labelsOk p t')
    pure t' : Except String T12) = _
  rw [inRange_fold hf', combOk_of_order t G H.group H.order,
    batJ_yes H d B hc (noDigest r) hf' row hr]
  show (do
    VerifiableInference.Desc.need "(z): a drawn position is out of its round's range" true
    VerifiableInference.Desc.need
      "(c): the group is not in order, or a batched row lies outside its members' tables" true
    VerifiableInference.Desc.need
      "(k): behind the batching the claim has a kept form, or the group a kept member"
      (noKept (batT t G row))
    VerifiableInference.Desc.need
      "(g): the group's trees in the record are not those that the place's numbers declare"
      (H2K.First.gpOk p (batT t G row) && H2K.First.labelsOk p (batT t G row))
    pure (batT t G row) : Except String T12) = _
  rw [hnk, (B.gp row hk).1, (B.gp row hk).2]
  rfl

/-- **The frame's own question behind the batching**: the group is the first stage's. -/
theorem group_batT (H : TestFront p cur nxt t G i n id) (row : GroupRow) :
    (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true := by
  have hE := extends_begun t.st t.g G
  have e : guardedProximityTestParts.group (batT t G row) =
      some (⟨cur.C.a, cur.C.l, cur.C.r⟩, ⟨cur.Z.a, cur.Z.l, cur.Z.r⟩, cur.k, cur.h) := by
    simp only [guardedProximityTestParts, batT, begun_group t.st t.g G H.group, hE.codes, H.code, H.maskCode,
      H.base, H.maskC, H.layK, H.layH]
  rw [e]
  simp [firstFits]

end Part

/-- **The plan**: at every place the first declared round passes batCut and counts N.rows rows. -/
theorem batCut_of_nums (N : H2U.TestNums) (d0 : Fmt.DeclaredRound) (ds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some (d0 :: ds)) : batCut [d0] = true ∧ d0.entry.rows = N.rows := by
  unfold H2U.roundsOfNums at h
  split at h
  · simp only [H2U.layOpens] at h
    have e1 : (Fmt.M1.rBat.opens.isEmpty) = true := rfl
    have e2 : (Fmt.M1.rBat.entry.name == "FOLD epsilon") = false := by decide
    simp only [e1, e2, Bool.and_false, Bool.false_eq_true, if_false, if_true] at h
    obtain ⟨a, _, ha⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, _⟩ := List.cons.inj ha
    exact ⟨by simp [batCut, batEntry, Fmt.M1.rBat], rfl⟩
  · cases h

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.batEntry_of
#print axioms Johnson.Prover.Link.heard_bat
#print axioms Johnson.Prover.Link.layoutOf_own
#print axioms Johnson.Prover.Link.layoutEqB_self
#print axioms Johnson.Prover.Link.combOk_of_order
#print axioms Johnson.Prover.Link.bat_yes
#print axioms Johnson.Prover.Link.combine_some
#print axioms Johnson.Prover.Link.batJ_yes
#print axioms Johnson.Prover.Link.bat5_yes
#print axioms Johnson.Prover.Link.group_batT
#print axioms Johnson.Prover.Link.batCut_of_nums
