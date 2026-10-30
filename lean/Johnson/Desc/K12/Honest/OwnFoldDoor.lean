-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/OwnFoldDoor.lean: the way into a proximity test whose first fold sends its
own fresh mask table: the front, the batching, the frame's question and the first fold of
`guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean) accept in a row, and the structures between are written
out.

The form for a mask that has come earlier is `door_yes` (Johnson/Prover/Link/FormDoorLaws.lean).
Its laws on the batching (`batJ_yes`, `bat5_yes`, `group_batT`,
Johnson/Prover/Link/FormBatLaws.lean) take `TestFront`, which asks that the mask has come; their
proofs read neither of its two clauses on the mask. They are stated here from `TestFrontOwn`
(Johnson/Desc/K12/Honest/OwnFoldFirst.lean), and proved step by step as there. The law on the front
(`front5_yes`) is general in the field `mask` and is called as it is.

Main names.
  `batJ_own`, `bat5_yes_own`   the batching's part accepts, and returns `batT`.
  `group_batT_own`   the frame's own question behind the batching: the group is the first stage's.
  `inStep_of_front`   the clause of `TestFrontOwn` on statement and book is one of the clauses that
      the front's part asks: it follows from `FrontOwes`.
  **`door_yes_own`**   the statement: from `TestFrontOwn`, `BatOwes`, `FrontOwes`, the plan's two
      tests (`batCut`, `foldCutOwn`) and the test on the view's format (`roundsFit`). The row is
      the one that `Bat.combine` returns.

Limits. The three structures of premises are premises: they are shown here of no
structure.
`BatOwes.gp` and `FrontOwes.front` take over whole tests of the verifier's (on the group's
trees; on the schedule as it lies). In this case these tests are handed an empty field `mask`; what
they then ask is not unfolded here. That the fold's own tree fits what the plan declares to be
opened sits inside `BatOwes.gp`: the test on the group's trees enters the table for itself and holds
the new tree against the declared openings; OwnFoldGuard.lean, which is not in the library yet,
derives that clause from a test on the members alone (`gp_of_members`). `TestFrontOwn.order` speaks
of every group of the statement, also of those that an earlier test of the same chain has left. The
statement ends behind the first fold: the switch, the later stages and the base case are not here,
so nothing is said of the block's own decision. Nothing on completeness, on soundness or on what is
hidden.
-/
import Johnson.Desc.K12.Honest.OwnFoldFirst
import Johnson.Desc.K12.Honest.OwnFoldLaws
import Johnson.Prover.Link.FormDoorLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.First.Close
open Johnson.Prover.Link

section Door
variable {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {G : Group} {i n : Nat × Nat}

/-- **The batching's part of Join.lean accepts, and the structure behind is `batT`.** -/
theorem batJ_own (H : TestFrontOwn p cur nxt t G i n) (d : Fmt.DeclaredRound)
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

/-- **The batching's part of `guardedProximityTestParts` accepts, and the structure behind is `batT`**, at the row
that `Bat.combine` returns. rs: its round as the view has it. -/
theorem bat5_yes_own (H : TestFrontOwn p cur nxt t G i n) (cut : List Fmt.DeclaredRound)
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
    batJ_own H d B hc (noDigest r) hf' row hr]
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
theorem group_batT_own (H : TestFrontOwn p cur nxt t G i n) (row : GroupRow) :
    (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true := by
  have hE := extends_begun t.st t.g G
  have e : guardedProximityTestParts.group (batT t G row) =
      some (⟨cur.C.a, cur.C.l, cur.C.r⟩, ⟨cur.Z.a, cur.Z.l, cur.Z.r⟩, cur.k, cur.h) := by
    simp only [guardedProximityTestParts, batT, begun_group t.st t.g G H.group, hE.codes, H.code, H.maskCode,
      H.base, H.maskC, H.layK, H.layH]
  rw [e]
  simp [firstFits]

/-- "Statement and book count the same number of oracle messages" is one of the front's clauses. -/
theorem inStep_of_front (F : FrontOwes p t G) : t.st.oracles.size = t.book.place.size := by
  have h := F.front ("front: statement and book are in step",
    t.st.oracles.size == t.book.place.size) (by simp [frontL])
  exact beq_iff_eq.1 h

/-- **The way in**: the front, the batching, the frame's question and the first fold, which sends
its own fresh table, accept in a row, and the structures between are written out. -/
theorem door_yes_own (H : TestFrontOwn p cur nxt t G i n) (cutB cutF : List Fmt.DeclaredRound)
    (B : BatOwes p cutB t G) (F : FrontOwes p t G) (hB : batCut cutB = true)
    (hF : foldCutOwn cur.k cutF = true) (rsB rsF : List Fmt.RoundView) (fB : roundsFit cutB rsB = true)
    (fF : roundsFit cutF rsF = true) :
    ∃ row,
      Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row ∧
      (guardedProximityTestParts.front p).decide t [] [] = .ok t ∧
      (guardedProximityTestParts.bat p cutB).decide t (rsB.map noDigest) [] = .ok (batT t G row) ∧
      (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true ∧
      (guardedProximityTestParts.fold p 0 cur cutF).decide (batT t G row) (rsF.map noDigest) [] =
        .ok (foldTOwn p (batT t G row) row (layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ n
          (rsF.map noDigest)) := by
  obtain ⟨row, hr, hb⟩ := bat5_yes_own H cutB B hB rsB fB
  exact ⟨row, hr, front5_yes B.pass H.group F, hb, group_batT_own H row,
    fold5_yes_own (foldFrontOwn_first H _ row hr) hF rsF fF⟩

end Door

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.batJ_own
#print axioms ProofFile.Honest.K12.bat5_yes_own
#print axioms ProofFile.Honest.K12.group_batT_own
#print axioms ProofFile.Honest.K12.inStep_of_front
#print axioms ProofFile.Honest.K12.door_yes_own
