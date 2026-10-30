-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/CondReal.lean: the two equations that Johnson/Desc/K1/Law/CondRow.lean leaves as
premises on a place ("its
codes and its messages are the record's"), by Lean's kernel, at fourteen places of a proof file: the
two sendings of the shared chain as the kind K14 itself hands them to the kind K1, the eleven code
switches of the three proximity tests of the shared and the second chain, and W's sending: at typed
sizes of the test on the table OVER THE PROOF FILE's OWN LIST OF CODES.

Johnson/Prices/SharedExists.lean has typed full-size sizes (`sharedSized`) with no codes before, so
its codes bear other numbers than a proof file's, in which the links' six codes stand before. Here
`realSized` is the same call of `linSizedWith` behind the first six main codes and the first six
mask
codes of the written list `codesFull2` (Johnson/G/PackLit.lean). `real_test`: it returns the written
list whole; its sizes meet `AtRecord`; the planner's `sharedPlan` and `secondPlan` at them return
plans that pass, whose entries are, one by one, those of the written lists of a proof file's second
and third chain; and what the description's own texts announce at these sizes is, sending by
sending, what the records of Johnson/Desc/K1/Law/CondLit.lean hold.
  codesBefore, realSized
  switchSent: what a code switch into a stage announces where masks are sent ahead: the text of a
      switch's place · switchesOf: of all switches of a test
  sharedSent: the shared chain's nine sendings: K14's `withU`, `withOmega`, the switches of the
      tests on
      G_u and on G_omega
  sentOf: the messages of a chain's records
  real_test: one evaluation in Lean's kernel (decide +kernel) · real_members: what it gives
  PlaceOk f c k P: the place P has the codes and messages of record number k of chain c of file f,
      and so the kind's one Boolean holds at that record's radii
  placeOk_of: from "the place's codes are the file's, and its messages are number k of a list that
      is the chain's records' messages"
  k01_real: there are sizes x with all of the above such that: for every K14's parameters Q with
      the written codes and x's shape, K14's two places for K1 are PlaceOk at (2, 1, 0) and
      (2, 1, 1); every place with the written codes that announces the j-th switch of the test on
      G_u | G_omega | a request's own group is PlaceOk at (2, 1, 2 + j) | (2, 1, 6 + j) | (2, 2, j);
      every place with the written codes that announces W's message is PlaceOk at (2, 0, 81)

By decide +kernel, that is, evaluated by Lean's kernel at the written numbers, and turning with
them: `real_test`, `codes_two`.

What is not claimed. That `linSized` returns these sizes behind these codes, or that the planner's
sizes of a proof at the release's files are these (Desc.K14.p14Of reads them off
made.sized.proof): no theorem. The 76 sendings of the links,
the five switches of the last group's test; the key file; the entry file. What the heads of
Johnson/Desc/K1/Law/CondRow.lean, CondLit.lean and Johnson/Prices/SharedExists.lean do not claim.
Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.CondWritten
import Johnson.Prices.SharedExists
import Johnson.Desc.K14.Blocks
import Johnson.Top.H0.Tw.L9.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Params.Prices Johnson.G

/-- The codes that stand before the test on the table's in a proof file: the links' and those of the
last group's test. -/
def codesBefore : Codes := ⟨codesFull2.base.extract 0 6, codesFull2.mask.extract 0 6⟩

/-- The sizes at the typed lines, groups and stages, behind these codes. -/
def realSized : Option (LinSized × Codes) :=
  linSizedWith recordSet (linLines recordLines 3076096 1 false) recordTable codesBefore
    (⟨⟨⟨24, 4194304, 101, true⟩, ⟨13, 64, 152, true⟩, 7, 0, 1, .johnson, 182⟩, 101, true⟩,
      ⟨⟨⟨22, 262144, 3571, true⟩, ⟨13, 64, 152, true⟩, 4, 0, 1, .johnson, 159⟩, 51, true⟩,
      ⟨⟨⟨22, 262144, 3571, true⟩, ⟨13, 256, 55, true⟩, 5, 1, 1, .johnson, 159⟩, 55, true⟩)
    sharedFolded sharedOmega sharedOwn

/-- What a code switch into the stage n announces, where masks are sent ahead. -/
def switchSent (answers : Nat) (n : IoppStage) (last : Bool) : Array OracleNotice :=
  Tw.L9.switchNotices (switchTargetStage n.code n.maskCode n.k n.h answers)
    (if last then #[baseMaskNotice n.code n.maskCode 1 0]
     else #[foldMaskNotice (ioppFoldShape n {})])

/-- All switches of a test, in order. -/
def switchesOf (answers : Nat) : List IoppStage → List (List OracleNotice)
  | _ :: n :: rest =>
    (switchSent answers n rest.isEmpty).toList :: switchesOf answers (n :: rest)
  | _ => []

/-- The shared chain's sendings, in order. -/
def sharedSent (S : LinShape) : Option (List (List OracleNotice)) :=
  (_root_.Desc.K14.withU S).map fun u =>
    u.toList :: (_root_.Desc.K14.withOmega S).toList ::
      (switchesOf 1 S.testU ++ switchesOf 1 S.testOmega)

/-- The messages of a chain's records. -/
def sentOf (f c : Nat) : List (List OracleNotice) :=
  (litAt sendsFullLit packFullLit f c).map (·.2.sent)

/-- **The typed sizes behind the proof file's own codes.** By evaluation in Lean's kernel. -/
theorem real_test : (realSized.any fun p => decide (p.2 = codesFull2) && atRecordB p.1 &&
    decide (sharedSent p.1.shape = some (sentOf 2 1)) &&
    decide (switchesOf 1 p.1.shape.testOwn = sentOf 2 2) &&
    decide ((linMessageW p.1.shape).map (·.toList) = (sentOf 2 0)[81]?) &&
    decide (recordSet.workOf .sample .shared = 0) &&
    (sharedPlan recordSet p.2 p.1).toOption.any (fun P => passes 28 P &&
      decide (P.rounds.map (·.entry) = dryProofFull.2.1.map (·.1.entry))) &&
    (secondPlan recordSet p.1).toOption.any (fun P => passes 20 P &&
      decide (P.rounds.map (·.entry) = dryProofFull.2.2.map (·.1.entry)))) = true := by
  decide +kernel

/-- Every record of the proof file stands under the written codes. -/
theorem codes_two : ([0, 1, 2].all fun c => (litAt sendsFullLit packFullLit 2 c).all fun y =>
    decide (y.2.cs = codesFull2)) = true := by
  decide +kernel

/-- What the test gives. -/
theorem real_members : ∃ (x : LinSized) (P P' : Planned),
    realSized = some (x, codesFull2) ∧ AtRecord x ∧
      sharedSent x.shape = some (sentOf 2 1) ∧ switchesOf 1 x.shape.testOwn = sentOf 2 2 ∧
      (linMessageW x.shape).map (·.toList) = (sentOf 2 0)[81]? ∧
      sharedPlan recordSet codesFull2 x = .ok P ∧ Passes 28 P ∧
      P.rounds.map (·.entry) = dryProofFull.2.1.map (·.1.entry) ∧
      secondPlan recordSet x = .ok P' ∧ Passes 20 P' ∧
      P'.rounds.map (·.entry) = dryProofFull.2.2.map (·.1.entry) := by
  have h := real_test
  cases hs : realSized with
  | none =>
    rw [hs] at h
    cases h
  | some p =>
  rw [hs] at h
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, -⟩, h7⟩, h8⟩ := h
  have hs' : some p = some (p.1, codesFull2) := by
    rw [← h1]
  rw [h1] at h7
  cases hP : sharedPlan recordSet codesFull2 p.1 with
  | error e =>
    rw [hP] at h7
    cases h7
  | ok P =>
  cases hP' : secondPlan recordSet p.1 with
  | error e =>
    rw [hP'] at h8
    cases h8
  | ok P' =>
  rw [hP] at h7
  rw [hP'] at h8
  simp only [Except.toOption, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h7 h8
  exact ⟨p.1, P, P', hs', (atRecord_of_test h2).1, h3, h4, h5, hP, passes_sound h7.1, h7.2, hP',
    passes_sound h8.1, h8.2⟩

/-! ## A place at a record -/

/-- The place P has the codes and messages of record number k of chain c of file f; and the kind's
one Boolean holds there at that record's radii. -/
def PlaceOk (f c k : Nat) (P : Par) : Prop :=
  ∃ y, (litAt sendsFullLit packFullLit f c)[k]? = some y ∧ y.2.At P ∧
    condPort P (radFrom P y.2.l) = true

theorem placeOk_of {c k : Nat} (hc : c ∈ [0, 1, 2]) {s : List OracleNotice}
    (hk : (sentOf 2 c)[k]? = some s) (P : Par) (h1 : P.codes = codesFull2)
    (h2 : P.sent.toList = s) : PlaceOk 2 c k P := by
  unfold sentOf at hk
  rw [List.getElem?_map] at hk
  cases hy : (litAt sendsFullLit packFullLit 2 c)[k]? with
  | none =>
    rw [hy] at hk
    cases hk
  | some y =>
  rw [hy] at hk
  have hs : y.2.sent = s := Option.some.inj hk
  have hm := List.mem_of_getElem? hy
  have hcs : y.2.cs = codesFull2 :=
    of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 codes_two c hc) y hm)
  have hat : y.2.At P := ⟨h1.trans hcs.symm, by rw [hs, ← h2]⟩
  exact ⟨y, hy, hat, (((k01_full y.2 (litAt_mem hm)).2).1 P hat).1⟩

theorem parK1_sent (Q : _root_.Desc.K14.P14) (piece : Nat) (part : String)
    (sent : Array OracleNotice) : (_root_.Desc.K14.parK1 Q piece part sent).sent = sent := by
  simp [_root_.Desc.K14.parK1, Par.sent]

/-- **Fourteen places of a proof file at typed sizes over the file's own codes.** -/
theorem k01_real : ∃ (x : LinSized) (Pl Pl' : Planned),
    realSized = some (x, codesFull2) ∧ AtRecord x ∧
      sharedPlan recordSet codesFull2 x = .ok Pl ∧ Passes 28 Pl ∧
      Pl.rounds.map (·.entry) = dryProofFull.2.1.map (·.1.entry) ∧
      secondPlan recordSet x = .ok Pl' ∧ Passes 20 Pl' ∧
      Pl'.rounds.map (·.entry) = dryProofFull.2.2.map (·.1.entry) ∧
      (∀ Q : _root_.Desc.K14.P14, Q.codes = codesFull2 → Q.S = x.shape →
        (∃ sent, _root_.Desc.K14.withU Q.S = some sent ∧
          PlaceOk 2 1 0 (_root_.Desc.K14.parK1 Q 2 "o_u and the first mask" sent)) ∧
        PlaceOk 2 1 1
          (_root_.Desc.K14.parK1 Q 5 "o_omega and o_sp" (_root_.Desc.K14.withOmega Q.S))) ∧
      (∀ (P : Par) (j : Nat) (s : List OracleNotice), P.codes = codesFull2 → P.sent.toList = s →
        ((switchesOf 1 x.shape.testU)[j]? = some s → PlaceOk 2 1 (2 + j) P) ∧
        ((switchesOf 1 x.shape.testOmega)[j]? = some s →
          PlaceOk 2 1 (2 + (switchesOf 1 x.shape.testU).length + j) P) ∧
        ((switchesOf 1 x.shape.testOwn)[j]? = some s → PlaceOk 2 2 j P)) ∧
      ∀ (P : Par) (w : Array OracleNotice), P.codes = codesFull2 →
        linMessageW x.shape = some w → P.sent = w → PlaceOk 2 0 81 P := by
  obtain ⟨x, Pl, Pl', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := real_members
  refine ⟨x, Pl, Pl', a1, a2, a6, a7, a8, a9, a10, a11, fun Q hc hS => ?_,
    fun P j s hc hs => ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, fun P w hc hw hs => ?_⟩
  · unfold sharedSent at a3
    rw [hS]
    cases hu : _root_.Desc.K14.withU x.shape with
    | none =>
      rw [hu] at a3
      cases a3
    | some u =>
    rw [hu] at a3
    have e := Option.some.inj a3
    refine ⟨⟨u, rfl, placeOk_of (by decide) (s := u.toList) (by rw [← e]; rfl) _ hc
      (by rw [parK1_sent])⟩, placeOk_of (by decide)
        (s := (_root_.Desc.K14.withOmega x.shape).toList) (by rw [← e]; rfl) _ hc
        (by rw [parK1_sent])⟩
  · unfold sharedSent at a3
    cases hu : _root_.Desc.K14.withU x.shape with
    | none =>
      rw [hu] at a3
      cases a3
    | some u =>
    rw [hu] at a3
    have e := Option.some.inj a3
    refine placeOk_of (by decide) (s := s) ?_ P hc hs
    rw [← e, Nat.add_comm 2 j]
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by
      exact (List.getElem?_eq_some_iff.1 h).1)]
    exact h
  · unfold sharedSent at a3
    cases hu : _root_.Desc.K14.withU x.shape with
    | none =>
      rw [hu] at a3
      cases a3
    | some u =>
    rw [hu] at a3
    have e := Option.some.inj a3
    refine placeOk_of (by decide) (s := s) ?_ P hc hs
    rw [← e, Nat.add_assoc, Nat.add_comm 2 _]
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact h
  · exact placeOk_of (by decide) (s := s) (by rw [← a4]; exact h) P hc hs
  · rw [hw] at a5
    exact placeOk_of (by decide) (s := w.toList) a5.symm P hc (by rw [hs])

end VerifiableInference.Desc.K1
