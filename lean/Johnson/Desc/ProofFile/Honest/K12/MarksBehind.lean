-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/MarksBehind.lean

What it proves. Wherever the fold over the eight sub-protocols of the linear claim's shared rounds
returns from the chain's first state, at whatever key, rounds and columns: (1) the statement behind
is tidy, every open row at every group passes the mark claimsAtB, and no row has a written-out
factor; (2) the shape of the state behind is the term endAt Q sentU key
(Johnson/Desc/K14/Shape/End.lean); (3) both groups are there and no test on them has begun. So what
the seat of the test on G_u enters there passes the three tests that a proximity test's door asks
beside the shape: stTidyB, stPlainB, claimsB; and its shape is doorU (endAt …).
Up to here all premises are on the plan.
Behind the test on G_u the same three hold at what the seat of the test on G_omega enters
(onGu_marks, three_at_Omega), from any state d in front of that test of which four things are asked:
its codes' lengths are in order; the three marks hold; the group G_omega is there and no test on it
has begun; the two groups' numbers differ. These four are premises on the state. The second and the
third are given behind the eight by marks_behind_eight and there_behind_eight; all four follow from
premises on the plan in three_behind_nine (MarksAtDoor.lean), not here.

Names.
  Marks3   the three marks of a statement: Marked (tidy; claimsAtB at every group) and stPlainB.
  Three    the three tests at a structure inside a proximity test: stTidyB, stPlainB, claimsB.
  eight_of, eight_steps   the plan's eight by name; the fold over them, step by step.
  marked_behind_eight, marks_behind_eight   (1).
  sh_behind_eight   (2).
  addRow_there, addRow_other, split_there, there_behind_eight   (3).
  three_at_U, shape_at_U   at what the seat of the test on G_u enters.
  onGu_marks, three_at_Omega   behind the test on G_u; at what the seat of the test on G_omega
      enters.

By what. Marked, groundQuiet_mark, admitOn_mark, marked_first (Johnson/Desc/K14/Shape/Mark.lean);
the library's blocks_steps (Johnson/Desc/K14/Quiet.lean) and foldBlocks_steps
(Johnson/Desc/StepKeeps.lean); upTo_step (End.lean); door_enter (Door.lean); Eight.back8
(Johnson/Desc/K14/Honest/StepsBack.lean); plain_behind_eight (PlainAtEight.lean);
k12_tidy_mark, k12_plain_mark (Johnson/Desc/K12/Honest/Shape/TestMarks.lean), k12_claims_mark
(TestMarksMore.lean), claimsB_of_mark (TestClaims.lean); inside_ok (Johnson/Desc/K12/SeatLaws.lean);
onGu_leaves (Johnson/Desc/K12/Coin/SamplesThrough.lean).

Limits.
- It stands over 21 files that are not in the library yet: nine under Johnson/Desc/K14/Shape/,
  three under Johnson/Desc/Ground/Shape/ and nine under Johnson/Desc/K12/Honest/.
- endAt Q sentU key reads the key's sizes. That it is one term for all keys at which the fold
  returns is not shown here.
- Where the fold does not return nothing is said: a fall-back is not treated here.
- One direction: from a return to the marks. When the fold returns is not treated.
- The marks read values of the rows. They say that the rows could be laid now and have no
  written-out factor, not that any row holds of anything.
- Steps of the verifier's: nothing is shown of any prover. Nothing on completeness, on soundness or
  on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlainAtEight
import Johnson.Desc.K14.Shape.Mark
import Johnson.Desc.K14.Shape.Door
import Johnson.Desc.K14.Shape.End
import Johnson.Desc.K12.Honest.Shape.TestMarksMore
import Johnson.Desc.K12.Honest.Shape.TestClaims
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.K12.Coin.SamplesThrough
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain Desc.K14
open VerifiableInference.Desc VerifiableInference.Desc.Ground VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Keeps VerifiableInference.Desc.K12
open Desc.K14.Shape (Marked MarkStay groundQuiet_mark admitOn_mark marked_first Sh2 sh2 endAt upTo
  upTo_step doorU door_enter)
open Desc.K14.Honest (Eight)
open VerifiableInference.Desc.K12.Coin (onGu_leaves)
open H2K.JointK (Gs Blk')
open ProofFile.Honest.Sh (claimsB testSh k12_tidy_mark k12_plain_mark k12_claims_mark claimsB_of_mark)

/-- The three marks of a statement. -/
structure Marks3 (S : Statement) : Prop where
  marked : Marked S
  plain : stPlainB S = true

/-- The three tests at a structure inside a proximity test. -/
structure Three (t : T12) : Prop where
  tidy : stTidyB t.st = true
  plain : stPlainB t.st = true
  claims : claimsB t = true

/-! ## 1 The eight by name, and the fold step by step -/

theorem eight_of (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs) :
    ∃ B : Eight Q, bs = [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] := by
  have h := hb
  unfold blocks at h
  dsimp only at h
  obtain ⟨w, _, h⟩ := obind_ok h
  cases h
  exact ⟨⟨_, _, _, _, _, _, _, _, hb⟩, rfl⟩

theorem eight_steps {ft : ℕ} {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} {s : St}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {r : St × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft [b1, b2, b3, b4, b5, b6, b7, b8] s rs cols = .ok r) :
    ∃ (d1 d2 d3 d4 d5 d6 d7 : St) (R1 R2 R3 R4 R5 R6 R7 R8 : List Fmt.RoundView)
      (C1 C2 C3 C4 C5 C6 C7 C8 : List OpenedColumn) (n1 n2 n3 n4 n5 n6 n7 n8 : ℕ),
      b1.step ft s R1 C1 = .ok (d1, n1) ∧ b2.step ft d1 R2 C2 = .ok (d2, n2) ∧
      b3.step ft d2 R3 C3 = .ok (d3, n3) ∧ b4.step ft d3 R4 C4 = .ok (d4, n4) ∧
      b5.step ft d4 R5 C5 = .ok (d5, n5) ∧ b6.step ft d5 R6 C6 = .ok (d6, n6) ∧
      b7.step ft d6 R7 C7 = .ok (d7, n7) ∧ b8.step ft d7 R8 C8 = .ok (r.1, n8) := by
  obtain ⟨_, d1, n1, h1, h⟩ := foldBlocks_cons_ok.1 h
  obtain ⟨_, d2, n2, h2, h⟩ := foldBlocks_cons_ok.1 h
  obtain ⟨_, d3, n3, h3, h⟩ := foldBlocks_cons_ok.1 h
  obtain ⟨_, d4, n4, h4, h⟩ := foldBlocks_cons_ok.1 h
  obtain ⟨_, d5, n5, h5, h⟩ := foldBlocks_cons_ok.1 h
  obtain ⟨_, d6, n6, h6, h⟩ := foldBlocks_cons_ok.1 h
  obtain ⟨_, d7, n7, h7, h⟩ := foldBlocks_cons_ok.1 h
  obtain ⟨_, d8, n8, h8, h⟩ := foldBlocks_cons_ok.1 h
  simp only [foldBlocks, Except.ok.injEq] at h
  subst h
  exact ⟨d1, d2, d3, d4, d5, d6, d7, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    n1, n2, n3, n4, n5, n6, n7, n8, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## 2 The marks behind the eight -/

/-- Tidy, and claimsAtB at every group. -/
theorem marked_behind_eight (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hp : ∀ b ∈ bs, b.planOk = true) (ft : ℕ) (key : TableKey) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs (first Q.codes key) rs cols = .ok r) : Marked r.1.st :=
  foldBlocks_steps (RelAt MarkStay) (fun s => groundQuiet_mark.refl s.st)
    (fun _ _ _ x y => groundQuiet_mark.trans x y) ft bs
    (blocks_steps groundQuiet_mark admitOn_mark Q bs hb) hp _ rs cols r h
    (marked_first Q.codes key)

/-- **All three marks behind the eight.** -/
theorem marks_behind_eight (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hp : ∀ b ∈ bs, b.planOk = true) (ft : ℕ) (key : TableKey) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs (first Q.codes key) rs cols = .ok r) : Marks3 r.1.st :=
  ⟨marked_behind_eight Q bs hb hp ft key rs cols r h,
    plain_behind_eight Q bs hb ft key rs cols r h⟩

/-! ## 3 The shape behind the eight -/

/-- **The shape behind the eight is the term endAt.** -/
theorem sh_behind_eight (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (sentU : Array OracleNotice) (hU : withU Q.S = some sentU)
    (hS : Q.S.sharedSplitNeeded = true) (ft : ℕ) (key : TableKey) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs (first Q.codes key) rs cols = .ok r) :
    sh2 r.1 = endAt Q sentU key := by
  obtain ⟨B, rfl⟩ := eight_of Q bs hb
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, R1, R2, R3, R4, R5, R6, R7, R8, C1, C2, C3, C4, C5, C6, C7,
    C8, n1, n2, n3, n4, n5, n6, n7, n8, h1, h2, h3, h4, h5, h6, h7, h8⟩ := eight_steps h
  have e1 := (upTo_step hU hS B ft (sh2 (first Q.codes key)) _ d1 R1 C1 n1).1 rfl h1
  have e2 := (upTo_step hU hS B ft (sh2 (first Q.codes key)) _ d2 R2 C2 n2).2.1 e1 h2
  have e3 := (upTo_step hU hS B ft (sh2 (first Q.codes key)) _ d3 R3 C3 n3).2.2.1 e2 h3
  have e4 := (upTo_step hU hS B ft (sh2 (first Q.codes key)) _ d4 R4 C4 n4).2.2.2.1 e3 h4
  have e5 := (upTo_step hU hS B ft (sh2 (first Q.codes key)) _ d5 R5 C5 n5).2.2.2.2.1 e4 h5
  have e6 := (upTo_step hU hS B ft (sh2 (first Q.codes key)) _ d6 R6 C6 n6).2.2.2.2.2.1 e5 h6
  have e7 :=
    (upTo_step hU hS B ft (sh2 (first Q.codes key)) _ d7 R7 C7 n7).2.2.2.2.2.2.1 e6 h7
  exact (upTo_step hU hS B ft (sh2 (first Q.codes key)) _ r.1 R8 C8 n8).2.2.2.2.2.2.2 e7 h8

/-! ## 4 Both groups are there, and no test on them has begun -/

/-- The group is there and no test on it has begun. -/
def There (S : Statement) (g : ℕ) : Prop :=
  ∃ G : Group, S.groups[g]? = some G ∧ G.inRun = false

/-- Behind the adding of a row the group is there and no test on it has begun. -/
theorem addRow_there {L : Type} (d d' : DState L) (g : ℕ) (row : Row)
    (h : addRowP d g row = some d') : There d'.st g := by
  unfold addRowP at h
  split at h
  · rename_i hok
    cases h
    simp only [Ground.ok, rowL, List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨h1, h2, -⟩ := hok
    obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 h1
    rw [hG] at h2
    refine ⟨{ G with rows := G.rows.push row }, ?_, by simpa [Ground.has] using h2⟩
    show (d.st.groups.modify g fun G => { G with rows := G.rows.push row })[g]? = _
    rw [Array.getElem?_modify, if_pos rfl, hG]
    rfl
  · cases h

/-- The adding of a row leaves that at every group. -/
theorem addRow_other {L : Type} (d d' : DState L) (g g' : ℕ) (row : Row)
    (h : addRowP d g row = some d') (k : There d.st g') : There d'.st g' := by
  by_cases e : g = g'
  · subst e
    exact addRow_there d d' g row h
  · obtain ⟨G, hG, hr⟩ := k
    unfold addRowP at h
    split at h
    · cases h
      refine ⟨G, ?_, hr⟩
      show (d.st.groups.modify g fun G => { G with rows := G.rows.push row })[g']? = _
      rw [Array.getElem?_modify, if_neg e, hG]
    · cases h

theorem addRow_loc {L : Type} (d d' : DState L) (g : ℕ) (row : Row)
    (h : addRowP d g row = some d') : d'.loc = d.loc := by
  unfold addRowP at h
  split at h
  · cases h
    rfl
  · cases h

theorem takeMask_loc {L : Type} (d d' : DState L) (o n : ℕ) (h : takeMaskP d o = some (n, d')) :
    d'.loc = d.loc := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj h
    rfl
  · cases h

/-- Behind "SPLIT", at a plan with two codes. -/
theorem split_there (p : Par) (hS : p.S.sharedSplitNeeded = true) (d d' : St) (rs : List Fmt.RoundView)
    (h : split p d rs = some d') :
    There d'.st d.loc.gU ∧ There d'.st d.loc.gOmega ∧ d'.loc = d.loc := by
  unfold split at h
  dsimp only at h
  obtain ⟨row, _, h⟩ := obind_ok h
  split at h
  · rename_i hf _
    rw [hS] at hf
    cases hf
  · split at h
    · obtain ⟨mu, _, h⟩ := obind_ok h
      obtain ⟨G, _, h⟩ := obind_ok h
      obtain ⟨_, _, h⟩ := obind_ok h
      obtain ⟨⟨kappa, d₁⟩, h1, h⟩ := obind_ok h
      dsimp only at h
      obtain ⟨d₂, h2, h⟩ := obind_ok h
      refine ⟨addRow_there _ _ _ _ h, addRow_other _ _ _ _ _ h (addRow_there _ _ _ _ h2), ?_⟩
      rw [addRow_loc _ _ _ _ h, addRow_loc _ _ _ _ h2, takeMask_loc _ _ _ _ h1]
    · obtain ⟨mu, hm, h⟩ := obind_ok h
      cases hm
  · cases h

/-- **Behind the eight both groups are there and no test on them has begun.** -/
theorem there_behind_eight (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (sentU : Array OracleNotice) (hU : withU Q.S = some sentU)
    (hS : Q.S.sharedSplitNeeded = true) (ft : ℕ) (s : St) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs s rs cols = .ok r) :
    There r.1.st r.1.loc.gU ∧ There r.1.st r.1.loc.gOmega := by
  obtain ⟨B, rfl⟩ := eight_of Q bs hb
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, R1, R2, R3, R4, R5, R6, R7, R8, C1, C2, C3, C4, C5, C6, C7,
    C8, n1, n2, n3, n4, n5, n6, n7, n8, -, -, -, -, -, -, -, h8⟩ := eight_steps h
  obtain ⟨R, -, -, k⟩ := B.back8 hU hS ft d7 r.1 R8 C8 n8 h8
  obtain ⟨a, b, c⟩ := split_there Q.par hS d7 r.1 _ k
  rw [c]
  exact ⟨a, b⟩

/-! ## 5 At what the seat of the test on G_u enters -/

/-- From the marks of a statement to the three tests, at a group that is there. -/
theorem three_of_marks {t : T12} (m : Marks3 t.st) (k : There t.st t.g) : Three t := by
  obtain ⟨G, hG, hr⟩ := k
  exact ⟨tidy_mark m.marked.1, m.plain, claimsB_of_mark hG hr (m.marked.2 t.g)⟩

/-- **The three tests at what the seat of the test on G_u enters behind the eight.** -/
theorem three_at_U (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hp : ∀ b ∈ bs, b.planOk = true) (sentU : Array OracleNotice) (hU : withU Q.S = some sentU)
    (hS : Q.S.sharedSplitNeeded = true) (ft : ℕ) (key : TableKey) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs (first Q.codes key) rs cols = .ok r) (t : T12)
    (ht : Seat.enter (·.gU) (·.firstMask) r.1 = .ok t) : Three t := by
  obtain rfl := Except.ok.inj ht
  exact three_of_marks (marks_behind_eight Q bs hb hp ft key rs cols r h)
    (there_behind_eight Q bs hb sentU hU hS ft _ rs cols r h).1

/-- **Its shape is a term of the plan and the key's sizes.** -/
theorem shape_at_U (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (sentU : Array OracleNotice) (hU : withU Q.S = some sentU)
    (hS : Q.S.sharedSplitNeeded = true) (ft : ℕ) (key : TableKey) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs (first Q.codes key) rs cols = .ok r) (t : T12)
    (ht : Seat.enter (·.gU) (·.firstMask) r.1 = .ok t) :
    testSh t = doorU (endAt Q sentU key) := by
  rw [door_enter r.1 t ht, sh_behind_eight Q bs hb sentU hU hS ft key rs cols r h]

/-! ## 6 Behind the test on G_u -/

/-- **The seated test on G_u keeps the three marks**, where the codes' lengths are in order. -/
theorem onGu_marks (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hl : d.st.codes.lengthsOk = true) (m : Marks3 d.st) : Marks3 d'.st := by
  obtain ⟨t, t', h1, h2, h3⟩ := (Seat.inside_ok _ _ _ d d' rs gs).1 h
  obtain rfl := Except.ok.inj h1
  obtain rfl := Except.ok.inj h3
  have ht := tidy_mark m.marked.1
  exact ⟨⟨tidy_of (k12_tidy_mark p _ t' rs gs h2 hl ht),
    fun q => k12_claims_mark p he ha _ t' rs gs h2 ht q (m.marked.2 q)⟩,
    k12_plain_mark p he ha _ t' rs gs h2 m.plain⟩

/-- **The three tests at what the seat of the test on G_omega enters behind the test on G_u.** d:
any state in front of the test on G_u of which hl, m, k and hne hold. -/
theorem three_at_Omega (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hl : d.st.codes.lengthsOk = true) (m : Marks3 d.st) (k : There d.st d.loc.gOmega)
    (hne : d.loc.gOmega ≠ d.loc.gU) (t : T12)
    (ht : Seat.enter (·.gOmega) (fun _ => none) d' = .ok t) : Three t := by
  obtain rfl := Except.ok.inj ht
  obtain ⟨-, -, hg, hloc, -⟩ := onGu_leaves p he ha d d' rs gs h
  obtain ⟨G, hG, hr⟩ := k
  have hlt : d.loc.gOmega < d.st.groups.size := (Array.getElem?_eq_some_iff.1 hG).1
  refine three_of_marks (onGu_marks p he ha d d' rs gs h hl m) ⟨G, ?_, hr⟩
  show d'.st.groups[d'.loc.gOmega]? = some G
  rw [hloc, hg _ hlt hne, hG]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.Marks3
#print axioms ProofFile.Honest.K12.Light.Three
#print axioms ProofFile.Honest.K12.Light.eight_of
#print axioms ProofFile.Honest.K12.Light.eight_steps
#print axioms ProofFile.Honest.K12.Light.marked_behind_eight
#print axioms ProofFile.Honest.K12.Light.marks_behind_eight
#print axioms ProofFile.Honest.K12.Light.sh_behind_eight
#print axioms ProofFile.Honest.K12.Light.There
#print axioms ProofFile.Honest.K12.Light.addRow_there
#print axioms ProofFile.Honest.K12.Light.addRow_other
#print axioms ProofFile.Honest.K12.Light.addRow_loc
#print axioms ProofFile.Honest.K12.Light.takeMask_loc
#print axioms ProofFile.Honest.K12.Light.split_there
#print axioms ProofFile.Honest.K12.Light.there_behind_eight
#print axioms ProofFile.Honest.K12.Light.three_of_marks
#print axioms ProofFile.Honest.K12.Light.three_at_U
#print axioms ProofFile.Honest.K12.Light.shape_at_U
#print axioms ProofFile.Honest.K12.Light.onGu_marks
#print axioms ProofFile.Honest.K12.Light.three_at_Omega
