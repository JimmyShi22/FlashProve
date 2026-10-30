--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/SentC.lean: the conditions under which kind K13's text behind W's commitment
accepts (`SentAtM4`, Johnson/Desc/K13/Honest/RowsAccept.lean), as a test with code. Definitions with
code, and statements with their proofs.

Why. A lemma under conditions that no state meets is true and says nothing. The test can be run on a
state, clause by clause; where it passes, the conditions hold.
Main names:
  `canJoinC`, `canJoinC_iff`: "the message can join", with code.
  `sentAtM4L`: the twelve clauses, each under a name, so that a run can tell which one fails.
  `sentAtM4C`: all of them. `sentAtM4Fails`: the names of those that fail.
  `sentAtM4_of_test`: **where the test passes, the conditions hold.**
States that pass it, and negative tests: Johnson/Desc/K13/Honest/MemberAtM4.lean.

What is not claimed. That the test passes at the state of a real proof: not run here. The converse
of `sentAtM4_of_test` is not stated. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.RowsAccept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Own (allZero)
open VerifiableInference.Desc.K13.Law

/-- The message o can join a group under the codes c and z: with code. -/
def canJoinC (St : Statement) (c z o : ℕ) : Bool :=
  (St.oracles[o]?).any fun x =>
    x.sampled && (x.shape.mainRows == 0 || x.shape.code == c) &&
      (x.shape.maskRows == 0 || x.shape.maskCode == z)

/-- The test with code says what `CanJoin` says. -/
theorem canJoinC_iff (St : Statement) (c z o : ℕ) :
    canJoinC St c z o = true ↔ CanJoin St c z o := by
  unfold canJoinC CanJoin
  cases St.oracles[o]? with
  | none =>
    constructor
    · intro h
      simp at h
    · rintro ⟨y, hy, _⟩
      cases hy
  | some x =>
    constructor
    · intro h
      simp only [Option.any_some, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      exact ⟨x, rfl, h.1.1, h.1.2, h.2⟩
    · rintro ⟨y, hy, h1, h2, h3⟩
      obtain rfl := Option.some.inj hy
      simp only [Option.any_some, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨⟨h1, h2⟩, h3⟩

/-- **The clauses**, each under a name. -/
def sentAtM4L (Sh : LinShape) (row : TensorRow) (ids : Array ℕ) (St : Statement) (w : ℕ) :
    List (String × Bool) :=
  [("first: W is the first of the messages sent", ids[0]? == some w),
   ("split: where a split is needed, its message is the second, can join and is no other member",
     !Sh.ownSplitNeeded || (ids[1]?).any fun sp =>
       canJoinC St Sh.w.code Sh.ownMaskCode sp && (sp != w) &&
         row.masks.all fun t => t.1.oracle != sp),
   ("codes: the own group's codes are lawful",
     Ground.groupOk St.codes Sh.w.code Sh.ownMaskCode),
   ("masks: the messages of the claim's masks can join, and none is W",
     row.masks.all fun t =>
       canJoinC St Sh.w.code Sh.ownMaskCode t.1.oracle && (t.1.oracle != w)),
   ("joins: W can join", canJoinC St Sh.w.code Sh.ownMaskCode w),
   ("point: the point has a coordinate for each column variable", row.psi.length == Sh.kCol),
   ("room: W's vector fits its table", decide (Sh.kCol ≤ (linLayW St.codes Sh).bits)),
   ("small: the table has at most 63 index bits", decide ((linLayW St.codes Sh).bits ≤ 63)),
   ("table: W has a main table", St.has w .main),
   ("bits: W's main table has the layout's index bits",
     St.tableBits w .main == (linLayW St.codes Sh).bits),
   ("within: the claim's mask entries lie within their tables",
     row.masks.all fun t =>
       St.has t.1.oracle .mask && decide (t.1.index < 2 ^ St.tableBits t.1.oracle .mask)),
   ("pad: (Eval) has no coefficient on a pad",
     (List.range St.oracles.size).all fun o =>
       (((St.oracles[o]?).map (·.pad)).getD []).all fun q =>
         allZero ((evalOf row w (linLayW St.codes Sh)).coefficient o q.1 q.2))]

/-- The names of the clauses that fail. -/
def sentAtM4Fails (Sh : LinShape) (row : TensorRow) (ids : Array ℕ) (St : Statement) (w : ℕ) :
    List String :=
  ((sentAtM4L Sh row ids St w).filter fun c => !c.2).map (·.1)

/-- All clauses hold. -/
def sentAtM4C (Sh : LinShape) (row : TensorRow) (ids : Array ℕ) (St : Statement) (w : ℕ) : Bool :=
  (sentAtM4L Sh row ids St w).all (·.2)

/-- **Where the test passes, the conditions hold.** -/
theorem sentAtM4_of_test {Sh : LinShape} {row : TensorRow} {ids : Array ℕ} {St : Statement}
    {w : ℕ} (h : sentAtM4C Sh row ids St w = true) : SentAtM4 Sh row ids St w := by
  simp only [sentAtM4C, sentAtM4L, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at h
  obtain ⟨h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  simp only [List.all_eq_true, Bool.and_eq_true, bne_iff_ne] at h5
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h12
  simp only [List.all_eq_true, List.mem_range] at h13
  refine ⟨beq_iff_eq.1 h1, fun hs => ?_, h4,
    fun t ht => ⟨(canJoinC_iff _ _ _ _).1 (h5 t ht).1, (h5 t ht).2⟩, (canJoinC_iff _ _ _ _).1 h6,
    beq_iff_eq.1 h7, of_decide_eq_true h8, of_decide_eq_true h9, h10, beq_iff_eq.1 h11, h12,
    fun o x hx q hq => ?_⟩
  · rw [hs] at h2
    simp only [Bool.not_true, Bool.false_or] at h2
    cases hi : ids[1]? with
    | none =>
      rw [hi] at h2
      simp at h2
    | some sp =>
      rw [hi] at h2
      simp only [Option.any_some, Bool.and_eq_true, bne_iff_ne, List.all_eq_true] at h2
      exact ⟨sp, rfl, (canJoinC_iff _ _ _ _).1 h2.1.1, h2.1.2, fun t ht => h2.2 t ht⟩
  · have ho : o < St.oracles.size := by
      by_contra c
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
      cases hx
    exact readE_of_isZeroE _ (h13 o ho q (by rw [hx]; exact hq))

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.canJoinC_iff
#print axioms VerifiableInference.Desc.K13.Honest.sentAtM4_of_test
