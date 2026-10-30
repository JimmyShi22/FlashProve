-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/GuardFastLaws.lean: the test by conditions (`okJF`,
OnBytes/Maker/Page/GuardFast.lean) is the test "the page writes a string for this query" (`okJ`,
OnBytes/Maker/Page/Guard.lean), at every page, oracle and query.

Main names:
  `codeJ_isSome`: the page has a string where a taken spelling or the page's own row writes.
  `fbCallJ_row`: at a chain query whose head is f2 or f5 the file's rows have a call for every block
    or for none: `fbTailF` says which.
  `fbCallJ_tail`: at every chain query `fbTailF` says whether they have a call for the tail's block.
  `gCallJ_isSome`: a query for the slot value has a call in the joining round alone.
  `okJF_eq`: `okJF P o q = okJ P o q`. No premise.
  `runGuard_fast`, `runGuardF_eq`: so the run that refuses by `okJF` is `runGuard`, at every oracle
    algorithm.
  `leafOf_isSome`: `leafOf bd` has a call where the body has 128 bits or more.
No letter stands under "there is".

What is not claimed. What the heads of OnBytes/Maker/Page/Guard.lean and
OnBytes/Maker/Page/GuardFast.lean do not claim. Nothing on soundness.


-/
import OnBytes.Maker.Page.GuardFast
import OnBytes.Maker.Page.GuardLaws
import OnBytes.Maker.Page.Trees

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

/-! ## Tools -/

section Tools
variable {α : Type}

theorem isSome_ite (p : Prop) [Decidable p] (a : α) :
    (if p then some a else none).isSome = decide p := by
  by_cases h : p <;> simp [h]

theorem isSome_ite_and (p r : Prop) [Decidable p] [Decidable r] (hr : r) (a : α) :
    (if p ∧ r then some a else none).isSome = decide p := by
  by_cases h : p <;> simp [h, hr]

theorem isSome_ite2 (p r : Prop) [Decidable p] [Decidable r] (a b : α) :
    (if p then some a else if r then some b else none).isSome = (decide p || decide r) := by
  by_cases h : p <;> by_cases h' : r <;> simp [h, h']

/-- A test that says c at every member, with c in front. -/
theorem and_all_const (l : List α) (c : Bool) : (c && l.all fun _ => c) = c := by
  cases c
  · rfl
  · induction l with
    | nil => rfl
    | cons a l ih => exact ih

/-- "f or c" at every member: c, or f at every member. -/
theorem all_or_const (l : List α) (f : α → Bool) (c : Bool) :
    (l.all fun a => f a || c) = (c || l.all f) := by
  induction l with
  | nil => cases c <;> rfl
  | cons a l ih =>
    show ((f a || c) && l.all fun a => f a || c) = (c || (f a && l.all f))
    rw [ih]
    cases c <;> cases f a <;> cases l.all f <;> rfl

end Tools

variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-! ## The rows -/

/-- **At a head f2 or f5: a call for every block, or for none.** -/
theorem fbCallJ_row {t : Tag} (F : FileJ L t) (K : ℕ) (q : FbIn 256 L t)
    (hq : tailOnly q = false) (j : Fin (K + 1)) : (fbCallJ F K q j).isSome = fbTailF F q := by
  obtain ⟨i, h, rt, pl⟩ := q
  cases h with
  | f1 cms x salt => exact absurd (show true = false from hq) (by decide)
  | f3 ρ0 c => exact absurd (show true = false from hq) (by decide)
  | f4 cms rtreq => exact absurd (show true = false from hq) (by decide)
  | f2 xl ρ =>
    cases xl with
    | none => exact isSome_ite2 (1 ≤ i ∧ i ≤ F.n₁) (F.J3 + 1 ≤ i ∧ i ≤ F.J3 + F.n₃) _ _
    | some x => rfl
  | f5 ρ => exact isSome_ite (F.J + 1 ≤ i ∧ i ≤ F.J + F.n₂) _

/-- **The tail's block.** -/
theorem fbCallJ_tail {t : Tag} (F : FileJ L t) (K : ℕ) (q : FbIn 256 L t) :
    (fbCallJ F K q (Fin.last K)).isSome = fbTailF F q := by
  obtain ⟨i, h, rt, pl⟩ := q
  cases h with
  | f1 cms x salt => exact isSome_ite_and (i = 0) ((Fin.last K).val = K) rfl _
  | f3 ρ0 c => exact isSome_ite_and (i = F.J3) ((Fin.last K).val = K) rfl _
  | f4 cms rtreq => exact isSome_ite_and (i = F.J) ((Fin.last K).val = K) rfl _
  | f2 xl ρ => exact fbCallJ_row F K ⟨i, .f2 xl ρ, rt, pl⟩ rfl _
  | f5 ρ => exact fbCallJ_row F K ⟨i, .f5 ρ, rt, pl⟩ rfl _

/-- A query for the slot value has a call in the joining round alone. -/
theorem gCallJ_isSome {t : Tag} (F : FileJ L t) (q : JoiningRoundQuery 256 L t) :
    (gCallJ F q).isSome = decide (q.round = F.J) :=
  isSome_ite (q.round = F.J) _

variable {K : ℕ}

/-! ## The page's strings -/

/-- **The page has a string where a taken spelling or its own row writes.** -/
theorem codeJ_isSome (P : PageJ L K) (o : OracleName) (q : domOf 256 L o) (j : Fin (blocksJ K o)) :
    (codeJ P o q j).isSome = ((takenJ P o q j).isSome || (callJ P o q j).isSome) := by
  unfold codeJ
  cases takenJ P o q j with
  | some s => rfl
  | none => cases callJ P o q j <;> rfl

theorem codeJ_onl (P : PageJ L K) (q : FbIn 256 L .onl) (j : Fin (K + 1)) :
    (codeJ P (.fb .onl) q j).isSome = (fbCallJ P.proof K q j).isSome :=
  (codeJ_isSome P (.fb .onl) q j).trans (Bool.false_or _)

theorem codeJ_test (P : PageJ L K) (q : FbIn 256 L .test) (j : Fin (K + 1)) :
    (codeJ P (.fb .test) q j).isSome =
      ((P.seeds (q, j)).isSome || (fbCallJ P.key K q j).isSome) :=
  codeJ_isSome P (.fb .test) q j

theorem codeJ_link (P : PageJ L K) (q : FbIn 256 L .link) (j : Fin (K + 1)) :
    (codeJ P (.fb .link) q j).isSome = (P.link (q, j)).isSome :=
  (codeJ_isSome P (.fb .link) q j).trans (Bool.or_false _)

/-! ## The two tests are one -/

theorem okJF_onl (P : PageJ L K) (q : FbIn 256 L .onl) :
    okJF P (.fb .onl) q = okJ P (.fb .onl) q := by
  show fbTailF P.proof q = ((codeJ P (.fb .onl) q (Fin.last K)).isSome &&
    (tailOnly (t := .onl) q ||
      (List.finRange K).all fun k => (codeJ P (.fb .onl) q k.castSucc).isSome))
  have eL : (codeJ P (.fb .onl) q (Fin.last K)).isSome = fbTailF P.proof q :=
    (codeJ_onl P q _).trans (fbCallJ_tail P.proof K q)
  rw [eL]
  cases hT : tailOnly (t := .onl) q with
  | true => simp only [Bool.true_or, Bool.and_true]
  | false =>
    have e1 : (fun k : Fin K => (codeJ P (.fb .onl) q k.castSucc).isSome) =
        fun _ => fbTailF P.proof q :=
      funext fun k => (codeJ_onl P q _).trans (fbCallJ_row P.proof K q hT _)
    rw [e1, Bool.false_or]
    exact (and_all_const _ _).symm

theorem okJF_test (P : PageJ L K) (q : FbIn 256 L .test) :
    okJF P (.fb .test) q = okJ P (.fb .test) q := by
  show (((P.seeds (q, Fin.last K)).isSome || fbTailF P.key q) &&
      (tailOnly (t := .test) q || fbTailF P.key q ||
        (List.finRange K).all fun k => (P.seeds (q, k.castSucc)).isSome)) =
    ((codeJ P (.fb .test) q (Fin.last K)).isSome &&
      (tailOnly (t := .test) q ||
        (List.finRange K).all fun k => (codeJ P (.fb .test) q k.castSucc).isSome))
  have eL : (codeJ P (.fb .test) q (Fin.last K)).isSome =
      ((P.seeds (q, Fin.last K)).isSome || fbTailF P.key q) :=
    (codeJ_test P q _).trans
      (congrArg (fun b => (P.seeds (q, Fin.last K)).isSome || b) (fbCallJ_tail P.key K q))
  rw [eL]
  cases hT : tailOnly (t := .test) q with
  | true => simp only [Bool.true_or]
  | false =>
    have e1 : (fun k : Fin K => (codeJ P (.fb .test) q k.castSucc).isSome) =
        fun k => (P.seeds (q, k.castSucc)).isSome || fbTailF P.key q :=
      funext fun k => (codeJ_test P q _).trans
        (congrArg (fun b => (P.seeds (q, k.castSucc)).isSome || b)
          (fbCallJ_row P.key K q hT _))
    have e2 : ((List.finRange K).all fun k => (codeJ P (.fb .test) q k.castSucc).isSome) =
        (fbTailF P.key q || (List.finRange K).all fun k => (P.seeds (q, k.castSucc)).isSome) := by
      rw [e1]
      exact all_or_const _ _ _
    rw [e2]
    simp only [Bool.false_or]

theorem okJF_link (P : PageJ L K) (q : FbIn 256 L .link) :
    okJF P (.fb .link) q = okJ P (.fb .link) q := by
  show ((P.link (q, Fin.last K)).isSome &&
      (tailOnly (t := .link) q ||
        (List.finRange K).all fun k => (P.link (q, k.castSucc)).isSome)) =
    ((codeJ P (.fb .link) q (Fin.last K)).isSome &&
      (tailOnly (t := .link) q ||
        (List.finRange K).all fun k => (codeJ P (.fb .link) q k.castSucc).isSome))
  have e1 : (fun k : Fin K => (codeJ P (.fb .link) q k.castSucc).isSome) =
      fun k => (P.link (q, k.castSucc)).isSome :=
    funext fun k => codeJ_link P q _
  rw [e1, codeJ_link]

/-- **The test by conditions is the test "the page writes a string for this query".** -/
theorem okJF_eq (P : PageJ L K) : ∀ (o : OracleName) (q : domOf 256 L o), okJF P o q = okJ P o q
  | .leaf, q => (codeJ_isSome P .leaf q (0 : Fin 1)).symm
  | .node, _ => rfl
  | .rleaf, q => (okJ_rleaf P q).symm
  | .rnode, _ => rfl
  | .fb .test, q => okJF_test P q
  | .fb .onl, q => okJF_onl P q
  | .fb .link, q => okJF_link P q
  | .fbw _ _, _ => rfl
  | .g .test, q =>
    ((codeJ_isSome P (.g .test) q (0 : Fin 1)).trans
      ((Bool.false_or _).trans (gCallJ_isSome P.key q))).symm
  | .g .onl, q =>
    ((codeJ_isSome P (.g .onl) q (0 : Fin 1)).trans
      ((Bool.false_or _).trans (gCallJ_isSome P.proof q))).symm
  | .g .link, _ => rfl
  | .ann, _ => rfl
  | .other, q => ((codeJ_isSome P .other q (0 : Fin 1)).trans (Bool.or_false _)).symm

/-- **The run that refuses by the conditions is `runGuard`.** -/
theorem runGuard_fast {α : Type} (P : PageJ L K) (O : ByteArray → ByteArray)
    (c : OComp (typedOracleFamily 256 K L) α) :
    detG (S := typedOracleFamily 256 K L) (okJF P) (gJ P O) c = runGuard P O c := by
  have e : okJF P = okJ P := funext fun o => funext fun q => okJF_eq P o q
  unfold runGuard
  rw [e]

/-- **The run with the test by conditions is `runGuard`**, at every page, function and oracle
algorithm. -/
theorem runGuardF_eq {α : Type} (P : PageJ L K) (O : ByteArray → ByteArray)
    (c : OComp (typedOracleFamily 256 K L) α) : runGuardF P O c = runGuard P O c :=
  runGuard_fast P O c

/-- `leafOf bd` has a call where the body has 128 bits or more. -/
theorem leafOf_isSome (bd : L.Bd → List Bool) (q : LeafIn L) :
    (leafOf bd q).isSome = decide (128 ≤ (bd q.body).length) := by
  unfold leafOf leafCall readBody
  by_cases h : 128 ≤ (bd q.body).length <;> simp [h]

end OnBytes.Maker.Page

#print axioms OnBytes.Maker.Page.fbCallJ_row
#print axioms OnBytes.Maker.Page.fbCallJ_tail
#print axioms OnBytes.Maker.Page.codeJ_isSome
#print axioms OnBytes.Maker.Page.okJF_eq
#print axioms OnBytes.Maker.Page.runGuard_fast
#print axioms OnBytes.Maker.Page.runGuardF_eq
#print axioms OnBytes.Maker.Page.leafOf_isSome
