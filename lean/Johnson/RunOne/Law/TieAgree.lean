-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieAgree.lean: THE WITNESS
MAP OF THE TIE: the links' decoder at the filling from the table's letters gives ONE pinned witness,
by choice; the table's claim speaks of ANY witness at which its open items hold. Under the table's
promise two pinned witnesses agree in what the items read at the borders of the two lookups' links:
the stored table's cells, and the tables of the messages 0 and 1. So the items that ride hold of the
one just if they hold of the other.

Main names:
  Agree R w w': the cells are equal; R.of · 0 and R.of · 1 are equal.
  agree_of_pins: under on₁ at a border 2 … 14: two witnesses that are both pinned agree.
  matOf_agree, valOf_agree: the matrix read off them is one; so are the words of every message of
    the statement but the one that the plan numbers as the witness's message 2.
  num_low: the plan numbers none of the statement's messages 0, 1, 2 as the witness's message 2.
  sumE_congr, rowHolds_val: a row holds at two families of words that are alike at the statement's
    messages.
  size_three: under on₁ at a border 2 … 15 the statement has three messages.
  inRange_agree, srow_agree: the riding items at two witnesses that agree.

Object: the table of the key file's first chain (KeyRows1At.lean); Msg.lean's pin_one.
User: claim_back₀ (TieClaimBack.lean).
Letters: the table's B, at_, R, coll.

Limits. The items forms, worth, rows, kclaims are not carried here. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieClaimFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieAgree
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi FirstState Source KRead Where matOf valOf sumE RowHolds
  shape₁_iff)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁)
open Johnson.RunOne.KeyRows1 (open₁ n₁ on₁_two plan₁ meaning₁At ties₁ sizesB counts₁)
open Johnson.RunOne.Law.TiePromise

variable {Cells Mm Smp Rec : Type}

/-- Two witnesses agree in what the links' borders' items read. -/
def Agree (R : KRead Cells Mm) (w w' : Wit Cells Unit Mm) : Prop :=
  w.cells = w'.cells ∧ R.of w 0 = R.of w' 0 ∧ R.of w 1 = R.of w' 1

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}
  {D : WholeD} {B : BaseSt Cells Mm Smp Rec} {at_ : Where} {R : KRead Cells Mm}
  {coll : Strs → Rec → Prop}

/-- **Under the table's promise two pinned witnesses agree.** -/
theorem agree_of_pins (k : ℕ) (h2 : 2 ≤ k) (h14 : k ≤ 14) (a : (Xi × FirstState) × (fr₁ D).E.Str)
    (hon : On₁ X N P D B at_ R coll k a) (w w' : Wit Cells Unit Mm)
    (hT : PINW B.h₁ a.1 (strsOf (fr₁ D) a.2) w) (hT' : PINW B.h₁ a.1 (strsOf (fr₁ D) a.2) w')
    (p0 : PIN (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 a.1 (strsOf (fr₁ D) a.2) w)
    (p0' : PIN (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 a.1 (strsOf (fr₁ D) a.2) w')
    (p1 : PIN (Fk X N P) B.h₁ (at_ 1).1 (at_ 1).2 a.1 (strsOf (fr₁ D) a.2) w)
    (p1' : PIN (Fk X N P) B.h₁ (at_ 1).1 (at_ 1).2 a.1 (strsOf (fr₁ D) a.2) w') : Agree R w w' := by
  have hn := on₁_two _ _ _ _ _ _ _ k a hon
  obtain hm | ⟨-, -, hf, hc⟩ := hon
  · exact absurd rfl hm
  rw [hn, pinned_link k h2 h14] at hc
  have hrp := hf.2.1.2
  obtain ⟨r, hr, hd⟩ := hT
  obtain ⟨r', hr', hd'⟩ := hT'
  obtain rfl : r = r' := Option.some.inj (hr.symm.trans hr')
  refine ⟨Option.some.inj (hd.symm.trans hd'), ?_, ?_⟩
  · rw [hrp w 0 (by simp), hrp w' 0 (by simp)]
    exact pin_one _ _ _ _ _ _ w w' (hc 0 (by simp)) p0 p0'
  · rw [hrp w 1 (by simp), hrp w' 1 (by simp)]
    exact pin_one _ _ _ _ _ _ w w' (hc 1 (by simp)) p1 p1'

theorem matOf_agree (one : OneTime) {w w' : Wit Cells Unit Mm} (h : Agree R w w') :
    matOf (plan₁ one) R w = matOf (plan₁ one) R w' := by
  unfold matOf
  rw [h.1]

/-- The plan numbers none of the statement's messages 0, 1, 2 as the witness's message 2. -/
theorem num_low (one : OneTime) (o : ℕ) (ho : o < 3) : (plan₁ one).num o = some 0 ∨
    (plan₁ one).num o = some 1 ∨ (plan₁ one).num o = none := by
  have c : o = 0 ∨ o = 1 ∨ o = 2 := by omega
  rcases c with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · refine Or.inr (Or.inr ?_)
    show (if (2 : ℕ) == 1 + 2 * one.ranges.stages.length then some 2 else none) = none
    rw [if_neg]
    intro h
    have := beq_iff_eq.1 h
    omega

theorem valOf_agree (one : OneTime) {w w' : Wit Cells Unit Mm} (h : Agree R w w') (o : ℕ)
    (ho : o < 3) : valOf (plan₁ one) R w o = valOf (plan₁ one) R w' o := by
  funext part i
  unfold valOf
  rcases num_low one o ho with e | e | e <;> rw [e]
  · show R.val (R.of w 0) part i = R.val (R.of w' 0) part i
    rw [h.2.1]
  · show R.val (R.of w 1) part i = R.val (R.of w' 1) part i
    rw [h.2.2]

theorem sumE_congr (n : ℕ) (f g : ℕ → E) (h : ∀ i < n, f i = g i) : sumE n f = sumE n g := by
  unfold sumE
  have : ∀ (l : List ℕ) (a : E), (∀ i ∈ l, f i = g i) →
      l.foldl (fun s i => addE s (f i)) a = l.foldl (fun s i => addE s (g i)) a := by
    intro l
    induction l with
    | nil =>
      intro a _
      simp only [List.foldl_nil]
    | cons x l ih =>
      intro a hl
      rw [List.foldl_cons, List.foldl_cons, hl x List.mem_cons_self]
      exact ih _ fun i hi => hl i (List.mem_cons_of_mem _ hi)
  exact this _ _ fun i hi => h i (List.mem_range.1 hi)

/-- A row holds at two families of words that are alike at the statement's messages. -/
theorem rowHolds_val (same : E → E → Prop) (St : Statement) (val val' : ℕ → Part → ℕ → E)
    (h : ∀ o < St.oracles.size, val o = val' o) (r : OnBytes.Row) :
    RowHolds same St val r ↔ RowHolds same St val' r := by
  unfold RowHolds
  rw [sumE_congr _ _ _ fun o ho => by rw [h o ho]]

/-- Under the table's promise at a border 2 … 15 the statement has three messages. -/
theorem size_three (k : ℕ) (h2 : 2 ≤ k) (h15 : k ≤ 15) (a : (Xi × FirstState) × (fr₁ D).E.Str)
    (hon : On₁ X N P D B at_ R coll k a) : a.1.2.d.st.oracles.size = 3 := by
  obtain hm | ⟨hs, -⟩ := hon
  · exact absurd rfl hm
  have ht : ties₁ X.Y.k.oneTime k a.1.2 = true := ((shape₁_iff _ _ _ _ _ _ _).1 hs).1
  unfold ties₁ sizesB at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  have e := ht.2.1.1.1.1.1.1.1
  have c : counts₁ X.Y.k.oneTime k = (3, 1, 2) := by
    unfold counts₁
    have k0 : (k == 0) = false := by simp; omega
    have k1 : (k == 1) = false := by simp; omega
    simp [k0, k1, h15]
  rw [c] at e
  exact e

theorem inRange_agree (one : OneTime) {w w' : Wit Cells Unit Mm} (h : Agree R w w') (l : ℕ)
    (hx : (meaning₁At one R).inRange l w) : (meaning₁At one R).inRange l w' := by
  obtain ⟨L, h1, h2⟩ := hx
  exact ⟨L, h1, matOf_agree one h ▸ h2⟩

theorem srow_agree (one : OneTime) {w w' : Wit Cells Unit Mm} (h : Agree R w w') (k : ℕ)
    (a : Xi × FirstState) (h3 : a.2.d.st.oracles.size = 3) (y : Strs)
    (hx : (meaning₁At one R).srow k a y w) : (meaning₁At one R).srow k a y w' := by
  obtain ⟨o, x, h1, h2, h4, h5, h6⟩ := hx
  exact ⟨o, x, h1, h2, h4, h5, fun r hr => (rowHolds_val R.same _ _ _
    (fun o ho => valOf_agree one h o (by rw [← h3]; exact ho)) r).1 (h6 r hr)⟩

end Johnson.RunOne.Law.TieAgree

#print axioms Johnson.RunOne.Law.TieAgree.agree_of_pins
#print axioms Johnson.RunOne.Law.TieAgree.valOf_agree
#print axioms Johnson.RunOne.Law.TieAgree.rowHolds_val
#print axioms Johnson.RunOne.Law.TieAgree.size_three
#print axioms Johnson.RunOne.Law.TieAgree.inRange_agree
#print axioms Johnson.RunOne.Law.TieAgree.srow_agree
