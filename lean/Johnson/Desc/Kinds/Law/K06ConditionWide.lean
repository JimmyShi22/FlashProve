-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06ConditionWide.lean: THE ROW «K06_condition», FURTHER: the premises ON PUBLIC NUMBERS ALONE of the road from the output head's relation on cells to the library's own relation of the head (Law/LibJoin.lean, a port of a text of ours, not in this repository:
Same · Wide · More; spent by Law/LibWhole.lean's headCl_of_two), AS TWO STRUCTURES WITH NAMED FIELDS, at the written records of Law/K06Condition.lean: this file stands beside it.
WHY. That port's own head: «JV = V FOLLOWS FROM NO TEST THAT THE KIND's planOk NAMES (at ls = 7 planOk passes and JV > V) · sh = 8 likewise (the ranges admit sh = 7, where the library's 2^8 and R23 are the wrong numbers)».
WHAT IT DOES NOT SHOW. NOTHING OF SOUNDNESS. THAT NO PREMISE IS MISSED. The letters of Same | More that are no numbers of the plan (the request's r and e; the policy's C, theta, cap against a library's request Y; the checked tokens win) ARE NOT HERE: they hang on Y.
K06Ref HOLDS AT THE FULL-SIZE RECORD ALONE, AND IS FALSE AT THE SMALL ONE (k06Ref_not_small): the library's reference model has one size. The written records' tie to files is a run (Law/K06Condition.lean's head).
  K06Whole h   at BOTH records: whole: JV = V (no padding of the vocabulary) · digits: sh = 8. THAT NEITHER FOLLOWS FROM THE KIND's planOk WITH THE PROGRAM's admitted AND numbers IS A THEOREM HERE (whole_untested · digits_untested: a record that passes all three and fails the field); the program's other tests (its policy) are not read.
  K06Ref h     the reference model's sizes: T = 1024 (Same's) · d = 5120 · V = 202048 · JV = 202048 · F = 24 · S2 ∣ 64 (Wide's five) · sh = 8 · JVa = 131072 (More's two).
  spends_wide  K06Ref h → Wide, BY THAT NAME.   spends_more  K06Ref h and the one letter win → More Y.   spends_T  Same's first field.   whole_of_ref.
  whole_untested | digits_untested   the small record with V := 513 | with digSh := 7 and tabS := 3: Par.ok, admitted and numbers say yes; JV = V | sh = 8 is false.
  limbs_untested   the small record with XL := 4: the three say yes; K06Cond's field limbs (XL = 5) is false.
  block_follows    A RIGHTING OF Law/K06Condition.lean's HEAD, which says of its field block (ls ≤ lPd) «NEITHER THE KIND NOR admitted TESTS IT»: true of the two texts, BUT THE FIELD FOLLOWS from features (0 < d) and blocks (S2 ∣ d), which both test: it is no further premise.
  k06Whole_bites   the structure says no at ls = 7 (la := lt + 7) with V as it is at the full record, and at digSh := 7.

-/
import Johnson.Desc.Kinds.Law.K06Condition
import Johnson.Desc.Kinds.Law.LibJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Cond

open OnBytes.Model.Head (Shape)

/-- At both records: no padding of the vocabulary; eight bits a digit. -/
structure K06Whole (h : Shape) : Prop where
  whole : letI := sizesOf h; JV = V
  digits : letI := sizesOf h; sh = 8

/-- The reference model's sizes. -/
structure K06Ref (h : Shape) : Prop where
  T : letI := sizesOf h; Norm.T = 1024
  d : letI := sizesOf h; Norm.d = 5120
  V : letI := sizesOf h; Head.V = 202048
  JV : letI := sizesOf h; Head.JV = 202048
  F : letI := sizesOf h; Head.F = 24
  blocks : letI := sizesOf h; Norm.S2 ∣ 64
  sh : letI := sizesOf h; Head.sh = 8
  JVa : letI := sizesOf h; Head.JVa = 131072

theorem k06Whole_small : K06Whole hSmall := ⟨by decide, by decide⟩
theorem k06Whole_full : K06Whole hFull := ⟨by decide, by decide⟩
theorem k06Ref_full : K06Ref hFull :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem k06Ref_not_small : ¬ K06Ref hSmall := fun C => absurd C.d (by decide)

theorem whole_of_ref {h : Shape} (C : K06Ref h) : K06Whole h :=
  ⟨by rw [C.JV, C.V], C.sh⟩

/-- The structure can say no: blocks of 2^7 positions at the full record's vocabulary (202048 is no multiple of 128); seven bits a digit. -/
theorem k06Whole_bites :
    ¬ K06Whole { hFull with la := hFull.lt + 7 } ∧ ¬ K06Whole { hFull with digSh := 7 } :=
  ⟨fun C => absurd C.whole (by decide), fun C => absurd C.digits (by decide)⟩

/-- A record that passes the kind's tests on the plan and the program's admitted and numbers, with a padded vocabulary. -/
theorem whole_untested :
    (parOf { hSmall with V := 513 } 0).ok = true ∧
      OnBytes.Model.Head.admitted { hSmall with V := 513 } = true ∧
      (OnBytes.Model.Head.numbers { hSmall with V := 513 }).toOption.isSome = true ∧
      ¬ K06Whole { hSmall with V := 513 } :=
  ⟨by decide, by decide, by decide, fun C => absurd C.whole (by decide)⟩

/-- The like with seven bits a digit. -/
theorem digits_untested :
    (parOf { hSmall with digSh := 7, tabS := 3 } 0).ok = true ∧
      OnBytes.Model.Head.admitted { hSmall with digSh := 7, tabS := 3 } = true ∧
      (OnBytes.Model.Head.numbers { hSmall with digSh := 7, tabS := 3 }).toOption.isSome = true ∧
      ¬ K06Whole { hSmall with digSh := 7, tabS := 3 } :=
  ⟨by decide, by decide, by decide, fun C => absurd C.digits (by decide)⟩

/-- The like with four limbs. -/
theorem limbs_untested :
    (parOf { hSmall with XL := 4 } 0).ok = true ∧
      OnBytes.Model.Head.admitted { hSmall with XL := 4 } = true ∧
      (OnBytes.Model.Head.numbers { hSmall with XL := 4 }).toOption.isSome = true ∧
      ({ hSmall with XL := 4 } : Shape).XL ≠ 5 :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem le_pow_clog2 (n : Nat) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  split
  · rename_i h1
    simpa using h1
  · have h2 := @Nat.lt_log2_self (n - 1)
    omega

/-- **K06Cond's field block follows from its fields features and blocks.** -/
theorem block_follows (h : Shape) (hd : letI := sizesOf h; 0 < Norm.d)
    (hS : letI := sizesOf h; Norm.S2 ∣ Norm.d) : letI := sizesOf h; Norm.ls ≤ Norm.lPd := by
  letI := sizesOf h
  have h1 : Norm.S2 ≤ Norm.d := Nat.le_of_dvd hd hS
  have h2 : Norm.d ≤ 2 ^ Norm.lPd := le_pow_clog2 _
  have h3 : 2 ^ Norm.ls ≤ 2 ^ Norm.lPd := le_trans h1 h2
  exact (Nat.pow_le_pow_iff_right (by decide)).1 h3

/-- **Wide, by that name.** -/
theorem spends_wide {h : Shape} (C : K06Ref h) : letI := sizesOf h; HeadJoin.Wide :=
  letI := sizesOf h
  ⟨C.d, C.V, C.JV, C.F, C.blocks⟩

/-- **More, by that name**, from the one letter that is no number of the plan. -/
theorem spends_more {h : Shape} (C : K06Ref h) [Request] [Token] (Y : Inst.Model.Head.Req)
    (hwin : letI := sizesOf h; ∀ t, Y.win t = Head.win t) : letI := sizesOf h; HeadJoin.More Y :=
  letI := sizesOf h
  ⟨C.sh, C.JVa, hwin⟩

/-- Same's first field. -/
theorem spends_T {h : Shape} (C : K06Ref h) : letI := sizesOf h; Norm.T = 1024 := C.T

/-- **The row's further part, as a closed proposition.** -/
def K06ConditionWide : Prop := K06Whole hSmall ∧ K06Whole hFull ∧ K06Ref hFull

theorem k06ConditionWide : K06ConditionWide := ⟨k06Whole_small, k06Whole_full, k06Ref_full⟩

end VerifiableInference.Desc.Kinds.Head.Law.Cond

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.k06ConditionWide
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.k06Whole_bites
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.whole_untested
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.digits_untested
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.limbs_untested
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.block_follows
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_wide
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_more
