-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2/TargetMeans.lean: the kind «the code switch»: WHAT THE PUBLIC TEST IN FRONT OF
THE
SWITCH [G0] MEANS: targetOk (K2/Target.lean) as a proposition of eighteen plain facts, one for each
clause and in the clauses' order. NO BLOCK IMPORTS THIS FILE.
  KeptFits · keptFits_iff       a kept member's old shape and the shape of its fresh copy: eight
  facts
  BlocksFill · blocksFill_iff   the two blocks are all the rows of g: by where the rest goes
  isPow2_iff · isPow2_pow       n is not 0 and 2 ^ ceilLog2 n = n; so n = 2 ^ k for some k
  TargetFits · targetOk_means   targetOk S old T = true  ⇔  TargetFits S old T
(K2/TargetAgree.lean's targetOk_iff only unfolds the list of clauses; its padFits_iff says what
padFits checks and is used here as it stands.)
WHAT THE TEST DOES NOT ASK, and so this proposition does not say: that a kept member's number names
a
message of the statement. Where it names none, the blank message's shape is taken
(S.oracles.getD … default), and a copy without rows passes this test. (By reading, the plain
ground's
clause on an announcement's shape asks for a row, so the sending behind the test refuses it; seen so
in one run, at one place of the small example. No theorem says it.)
No soundness is claimed: this says what the test asks, not that it asks enough.

-/
import Johnson.Top.H0.Tw.K2.TargetAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes

/-- A kept member's old shape o and the shape n of its fresh copy. -/
structure KeptFits (codes : Codes) (o n : OracleShape) : Prop where
  /-- the old message has no mask rows -/
  oldBare : o.maskRows = 0
  /-- nor has the copy -/
  newBare : n.maskRows = 0
  /-- the copy's main code is in the list -/
  code : n.code < codes.base.size
  /-- the old message's row is long enough for its pad -/
  pad : padFits codes o = true
  /-- as many main rows -/
  rows : n.mainRows = o.mainRows
  /-- over the same field -/
  degree : n.mainDeg = o.mainDeg
  /-- as many answers -/
  answers : n.answers = o.answers
  /-- messages of one length -/
  length : (codes.base.getD n.code default).ell = (codes.base.getD o.code default).ell

theorem keptFits_iff (codes : Codes) (o n : OracleShape) : keptFits codes o n = true ↔ KeptFits
    codes o n := by
  simp only [keptFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, h⟩
    exact ⟨a, b, c, d, e, f, g, h⟩
  · intro k
    exact ⟨⟨⟨⟨⟨⟨⟨k.oldBare, k.newBare⟩, k.code⟩, k.pad⟩, k.rows⟩, k.degree⟩, k.answers⟩, k.length⟩

/-- The two blocks are all the rows of g. -/
def BlocksFill (codes : Codes) (T : SwitchTarget) : Prop :=
  match T.rest.part with
  | .mask =>
    T.shape.maskCode < codes.mask.size ∧ T.main.firstRow = 0 ∧ 2 ^ T.main.bits = T.shape.mainRows ∧
      T.rest.firstRow = 0 ∧ 2 ^ T.rest.bits = T.shape.maskRows
  | .main =>
    T.shape.maskRows = 0 ∧ T.main.firstRow = 0 ∧ T.rest.firstRow = 2 ^ T.main.bits ∧
      2 ^ T.main.bits + 2 ^ T.rest.bits = T.shape.mainRows

theorem blocksFill_iff (codes : Codes) (T : SwitchTarget) : blocksFill codes T = true ↔ BlocksFill
    codes T := by
  unfold blocksFill BlocksFill
  cases T.rest.part <;> simp [and_assoc]

theorem isPow2_iff (n : Nat) : isPow2 n = true ↔ n ≠ 0 ∧ 2 ^ ceilLog2 n = n := by
  simp [isPow2]

/-- So n is a power of two. -/
theorem isPow2_pow {n : Nat} (h : isPow2 n = true) : ∃ k, n = 2 ^ k :=
  ⟨ceilLog2 n, ((isPow2_iff n).1 h).2.symm⟩

/-- **[G0] as plain facts**, in the clauses' order. ell: the old message's length. -/
structure TargetFits (S : Statement) (old : SingleRows) (T : SwitchTarget) : Prop where
  /-- the old rows have both masks -/
  masks : old.masks = 2
  /-- the old main code is in the list -/
  oldCode : old.code < S.codes.base.size
  /-- the old mask code is in the list -/
  oldMaskCode : old.maskCode < S.codes.mask.size
  /-- g's main code is in the list -/
  code : T.shape.code < S.codes.base.size
  /-- g has a main row -/
  rows : 0 < T.shape.mainRows
  /-- g's main rows are over the extension field -/
  degree : T.shape.mainDeg = 3
  /-- g is sampled -/
  sampled : 1 ≤ T.shape.answers
  /-- g's row is long enough for its pad (what that asks: padFits_iff) -/
  pad : padFits S.codes T.shape = true
  /-- the main row's message goes to g's main rows -/
  mainPart : T.main.part = .main
  /-- the old message length is a power of two -/
  power : (S.codes.base.getD old.code default).ell ≠ 0 ∧
    2 ^ ceilLog2 (S.codes.base.getD old.code default).ell = (S.codes.base.getD old.code default).ell
  /-- the main block begins at a multiple of its size -/
  mainAligned : T.main.firstRow % 2 ^ T.main.bits = 0
  /-- the rest block begins at a multiple of its size -/
  restAligned : T.rest.firstRow % 2 ^ T.rest.bits = 0
  /-- the two blocks are all the rows of g -/
  fill : BlocksFill S.codes T
  /-- the main block has at most as many rows as the old message has entries -/
  mainSmall : 2 ^ T.main.bits ≤ (S.codes.base.getD old.code default).ell
  /-- the old message fits into the main block -/
  mainRoom : (S.codes.base.getD old.code default).ell ≤ (S.codes.base.getD T.shape.code default).ell
      * 2 ^ T.main.bits
  /-- the rest fits into the rest block's places -/
  restRoom : (switchParts S old).length ≤ (SwitchPlaces.make S.codes T).size
  /-- there is a target for each kept member -/
  keptCount : T.kept.size = (switchKept old).size
  /-- each kept member's copy has its shape -/
  keptShapes : ∀ p ∈ (switchKept old).zip T.kept, KeptFits S.codes (S.oracles.getD p.1
      default).shape p.2.shape

theorem targetOk_means (S : Statement) (old : SingleRows) (T : SwitchTarget) :
    targetOk S old T = true ↔ TargetFits S old T := by
  simp only [targetOk, targetL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      beq_iff_eq,
    decide_eq_true_eq, isPow2_iff, blocksFill_iff, Array.all_eq_true_iff_forall_mem, keptFits_iff]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩
  · intro k
    exact ⟨k.masks, k.oldCode, k.oldMaskCode, k.code, k.rows, k.degree, k.sampled, k.pad,
        k.mainPart, k.power,
      k.mainAligned, k.restAligned, k.fill, k.mainSmall, k.mainRoom, k.restRoom, k.keptCount,
          k.keptShapes⟩

end Tw.K2

#print axioms Tw.K2.keptFits_iff
#print axioms Tw.K2.blocksFill_iff
#print axioms Tw.K2.isPow2_iff
#print axioms Tw.K2.targetOk_means
