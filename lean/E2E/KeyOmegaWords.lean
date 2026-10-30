-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyOmegaWords.lean: the honest words of the linear claim's sending hold, at Omega's number IN
THE SHARED CHAIN's STATEMENT and through Omega's layout, the vector `omegaAtE` of the shared point.
`dot_says_key` (E2E/KeyDotSays.lean) asks that at Omega's number in the statement at which the row
is laid, which on the last chain is another number: the tie is not here.

Why. The library says of these words that o_omega's table is what o_u's gives at the point's low
part (`omU_at`), and that o_u's table holds the rows' fold on a row's message and on its tail
(`fold_at`). The vector of the row (Dot) reads the folded row at the places of the matrix's rows. So
the two meet where those places lie in a row's message, and the test on the plan says that they do.

Main names.
  `room_of_plan`: the matrix's places lie in a row's message, from the plan's premise.
  `hOm_words2`: the law, at a run's shared point.
  `room_full`: the same room evaluated at the written sizes of the key. By Lean's kernel.

What stays open. The words are the linear claim's, at the shared chain's number. That the last
chain's witness holds the same entries at Omega's copy, its own number, is a tie, not said here.
`room_full` is joined to no run: that the parameters at the key are `keyFull` is not said here. The
premise on the length of the point's high part is a premise.

NOT IN FRONT OF A LAW OVER COINS: `hOm_words2` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: `hRw`, of the first kind, ties the field `Rw` of
the letter `H` to `RwE`, which at the key is made of the committer's coins. None: the bar is flat: no
lemma here lays the made term `holds2` in for `H`. `room_full` is closed and `room_of_plan` reads public
values: neither names a coin.

Nothing on soundness, completeness, hiding or binding.

-/
import Johnson.Desc.K14.Honest.ItemsHold
import Johnson.Desc.K14.Honest.CodedReads
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyOmegaWords
open OnBytes OnBytes.Params
open OnBytes.Slice (rdE)
open _root_.Desc.K14 (P14 St Lin gamma)
open _root_.Desc.K14.Law (eqK uOf)
open _root_.Desc.K14.Honest

/-- **The matrix's places lie in a row's message**, by the plan's own test on the shape. -/
theorem room_of_plan {P : P14} {sentU : Array OracleNotice} {layO : TreeLay}
    (hP : PlanFacts P.par P.codes sentU layO) :
    P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.code.ell := by
  have hsh := (VerifiableInference.Desc.Own.linFits_iff P.codes P.par.S).1 hP.lin
  have hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain :=
    hsh.1.2.2.2.2.2.1
  exact Nat.le_trans hroom (Nat.sub_le _ _)

/-- **The honest words hold the vector of the row (Dot) at Omega's number in the shared statement.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem hOm_words2 {P : P14} {sentU : Array OracleNotice} {layO : TreeLay}
    (hP : PlanFacts P.par P.codes sentU layO) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs) {l : Lin}
    (hl : Notes P d0 r1 l) (RwE : Nat → Nat → E) (hRw : ∀ r j, H.Rw r j = rdE.val (RwE r j))
    (hg : (gamma P.par.S l).length = P.par.S.fold.index.v) (y : Nat)
    (hy : y < P.par.S.matrixRows) :
    omegaAt P d0 (words2 P sentU d0 r1 H) y = rdE.val (omegaAtE P.par.S l.psiSh RwE y) := by
  have hL := room_of_plan hP
  have hE : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.entries :=
    Nat.le_trans hL (Nat.le_trans (ell_le_tailFirst _) (Nat.le_add_right _ _))
  rw [omU_at hP d0 r1 H hl y hy, val_omegaAtE rdE]
  unfold omegaHon
  rw [if_pos hy]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t < 2 ^ P.par.S.kLo := Finset.mem_range.1 ht
  have h1 : t + 2 ^ P.par.S.kLo * y < 2 ^ P.par.S.kLo * (y + 1) := by
    rw [Nat.mul_succ]
    omega
  have h2 : 2 ^ P.par.S.kLo * (y + 1) ≤ P.par.S.matrixRows * 2 ^ P.par.S.kLo := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ hy
  have hk : t + 2 ^ P.par.S.kLo * y < P.par.S.matrixRows * 2 ^ P.par.S.kLo :=
    Nat.lt_of_lt_of_le h1 h2
  have hu : uOf l (words2 P sentU d0 r1 H) (t + 2 ^ P.par.S.kLo * y) =
      rdE.val (uAtE P.par.S l.psiSh RwE (t + 2 ^ P.par.S.kLo * y)) := by
    rw [val_uAtE rdE, (fold_at hP d0 r1 H hl).onMsg _ (Nat.lt_of_lt_of_le hk hL)]
    unfold uHon
    rw [if_pos (Nat.lt_of_lt_of_le hk hE)]
    unfold foldRows
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [wOf_eq rdE P.par.S l hg r (Finset.mem_range.1 hr), hRw r _]
    rfl
  rw [hu]

/-- **The matrix's places lie in a row's message, at the written sizes of the key.** -/
theorem room_full :
    Lk6.AtPlan.keyFull.once.shape.matrixRows * 2 ^ Lk6.AtPlan.keyFull.once.shape.kLo ≤
        Lk6.AtPlan.keyFull.once.shape.fold.index.code.ell ∧
      Lk6.AtPlan.keyFull.once.shape.matrixRows * 2 ^ Lk6.AtPlan.keyFull.once.shape.kLo ≤
        Lk6.AtPlan.keyFull.once.shape.fold.entries := by decide +kernel

end AtPublicFiles.KeyOmegaWords

#print axioms AtPublicFiles.KeyOmegaWords.room_of_plan
#print axioms AtPublicFiles.KeyOmegaWords.hOm_words2
#print axioms AtPublicFiles.KeyOmegaWords.room_full
