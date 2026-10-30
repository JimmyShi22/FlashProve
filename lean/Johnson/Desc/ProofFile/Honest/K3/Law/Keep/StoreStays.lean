-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/StoreStays.lean: `StoreOk` (Honest/K3/StoreMake.lean)
stays true as more challenges are heard. Conditional on: the reader of the challenges is steady from
a number of rounds on (`Reads.Steady`), the input is settled there (`Ask.Settled`,
Honest/K3/WitLaw.lean), and so many rounds have been heard. The first hypothesis is shown at the
reader that a lot seats (`theReads`, Honest/K3/LotRow.lean). One definition of a hypothesis, one
number, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file h is the list of the chain's challenges heard so far, one
entry a round, from the chain's first round on; a.base is the number of the chain's rounds in front
of the lookup.

What is defined.
  `Reads.Steady R a n`: once n rounds have been heard, the shift and alpha that R reads no longer
    move as more is heard; and the list that R hands to the input is the list that it was given.
  `pastAlpha a`: the number of the chain's rounds through the round that samples alpha:
    a.base + 2 where the face has a shift, else a.base + 1.

What is shown.
  `Ask.Settled.mono`: an input that is settled at a number is settled at every greater one.
  `storeAt_append`, `storeOk_stays`: conditional, as above: the store made of more challenges is
    the same store; so `StoreOk` stays.
  `storeOk_laid`: conditional, as above: the store that was made when h had been heard meets
    `StoreOk` at h and whatever is heard later.
  `elemAt_append`, `firstRound_shift`, `firstRound_alpha`, `ptsOf_theta`, `ptsOf_alpha`: a round
    that has been heard is read the same later; the shift's round is the lookup's first, where there
    is one; alpha's comes next.
  `base_le_pastAlpha`: a.base is not beyond `pastAlpha a`.
  `steady_ptsOf`, `steady_real`: **every reader whose points are `ptsOf`, and so `theReads`, is
    steady from `pastAlpha a` on**: no hypothesis.
  `storeOk_real`: at `theReads`. Conditional on: the input is settled at a.base, and
    `pastAlpha a` rounds are among those heard when the store was made.

Hypotheses that remain.
  `hn : pastAlpha a ≤ h.length` (in the general form n ≤ h.length). h is the list as the move that
    lays the store is handed it, that round's own challenge last. Where just a.base rounds were
    heard in front of the row, hn holds with equality and that last challenge is alpha. Where more
    were heard in front, hn and the equation still hold, and what is read as alpha is not that
    move's own challenge. Where fewer were heard, hn fails. That a.base is the number of rounds in
    front is not shown here: it is the matter of whoever seats the row. Below `hn` the equation can
    fail: a store made of a shorter list is made at alpha = 0, and the earlier jobs later read the
    alpha that was sampled (Honest/K3/StoreToy.lean [not in this library], § 5, at two synthetic
    faces).
  `hw : Ask.Settled a.base w` (in the general form at n). `askOf_settled` (Honest/K3/WitLaw.lean)
    shows it at the inputs that a lot seats, under its own condition on the digits.
  `hR`: (in `storeAt_append`, `storeOk_stays`, `storeOk_laid`) `R.Steady a n`. `hx`: (in
    `storeOk_stays`) `StoreOk` at the challenges heard so far.
  `hw`, `hbn`: (in `Ask.Settled.mono`) settled at b; b ≤ n. `hi`: (in `elemAt_append`) the round has
    been heard. `hs`: (in `firstRound_shift`) the face has a shift.

Imported. Honest/K3/StoreMake.lean, Honest/K3/Law/Keep/StoreLaw.lean, Honest/K3/WitLaw.lean,
Honest/K3/LotRow.lean, Honest/K3/Parts/Index.lean (the row, stretch by stretch) and through it
Honest/K3/HeardLaw.lean.

Users. Honest/K3/Law/Keep/SameRounds.lean and Honest/K3/StoreToy.lean [not in this library] import
this file. Meant for the row with a kept state (Honest/K3/RowKeep.lean).

Limits. Nothing is said on the other points that R reads (the trees' points, JOIN's, ZERO's): the
store hangs on none of them. Nothing says that a row's moves leave the store as it is.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.StoreLaw
import Johnson.Desc.ProofFile.Honest.K3.WitLaw
import Johnson.Desc.ProofFile.Honest.K3.LotRow
import Johnson.Desc.ProofFile.Honest.K3.Parts.Index

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)

/-! ## 1 The hypothesis, and what follows from it -/

/-- **The reader of the challenges is steady from n rounds on.** A definition, meant as a
hypothesis. -/
structure Reads.Steady (R : Reads) (a : At) (n : Nat) : Prop where
  /-- the shift no longer moves -/
  theta : ∀ h more : List Fmt.Drawn, n ≤ h.length →
    (R.pts a.face a.base (h ++ more)).theta = (R.pts a.face a.base h).theta
  /-- alpha no longer moves -/
  alpha : ∀ h more : List Fmt.Drawn, n ≤ h.length →
    (R.pts a.face a.base (h ++ more)).alpha = (R.pts a.face a.base h).alpha
  /-- what the input is asked at is the list itself -/
  heard : ∀ h : List Fmt.Drawn, (R.pts a.face a.base h).heard = h

/-- An input that is settled at a number is settled at every greater one. -/
theorem Ask.Settled.mono {b n : Nat} {w : Ask} (hw : Ask.Settled b w) (hbn : b ≤ n) :
    Ask.Settled n w := fun front more h => hw front more (Nat.le_trans hbn h)

/-- **The store made of more challenges is the same store.** Conditional on `Reads.Steady`,
`Ask.Settled`, and that n rounds have been heard. -/
theorem storeAt_append {R : Reads} {a : At} {n : Nat} {w : Ask} (row : E → Nat → E)
    (hR : R.Steady a n) (hw : Ask.Settled n w) (h more : List Fmt.Drawn) (hn : n ≤ h.length) :
    storeAt R row a w (h ++ more) = storeAt R row a w h := by
  simp only [storeAt_eq, hR.heard, hR.theta h more hn, hR.alpha h more hn, hw h more hn]

/-- **`StoreOk` stays as more is heard.** Conditional on `Reads.Steady`, `Ask.Settled`, and that n
rounds have been heard. -/
theorem storeOk_stays {R : Reads} {a : At} {n : Nat} {w : Ask} (row : E → Nat → E)
    (hR : R.Steady a n) (hw : Ask.Settled n w) (h more : List Fmt.Drawn) (hn : n ≤ h.length)
    (x : Option Store) (hx : StoreOk R row a w h x) : StoreOk R row a w (h ++ more) x :=
  fun st e => (hx st e).trans (storeAt_append row hR hw h more hn).symm

/-- **The store that was made when h had been heard is right from then on.** Conditional on
`Reads.Steady`, `Ask.Settled`, and that n rounds were heard when it was made. -/
theorem storeOk_laid {R : Reads} {a : At} {n : Nat} {w : Ask} (row : E → Nat → E)
    (hR : R.Steady a n) (hw : Ask.Settled n w) (h more : List Fmt.Drawn) (hn : n ≤ h.length) :
    StoreOk R row a w (h ++ more) (some (storeAt R row a w h)) :=
  storeOk_stays row hR hw h more hn _ (storeOk_at R row a w h)

/-! ## 2 The hypothesis at the reader that is seated -/

/-- The number of the chain's rounds through the round that samples alpha. -/
def pastAlpha (a : At) : Nat := a.base + oAlpha a.face + 1

/-- A round that has been heard is read the same later. -/
theorem elemAt_append (h more : List Fmt.Drawn) (i : Nat) (hi : i < h.length) :
    elemAt (h ++ more) i = elemAt h i := by
  unfold elemAt elemsAt
  rw [List.getElem?_append_left hi]

/-- Where there is a shift, its round is the lookup's first. -/
theorem firstRound_shift (f : LFace) (hs : f.shifted = true) : firstRound f .shift = 0 := by
  obtain ⟨post, e⟩ : ∃ post, stages f = [] ++ Stage.shift :: post := by
    rw [Parts.stagesP, blkA, if_pos hs]
    exact ⟨_, rfl⟩
  exact (firstRound_split f .shift [] post e (by simp)).trans rfl

/-- Alpha's round comes behind the shift's, or is the first. -/
theorem firstRound_alpha (f : LFace) : firstRound f .alpha = oAlpha f :=
  (firstRound_split f .alpha (blkA f) _ (Parts.stagesP f) (notMem_blkA (by simp))).trans
    (sum_blkA f)

/-- The text of `ptsOf`'s shift. -/
theorem ptsOf_theta (f : LFace) (base : Nat) (h : List Fmt.Drawn) :
    (ptsOf f base h).theta = if f.shifted then elemAt h (roundAt f base .shift) else zeroE := rfl

/-- The text of its alpha. -/
theorem ptsOf_alpha (f : LFace) (base : Nat) (h : List Fmt.Drawn) :
    (ptsOf f base h).alpha = elemAt h (roundAt f base .alpha) := rfl

/-- **Every reader whose points are `ptsOf` is steady from `pastAlpha a` on.** -/
theorem steady_ptsOf (P : LFace → Stage → Pts → List E) (a : At) :
    Reads.Steady ⟨ptsOf, P⟩ a (pastAlpha a) where
  theta := fun h more hn => by
    show (ptsOf a.face a.base (h ++ more)).theta = (ptsOf a.face a.base h).theta
    rw [ptsOf_theta, ptsOf_theta]
    by_cases hs : a.face.shifted = true
    · have hi : roundAt a.face a.base .shift < h.length := by
        unfold roundAt
        rw [firstRound_shift a.face hs]
        unfold pastAlpha at hn
        omega
      rw [if_pos hs, if_pos hs, elemAt_append h more _ hi]
    · rw [if_neg hs, if_neg hs]
  alpha := fun h more hn => by
    show (ptsOf a.face a.base (h ++ more)).alpha = (ptsOf a.face a.base h).alpha
    have hi : roundAt a.face a.base .alpha < h.length := by
      unfold roundAt
      rw [firstRound_alpha a.face]
      unfold pastAlpha at hn
      omega
    rw [ptsOf_alpha, ptsOf_alpha, elemAt_append h more _ hi]
  heard := fun _ => rfl

/-- **The reader that a lot seats is steady from `pastAlpha a` on.** -/
theorem steady_real (a : At) : theReads.Steady a (pastAlpha a) := steady_ptsOf pointsAt a

/-- a.base is not beyond `pastAlpha a`. -/
theorem base_le_pastAlpha (a : At) : a.base ≤ pastAlpha a := by
  unfold pastAlpha
  omega

/-- **At the reader that a lot seats: the store that was made when h had been heard is right from
then on.** Conditional on: the input is settled at a.base; h holds alpha's own challenge, counted
from the chain's first round. -/
theorem storeOk_real (row : E → Nat → E) (a : At) (w : Ask) (hw : Ask.Settled a.base w)
    (h more : List Fmt.Drawn) (hn : pastAlpha a ≤ h.length) :
    StoreOk theReads row a w (h ++ more) (some (storeAt theReads row a w h)) :=
  storeOk_laid row (steady_real a) (hw.mono (base_le_pastAlpha a)) h more hn

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.Ask.Settled.mono
#print axioms ProofFile.Honest.K3.storeAt_append
#print axioms ProofFile.Honest.K3.storeOk_stays
#print axioms ProofFile.Honest.K3.storeOk_laid
#print axioms ProofFile.Honest.K3.elemAt_append
#print axioms ProofFile.Honest.K3.firstRound_shift
#print axioms ProofFile.Honest.K3.firstRound_alpha
#print axioms ProofFile.Honest.K3.ptsOf_theta
#print axioms ProofFile.Honest.K3.ptsOf_alpha
#print axioms ProofFile.Honest.K3.steady_ptsOf
#print axioms ProofFile.Honest.K3.steady_real
#print axioms ProofFile.Honest.K3.base_le_pastAlpha
#print axioms ProofFile.Honest.K3.storeOk_real
