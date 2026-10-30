-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ChainCloses.lean: the hypothesis on the rounds after the link's fifth, for any
decision whose yes gives the yes in the field.

OnBytes/Slice/LinkSound.lean states one hypothesis on the written link (the format's protocol
between two stored tables), on the rounds after the fifth, `Closes`: if the statement after
the fifth round has no witness, the prover has lost towards the written protocol's no (the library's
`Doomed`, Iop/Rbr.lean). It speaks of a list of written rounds. OnBytes/Slice/ChainSem.lean takes
these rounds off over the blocks' shapes joined. The shape of a joined list of rounds and the joined
shapes are equal, by induction on the lists. This file carries the chain along that equation.
Main definitions.
 `tailRds`    the rounds after the fifth as a list: the batching, then fold, switch, fold, switch,
              base case.
 `tailShOf`   the blocks' shapes joined.
 `joinErr`    the blocks' error counts in a row, carried to the list's shape.
 `tailTr`     a transcript of the list, from the blocks' transcripts.
Main theorems.
 `uL_tail`        the two shapes are equal.
 `tailTr_cast`    the library's joined transcript, carried to the list's shape, is `tailTr`.
 `closes_sem`     `Closes` holds for every decision whose yes, in the written protocol, gives
                  `SemAccept`. That all tests of work pass need not be asked: it is a part of the
                  written protocol's yes. Asked besides: the six blocks' statements and the two
                  properties of the record of readings, as in `chain_sem`.
 `closes_sem_at`  the same with the first stage under a name of its own.
At lists of rounds that are written out the two shapes are the same by evaluation, and `joinErr` is
then the blocks' counts in a row, unchanged. No theorem of this file says so.
Not claimed. That any decision's yes gives `SemAccept`. Nothing on the sizes of the error counts. No
theorem of this library takes `Closes` as a hypothesis; the link's soundness theorems ask `ClosesR`.
-/
import OnBytes.Slice.ChainSem
import OnBytes.Slice.ChainTop
import OnBytes.Slice.LinkSound

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

/-! ## From one shape to an equal one -/

/-- The prover has lost in a shape if it has lost in an equal shape. -/
theorem doomed_cast {s t : Shape} (h : s = t) (ε : Err t) (bad : Tr s → Prop)
    (H : Doomed t ε fun τ => bad (cast (congrArg Iop.Tr h.symm) τ)) : Doomed s (h ▸ ε) bad := by
  subst h
  exact H

/-- Joining by the list of rounds is the library's joining, also where the second part is given over
an equal shape. -/
theorem joinT_heq_app (ds₁ ds₂ : List PQ.RD) (t : Shape) (ht : PQ.uL (ckP .two) ds₂ = t)
    (τ : Tr (PQ.uL (ckP .two) ds₁)) (b : Tr (PQ.uL (ckP .two) ds₂)) (b' : Tr t) (hb : HEq b b') :
    HEq (joinT ds₁ ds₂ τ b) (Tr.app τ b') := by
  subst ht
  rw [← eq_of_heq hb]
  exact joinT_heq ds₁ ds₂ τ b

section
variable (s1 s2 : Sg) (dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB : PQ.RD)

/-- The rounds after the link's fifth, as a list. -/
abbrev tailRds : List PQ.RD :=
  dA :: (foldRds s1 dE1 dT1 ++ ([dS2, dC1] ++ (foldRds s2 dE2 dT2 ++
    ([dS3, dC2] ++ [dL, dB]))))

/-- The blocks' shapes joined. -/
abbrev tailShOf : Shape :=
  wRound dA :: (PQ.uL (ckP .two) (foldRds s1 dE1 dT1) ++ (PQ.uL (ckP .two) [dS2, dC1] ++
    (PQ.uL (ckP .two) (foldRds s2 dE2 dT2) ++ (PQ.uL (ckP .two) [dS3, dC2] ++
      PQ.uL (ckP .two) [dL, dB]))))

/-- The shape of that list is the blocks' shapes joined. -/
theorem uL_tail : PQ.uL (ckP .two) (tailRds s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB) =
    tailShOf s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB := by
  show wRound dA :: PQ.uL (ckP .two) _ = _
  rw [uL_append, uL_append, uL_append, uL_append]

/-- The error counts of these rounds: each block's own, in a row. -/
def joinErr (εa : ℕ) (εf1 : Err (PQ.uL (ckP .two) (foldRds s1 dE1 dT1)))
    (εc1 : Err (PQ.uL (ckP .two) [dS2, dC1])) (εf2 : Err (PQ.uL (ckP .two) (foldRds s2 dE2 dT2)))
    (εc2 : Err (PQ.uL (ckP .two) [dS3, dC2])) (εb : Err (PQ.uL (ckP .two) [dL, dB])) :
    Err (PQ.uL (ckP .two) (tailRds s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB)) :=
  uL_tail s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB ▸
    ((εa, Err.app εf1 (Err.app εc1 (Err.app εf2 (Err.app εc2 εb)))) :
      Err (tailShOf s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB))

/-- A transcript of these rounds, from the blocks' transcripts. -/
def tailTr (mA : (wRound dA).Msg) (cA : (wRound dA).Chal)
    (τF1 : Tr (PQ.uL (ckP .two) (foldRds s1 dE1 dT1)))
    (τC1 : Tr (PQ.uL (ckP .two) [dS2, dC1]))
    (τF2 : Tr (PQ.uL (ckP .two) (foldRds s2 dE2 dT2)))
    (τC2 : Tr (PQ.uL (ckP .two) [dS3, dC2])) (τB : Tr (PQ.uL (ckP .two) [dL, dB])) :
    Tr (PQ.uL (ckP .two) (tailRds s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB)) :=
  (mA, cA, joinT _ _ τF1 (joinT _ _ τC1 (joinT _ _ τF2 (joinT _ _ τC2 τB))))

/-- It is the library's joined transcript, carried to the list's shape. -/
theorem tailTr_cast (mA : (wRound dA).Msg) (cA : (wRound dA).Chal)
    (τF1 : Tr (PQ.uL (ckP .two) (foldRds s1 dE1 dT1)))
    (τC1 : Tr (PQ.uL (ckP .two) [dS2, dC1]))
    (τF2 : Tr (PQ.uL (ckP .two) (foldRds s2 dE2 dT2)))
    (τC2 : Tr (PQ.uL (ckP .two) [dS3, dC2])) (τB : Tr (PQ.uL (ckP .two) [dL, dB])) :
    cast (congrArg Iop.Tr (uL_tail s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB).symm)
      ((mA, cA, Tr.app τF1 (Tr.app τC1 (Tr.app τF2 (Tr.app τC2 τB)))) :
        Tr (tailShOf s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB)) =
      tailTr s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB mA cA τF1 τC1 τF2 τC2 τB := by
  refine eq_of_heq ((cast_heq _ _).trans (HEq.symm ?_))
  have h4 := joinT_heq [dS3, dC2] [dL, dB] τC2 τB
  have h3 := joinT_heq_app (foldRds s2 dE2 dT2) _ _ (uL_append _ _) τF2 _ _ h4
  have h2 := joinT_heq_app [dS2, dC1] _ _
    ((uL_append _ _).trans (congrArg _ (uL_append _ _))) τC1 _ _ h3
  have h1 := joinT_heq_app (foldRds s1 dE1 dT1) _ _
    ((uL_append _ _).trans (congrArg _ ((uL_append _ _).trans (congrArg _ (uL_append _ _)))))
    τF1 _ _ h2
  refine heq_cons ?_ mA cA _ _ h1
  rw [uL_append, uL_append, uL_append, uL_append]

end

/-! ## The hypothesis on the rounds after the fifth -/

section
variable {S : Sz} {t₀ : ℕ} {s2 s3 : Sg} {d2 dS2 dS3 dL dB : PQ.RD}
  (R : Reads S t₀ s2 s3 d2 dS2 dS3 dL dB) (hf1 : CsFit (S.sg t₀) s2) (hf2 : CsFit s2 s3)
  (d1 d3 d4 d5 dA dE1 dT1 dC1 dE2 dT2 dC2 : PQ.RD) (xs : List PQ.XO) (dec : PQ.View → Bool)

/-- The rounds after the fifth close the link (`Closes`), for any decision whose yes in the written
protocol gives the yes in the field (`hsem`). Asked besides: the six blocks' statements, and
`IsRows` and `WordTie` of the record of readings. -/
theorem closes_sem (e1 e2 e3 εa : ℕ)
    (εf1 : Err (PQ.uL (ckP .two) (foldRds (S.sg t₀) dE1 dT1)))
    (εc1 : Err (PQ.uL (ckP .two) [dS2, dC1])) (εf2 : Err (PQ.uL (ckP .two) (foldRds s2 dE2 dT2)))
    (εc2 : Err (PQ.uL (ckP .two) [dS3, dC2])) (εb : Err (PQ.uL (ckP .two) [dL, dB]))
    (hBat : BatSem S t₀ e1 d2 dA εa) (hF1 : FoldSem (S.sg t₀) R.n1 e1 dE1 dT1 εf1)
    (hC1 : CsSem hf1 e1 e2 dS2 dC1 εc1) (hF2 : FoldSem s2 R.n2 e2 dE2 dT2 εf2)
    (hC2 : CsSem hf2 e2 e3 dS3 dC2 εc2) (hB : BaseSem s3 e3 dL dB εb)
    (hrows : ∀ x, IsRows S t₀ x (R.rows x).1 (R.rows x).2)
    (hw1 : ∀ o, WordTie S t₀ d2 o (R.w1 o))
    (hsem : ∀ (y : S.lk.E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA τF1 τC1 τF2 τC2 τB,
      (written S d1 d2 d3 d4 d5 (tailRds (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB) xs
        dec).accept () y (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5,
          tailTr (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB mA cA τF1 τC1 τF2 τC2 τB) =
        true →
      SemAccept R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2
        (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 m2.1 cA τF1 τC1 τF2 τC2 τB) :
    Closes S d1 d2 d3 d4 d5 (tailRds (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB) xs dec
      (joinErr (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB εa εf1 εc1 εf2 εc2 εb) := by
  intro y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 hno
  refine doomed_cast (uL_tail (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB) _ _ ?_
  refine chain_sem_acc R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 e1 e2 e3 εa εf1 εc1 εf2 εc2 εb hBat hF1
    hC1 hF2 hC2 hB hrows hw1 (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 m2.1 hno
    (fun τ => (written S d1 d2 d3 d4 d5
      (tailRds (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB) xs dec).accept () y
      (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, cast (congrArg Iop.Tr
        (uL_tail (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB).symm) τ)) ?_
  intro mA cA τF1 τC1 τF2 τC2 τB hacc
  beta_reduce at hacc
  rw [tailTr_cast] at hacc
  refine ⟨?_, hsem y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA τF1 τC1 τF2 τC2 τB hacc⟩
  have hp : PQ.passSL (ckP .two)
      (d1 :: d2 :: d3 :: d4 :: d5 :: tailRds (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB)
      (PQ.rhoSL (ckP .two) (d1 :: d2 :: d3 :: d4 :: d5 ::
          tailRds (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB)
        (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5,
          tailTr (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB mA cA τF1 τC1 τF2 τC2 τB)) =
      true := by
    have h4 : (PQ.passSL (ckP .two) _ _ && _ && _ && _) = true := hacc
    simp only [Bool.and_eq_true] at h4
    exact h4.1.1.1
  simp only [tailTr, PQ.passSL, PQ.rhoSL, pass_joinT, Bool.and_eq_true] at hp ⊢
  tauto

/-- The same with the first stage under a name of its own. -/
theorem closes_sem_at (s1 : Sg) (h1 : S.sg t₀ = s1) (hf : CsFit s1 s2) (e1 e2 e3 εa : ℕ)
    (εf1 : Err (PQ.uL (ckP .two) (foldRds s1 dE1 dT1)))
    (εc1 : Err (PQ.uL (ckP .two) [dS2, dC1])) (εf2 : Err (PQ.uL (ckP .two) (foldRds s2 dE2 dT2)))
    (εc2 : Err (PQ.uL (ckP .two) [dS3, dC2])) (εb : Err (PQ.uL (ckP .two) [dL, dB]))
    (hBat : BatSem S t₀ e1 d2 dA εa) (hF1 : FoldSem s1 R.n1 e1 dE1 dT1 εf1)
    (hC1 : CsSem hf e1 e2 dS2 dC1 εc1) (hF2 : FoldSem s2 R.n2 e2 dE2 dT2 εf2)
    (hC2 : CsSem hf2 e2 e3 dS3 dC2 εc2) (hB : BaseSem s3 e3 dL dB εb)
    (hrows : ∀ x, IsRows S t₀ x (R.rows x).1 (R.rows x).2)
    (hw1 : ∀ o, WordTie S t₀ d2 o (R.w1 o))
    (hsem : ∀ (y : S.lk.E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA τF1 τC1 τF2 τC2 τB,
      (written S d1 d2 d3 d4 d5 (tailRds (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB) xs
        dec).accept () y (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5,
          tailTr (S.sg t₀) s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB mA cA τF1 τC1 τF2 τC2 τB) =
        true →
      SemAccept R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2
        (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 m2.1 cA τF1 τC1 τF2 τC2 τB) :
    Closes S d1 d2 d3 d4 d5 (tailRds s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB) xs dec
      (joinErr s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB εa εf1 εc1 εf2 εc2 εb) := by
  subst h1
  exact closes_sem R hf1 hf2 d1 d3 d4 d5 dA dE1 dT1 dC1 dE2 dT2 dC2 xs dec e1 e2 e3 εa εf1 εc1 εf2
    εc2 εb hBat hF1 hC1 hF2 hC2 hB hrows hw1 hsem

end

end OnBytes.Slice

#print axioms OnBytes.Slice.closes_sem
#print axioms OnBytes.Slice.closes_sem_at
