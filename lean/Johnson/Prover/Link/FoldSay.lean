-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FoldSay.lean: WHAT A PROVER SHOWS IN A FOLD's ROUNDS, AS ROUNDS OF A VIEW, from
the draws as a function of the round's number. Definitions, statements and proofs. It writes what
fold_V (Johnson/Prover/Link/FoldHolds.lean) asks of the rounds, and shows that it is met, and that
each round's items hang on earlier draws alone.

  drawnE d       the first element that a round drew, read in the field; at an empty list the
                 field's 0. In this folder three more definitions have the same default: drawnOf
                 (FormFold.lean), pointW (TabOf.lean), lastOut (BodyAll.lean).
                 That the four are one value, and which: drawnE_empty, drawnE_zero, readE_drawnOf
                 (DrawnLaw.lean); pointW_drawnOf, toE_headD (DrawnMore.lean)
  (ptK k f       the point with the coordinates f 0, ..., f (k - 1): the library's,
                 OnBytes/Slice/SimFold.lean)
  showRV k q D   k rounds: round i shows the coefficients 0 and 2 of its part of q, written, and
                 drew D i
  foldRV s v μ W D   "FOLD epsilon" (shows the sum hMu W; drew D 0), then the s.h + s.g rounds
                 "FOLD round" of foldQ s v μ W at the drawn coefficient and the drawn point
  length_showRV, length_foldRV
  shows_showRV   Shows k (showRV k q D) q (the drawn point)
  foldRV_sigma, foldRV_shows   fold_V's two premises on the rounds, at foldRV's head and tail
  showRV_vals    a round's items at two lists of draws that agree in front of it are the same, for
                 a family q that is causal (SCausal, Cb/Ld/LdSumRun.lean)
  foldRV_vals    so for foldRV (by foldQ_causal)

Not shown here. Nothing on a decision. Nothing on how W is chosen; nothing on soundness; nothing
on what any value that is sent discloses or does not disclose of μ or W.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FoldHolds
import OnBytes.Slice.SimFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The first element that a round drew, read in the field. AT AN EMPTY LIST: (0, 0, 0), the field's
0: the value that a round which drew the element 0 gives. Nothing here tests that the list is not
empty. -/
def drawnE (d : Fmt.Drawn) : GE := readE (E.ofTriple (d.elems.headD (0, 0, 0)))

def showRV : (k : ℕ) → (RIdx (sVars GE 2 k) → GE) → (ℕ → Fmt.Drawn) → List Fmt.RoundView
  | 0, _, _ => []
  | k + 1, q, D =>
    ⟨[.e (ofE (q (Sum.inl (0 : Fin 3)))), .e (ofE (q (Sum.inl (2 : Fin 3))))], D 0⟩ ::
      showRV k (fun i => q (Sum.inr i)) fun n => D (n + 1)

theorem length_showRV : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    (showRV k q D).length = k
  | 0, _, _ => rfl
  | k + 1, _, _ => congrArg (· + 1) (length_showRV k _ _)

theorem shows_showRV : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    Shows k (showRV k q D) q (ptK k fun n => drawnE (D n))
  | 0, _, _ => trivial
  | k + 1, q, D =>
    ⟨(sent_written _ _ _ rfl).1, (sent_written _ _ _ rfl).2, rfl,
      shows_showRV k (fun i => q (Sum.inr i)) fun n => D (n + 1)⟩

/-- **A fold's rounds.** -/
def foldRV (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) : List Fmt.RoundView :=
  ⟨[.e (ofE (hMu (sVars GE 2 (s.h + s.g)) W))], D 0⟩ ::
    showRV (s.h + s.g)
      (foldQ s v μ W (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1))))
      fun n => D (n + 1)

theorem length_foldRV (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) : (foldRV s v μ W D).length = 1 + (s.h + s.g) := by
  show (showRV _ _ _).length + 1 = _
  rw [length_showRV, Nat.add_comm]

theorem foldRV_sigma (s : Sg) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (d : Fmt.Drawn) :
    readE ((sentOf ⟨[.e (ofE (hMu (sVars GE 2 (s.h + s.g)) W))], d⟩).getD 0 zeroE) =
      hMu (sVars GE 2 (s.h + s.g)) W :=
  sent_written_one _ _ rfl

theorem foldRV_shows (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) :
    Shows (s.h + s.g) (foldRV s v μ W D).tail
      (foldQ s v μ W (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1))))
      (ptK (s.h + s.g) fun n => drawnE (D (n + 1))) :=
  shows_showRV _ _ _

/-- A round's items hang on the draws in front of it alone. -/
theorem showRV_vals : ∀ (k : ℕ) (q : HPt (sVars GE 2 k) → RIdx (sVars GE 2 k) → GE),
    SCausal 2 k q → ∀ (D D' : ℕ → Fmt.Drawn) (i : ℕ), (∀ j, j < i → D j = D' j) →
      ((showRV k (q (ptK k fun n => drawnE (D n))) D).getD i ⟨[], D i⟩).vals =
        ((showRV k (q (ptK k fun n => drawnE (D' n))) D').getD i ⟨[], D' i⟩).vals
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, q, hq, D, D', 0, _ => by
    show [Fmt.ItemValue.e (ofE (q _ (Sum.inl 0))), .e (ofE (q _ (Sum.inl 2)))] =
      [Fmt.ItemValue.e (ofE (q _ (Sum.inl 0))), .e (ofE (q _ (Sum.inl 2)))]
    rw [hq.1 _ (ptK (k + 1) fun n => drawnE (D' n)) 0,
      hq.1 _ (ptK (k + 1) fun n => drawnE (D' n)) 2]
  | k + 1, q, hq, D, D', i + 1, h => by
    have h0 : D 0 = D' 0 := h 0 (Nat.succ_pos i)
    have ih := showRV_vals k (fun γ j => q (drawnE (D 0), γ) (Sum.inr j)) (hq.2 _)
      (fun n => D (n + 1)) (fun n => D' (n + 1)) i fun j hj => h (j + 1) (Nat.succ_lt_succ hj)
    show ((showRV k (fun j => q (drawnE (D 0), ptK k fun n => drawnE (D (n + 1))) (Sum.inr j))
      fun n => D (n + 1)).getD i _).vals =
      ((showRV k (fun j => q (drawnE (D' 0), ptK k fun n => drawnE (D' (n + 1))) (Sum.inr j))
        fun n => D' (n + 1)).getD i _).vals
    rw [← h0]
    exact ih

/-- The same for a fold's rounds. -/
theorem foldRV_vals (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D D' : ℕ → Fmt.Drawn) (i : ℕ) (h : ∀ j, j < i → D j = D' j) :
    ((foldRV s v μ W D).getD i ⟨[], D i⟩).vals = ((foldRV s v μ W D').getD i ⟨[], D' i⟩).vals := by
  cases i with
  | zero => rfl
  | succ i =>
    have h0 : D 0 = D' 0 := h 0 (Nat.succ_pos i)
    have ih := showRV_vals (s.h + s.g) (foldQ s v μ W (drawnE (D 0))) (foldQ_causal s v μ W _)
      (fun n => D (n + 1)) (fun n => D' (n + 1)) i fun j hj => h (j + 1) (Nat.succ_lt_succ hj)
    show ((showRV (s.h + s.g) (foldQ s v μ W (drawnE (D 0)) _) fun n => D (n + 1)).getD i _).vals =
      ((showRV (s.h + s.g) (foldQ s v μ W (drawnE (D' 0)) _) fun n => D' (n + 1)).getD i _).vals
    rw [← h0]
    exact ih

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.foldRV_vals
#print axioms Johnson.Prover.Link.length_showRV
#print axioms Johnson.Prover.Link.shows_showRV
#print axioms Johnson.Prover.Link.length_foldRV
#print axioms Johnson.Prover.Link.foldRV_sigma
#print axioms Johnson.Prover.Link.foldRV_shows
#print axioms Johnson.Prover.Link.showRV_vals
