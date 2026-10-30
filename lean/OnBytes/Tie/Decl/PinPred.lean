-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Decl/PinPred.lean: an algorithm over one oracle on strings with its queries at the
strings that have a property answered by a table, without asking.

OnBytes/Slice/AtSet.lean has this for a finite set of strings (`pinOn`, `over`). A bound that takes
a reading in front of the arms of the compiled verifier asks of the reading that it asks NO public
string, where the public strings are one set, fixed before the public digests are known: the strings
of the later public calls hang on the answer to the first, so that set is not finite data at one
digest. Here the set is a property. Definitions, statements and proofs; the proofs follow those of
OnBytes/Slice/AtSet.lean.

Main names:
  `overP P T g`: the oracle g with the table's values put at the strings that have P.
  `pinP P T c`: the algorithm c with its queries at such strings answered by T, without asking.
  `asksIn_pinP`: it asks no string that has P. `noCoin_pinP`, `queryBound_pinP`: no coin if c tosses
    none; it asks no more than c.
  `det_pinP`: its value under g is c's under `overP P T g`. `det_pinP_of_eq`: if T holds g's own
    values at the strings that have P, it is c's value under g.
Limits: no probability. Nothing says which strings c asks.

-/
import OnBytes.Slice.AtSet
import Rom.SigmaExits

set_option autoImplicit false

namespace OnBytes.Tie

open Rom
open _root_.Iop (Dig)

variable {lam : ℕ} {α : Type} (P : List Bool → Prop) [DecidablePred P] (T : List Bool → Dig lam)

/-- The oracle g with the table's values put at the strings that have P. -/
def overP (g : Fam (rom lam)) : Fam (rom lam) := fun _ s => if P s then T s else g () s

/-- The algorithm that answers its own queries at the strings that have P by the table, without
asking. -/
def pinP : OComp (rom lam) α → OComp (rom lam) α
  | .pure a => .pure a
  | .query () s k => if P s then pinP (k (T s)) else .query () s fun r => pinP (k r)
  | .sample n k => .sample n fun r => pinP (k r)

/-- It asks no string that has P. -/
theorem asksIn_pinP (c : OComp (rom lam) α) :
    (pinP P T c).AsksIn fun _ (s : List Bool) => ¬ P s := by
  induction c with
  | pure a => trivial
  | query o s k ih =>
    cases o
    by_cases hs : P s
    · simp only [pinP, if_pos hs]
      exact ih _
    · simp only [pinP, if_neg hs]
      exact ⟨hs, fun r => ih r⟩
  | sample n k ih => exact fun r => ih r

/-- It tosses no coin if c tosses none. -/
theorem noCoin_pinP (c : OComp (rom lam) α) (h : c.NoCoin) : (pinP P T c).NoCoin := by
  induction c with
  | pure a => trivial
  | query o s k ih =>
    cases o
    by_cases hs : P s
    · simp only [pinP, if_pos hs]
      exact ih _ (h _)
    · simp only [pinP, if_neg hs]
      exact fun r => ih r (h r)
  | sample n k _ => exact h.elim

/-- It asks no more than c. -/
theorem queryBound_pinP (c : OComp (rom lam) α) :
    ∀ t, c.QueryBound t → (pinP P T c).QueryBound t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | query o s k ih =>
    cases o
    intro t h
    cases t with
    | zero => exact h.elim
    | succ t =>
      by_cases hs : P s
      · simp only [pinP, if_pos hs]
        exact (ih _ t (h _)).mono (Nat.le_succ t)
      · simp only [pinP, if_neg hs]
        exact fun r => ih r t (h r)
  | sample n k ih => exact fun t h r => ih r t (h r)

/-- Its value under g is that of c under g with the table put over it. -/
theorem det_pinP (g : Fam (rom lam)) (c : OComp (rom lam) α) :
    (pinP P T c).det g = c.det (overP P T g) := by
  induction c with
  | pure a => rfl
  | query o s k ih =>
    cases o
    by_cases hs : P s
    · simp only [pinP, if_pos hs, OComp.det, overP]
      exact ih _
    · simp only [pinP, if_neg hs, OComp.det, overP]
      exact ih _
  | sample n k ih => simp only [pinP, OComp.det, ih]

/-- A table that holds g's own values changes nothing. -/
theorem overP_of_eq (g : Fam (rom lam)) (h : ∀ x, P x → T x = g () x) : overP P T g = g := by
  funext o s
  cases o
  unfold overP
  split
  · exact h s ‹_›
  · rfl

/-- With such a table the value under g is that of c itself. -/
theorem det_pinP_of_eq (g : Fam (rom lam)) (h : ∀ x, P x → T x = g () x)
    (c : OComp (rom lam) α) : (pinP P T c).det g = c.det g := by
  rw [det_pinP, overP_of_eq P T g h]

end OnBytes.Tie

#print axioms OnBytes.Tie.asksIn_pinP
#print axioms OnBytes.Tie.queryBound_pinP
#print axioms OnBytes.Tie.det_pinP_of_eq
