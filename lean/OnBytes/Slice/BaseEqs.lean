-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BaseEqs.lean: the decision of the library's base case at a stage of single rows, as
three plain equations in the field.

OnBytes/Slice/Base.lean takes the last two rounds of the written proximity test off, towards any
goal that holds wherever the library's decision `Cb.LdwAccept` fails. An implementation of the
verifier's last step, whichever it is, has to be shown to imply that decision. This file brings the
decision to the three equations that such an implementation tests, with none of the library's
parameters in them but the claim's vector and the two words:
 - the claim's vector on the two shown messages gives the masking word's target plus mu times the
   claim's target;
 - at every listed position the shown main message and tail, evaluated at the position's point, give
   the masking word's main symbol plus mu times the word's;
 - the shown mask message and tail, evaluated at the point of the position modulo the mask code's
   length, give the masking word's mask symbol at the position itself plus mu times the word's.
The head of OnBytes/Slice/Base.lean explains the words written and taken off.

Main definitions.
 `polyV`     the value, at the point of a position, of the polynomial whose coefficients are a
             tail's and then a message's entries; message and tail are functions of the index.
 `shownOf`   two messages and two tails as what the library's prover shows in full.
Main theorems: `polyV_enc` (it is the library's encoder), `accept_of_eqs`.
Not claimed. The converse. Nothing on a stage with more than one main row or mask row.
-/
import OnBytes.Slice.Base

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- The value, at the point of position x, of the polynomial whose coefficients are the r entries of
the tail R and then the l entries of the message M. -/
def polyV (C : Fmt.M1.Code) (x : ℕ) (M R : ℕ → GE) : GE :=
  (∑ q ∈ Finset.range C.r, algebraMap GF GE (toF (Fmt.M1.point C.a x) ^ q) * R q) +
    ∑ j ∈ Finset.range C.l, algebraMap GF GE (toF (Fmt.M1.point C.a x) ^ (C.r + j)) * M j

/-- The closed form of a symbol of the format is this value at the lists' entries. -/
theorem symV_eq_polyV (C : Fmt.M1.Code) (x : ℕ) (m rho : List Fmt.M1.E) :
    symV C x m rho = polyV C x (lst m) (lst rho) := rfl

/-- `polyV` is the library's encoder. -/
theorem polyV_enc (C : Fmt.M1.Code) (x : Fin (2 ^ C.a)) (M R : ℕ → GE) :
    polyV C x.val M R = (ldOf C C.a).enc (fun j => M j.val) (fun q => R q.val) x () := by
  unfold polyV
  rw [← Fin.sum_univ_eq_sum_range
      (fun q => algebraMap GF GE (toF (Fmt.M1.point C.a x.val) ^ q) * R q) C.r,
    ← Fin.sum_univ_eq_sum_range
      (fun j => algebraMap GF GE (toF (Fmt.M1.point C.a x.val) ^ (C.r + j)) * M j) C.l]
  rfl

/-- Two messages and two tails, given as functions of the index, as what the prover shows in full:
each row of a table the same. -/
def shownOf (s : Sg) (M0 M1 R0 R1 : ℕ → GE) : s.cIn.MR :=
  (Sum.elim (fun x => M0 x.2.val) (fun x => M1 x.2.val),
    Sum.elim (fun x => R0 x.2.val) (fun x => R1 x.2.val))

/-- What is shown as lists of words is `shownOf` at the lists' entries. -/
theorem shown_eq (s : Sg) (M0 M1 R0 R1 : List Fmt.M1.E) :
    shown s M0 M1 R0 R1 = shownOf s (lst M0) (lst M1) (lst R0) (lst R1) := rfl

/-- A cube without variables has one vertex. -/
theorem row0 {k : ℕ} (hk : k = 0) (b : Fin k → Bool) : b = fun _ => false := by
  subst hk
  exact funext fun i => i.elim0

/-- Three equations in the field give the library's decision, at a stage whose two tables have one
row each. x is the claim, f the word, g the masking word, u its target, μ the drawn element. -/
theorem accept_of_eqs (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (x : GE × (s.cIn.J → GE))
    (f g : s.cIn.Word) (u μ : GE) (M0 M1 R0 R1 : ℕ → GE) (Q : Fin s.t → s.Ps)
    (hlin : (∑ j : Fin s.C.l, x.2 (.inl (fun _ => false, j)) * M0 j.val) +
      (∑ j : Fin s.Z.l, x.2 (.inr (fun _ => false, j)) * M1 j.val) = u + μ * x.1)
    (hmain : ∀ i, polyV s.C (Q i).val M0 R0 =
      g (.inl (Q i)) (fun _ => false, ()) + μ * f (.inl (Q i)) (fun _ => false, ()))
    (hmask : ∀ i, polyV s.Z (posIn s.Z (Q i)).val M1 R1 =
      g (.inr (Q i)) (fun _ => false, ()) + μ * f (.inr (Q i)) (fun _ => false, ())) :
    LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) x) x.1 (s.cIn.T f)
      (s.cIn.T g) u μ (shownOf s M0 M1 R0 R1) Q := by
  have hk : s.h + s.g = 0 := by omega
  refine ⟨?_, fun i => ?_⟩
  · refine Eq.trans ?_ hlin
    show ∑ j : s.cIn.J, x.2 j * (shownOf s M0 M1 R0 R1).1 j = _
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type, sum_rows0 hk,
      sum_rows0 h0]
    rfl
  · funext α
    rcases α with ⟨b, ⟨⟩⟩ | ⟨b, ⟨⟩⟩
    · have hpc : posIn s.C (Q i) = Q i := Fin.ext (Nat.mod_eq_of_lt (Q i).isLt)
      show (ldOf s.C s.C.a).enc (fun j => M0 j.val) (fun q => R0 q.val) (posIn s.C (Q i)) () =
        g (.inl (posIn s.C (Q i))) (b, ()) + μ * f (.inl (posIn s.C (Q i))) (b, ())
      rw [hpc, ← polyV_enc, hmain i, row0 hk b]
    · show (ldOf s.Z s.Z.a).enc (fun j => M1 j.val) (fun q => R1 q.val) (posIn s.Z (Q i)) () =
        g (.inr (Q i)) (b, ()) + μ * f (.inr (Q i)) (b, ())
      rw [← polyV_enc, hmask i, row0 h0 b]

end OnBytes.Slice

#print axioms OnBytes.Slice.polyV_enc
#print axioms OnBytes.Slice.accept_of_eqs
