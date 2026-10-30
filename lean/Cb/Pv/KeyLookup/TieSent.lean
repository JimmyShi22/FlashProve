-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/TieSent.lean: how many scalars the prover's message in the clear holds in each round
of the draw and the fused tie (Cb/Pv/KeyLookup/TieM.lean), at the library's sumcheck and at the
short one;
and how many end values each step of the tie has. The draw and the tie together are called the head.

It imports no file of the program (OnBytes/Iop, OnBytes/Params, ...). Terms: lean/GLOSSARY.md.

Main names:
  `Tie.card0`, `Tie.cardS`: for every `D : TieF E` the index type of step 0's end values has 3
  elements, that of every later step's has 2.
  `Tie.step0_lib`, `Tie.stepS_lib`, `Tie.step0_short`, `Tie.stepS_short`: in a step's three rounds
  q, q^4, q^3 (later steps: q, q^4, q^2) messages in the clear are possible at the library's
  sumcheck, and q, q^3, q^3 (later: q, q^3, q^2) at the short one; q is the number of elements of
  the field.
  `Tie.tie_plain`: the steps 0, .., n in a row.
  `head_isS_lib`: n + 2 = pl ⇒ `IsS q (A.headK L (PscLtK.lib E Ex) n) ((lamHead q A.toPub).map id)`.
  `head_isS_short`: n + 2 = pl ⇒ `IsS q (A.headK L (SK₀ E Ex) n) ((lamHead q A.toPub).map
  LRow.short)`.
Limits: the one condition is n + 2 = pl, a public number. Not said: anything on oracle messages; the
column kind of the list of rounds, which is a name that no shape has; anything on the program.

-/
import Cb.Pv.KeyLookup.PlainLt
import Cb.Pv.KeyLookup.TieShort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn

variable {E : Type} [Field E] [Fintype E]

namespace Tie
variable (D : TieF E) (Ex : ExtSpec)

/-- Step 0 shows three values. -/
theorem card0 : Fintype.card (D.lv 0).T.par.A = 3 := rfl

/-- Every later step shows two. -/
theorem cardS (l : ℕ) : Fintype.card (D.lv (l + 1)).T.par.A = 2 := rfl

theorem step0_lib :
    plainList (D.stepK (PscLtK.lib E Ex) 0).R.shape =
      [Fintype.card E ^ 1, Fintype.card E ^ 4, Fintype.card E ^ 3] :=
  (Plain.full_lib (D.lv 0).T.par Ex).trans (by rw [card0]; rfl)

theorem stepS_lib (l : ℕ) :
    plainList (D.stepK (PscLtK.lib E Ex) (l + 1)).R.shape =
      [Fintype.card E ^ 1, Fintype.card E ^ 4, Fintype.card E ^ 2] :=
  (Plain.full_lib (D.lv (l + 1)).T.par Ex).trans (by rw [cardS]; rfl)

theorem step0_short :
    plainList (D.stepK (SK₀ E Ex) 0).R.shape =
      [Fintype.card E ^ 1, Fintype.card E ^ 3, Fintype.card E ^ 3] :=
  (Plain.full_short (D.lv 0).T.par Ex).trans (by rw [card0]; rfl)

theorem stepS_short (l : ℕ) :
    plainList (D.stepK (SK₀ E Ex) (l + 1)).R.shape =
      [Fintype.card E ^ 1, Fintype.card E ^ 3, Fintype.card E ^ 2] :=
  (Plain.full_short (D.lv (l + 1)).T.par Ex).trans (by rw [cardS]; rfl)

variable {Ex}

/-- The steps 0, .., n in a row. -/
theorem tie_plain (SK : PscLtK E Ex) (s0 s1 : List ℕ) (h0 : plainList (D.stepK SK 0).R.shape = s0)
    (hS : ∀ l, plainList (D.stepK SK (l + 1)).R.shape = s1) :
    ∀ n, plainList (D.tieK SK n).R.shape = s0 ++ (List.range n).flatMap fun _ => s1
  | 0 => by
    show plainList (D.stepK SK 0).R.shape = _
    rw [h0]
    simp
  | n + 1 => by
    show plainList ((D.tieK SK n).R.shape ++ (D.stepK SK (n + 1)).R.shape) = _
    have e : plainList ((D.tieK SK n).R.shape ++ (D.stepK SK (n + 1)).R.shape) =
        plainList (D.tieK SK n).R.shape ++ plainList (D.stepK SK (n + 1)).R.shape := List.map_append
    rw [e, tie_plain SK s0 s1 h0 hS n, hS n, List.range_succ, List.flatMap_append,
      List.append_assoc]
    simp

end Tie

/-- The head's messages in the clear. -/
theorem Tie.head_plain (A : Dat E) (L : TiePl E A.J) {Ex : ExtSpec} (SK : PscLtK E Ex)
    (s0 s1 : List ℕ)
    (h0 : plainList ((A.tie L).stepK SK 0).R.shape = s0)
    (hS : ∀ l, plainList ((A.tie L).stepK SK (l + 1)).R.shape = s1) (n : ℕ) :
    plainList (A.headK L SK n).R.shape = [1] ++ (s0 ++ (List.range n).flatMap fun _ => s1) := by
  show plainList ((A.drawK Ex).R.shape ++ ((A.tie L).tieK SK n).R.shape) = _
  have e : plainList ((A.drawK Ex).R.shape ++ ((A.tie L).tieK SK n).R.shape) =
      plainList (A.drawK Ex).R.shape ++ plainList ((A.tie L).tieK SK n).R.shape := List.map_append
  rw [e, Tie.tie_plain (A.tie L) SK s0 s1 h0 hS n]
  exact congrArg (fun t => t ++ _) (Plain.draw E A.ini Ex)

theorem head_isS_lib (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (n : ℕ) (hn : n + 2 = A.pl) :
    IsS (Fintype.card E) (A.headK L (PscLtK.lib E Ex) n)
      ((lamHead (Fintype.card E) A.toPub).map id) := by
  have hp : A.pl - 2 = n := by omega
  unfold IsS
  rw [Tie.head_plain A L _ _ _ (Tie.step0_lib (A.tie L) Ex) (Tie.stepS_lib (A.tie L) Ex) n]
  unfold lamHead
  rw [hp]
  simp [psc, List.map_flatMap]

theorem head_isS_short (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (n : ℕ) (hn : n + 2 = A.pl) :
    IsS (Fintype.card E) (A.headK L (SK₀ E Ex) n)
      ((lamHead (Fintype.card E) A.toPub).map LRow.short) := by
  have hp : A.pl - 2 = n := by omega
  unfold IsS
  rw [Tie.head_plain A L _ _ _ (Tie.step0_short (A.tie L) Ex) (Tie.stepS_short (A.tie L) Ex) n]
  unfold lamHead
  rw [hp]
  simp [psc, LRow.short, List.map_flatMap]

end Lk6

#print axioms Lk6.Tie.card0
#print axioms Lk6.Tie.cardS
#print axioms Lk6.head_isS_lib
#print axioms Lk6.head_isS_short
