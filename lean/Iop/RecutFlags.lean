-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/RecutFlags.lean: flags for pruned Merkle paths carried along a plan of splits and merges.

The flags "this round's trees have pruned sets of paths" are a list with one number for each round
(an `OpenList`; Iop/BatchWirePr.lean): 0 means whole paths, any other number pruned paths. The plan
is an `XPlan` (Iop/Recut.lean).
  `OpenList.recutF X o`: a round that stays has its old flag; both parts of a split round inherit
      its flag; a merge of two prover messages, (J1) of Iop/Join.lean, is flagged if and only if
      both rounds are (the product of the two numbers); a merge of two challenges, (J2), where the
      second round has no oracle position, has the flag of the first round
  `recutF_keepAll`: a plan that changes no round gives the same numbers (stated for `toList`,
      because the two lists of rounds are equal only by a proof)

Limits: definitions and three lemmas; nothing is proved about a scheme here. The rules "a piece
inherits its round's flag" and "a join of a flagged and an unflagged round is unflagged" are those
of the author of the pruned sets; that the second is written as a product, and the rule for (J2)
(the second round has no position, so no tree of its own), are this file's. (A piece is a part of a
split round, a join a merge.)
-/
import Iop.RecutKit
import Iop.SerS
import Iop.Sizes

set_option autoImplicit false

namespace Iop

/-- The flags after the plan is applied. -/
def OpenList.recutF : {s : Shape} → (X : XPlan s) → OpenList s → OpenList X.shape
  | _, .nil => fun _ => ()
  | _, .keep _ X => fun (o : ℕ × OpenList _) => (o.1, OpenList.recutF X o.2)
  | _, .cut (s := s) c X =>
    fun (o : ℕ × OpenList s) =>
      (o.1, OpenList.recutF X (show OpenList (c.snd :: s) from (o.1, o.2)))
  | _, .msg r1 r2 (s := s) _ X =>
    fun (o : ℕ × ℕ × OpenList s) =>
      OpenList.recutF X (show OpenList (r1.joinMsg r2 :: s) from (o.1 * o.2.1, o.2.2))
  | _, .chal r1 r2 (s := s) _ X =>
    fun (o : ℕ × ℕ × OpenList s) =>
      OpenList.recutF X (show OpenList (r1.joinChal r2 :: s) from (o.1, o.2.2))

/-- The numbers of an `OpenList`, as a list. -/
def OpenList.toList : {s : Shape} → OpenList s → List ℕ
  | [], _ => []
  | _ :: _, (n, o) => n :: OpenList.toList o

/-- A plan that changes no round changes no flag. -/
theorem OpenList.recutF_keepAll :
    ∀ (s : Shape) (o : OpenList s), (OpenList.recutF (XPlan.keepAll s) o).toList = o.toList
  | [], _ => rfl
  | _ :: s, (n, o) => congrArg (n :: ·) (OpenList.recutF_keepAll s o)

/-- Unchanged rounds before any plan have their old flags. -/
theorem OpenList.recutF_keepAll_app :
    ∀ (s : Shape) {t : Shape} (Y : XPlan t) (o : OpenList s) (o' : OpenList t),
      (OpenList.recutF (XPlan.app (XPlan.keepAll s) Y) (OpenList.app o o')).toList =
        o.toList ++ (OpenList.recutF Y o').toList
  | [], _, _, _, _ => rfl
  | _ :: s, _, Y, (n, o), o' => congrArg (n :: ·) (OpenList.recutF_keepAll_app s Y o o')

/-- No flag before the plan is applied, no flag after it. -/
theorem OpenList.recutF_zero {s : Shape} (X : XPlan s) :
    ∀ x ∈ (OpenList.recutF X (OpenList.zero s)).toList, x = 0 := by
  induction X with
  | nil => intro x hx; cases hx
  | keep r X ih =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | h
      · rfl
      · exact ih x h
  | cut c X ih =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | h
      · rfl
      · exact ih x h
  | msg r1 r2 u X ih => exact ih
  | chal r1 r2 np X ih => exact ih

end Iop
