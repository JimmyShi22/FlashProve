-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/HotLaw.lean: each definition of Honest/K3/Hot.lean is the
definition whose text it copies; where the copied text has no name, it is that term, typed anew
here. Theorems without a hypothesis.

Terms. Honest/K3/GLOSSARY.md.

What is shown. As functions:
  `at0_eq`, `bindAt_eq`, `coord_eq`: `Hot.at0` is `Fast.at0`; the like of `bindAt` and `coord`.
  `pos_eq`: `Hot.pos` at a cube's free bits is `Fast.Cube.pos`.
  `leafTab_eq`, `lessOne_eq`, `halves_eq`: these three unfold to the terms that stand, without a
    name, in `Fast.storeOf`, in `bitsKeep`'s start and in `keyKeep`'s and `tabKeep`'s. That the
    terms stand there is not said by these three equations: it is said first in
    Honest/K3/RowKeepHot.lean (`hotStoreOf_eq`, `keyKeepHot_eq`, `tabKeepHot_eq`, `bitsKeepHot_eq`).
  `round_eq`: `Hot.round` is `Fast.keptRound`.
  `bind_eq`: `Hot.bind` is `Fast.keptBind`.
  `up_eq`, `lvlsFrom_eq`, `lvlsUp_eq`: `Hot.up` is `Fast.up`; the like of `lvlsFrom` and `lvlsUp`.
  `bitTab_eq`, `facTab_eq`, `keyLeaves_eq`: at the input's own readers `Hot.bitTab`, `Hot.facTab`
    and `Hot.keyLeaves` are the two tables of `Fast.srcOf` and the lowest level of a part's key
    tree.
All by `rfl` but `lvlsFrom_at`, by induction on the number of levels; `lvlsFrom_eq` and `lvlsUp_eq`,
by that one; and `keyLeaves_eq`, where v - v is rewritten to 0.

Imported. Honest/K3/Hot.lean; Honest/K3/JobsKeep.lean and Honest/K3/StoreMake.lean, and through
these two the frame's files.

Users. Honest/K3/RowKeepHot.lean.

Limits. Equations of functions: nothing is said on how long either side takes.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Hot
import Johnson.Desc.ProofFile.Honest.K3.JobsKeep
import Johnson.Desc.ProofFile.Honest.K3.StoreMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Hot
open OnBytes (E addE subE mulE oneE)

theorem at0_eq : at0 = Fast.at0 := rfl

theorem bindAt_eq : bindAt = Fast.bindAt := rfl

theorem coord_eq : coord = Fast.coord := rfl

theorem pos_eq (c : Fast.Cube) (b : Nat) : pos c.free b = c.pos b := rfl

theorem leafTab_eq (b a : Array E) :
    leafTab b a = Array.zipWith (fun b a => addE oneE (mulE b a)) b a := rfl

theorem lessOne_eq (b : Array E) : lessOne b = b.map fun x => subE x oneE := rfl

theorem halves_eq (m : Nat) (n : Array E) :
    halves m n = [n.extract 0 (2 ^ m), n.extract (2 ^ m) (2 ^ (m + 1))] := rfl

/-- `Hot.round` is `Fast.keptRound`. -/
theorem round_eq : round = Fast.keptRound := rfl

/-- `Hot.bind` is `Fast.keptBind`. -/
theorem bind_eq : bind = Fast.keptBind := rfl

theorem up_eq : up = Fast.up := rfl

theorem lvlsFrom_at : ∀ (n : Nat) (a : Array E) (acc : List (Array E)),
    lvlsFrom n a acc = Fast.lvlsFrom n a acc
  | 0, _, _ => rfl
  | n + 1, a, acc => lvlsFrom_at n (up a) (a :: acc)

theorem lvlsFrom_eq : lvlsFrom = Fast.lvlsFrom :=
  funext fun n => funext fun a => funext fun acc => lvlsFrom_at n a acc

/-- `Hot.lvlsUp` is `Fast.lvlsUp`. -/
theorem lvlsUp_eq : lvlsUp = Fast.lvlsUp :=
  funext fun n => funext fun a => congrArg List.toArray (lvlsFrom_at n a [])

/-- The bits' table of `Fast.srcOf`. -/
theorem bitTab_eq (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) :
    bitTab f.mu f.d f.planes w.bit = (Fast.srcOf f row w theta alpha).bitTab () := rfl

/-- The factors' table of `Fast.srcOf`. -/
theorem facTab_eq (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) :
    facTab f.mu f.d alpha (row theta) = (Fast.srcOf f row w theta alpha).facTab () := rfl

/-- The lowest level of part i's key tree. -/
theorem keyLeaves_eq (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) (i : Nat) :
    keyLeaves alpha (f.parts.getD i 0) (w.key theta i) =
      (Fast.srcOf f row w theta alpha).keyLvl i (f.parts.getD i 0) := by
  show _ = Fast.upN (f.parts.getD i 0 - f.parts.getD i 0) _
  rw [Nat.sub_self]
  rfl

end ProofFile.Honest.K3.Hot

#print axioms ProofFile.Honest.K3.Hot.pos_eq
#print axioms ProofFile.Honest.K3.Hot.leafTab_eq
#print axioms ProofFile.Honest.K3.Hot.lessOne_eq
#print axioms ProofFile.Honest.K3.Hot.halves_eq
#print axioms ProofFile.Honest.K3.Hot.bitTab_eq
#print axioms ProofFile.Honest.K3.Hot.facTab_eq
#print axioms ProofFile.Honest.K3.Hot.keyLeaves_eq
#print axioms ProofFile.Honest.K3.Hot.at0_eq
#print axioms ProofFile.Honest.K3.Hot.bindAt_eq
#print axioms ProofFile.Honest.K3.Hot.coord_eq
#print axioms ProofFile.Honest.K3.Hot.round_eq
#print axioms ProofFile.Honest.K3.Hot.bind_eq
#print axioms ProofFile.Honest.K3.Hot.up_eq
#print axioms ProofFile.Honest.K3.Hot.lvlsFrom_at
#print axioms ProofFile.Honest.K3.Hot.lvlsFrom_eq
#print axioms ProofFile.Honest.K3.Hot.lvlsUp_eq
