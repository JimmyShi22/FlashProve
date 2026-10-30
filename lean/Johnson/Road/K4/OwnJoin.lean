-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnJoin.lean: WHAT THE LOOKUP's JOIN AT THE TRUE SUM OF THE TERMS SAYS IN THE
LIBRARY's KEY VECTORS. Cb/Pv/Lay/At/Fore.lean and OwnW.lean name a theorem `OnBytes.Road.own_join`
"in a later file". Two theorems: the first
joins two theorems of the library; the second unfolds `Plan4.Keys` and calls one of them.

  `own_join`: at every `ForePar`, under the three conditions of `jn_iff` (Cb/Pv/Lay/At/Fore.lean)
    and D.lT ≤ D.cap: the join's gap at the true sum of the terms is 0 exactly if the sum over the
    eight calls c of the call's weight times THE MULTILINEAR EXTENSION OF THE CALL's KEY VECTOR AT
    THE CALL's POINT is what the lookup's end leaves (`kEnd`). By `jn_iff` and `ext_keyVec_KF`
    (Johnson/Road/FormsKeysVec.lean).
  `Plan4.keys_vec`: the same of `Plan4.Keys` (Johnson/Road/K4/ValueSays.lean).

Limits. Those of the two joined theorems. kEnd's letters kTg and kInc are free. An equivalence of
two equations: no draw, no count, nothing on a program.
-/
import Johnson.Road.K4.ValueSays
import Johnson.Road.FormsKeysVec

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road
open Finset Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (aC zc wc keyVec)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

/-- **The lookup's join at the true sum of the terms, in the library's key vectors.** -/
theorem own_join (P : ForePar E M X) (C : P.D.ChOK)
    (hk : ∀ l, l < P.D.nl →
      (P.D.Pl l).kq = (P.D.Pl l).kk ∨ (16 ≤ (P.D.Pl l).kq ∧ 16 ≤ (P.D.Pl l).kk))
    (hf : P.D.f = 2 * P.D.fe) (hcap : P.D.lT ≤ P.D.cap) (x : X) (m : M) :
    P.jg x (P.tS x m) m = 0 ↔
      ∑ c, wc P.D (P.zOf x) c * Blocks.ext (aC P.D c)
          (keyVec P.D (P.rd (P.msg m)) P.tb P.L0 (P.rw (P.msg m)) c) (zc P.D (P.zOf x) c) =
        P.kEnd x m := by
  rw [P.jn_iff C hk hf x m]
  simp only [ext_keyVec_KF P.D (P.rd (P.msg m)) P.tb P.L0 (P.rw (P.msg m)) hcap]

namespace K4

/-- The same of the value's `Keys`. -/
theorem Plan4.keys_vec (Q : Plan4 E M X) (hcap : Q.D.lT ≤ Q.D.cap) (x : X) (m : M) :
    Q.Keys x m ↔
      ∑ c, wc Q.D (Q.zOf x) c * Blocks.ext (aC Q.D c)
          (keyVec Q.D (Q.cells m) Q.tb Q.L0 (Q.weights m) c) (zc Q.D (Q.zOf x) c) =
        Q.kTg x - ∑ s : Fin (Q.ns + 1), Q.kIncS x s * Q.maskAt m s := by
  unfold Plan4.Keys
  simp only [ext_keyVec_KF Q.D (Q.cells m) Q.tb Q.L0 (Q.weights m) hcap]

end K4
end OnBytes.Road

#print axioms OnBytes.Road.own_join
#print axioms OnBytes.Road.K4.Plan4.keys_vec
