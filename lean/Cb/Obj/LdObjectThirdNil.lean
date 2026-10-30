-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectThirdNil.lean: the errors of the test at one instance, in the order of the rounds,
for any bound on the bad points of the fold.

In standard terms: the round-by-round errors of the test at one instance, for any bound on the
points that are bad for a fold of the index.


Definitions, statements and proofs (an assembly).
Cb/Obj/LdObjectThirdTests.lean and Cb/Obj/LdObjectLinkAt.lean bound the points that are bad for a
fold of the index by εThird e = v (e + 1) q^(v-1) + v q^(v-1). The second summand pays for members
of the list that violate the record.



Here q = |E|, and v is the number of row variables of the index.

Main names:






  `Spec.ldT3n_lin_err`: the test's errors in the order of the rounds, for any εf, all list bounds 1,
    `Fin O.Cf.C₀.n` non-empty. (The link's, for any ε₀, ε₁: `ldT3e_link_far`,
    Cb/Obj/LdObjectLinkAt.lean.)
















Terms: lean/GLOSSARY.md.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldT3_link` or `ldT3_lin` can
   be met together. -/
import Cb.Obj.LdObjectLinkAtProofs
import Cb.Ld.LdFoldEqProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- the test's errors, for any bound on the fold's bad points. (not all hypotheses are named here:
see the statement below) -/
def ldT3n_lin_err : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (p : LdLinPl O.toC) (T : LdLinPlT p)
      (Sn : O.toC.P.Snd) (εf : ℕ) (d : O.toC.P.W0),
    (∀ a, Sn.LW a = 1) → (∀ a, Sn.LU a = 1) → (∀ a, Sn.LO a = 1) → T.L₁ = 1 → T.L₂ = 1 →
    (O.numsF Sn εf T.Q T.fq d).err.toList =
      [0, 0, O.toC.P.errPt εf, 0, 0, O.toC.P.errLoc, 0, 0, O.toC.P.errZeta] ++
        (T.Z₁.err :: T.T₁.N.err.toList ++ (T.Z₂.err :: T.T₂.N.err.toList ++ T.Q'.c.errs))

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldT3n_lin_err : Spec.ldT3n_lin_err F E := by
  intro O _ p T Sn εf d hW hU hO h1 h2
  rw [ldOErr_lin F E O _ Sn T.Q T.fq d, ldT3e_send E _ _ Sn.LW hW,
    ldT3e_send E _ _ Sn.LU hU, ldT3e_send E _ _ Sn.LO hO]
  have e1 := (ldOErr_cons E _ _ _ T.D₁ (LdTc.cons T.D₂ T.Q' T.d₂ T.d₂') T.d₁ T.d₁').1
  have e2 := (ldOErr_cons E _ _ _ T.D₂ T.Q' T.d₂ T.d₂').1
  have e3 : T.Q.c.errs =
      (T.L₁ * T.Z₁.err) :: T.T₁.N.err.toList ++
        ((T.L₂ * T.Z₂.err) :: T.T₂.N.err.toList ++ T.Q'.c.errs) :=
    e1.trans (congrArg _ e2)
  rw [e3, h1, h2, Nat.one_mul, Nat.one_mul]

end
end Cb
