-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdZeroPsc.lean: a step into a sumcheck, then the sumcheck.

In standard terms: sequential composition of two interactive oracle reductions: one verifier message
that combines many claims into one sumcheck claim, then the sumcheck for that claim.

Definitions, statements and proofs: the step of Cb/Ld/LdZero.lean (claims on values into one sum
claim; the zerocheck) followed by the zero-knowledge sumcheck for a polynomial summand
(Cb/Ld/LdPsc.lean), over a signature of oracle messages with samples (Cb/Ld/LdSig.lean).

Main names:
  `PscIn.chain`, `PscIn.chainH`, `PscIn.chainN`: the two blocks in a row (`IOR.seq`), the honest
    side, the numbers: the step's one error, then 1, the degrees of the k variables, `Z.T.DY`, 0.
  `Spec.pscIn_psc`: under `Z.Link`, `Z.Back`, `Z.ev.OK`, `Z.T.VarsOK`, `Z.T.DegX`, `Z.T.DegY` and
    `Z.T.ValInj`: from S.over (all claims, and R0) to S.over (the sumcheck's output rows, and R0):
    all of `IOR.GoodT` but zero knowledge (`IOR.GoodB`); the extractor is the identity. (R0: any
    `IOR.Rels`, a binder of the statement; `Sig.over`, Cb/Ld/LdSig.lean; `PscIn.ride`,
    Cb/Ld/LdZero.lean)
  `Spec.ldZero_psc`: under `Z.co.OK`, `Z.next.DegX` and `Z.next.DegY`: the zerocheck on the cube,
    then the sumcheck: `IOR.GoodB` from "every function vanishes at every corner" to the output
    rows.
  `Spec.pscIn_psc_len`: the number of rounds: 1 + (k + 3), k = `Z.T.fmt.length`; nothing is merged.

`GoodB` is `IOR.GoodT` without its clause on zero knowledge. `IOR.GoodT` (likewise `IOR.Good`,
Ior/Chain.lean) bundles what is asked of one reduction, with its honest side, between two joints, at
given numbers; among its clauses: completeness between the honest relations, outside sets of
verifier randomness whose probabilities further clauses bound by the numbers; round-by-round
knowledge soundness (`Know`) between the relaxed relations, on the input joint's set of statements,
with a given extractor, at the numbers' list of errors; and one on honest-verifier zero knowledge.
Here `GoodB` is the conclusion of `Spec.pscIn_psc` and of `Spec.ldZero_psc`.

Limits: on zero knowledge the statements of this file say nothing: `Spec.pscIn_psc` and
`Spec.ldZero_psc` conclude `IOR.GoodB` (all of `IOR.GoodT` but zero knowledge), `Spec.pscIn_psc_len`
a number of rounds. In other files: the step has nothing to simulate (Cb/Ld/LdZeroAt.lean:
`draw_exact_any`); under the hypotheses of its statement, the sumcheck has the item "masked
messages" (Cb/Ld/LdPscZk.lean: `Spec.psc_our_mm`); under the hypotheses of its statement, a draw
followed by a masked block is a masked block (Ior/MaskedDraw.lean: `Spec.mm_draw_seq`).
The degrees of the summand stay hypotheses (`PscOur.DegX`, `PscOur.DegY`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdZeroProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

namespace PscIn
variable {E : Type} [Field E] [Fintype E] (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec)

/-- The step, then the sumcheck. -/
def chain : IOR (Z.St0 × S.Smp) (E₀.prod S.ext) (Z.T.par.Out × S.Smp) (E₀.prod S.ext) :=
  (IOR.draw Z.ev.D (S.drawNx Z.nxX) (E₀.prod S.ext)).seq ((Z.T.par.psc E₀).keep S.Smp S.ext)
def chainH (Wp : Type) (msg : S.Msg → Z.T.J → E) :
    (Z.chain S E₀).Honest (S.Wit × Wp) (S.Wit × Wp) :=
  (IOR.Honest.draw Z.ev.D (S.drawNx Z.nxX) (E₀.prod S.ext) (S.Wit × Wp)).seq
    (S.liftH (Z.T.par.hon E₀ fun w : S.Msg × Wp => msg w.1))
def chainN (Kc : Type) : IOR.Nums Kc (Z.chain S E₀) :=
  (IOR.Nums.draw Kc Z.ev.D (S.drawNx Z.nxX) (E₀.prod S.ext) Z.ev.err).seq
    ((Z.T.par.nums E₀ Kc).keep S.Smp S.ext)

end PscIn

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

def pscIn_psc : Prop :=
  ∀ (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type)
      (R0 : Rels Kc Z.St0 E₀ (S.Msg × Wp)) (msg : S.Msg → Z.T.J → E),
    Z.Link → Z.Back → Z.ev.OK → Z.T.VarsOK → Z.T.DegX → Z.T.DegY → Z.T.ValInj →
    GoodB (Z.chain S E₀) (Z.chainH S E₀ Wp msg) (S.over (Z.relsIn R0 msg))
      (S.over (Z.T.par.baseOut (Z.ride R0) fun w => msg w.1)) (fun _ _ w => w) (Z.chainN S E₀ Kc)

def ldZero_psc : Prop :=
  ∀ (Z : ZeroCube E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type)
      (R0 : Rels Kc Z.St E₀ (S.Msg × Wp)) (msg : S.Msg → Z.J → E),
    Z.co.OK → Z.next.DegX → Z.next.DegY →
    GoodB (Z.toIn.chain S E₀) (Z.toIn.chainH S E₀ Wp msg)
      (S.over ⟨fun st y w => R0.rel st y w ∧ Z.ZeroHolds st (msg w.1),
        fun a w => R0.relR a w ∧ Z.ZeroHolds a.1 (msg w.1),
        R0.on, R0.core⟩)
      (S.over (Z.next.par.baseOut (Z.toIn.ride R0) fun w => msg w.1))
      (fun _ _ w => w) (Z.toIn.chainN S E₀ Kc)

def pscIn_psc_len : Prop :=
  ∀ (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec), (Z.chain S E₀).shape.length = 1 + (Z.T.fmt.length + 3)

end Spec

section Proofs
variable (E : Type) [Field E] [Fintype E]

theorem pscIn_psc : Spec.pscIn_psc E := by
  intro Z S E₀ Wp Kc R0 msg hL hB hOK hV hX hY hI
  have h1 := (pscIn_piece E Z S E₀ Wp Kc R0 msg (fun _ => True) hL hB hOK).good
  have h1' :=
    ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 (goodT_of_good _ _ _ _ _ _ _ _ _ _ _ _ _ h1)).1
  have h2 := psc_our_goodB_true E S Z.T E₀ Wp Kc (Z.ride R0) msg hV hX hY hI
  exact goodB_seq_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ w => w)
    _ _ h1' h2 fun _ _ _ _ _ _ => rfl

theorem ldZero_psc : Spec.ldZero_psc E := by
  intro Z S E₀ Wp Kc R0 msg hco hX hY
  have e : Z.toIn.AllHold = Z.ZeroHolds :=
    funext fun st => funext fun m => propext (ldZero_all E Z st m)
  have h := pscIn_psc E Z.toIn S E₀ Wp Kc R0 msg (ldZero_link E Z) (ldZero_back E Z)
    (ldZero_ok E Z hco) (ldZero_vars E Z).1 hX hY (ldZero_vars E Z).2
  unfold PscIn.relsIn at h
  rw [e] at h
  exact h

theorem pscIn_psc_len : Spec.pscIn_psc_len E := fun Z S E₀ => by
  show ([IOR.drawRound Z.ev.D] ++ (Z.T.par.psc E₀).shape).length = _
  rw [List.length_append, psc_our_len E Z.T E₀]
  rfl

end Proofs
end
end Cb
