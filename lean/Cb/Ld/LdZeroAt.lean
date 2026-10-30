-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdZeroAt.lean: the step into a sumcheck, and the zerocheck, at the base: for each fixed tuple
of messages. Statements and proofs.

In standard terms: the one-round step of Cb/Ld/LdZero.lean, in which the verifier's seed turns many
claims into one sumcheck claim, and the zerocheck, stated with the messages as a part of the witness
and not as oracles.

Why: Cb/Ld/LdZero.lean states the step (claims on values into one sum claim) over a signature of
oracle messages. The lifting rules (Cb/Ld/LdSigLift.lean; for statements with an encoded index,
Cb/Ld/LdWfIdx.lean) take a block at the base, where a tuple of any type M is a part of the witness,
in the bundle `GoodAt`. Here is the step in that form.
`Cb.GoodAt` asks, of a reduction with its honest side between two joints whose witnesses pair a
value of one type M with a further witness, the clauses of `GoodB` with two differences: a further
clause `same` asks that, on every run, the honest prover's output witness carries the M-part of its
input witness unchanged; and the clause `know`, in place of `GoodB`'s, asks, for each fixed m of
type M, round-by-round knowledge soundness (`Know`) on the input joint's set of statements and at
the numbers' list of errors, as `GoodB`'s does, but between the relaxed relations at (m, ·) and with
the extractor `ext m`. `GoodB` is `IOR.GoodT` without its clause on zero knowledge. `IOR.GoodT`
(likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its honest side,
between two joints, at given numbers; among its clauses: completeness between the honest relations,
outside sets of verifier randomness whose probabilities further clauses bound by the numbers;
round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input joint's set
of statements, with a given extractor, at the numbers' list of errors; and one on honest-verifier
zero knowledge. In this file `GoodAt` is what `Spec.pscIn_goodAt` and `Spec.ldZero_goodAt` conclude.

Main names:
  `Spec.pscIn_goodAt`: here T is `Z.T`, the sumcheck that follows; R0 is any joint carried along; ev
    is `Z.ev`, the evader; the names in brackets are fields of `GoodAt` (Cb/Ld/LdSigLift.lean).
    Under `Z.Link`, `Z.Back`, `Z.ev.OK`, `IOR.draw` of the evader's seed leads from (all claims, and
    R0) to (T's true sum claim, and R0): strings (`point`); local (`isLocal`); perfectly complete
    (`acc`); the condition handed on (`onOut`); the field `keeps`; the tuple kept (`same`); nothing
    withheld, in this sense: `prBad`, `cover`, `prCov` at `pBad` = 0, `pHid` = 0 (`Nums.draw`,
    Ior/Draw.lean); knowledge sound for each fixed tuple with the one error ev.err and the identity
    as extractor (`know`).
  `Spec.pscIn_exact`: nothing is sent, so there is nothing to simulate: honest-verifier zero
    knowledge in the exact form, at every budget (`Honest.Exact`, Ior/Honest.lean).
  `Spec.ldZero_goodAt` (under `Z.co.OK`), `Spec.ldZero_exact`: the zerocheck on the cube.

Notation: `Z.Link`: the new claim is a sum claim (`PscIn.Link`, Cb/Ld/LdZero.lean); `Z.Back`:
`Z.old (Z.nx st β) = st` for all st and β (`PscIn.Back`, Cb/Ld/LdZero.lean); `Z.ev.OK`, `Z.co.OK`:
the property of a zero-evader: a vector other than 0 is annihilated by at most err seeds
(`Evader.OK`, Cb/Gen/BatEvader.lean).

Limits: what the head of Cb/Ld/LdZero.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdZeroProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

def pscIn_goodAt : Prop :=
  ∀ (Z : PscIn E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc Z.St0 Ex (M × Wp)) (msg : M → Z.T.J → E),
    Z.Link → Z.Back → Z.ev.OK →
    GoodAt (IOR.draw Z.ev.D Z.nxX Ex) (Honest.draw Z.ev.D Z.nxX Ex (M × Wp)) (Z.relsIn R0 msg)
      (Z.relsOut R0 msg) (fun _ _ _ wp => wp) (Nums.draw Kc Z.ev.D Z.nxX Ex Z.ev.err)

def pscIn_exact : Prop :=
  ∀ (Z : PscIn E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc Z.St0 Ex (M × Wp)) (msg : M → Z.T.J → E),
    (Honest.draw Z.ev.D Z.nxX Ex (M × Wp)).Exact (Z.relsIn R0 msg).rel fun _ _ => True

def ldZero_goodAt : Prop :=
  ∀ (Z : ZeroCube E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc Z.St Ex (M × Wp)) (msg : M → Z.J → E),
    Z.co.OK →
    GoodAt (IOR.draw Z.toIn.ev.D Z.toIn.nxX Ex) (Honest.draw Z.toIn.ev.D Z.toIn.nxX Ex (M × Wp))
      ⟨fun st y w => R0.rel st y w ∧ Z.ZeroHolds st (msg w.1),
        fun a w => R0.relR a w ∧ Z.ZeroHolds a.1 (msg w.1),
        R0.on, R0.core⟩
      (Z.toIn.relsOut R0 msg) (fun _ _ _ wp => wp)
      (Nums.draw Kc Z.toIn.ev.D Z.toIn.nxX Ex Z.toIn.ev.err)

def ldZero_exact : Prop :=
  ∀ (Z : ZeroCube E) (Ex : ExtSpec) (M Wp : Type) (P : Z.St → Ex.Str → M × Wp → Prop),
    (Honest.draw Z.toIn.ev.D Z.toIn.nxX Ex (M × Wp)).Exact P fun _ _ => True

end Spec

section Proofs
open IOR
variable (E : Type) [Field E] [Fintype E]

/-- for D not empty: a draw has nothing to simulate, whatever the relation -/
theorem draw_exact_any {X X' : Type} (Ex : ExtSpec) (W D : Type) [Fintype D] [Nonempty D]
    (nx : X → D → X') (P : X → Ex.Str → W → Prop) :
    (Honest.draw D nx Ex W).Exact P fun _ _ => True :=
  (piece_draw Unit X X' Ex W D nx ⟨P, fun _ _ => True, fun _ => True, fun _ => ()⟩
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ 0 (fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ => rfl)
    (fun _ _ _ => by rw [cnt_false fun _ h => h.elim fun _ h' => h'.2 trivial])).good.exact

theorem pscIn_exact : Spec.pscIn_exact E := fun Z Ex M Wp _ R0 msg =>
  draw_exact_any Ex (M × Wp) Z.ev.D Z.nxX (Z.relsIn R0 msg).rel

theorem ldZero_exact : Spec.ldZero_exact E := fun Z Ex M Wp P =>
  draw_exact_any Ex (M × Wp) Z.toIn.ev.D Z.toIn.nxX P

theorem pscIn_goodAt : Spec.pscIn_goodAt E := by
  intro Z Ex M Wp Kc R0 msg hL hB hOK
  have hfw : ∀ st y w β,
      (Z.relsIn R0 msg).rel st y w → (Z.relsOut R0 msg).rel (Z.nxX st β) y w := by
    intro st y w β h
    refine ⟨?_, pscIn_fwd E Z hL st β (msg w.1) h.2⟩
    show R0.rel (Z.old (Z.nx st β)) y w
    rw [hB]
    exact h.1
  have hon : ∀ st y β, (Z.relsIn R0 msg).on (st, y) → (Z.relsOut R0 msg).on (Z.nxX st β, y) := by
    intro st y β h
    show R0.on (Z.old (Z.nx st β), y)
    rw [hB]
    exact h
  have g := (piece_draw Kc Z.St0 (E × Z.T.St) Ex (M × Wp) Z.ev.D Z.nxX
    ⟨(Z.relsIn R0 msg).rel, fun _ _ => True, (Z.relsIn R0 msg).on, (Z.relsIn R0 msg).core⟩
    ⟨(Z.relsOut R0 msg).rel, fun _ _ => True, (Z.relsOut R0 msg).on, (Z.relsOut R0 msg).core⟩
    Z.ev.err (fun _ => True) hfw hon (fun _ => rfl) (fun _ _ _ => by
      rw [cnt_false fun _ h => h.elim fun _ h' => h'.2 trivial]; exact Nat.zero_le _)).good
  refine ⟨g.point, g.isLocal, g.acc, g.onOut, g.keeps, g.prBad, g.cover, g.prCov,
    fun _ _ _ _ => rfl, fun m => ?_⟩
  refine (piece_draw Unit Z.St0 (E × Z.T.St) Ex Wp Z.ev.D Z.nxX
    ⟨fun _ _ _ => False, fun a wp => (Z.relsIn R0 msg).relR a (m, wp),
      (Z.relsIn R0 msg).on, fun _ => ()⟩
    ⟨fun _ _ _ => True, fun b wp => (Z.relsOut R0 msg).relR b (m, wp),
      (Z.relsOut R0 msg).on, fun _ => ()⟩
    Z.ev.err (fun _ => True) (fun _ _ _ _ h => h.elim) hon (fun _ => rfl) ?_).good.know
  intro st y _
  by_cases hA : Z.AllHold st (msg m)
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro β ⟨wp, h1, h2⟩
      have h3 : R0.relR (Z.old (Z.nx st β), y) (m, wp) := h1.1
      rw [hB] at h3
      exact h2 ⟨h3, hA⟩
  · exact (cnt_mono fun β h => h.elim fun wp h1 => h1.1.2).trans
      (pscIn_cnt E Z hL hOK st (msg m) hA)

theorem ldZero_goodAt : Spec.ldZero_goodAt E := by
  intro Z Ex M Wp Kc R0 msg hco
  have e : Z.toIn.AllHold = Z.ZeroHolds :=
    funext fun st => funext fun m => propext (ldZero_all E Z st m)
  have h :=
    pscIn_goodAt E Z.toIn Ex M Wp Kc R0 msg (ldZero_link E Z) (ldZero_back E Z) (ldZero_ok E Z hco)
  unfold PscIn.relsIn at h
  rw [e] at h
  exact h

end Proofs
end Cb
