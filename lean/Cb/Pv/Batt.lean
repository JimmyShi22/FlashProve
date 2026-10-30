-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Batt.lean: the batching of tensor rows on one matrix, as one kind of block: the
reduction, its joints, the statement that it is knowledge sound, and what is proved beside it.

Several claims, each a row vector, a point for the columns and a mask form with a target, become
one: the verifier draws the seed of coefficients, and a sumcheck over the cube of the columns
follows. The reduction is the library's `BattPar.batt` (Cb/Ld/LdBatt.lean); nothing of it is stated
anew. The file imports no file of the program.

Main names. B is a value of the library's record `BattPar E`, which is the size of this kind: the
entries, the matrix's rows and k column variables, the claims' names, row vectors, points and mask
forms, the coefficients Z, the degree n of a round's polynomial, and where the sumcheck's own mask
entries are.
  `HAt B`     the statement at the size B. Bound inside: the further oracles, the types of message
              tuples, further witnesses and cores, a joint A0 that is carried along, the reading msg
              of the entries off the messages, and a tuple m of messages. It says: for each fixed m
              the reduction is knowledge sound (`Reduction.Know`) on the statements of A0, from "A0,
              and all claims hold of the entries" (`B.baseIn`) to "A0, and the one claim at the
              sumcheck's point holds" (`B.baseOut`), with the identity as extractor, at the
              library's errors (`B.nums`).
  `hAt`       the statement holds if 2 ≤ B.n and the coefficients evade zero (B.Z.OK): the library's
              `batt_goodAt`.
  `point`, `isLocal`, `onOut`   under the same two conditions.
  `copies`, `passes`, `rounds`   for all sizes: the reduction reads none of its oracles and only
              copies them; it hands the state on; it has k + 2 rounds.

Limits. The sumcheck is the library's, in which every coefficient of a round's polynomial is sent.
That a matrix, claims or coefficients are those of a key file's chains is not said. Nothing on an
honest prover.

-/
import Cb.Ld.LdBattProofs
import Cb.Ld.LdLkpFormat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Batt
open Iop IOR Cb

variable {E : Type} [Field E] [Fintype E] (B : BattPar E)

/-- The statement that the batching at the size B is knowledge sound. -/
def HAt : Prop :=
  ∀ (Ex : ExtSpec) (M Wp Kc : Type) (A0 : Rels Kc B.St Ex (M × Wp)) (msg : M → B.J → E) (m : M),
    (B.batt Ex).red.Know (B.baseIn Ex A0 fun w => msg w.1).on
      (fun a wp => (B.baseIn Ex A0 fun w => msg w.1).relR a (m, wp))
      (fun b wp => (B.baseOut Ex A0 fun w => msg w.1).relR b (m, wp))
      (fun _ _ wp => wp) (B.nums Ex Kc).err

/-- The statement holds if 2 ≤ B.n and the coefficients evade zero. -/
theorem hAt (hn : 2 ≤ B.n) (hZ : B.Z.OK) : HAt B :=
  fun Ex M Wp Kc A0 msg m => (batt_goodAt E B Ex M Wp Kc A0 msg hn hZ).know m

/-! ### beside the statement -/

theorem point (hn : 2 ≤ B.n) (hZ : B.Z.OK) (Ex : ExtSpec) :
    Nonempty (B.batt Ex).shape.IsPoint :=
  (batt_goodAt E B Ex Unit Unit Unit
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ (fun _ _ => 0) hn hZ).point

theorem isLocal (hn : 2 ≤ B.n) (hZ : B.Z.OK) (Ex : ExtSpec) : (B.batt Ex).IsLocal :=
  (batt_goodAt E B Ex Unit Unit Unit
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ (fun _ _ => 0) hn hZ).isLocal

theorem onOut (hn : 2 ≤ B.n) (hZ : B.Z.OK) (Ex : ExtSpec) (M Wp Kc : Type)
    (A0 : Rels Kc B.St Ex (M × Wp)) (msg : M → B.J → E) :
    ∀ a τ b, (B.baseIn Ex A0 fun w => msg w.1).on a → (B.batt Ex).red.out a τ = some b →
      (B.baseOut Ex A0 fun w => msg w.1).on b :=
  (batt_goodAt E B Ex M Wp Kc A0 msg hn hZ).onOut

/-- The reduction reads none of its oracles and only copies them. -/
theorem copies (Ex : ExtSpec) : (B.batt Ex).OnlyCopies :=
  (OnlyCopies.draw _ _ _).seq (core_onlyCopies B.par Ex)

/-- The state is handed on. -/
theorem passes (Ex : ExtSpec) : (B.batt Ex).Passes Prod.snd (fun z => z.st.1) :=
  Passes.seq (r₂ := fun x : E × B.par.St => x.2.1) (Passes.draw _ _ _ _ _ fun _ _ => rfl)
    fun x y τ z h => congrArg Prod.fst (core_passes B.par Ex x y τ z h)

theorem rounds (Ex : ExtSpec) : (B.batt Ex).shape.length = B.k + 2 := batt_len E B Ex

end Cb.Pv.Batt

#print axioms Cb.Pv.Batt.hAt
#print axioms Cb.Pv.Batt.point
#print axioms Cb.Pv.Batt.isLocal
#print axioms Cb.Pv.Batt.onOut
#print axioms Cb.Pv.Batt.copies
#print axioms Cb.Pv.Batt.passes
#print axioms Cb.Pv.Batt.rounds
