-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PlainLt.lean: how many messages in the clear are possible for the prover, round by
round, in a sumcheck.

For every record `P : PscPar E` (in the file: Y), in its two kinds (whole; without the end values),
at the library's own sumcheck and at the short one (`SK₀`: Cb/Pv/KeyLookup/Short0.lean). The reader
is `plainList` (Cb/Pv/KeyLookup/AsmErr.lean); q is the number of elements of the field, so q^k
stands for k scalars. It imports no file of the program (OnBytes/Iop, OnBytes/Params, ...).

Main names:
  `Plain.full_lib`: q^1 :: (for each variable of format f: q^(f.n + 1)) ++ [q^(the number of end
  values)].
  `Plain.core_lib`: q^1 :: (for each variable: q^(f.n + 1)).
  `Plain.full_short`: q^1 :: (for each variable: q^(f.n)) ++ [q^(the number of end values)]: one
  scalar fewer in each round with a polynomial.
  `Plain.core_short`: q^1 :: (for each variable: q^(f.n)).
  `Plain.draw`: a draw: [1]: nothing is sent.
  `Plain.our_fmt`: at a record `T : PscOur E` the variables are T's and behind them the library's
  dummy variable, of degree `T.DY`.
Limits: there is no condition. Not said: anything on what the messages hold; anything on oracle
messages.

-/
import Cb.Pv.KeyLookup.AsmErr
import Cb.Pv.KeyLookup.Short0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
namespace Plain
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn Johnson.L5.Layers

variable {E : Type} [Field E] [Fintype E]

omit [Field E] in
theorem card_E : Nat.card E = Fintype.card E ^ 1 := by rw [pow_one, Nat.card_eq_fintype_card]

omit [Field E] in
theorem card_fun (A : Type) [Fintype A] : Nat.card (A → E) = Fintype.card E ^ Fintype.card A := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

omit [Field E] in
theorem card_vec (n : ℕ) : Nat.card (Fin n → E) = Fintype.card E ^ n := by
  rw [card_fun, Fintype.card_fin]

theorem long (l : List (PFmt E)) :
    plainList (pRounds l) = l.map fun f => Fintype.card E ^ (f.n + 1) := by
  unfold plainList
  rw [List.map_map]
  exact List.map_congr_left fun f _ => card_vec (f.n + 1)

theorem short (l : List (PFmt E)) :
    plainList (sRounds l) = l.map fun f => Fintype.card E ^ f.n := by
  unfold plainList
  rw [List.map_map]
  exact List.map_congr_left fun f _ => card_vec f.n

theorem cons_app (r v : Round) (s : Shape) :
    plainList (r :: (s ++ [v])) = Nat.card r.Plain :: (plainList s ++ [Nat.card v.Plain]) := by
  unfold plainList
  rw [List.map_cons, List.map_append, List.map_singleton]

variable (Y : PscPar E) (Ex : ExtSpec)

theorem full_lib :
    plainList ((PscLtK.lib E Ex).full Y).R.shape =
      Fintype.card E ^ 1 ::
        ((Y.fmt.map fun f => Fintype.card E ^ (f.n + 1)) ++
          [Fintype.card E ^ Fintype.card Y.A]) := by
  show plainList (pRound0 E :: (pRounds Y.fmt ++ [pRoundV E Y.A])) = _
  rw [cons_app, long]
  exact congrArg₂ List.cons card_E (congrArg (fun x => _ ++ [x]) (card_fun Y.A))

theorem core_lib :
    plainList ((PscLtK.lib E Ex).core Y).R.shape =
      Fintype.card E ^ 1 :: (Y.fmt.map fun f => Fintype.card E ^ (f.n + 1)) := by
  show Nat.card E :: plainList (pRounds Y.fmt) = _
  rw [long, card_E]

theorem full_short :
    plainList ((SK₀ E Ex).full Y).R.shape =
      Fintype.card E ^ 1 ::
        ((Y.fmt.map fun f => Fintype.card E ^ f.n) ++ [Fintype.card E ^ Fintype.card Y.A]) := by
  show plainList (pRound0 E :: (sRounds Y.fmt ++ [pRoundV E Y.A])) = _
  rw [cons_app, short]
  exact congrArg₂ List.cons card_E (congrArg (fun x => _ ++ [x]) (card_fun Y.A))

theorem core_short :
    plainList ((SK₀ E Ex).core Y).R.shape =
      Fintype.card E ^ 1 :: (Y.fmt.map fun f => Fintype.card E ^ f.n) := by
  show Nat.card E :: plainList (sRounds Y.fmt) = _
  rw [short, card_E]

omit [Field E] [Fintype E] in
theorem draw {X X' : Type} (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (Ex : ExtSpec) :
    plainList (IOR.draw D nx Ex).shape = [1] := by
  show [Nat.card Unit] = [1]
  simp

theorem our_fmt (T : PscOur E) : T.par.fmt = T.fmt ++ [pDummy E T.DY] := rfl

end Plain
end Lk6

#print axioms Lk6.Plain.full_lib
#print axioms Lk6.Plain.core_lib
#print axioms Lk6.Plain.full_short
#print axioms Lk6.Plain.core_short
#print axioms Lk6.Plain.draw
