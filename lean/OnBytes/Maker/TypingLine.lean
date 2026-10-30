-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingLine.lean: the typed plain parts and the roots that OnBytes/Maker/TypingT.lean
makes of a chain's rounds as read are those of OnBytes/TypedOracleCompiler/Run/PlanQSMore.lean (`plainsSL`) and of
OnBytes/TypedOracleCompiler/Run/ChainF.lean (`rootsD`).

  `plainsT_line`: `plainsT C ds os` is `plainsSL C (toRDs ds) os`: the two are one text over lists
    of two types of rounds' data; shown by induction.
  `rootsT_line`: `rootsT` is `rootsD`, by unfolding.

What is not claimed. Nothing on a proof string, on which rounds of a chain are typed, or on a
reader.


-/
import OnBytes.Maker.TypingT
import OnBytes.TypedOracleCompiler.Run.ChainF

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Iop _root_.Run _root_.Run.PQ

theorem plainsT_line (C : CK) : ∀ (ds : List RDT) (os : List Fmt.RoundOut),
    plainsT C ds os = TypedOracleCompiler.Run.PQ.plainsSL C (toRDs ds) os
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, o :: os => by
      have ih := plainsT_line C ds os
      unfold plainsT
      show _ = TypedOracleCompiler.Run.PQ.plainsSL C (d.toRD :: toRDs ds) (o :: os)
      unfold TypedOracleCompiler.Run.PQ.plainsSL
      rw [ih]
      cases PlainOf.ofGots d.items o.vals <;> cases TypedOracleCompiler.Run.PQ.plainsSL C (toRDs ds) os <;> rfl

theorem rootsT_line (os : List Fmt.RoundOut) : rootsT os = TypedOracleCompiler.Run.PQ.rootsD os := rfl

end OnBytes.Maker
