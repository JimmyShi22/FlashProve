-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/Buys.lean: what the test on numbers of Johnson/Pack/Check.lean gives for a sending, in
one record.

A definition, a statement and its proof.
Main names:
  `Buys cs l`: of the sending of the sampled messages l under the codes cs: every member's lists
    have at most `lOf` messages; every member's sample map evades; every member's code has its laws;
    the joint seeds are fair; the sending's verifier is local and its oracles are point oracles;
    and, for every joint and every way back, the sending is knowledge sound into collision-free
    statements, with the library's error at these lists.
  `allMeet_buys`: `allMeet cs l = true → Buys cs l`.
Limits: what Johnson/Pack/PortZ.lean, PortF.lean, PortTie.lean and PortS.lean name as their limits:
among them the coefficients of `Send.form`, the pad's basis elements and the way the factor is
drawn. Nothing on messages that are not sampled (they are in no list), on the proximity tests behind
a sending, on the honest prover or on hiding.
-/
import Johnson.Pack.PortS
import Johnson.Pack.Check

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Cb.Ood Iop IOR Prob OnBytes.Slice

/-- What a sending has. -/
structure Buys (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) : Prop where
  list : Cb.Pack.HList (sigOf cs l) fun i => lOf cs (l.get i).1 (l.get i).2
  evades : Cb.Pack.HEvades (sigOf cs l)
  laws : Cb.Pack.HLaws (sigOf cs l)
  fair : (seedsOf cs l).Fair
  localPt : ∀ (X : Type) (E₀ : ExtSpec), (ldSendFam (sigOf cs l) (seedsOf cs l) X E₀).IsLocal ∧
    Nonempty (ldSendFam (sigOf cs l) (seedsOf cs l) X E₀).shape.IsPoint
  know : ∀ (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
    (back : (sigOf cs l).Msg → W' → W),
    (ldSendFam (sigOf cs l) (seedsOf cs l) X E₀).red.KnowInto A.on
      ((sigOf cs l).over ((sigOf cs l).pull A back)).on A.relR
      ((sigOf cs l).over ((sigOf cs l).pull A back)).relR
      (fun _ _ w => back ((sigOf cs l).msgs w.1) w.2)
      (Cb.Pack.sendErr (sigOf cs l) (seedsOf cs l) (fun i => lOf cs (l.get i).1 (l.get i).2) X E₀)

theorem allMeet_buys (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (h : allMeet cs l = true) : Buys cs l :=
  have g := allMeet_sound cs l h
  have H := sigOf_holes cs l (fun i => dOf cs (l.get i).1)
    (fun i => lOf cs (l.get i).1 (l.get i).2) g
  ⟨H.1, H.2.1, H.2.2, seedsOf_fair cs l,
    fun X E₀ => Cb.Pack.send_pl (sigOf cs l) (seedsOf cs l) X E₀ H.2.2,
    fun Kc X W W' E₀ A back => send_closed cs l _ _ g Kc X W W' E₀ A back⟩

end Johnson.Pack

#print axioms Johnson.Pack.allMeet_buys
