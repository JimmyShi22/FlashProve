-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/TieKit.lean: two laws on the record `InputV` and on `verifyV`
(Johnson/Top/InputV.lean), general in all letters: for proofs that two inputs of `verifyV`, made on
two roads, are one.
  `InputV.mk_congr`: two values of `InputV` over one X, L, Bd, aT, aL are equal if their eight
    further fields are. Sd's and m's types hang on the wire's number of blocks: these two are asked
    as HEq.
  `verifyV_congr`: at equal inputs and at proofs that are equal (as HEq: a proof's type hangs on the
    input) `verifyV` is the same algorithm.
Limits: congruence alone. Nothing on soundness.

-/
import Johnson.Top.InputV

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- Two values of `InputV` over one X, L, Bd, aT, aL are equal if their eight further fields are. -/
theorem InputV.mk_congr {X : Type} {L : LHV X} {Bd : Type} {aT : RoundSplits L.test.shape}
    {aL : RoundSplits L.link.shape} {W W' : QueryLayout 256 (carrierV L Bd aT aL)} (hW : W = W')
    {Sd : SeedV 256 W.K L Bd aT aL} {Sd' : SeedV 256 W'.K L Bd aT aL} (hS : HEq Sd Sd')
    {cA cA' : L.Ans → List (Dig 256)} (hc : cA = cA') {r₀ r₀' : L.Rec} (hr : r₀ = r₀')
    {p p' : Params} (hp : p = p')
    {m : ImplV (typedOracleFamily 256 W.K (carrierV L Bd aT aL)) 256}
    {m' : ImplV (typedOracleFamily 256 W'.K (carrierV L Bd aT aL)) 256} (hm : HEq m m')
    {enc enc' : KeyRootV 256 L → Option ZKCP.Str} (he : enc = enc')
    {build build' : List Token × List Token → List Token → Option X} (hb : build = build') :
    (⟨X, L, Bd, aT, aL, W, Sd, cA, r₀, p, m, enc, build⟩ : InputV) =
      ⟨X, L, Bd, aT, aL, W', Sd', cA', r₀', p', m', enc', build'⟩ := by
  subst hW hc hr hp he hb
  cases hS
  cases hm
  rfl

/-- At equal inputs and equal proofs `verifyV` is the same algorithm. -/
theorem verifyV_congr {v v' : InputV} (h : v = v') (commitment : Commitment)
    (prompt output : List Token)
    {q : List Token × (KeyRootV 256 v.L × PrfRootV 256 v.L v.aT v.aL)}
    {q' : List Token × (KeyRootV 256 v'.L × PrfRootV 256 v'.L v'.aT v'.aL)} (hq : HEq q q') :
    verifyV v commitment prompt output q = verifyV v' commitment prompt output q' := by
  subst h
  cases hq
  rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.InputV.mk_congr
#print axioms VerifiableInference.OnPublicFiles.verifyV_congr
