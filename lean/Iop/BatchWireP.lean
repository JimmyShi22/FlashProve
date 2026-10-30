-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchWireP.lean: what the compiled prover of a protocol with slots needs beside
Iop/BatchWire.lean in order to be written down as a term without choice: enumerations of the coins
and a decision of the abort set (`Honest.withheld`). Data and conditions. (Words of this library:
lean/GLOSSARY.md.)
-/
import Iop.BatchWire
import Iop.BatchOne

namespace Iop

structure WirePB {X : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof X E) {Wt : Type} (H : BatchHonestProver Q Wt) where
  coin0 : Enum H.Coin0
  coin : Enum H.Coin
  decW : ∀ w x ρ, Decidable (ρ ∈ H.one.withheld w x)

structure WirePB.OK {X : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof X E} {Wt : Type}
    {H : BatchHonestProver Q Wt} (wp : WirePB Q H) : Prop where
  coin0 : wp.coin0.OK
  coin : wp.coin.OK

/-- the prover's data for the three protocols, and the enumeration of the encoding randomness -/
structure WireBP {I X : Type} (L : BatchProtocol I X) where
  T : WirePB (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver)
  Lk : WirePB (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver)
  B : WirePB L.onlineBatch L.honestOnlineBatchProver
  ri : Enum L.EncodingRandomness
  /-- the placements of the requests of a batch in the slots -/
  perm : Enum (Equiv.Perm (Fin L.maxBatchSize))

structure WireBP.OK {I X : Type} {L : BatchProtocol I X} (W : WireBP L) : Prop where
  T : W.T.OK
  Lk : W.Lk.OK
  B : W.B.OK
  ri : W.ri.OK
  perm : W.perm.OK

end Iop
