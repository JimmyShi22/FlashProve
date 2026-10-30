-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/CarrierSide.lean: copies of `typedOracleCarrier`, `batTC`, `batLC`
(Johnson/TypedOracleCompiler/RecCompile/Carrier.lean), typed over the verifier's side of the object (`LHV`:
Hiop/RecSide.lean says what that is and why it is there).

Main names: `carrierV`, `batTV`, `batLV`.
The ties (`XC_v`, `carrierT_v`, `batTC_v`, `batLC_v`): each of these at L equals its copy here at
`L.v`, at every argument; `XC_v`: the type `HolographicProtocol.XC` unfolds to `LHV.XC`. If one of the two copies is
changed alone, this file no longer compiles: do not drop the ties in a clean-up.
Limits: definitions and these equations. Nothing on soundness.

-/
import Johnson.TypedOracleCompiler.RecCompile.Carrier
import Hiop.RecSide

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

/-- The carrier of the typed oracles: the object's word length, alphabet and three shapes, the
session's annotation, the number of slots, what of an instance comes early and late; and three
letters: the type of the body of a leaf, an annotation of Test's rounds and one of Link's. All else
is empty: there is no index (the type of indices is `Empty`), so there is no encoding, and the three
honest sides are hollow. So the carrier does not hang on the object's honest side. -/
def carrierV {X : Type} (L : LHV X) (Bd : Type) (aT : RoundSplits L.test.shape)
    (aL : RoundSplits L.link.shape) : BatchProtocolWithLeafBody Empty L.XC where
  wordLength := L.n
  Symbol := L.Sg
  EncodingRandomness := Unit
  encodeIndex := fun i _ => i.elim
  decodeIndex := fun _ => none
  offline := InteractiveOracleProof.hollow L.test.shape
  link := InteractiveOracleProof.hollow L.link.shape
  maxBatchSize := L.N
  onlineBatch := ⟨InteractiveOracleProof.hollow L.bat.loc.shape, L.bat.ann⟩
  honestOfflineProver := { Coin := Unit, ext := fun w => w.1.elim, strat := fun _ _ _ => Strat.dflt _ (),
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun w => w.1.elim, strat := fun _ _ _ => Strat.dflt _ (),
                        Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun w => w.1.elim,
                               strat0 := fun _ _ => SStrat.hollow _ _, strat := fun _ _ _ _ => LStrat.hollow _ _,
                               Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := fun a => (a.1.map L.early, a.2)
  late := L.late
  Bd := Bd
  annT := aT
  annL := aL

/-- Test with an annotation of its rounds as local or shared: the key's protocol. At the annotation
`RoundSplits.allLocal` it is `BatchInteractiveOracleProof.ofProto L.test`. -/
def batTV {X : Type} (L : LHV X) (aT : RoundSplits L.test.shape) :
    BatchInteractiveOracleProof L.Rec (oneExternalString L.n L.Sg) := ⟨L.test, aT⟩

/-- Link with an annotation. -/
def batLV {X : Type} (L : LHV X) (aL : RoundSplits L.link.shape) :
    BatchInteractiveOracleProof (L.Rec × L.Rec) (twoExternalStrings L.n L.Sg) := ⟨L.link, aL⟩

/-! ## The ties -/

section Ties

variable {I X : Type}

/-- What a chain's first query holds of an instance has one type at both sides. -/
theorem XC_v (L : HolographicProtocol I X) : L.v.XC = L.XC := rfl

theorem carrierT_v (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape) :
    typedOracleCarrier L Bd aT aL = carrierV L.v Bd aT aL := rfl

theorem batTC_v (L : HolographicProtocol I X) (aT : RoundSplits L.offline.shape) : batTC L aT = batTV L.v aT := rfl

theorem batLC_v (L : HolographicProtocol I X) (aL : RoundSplits L.link.shape) : batLC L aL = batLV L.v aL := rfl

end Ties

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.XC_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.carrierT_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.batTC_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.batLC_v
