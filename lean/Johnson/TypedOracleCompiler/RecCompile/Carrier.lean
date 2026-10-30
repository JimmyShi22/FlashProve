-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/Carrier.lean: the carrier of the typed oracles for an object with records
(`Iop.HolographicProtocol`), over the compiler's verifier side in lean/OnBytes/TypedOracleCompiler/. Three
definitions.

`typedOracleCarrier L Bd aT aL` holds what `L.carrierC` of lean/Johnson/RecCompile/Cms.lean holds of the
verifier's side (the word length, the alphabet, the three shapes, the session's annotation, the
number of slots, what of an instance comes early and late), and three letters more: the type of the
body of a leaf, and an annotation of the rounds of Test and of Link as local or shared. Unlike
`L.carrierC` it holds nothing of the honest side: its type of indices is `Empty` and its encoding
randomness `Unit`, so it has no encoding. Why: the types of typed queries, of wires and of codings
have the carrier as a parameter. If the object's encoding stood in the carrier, two objects that
differ in the honest side alone would have two such types, and "the verdict is the same at both"
could not be shown by unfolding. A search of the text for these fields by name finds no definition
that reads an index, an encoding or an honest side of a carrier; a reading by position would escape
such a search; no theorem says it. lean/Johnson/RecCompile/Cms.lean is imported for `L.XC`.
`batTC L aT` and `batLC L aL` are Test and Link with these annotations.

Limits: a carrier is there for its types alone. Every clause of the library's laws on an interface
that begins with an index, an encoding randomness or an honest side's private input holds emptily at
a carrier: `BatchProtocol.Wired` (Iop/Batch.lean), which fails at `L.carrierC` wherever there is an index (its
decoder returns nothing), holds here, but only because there is no index of which it could speak. So
no such law says anything at a carrier.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier
import Johnson.RecCompile.Cms

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
def typedOracleCarrier {I X : Type} (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) : BatchProtocolWithLeafBody Empty L.XC where
  wordLength := L.wordLength
  Symbol := L.Symbol
  EncodingRandomness := Unit
  encodeIndex := fun i _ => i.elim
  decodeIndex := fun _ => none
  offline := InteractiveOracleProof.hollow L.offline.shape
  link := InteractiveOracleProof.hollow L.link.shape
  maxBatchSize := L.maxBatchSize
  onlineBatch := ⟨InteractiveOracleProof.hollow L.onlineBatch.loc.shape, L.onlineBatch.ann⟩
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
`RoundSplits.allLocal` it is `BatchInteractiveOracleProof.ofProto L.offline`. -/
def batTC {I X : Type} (L : HolographicProtocol I X) (aT : RoundSplits L.offline.shape) :
    BatchInteractiveOracleProof L.Rec (oneExternalString L.wordLength L.Symbol) := ⟨L.offline, aT⟩

/-- Link with an annotation. -/
def batLC {I X : Type} (L : HolographicProtocol I X) (aL : RoundSplits L.link.shape) :
    BatchInteractiveOracleProof (L.Rec × L.Rec) (twoExternalStrings L.wordLength L.Symbol) := ⟨L.link, aL⟩

end TypedOracleCompiler.Compile.Batch.Cms
