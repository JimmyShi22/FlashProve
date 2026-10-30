-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/NoStop.lean: where no `Part` of a prover structure H (`ProofFile.Honest.Prover`,
Johnson/Desc/ProofFile/Honest/Frame.lean) ever stops (`NoStopAll H`), the abort set of
`(honestBatchProverOfFile …).one` is empty. `honestBatchProverOfFile` (Johnson/Desc/ProofFile/Honest/StratC.lean) builds the
library's structure of an honest side (`Iop.BatchHonestProver`) from H, and `.one` is that structure's prover
of a single run. General in the description F, the book of coins B (`ProverCoinCounts`), H and all other
parameters of `honestBatchProverOfFile`. The same is then stated of `keyHonestAny` (E2E/KeyHonest.lean), a prover
structure for the key file's protocol that is built by `honestBatchProverOfFile` from parameters that nothing here
fixes (below: the shell `keyHonestAny`). For what: E2E/KeyBridge.lean names three bounds on measures
as hypotheses on the key file's honest prover. Under `NoStopAll H` two of them, `BadSmall` and
`HidSmall`, hold of the shell at 0. The third, `FallSmall`, is shown at 0 for the empty fall only.

  `bad_empty`, `hid_empty`, `withheld_empty`: under `NoStopAll H`, the two parts of the abort set of
    `(honestBatchProverOfFile …).one` are empty: the public abort set `Bad`, and the abort set `Hid`, which may
    depend on the private input, at every private input w and instance x. So is the abort set,
    `withheld`, their union
  `withheld_key`: under `NoStopAll H`, the abort set of the shell `keyHonestAny` is empty, at every
    private input w and OOD sample x
  `badSmall_key`, `hidSmall_key`: under `NoStopAll H`, `BadSmall` at 0 and `HidSmall` at 0 hold of
    the shell, the second at every relation `Tied`
  `fallSmall_none`: `FallSmall` at 0 for the fall that is the empty set at every private input,
    instance and coin. General: at every object L, honest prover hT of `L.offline` and relation `Tied`;
    `NoStopAll` is not among its hypotheses
  `Quiet p`: a definition: the two tests for a stop of a `Part` p, its fields `bad` and `hid`,
    return `none` at all arguments
  `NoStop hs`: a definition: in a list hs of the prover's parts for a chain's sub-protocols
    (`Placed`), every `Part` of every entry is `Quiet`
  `NoStopAll H`: a definition: `NoStop` of `H.first`, `H.shared` and `H.second`, the lists of H for
    the three chains
  `stopAt_none`, `rowStopAt_none`, `chainStopAt_none`: a `Quiet` `Part`, a list of `Quiet` `Part`s,
    and a chain under `NoStop hs` stop at no list of challenges: `Part.stopAt`, `rowStopAt` and
    `chainStopAt` return `none`
  `badB_false`, `hidB_false`, `stop0B_false`: under `NoStopAll H`, the three tests `badB`, `hidB`
    and `stop0B` return false at all arguments

By what. Honest/ is short for Johnson/Desc/ProofFile/Honest/. The fields `Bad` and `Hid` of
`honestBatchProverOfFile` are the sets of verifier randomness at which `badB` and `hidB` return true, and its field
`stop0` is `stop0B`, each at the lists of challenges that `drawsLo` or `drawsSh` reads off the
verifier randomness (all five: Honest/Record.lean). Each of the three tests returns true only where
a call of `chainStopAt` (Honest/Rule.lean) returns something other than `none`. `chainStopAt` calls
`rowStopAt`, that calls `Part.stopAt` (both Honest/Side.lean), and that asks the fields `bad` and
`hid`. `BatchHonestProver.one` (Iop/Batch.lean) joins `Bad` and `stop0` to the `Bad` of the prover of a single
run; `Honest.withheld` (Iop/InteractiveOracleProof.lean) is the union of `Bad` and `Hid`. The sets `Bad` and `Hid` of
`keyHonestAny` are, by unfolding, those of `(honestBatchProverOfFile …).one` at the key file's parameters, `Hid` at
the written key `keyInstanceOfOutOfDomainSample x` of the OOD sample x (stated in `keyHonestAny_fields`, E2E/KeyHonest.lean).
`prRho_empty` (Iop/ViewKit.lean): a set without elements has measure at most 0.

Limits.
- `NoStopAll` is a hypothesis: it is shown here of no prover structure. It is a statement on the
  definition of one prover structure: whoever builds a structure from other `Placed`s has to show it
  of these.
- `NoStopAll` holds vacuously of a prover structure whose lists `first`, `shared` and `second` are
  empty; nothing here excludes that.
- `NoStopAll` reads the fields `bad` and `hid` as functions: a `Part` one of whose two tests returns
  something other than `none` at arguments that no run meets is not `Quiet`.
- The bound on a fall's measure stays a hypothesis (`FallSmall`). A fall (`FallT`,
  E2E/KeyBridge.lean: at each private input, instance and coin of the prover's, a set of verifier
  randomness that is set aside on the acceptance side) is not a stop. `fallSmall_none` speaks of the
  empty fall: whoever uses that fall has to show the acceptance statement (`AccLaw`,
  Johnson/Prover/Law/Defs.lean) at all verifier randomness outside the abort set.
- That no fall is needed at the key file is shown nowhere in Lean. On paper it depends on four
  things: an identity on the covered sum (`Wf.coveredSum`, as `tableRowsOf` tests it,
  Johnson/Desc/Key/TableRows.lean) at every point; the two tests of the proximity tests' base cases
  at every coin; the sub-protocols' own guards, for those that send and those that test proximity;
  two rare events at the routine that reads the file. It also depends on conditions: an index in
  range; a key whose seed's factor is not 0 (at the written key of an OOD sample this holds by the
  type: `seed_ne_zero`, E2E/TiedAtFiles.lean); lists of challenges that are due (`Draws.due`,
  Honest/Frame.lean).
- The fall's set depends on the prover's coin. A bound on its measure at each fixed coin bounds the
  share over verifier randomness and coins together; it does not bound the set of verifier
  randomness at which some coin's run falls. So a statement of completeness takes the number as an
  error over verifier randomness and coins together; the fall is a second set, which reads the coin,
  next to the abort set, and is not folded into it: the form of `OnBytes.Prover.HonFit`
  (Johnson/Prover/All/OfHonest.lean: its acceptance statements outside the abort set and the fall at
  that coin; its measures at each fixed coin).
- It is the sum of the three measures that counts. In which of the three sets a list of challenges
  that is not due is put, where the protocol's verifier randomness gives one (`drawsAt`,
  Honest/Law/StratWords.lean), is a choice of whoever states the sets. Here it is in neither part of
  the abort set: that every such list is due is a hypothesis of the acceptance statement (hdue in
  `yesAt_of_debts`, E2E/BridgeLink.lean).
- An empty abort set does not say that the honest side always sends its own messages. Its strategies
  (`sharedPartStrategyTrackingVerifier`, `requestStrategyTrackingVerifier`, Honest/StratC.lean) cannot refuse to send: where the run cannot be made
  ready (`ready` or `readyShared` returns an error), at a fault of a `Part` (a move returns an
  error, or a message of another shape than the sub-protocol states), at a column that is not at
  hand, and after a rejection by the verifier's own step they send fixed substitutes, and none of
  these lies in an abort set.
- Nor does an empty abort set say that the verifier accepts what is sent.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBridge
import E2E.KeyHonest

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Stops
open VerifiableInference.Desc (FileDescription Block)
open ProofFile.Honest

section Parts
variable {S Cl V W X : Type}

/-- The two tests for a stop of a `Part` p, its fields `bad` and `hid`, return `none` at all
arguments. -/
def Quiet (p : Part V W X) : Prop :=
  (∀ loc ds, p.bad loc ds = none) ∧ ∀ u loc ds, p.hid u loc ds = none

/-- Every `Part` of every `Placed` in hs is `Quiet`. hs: the prover's parts for a chain's
sub-protocols. -/
def NoStop (hs : List (Placed V W X)) : Prop := ∀ h ∈ hs, ∀ p ∈ h.parts, Quiet p

/-- A `Quiet` `Part` stops at no list of challenges: `Part.stopAt` returns `none`. -/
theorem stopAt_none {p : Part V W X} (h : Quiet p) (v : Option V) (loc ds : List Fmt.Drawn) :
    p.stopAt v loc ds = none := by
  unfold Part.stopAt
  refine List.findSome?_eq_none_iff.2 fun j _ => ?_
  have e2 : (v.bind fun u => p.hid u loc (ds.take j)) = none := by
    cases v with
    | none => rfl
    | some u => exact h.2 u loc (ds.take j)
  rw [h.1, e2]
  rfl

/-- A list of `Quiet` `Part`s stops at no list of challenges: `rowStopAt` returns `none`. -/
theorem rowStopAt_none (v : Option V) :
    ∀ (ps : List (Part V W X)), (∀ p ∈ ps, Quiet p) → ∀ loc ds, rowStopAt v ps loc ds = none
  | [], _, _, _ => rfl
  | p :: ps, h, loc, ds => by
    show ((p.stopAt v loc (ds.take p.moves.length)).or
      (rowStopAt v ps (loc ++ ds.take p.moves.length) (ds.drop p.moves.length))) = none
    rw [stopAt_none (h p (List.mem_cons_self ..)),
      rowStopAt_none v ps (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    rfl

/-- Under `NoStop hs` a chain stops at no list of challenges: `chainStopAt` returns `none`, at every
list bs of sub-protocols. -/
theorem chainStopAt_none (v : Option V) {hs : List (Placed V W X)} (h : NoStop hs) :
    ∀ (bs : List (Block S Cl)) loc ds, chainStopAt v bs hs loc ds = none
  | [], _, _ => rfl
  | b :: bs, loc, ds => by
    show (((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt v g.parts loc (ds.take b.rounds.length)).or
      (chainStopAt v bs hs (loc ++ ds.take b.rounds.length) (ds.drop b.rounds.length))) = none
    rw [chainStopAt_none v h bs]
    cases e : hs.find? (fun g => g.place == b.place) with
    | none => rfl
    | some g =>
      show ((rowStopAt v g.parts loc (ds.take b.rounds.length)).or none) = none
      rw [rowStopAt_none v g.parts (h g (List.mem_of_find?_eq_some e))]
      rfl

end Parts

section File
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- No `Part` of the prover structure H ever stops: `NoStop` of its lists for the three chains. -/
def NoStopAll (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Prop :=
  NoStop H.first ∧ NoStop H.shared ∧ NoStop H.second

variable (F : FileDescription Xi) {H : Prover W₀ Rc Xi Ky Tr X₀ X} (h : NoStopAll H)
include h

theorem badB_false (ds : List Fmt.Drawn × List Fmt.Drawn) : badB F H ds = false := by
  unfold badB
  rw [chainStopAt_none _ h.1, chainStopAt_none _ h.2.2]
  rfl

theorem hidB_false (w₀ : W₀) (rc : Rc) (x : Xi) (ds : List Fmt.Drawn × List Fmt.Drawn) :
    hidB F H w₀ rc x ds = false := by
  unfold hidB
  cases H.trace w₀ x with
  | none => rfl
  | some tr =>
    show (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder H.first []
        ds.1 == some .hid ||
      chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second ds.1
        ds.2 == some .hid) = false
    rw [chainStopAt_none _ h.1, chainStopAt_none _ h.2.2]
    rfl

theorem stop0B_false (ds : List Fmt.Drawn) : stop0B F H ds = false := by
  unfold stop0B
  rw [chainStopAt_none _ h.2.1]
  rfl

end File

section Side
open Iop
open OnBytes.Maker (WholeD)
open _root_.Run.PQ (CK SgX)
variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD) (tF : TF) (tJ : TJ)
  (t3 : T3) (F : FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts)
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : R₂ → R₃ → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str) (h : NoStopAll H)
include h

/-- **The public part of the abort set, `Bad`, is empty.** -/
theorem bad_empty : (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Bad = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hρ => hρ.elim
    (fun a => Bool.false_ne_true ((badB_false F h _).symm.trans a))
    (fun a => Bool.false_ne_true ((stop0B_false F h _).symm.trans a))

/-- **So is `Hid`, the part that may depend on the private input.** -/
theorem hid_empty (w : W₀ × Rc × Sd) (x : Xi) :
    (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Hid w x = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ a =>
    Bool.false_ne_true ((hidB_false F h _ _ _ _).symm.trans a)

/-- **So the abort set, `withheld`, is empty.** -/
theorem withheld_empty (w : W₀ × Rc × Sd) (x : Xi) :
    (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.withheld w x = ∅ := by
  show (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Bad ∪
    (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Hid w x = ∅
  rw [bad_empty C D tF tJ t3 F silent B J sh ext h, hid_empty C D tF tJ t3 F silent B J sh ext h,
    Set.union_empty]

end Side

end AtPublicFiles.Stops

namespace AtPublicFiles.KeyBridge
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The fall that is the empty set at every private input, instance and coin has measure 0. -/
theorem fallSmall_none {I X : Type} {L : HolographicProtocol I X} (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
    (Tied : TiedT L) : FallSmall hT (fun _ _ _ => ∅) Tied 0 :=
  fun _ _ _ _ => prRho_empty _ fun _ a => a

end AtPublicFiles.KeyBridge

namespace AtPublicFiles.AtFiles
open Prob Hiop AtPublicFiles.Cut AtPublicFiles.KeyBridge AtPublicFiles.Stops
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts)

variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD) (Fx : FileDescription KeyInst)
  (runP : X × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
  {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  {H : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) KeyInst Ky Tr X₀ X'}
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (DecR.configurationOfStoredTable A R).Seed KeyInst Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → Fx.S₂)
  (ext : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
    (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (runK : RecFull → View → View → View → Bool)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
  (h : NoStopAll H)
include h

/-- **The abort set of the shell `keyHonestAny` (E2E/KeyHonest.lean) is empty.** -/
theorem withheld_key (w) (x : RecFull) :
    (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
      P).withheld w x = ∅ :=
  withheld_empty (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
    ByteArray.empty Fx silKey B J sh ext h w (keyInstanceOfOutOfDomainSample x)

/-- `BadSmall` at 0, of the shell `keyHonestAny`. -/
theorem badSmall_key :
    BadSmall
      (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P) 0 :=
  prRho_empty _ fun ρ a => by
    have e := bad_empty (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
      (OnBytes.Flat.join₀ rK) ByteArray.empty Fx silKey B J sh ext h
    exact (Set.eq_empty_iff_forall_notMem.1 e) ρ a

/-- `HidSmall` at 0, of the shell `keyHonestAny`, at every relation `Tied`. -/
theorem hidSmall_key
    (Tied : TiedT ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P)) :
    HidSmall
      (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P) Tied
      0 :=
  fun w x _ => prRho_empty _ fun ρ a => by
    have e := hid_empty (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
      (OnBytes.Flat.join₀ rK) ByteArray.empty Fx silKey B J sh ext h w (keyInstanceOfOutOfDomainSample x)
    exact (Set.eq_empty_iff_forall_notMem.1 e) ρ a

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.Stops.stopAt_none
#print axioms AtPublicFiles.Stops.rowStopAt_none
#print axioms AtPublicFiles.Stops.chainStopAt_none
#print axioms AtPublicFiles.Stops.badB_false
#print axioms AtPublicFiles.Stops.hidB_false
#print axioms AtPublicFiles.Stops.stop0B_false
#print axioms AtPublicFiles.Stops.bad_empty
#print axioms AtPublicFiles.Stops.hid_empty
#print axioms AtPublicFiles.Stops.withheld_empty
#print axioms AtPublicFiles.KeyBridge.fallSmall_none
#print axioms AtPublicFiles.AtFiles.withheld_key
#print axioms AtPublicFiles.AtFiles.badSmall_key
#print axioms AtPublicFiles.AtFiles.hidSmall_key
#print axioms AtPublicFiles.Stops.Quiet
#print axioms AtPublicFiles.Stops.NoStop
#print axioms AtPublicFiles.Stops.NoStopAll
