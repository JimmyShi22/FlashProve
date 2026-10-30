-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`E2E/ExtractorAtHonestTables.lean`: completeness and soundness of the interactive oracle proof speak of one index and one relation,
at the protocol object `protocolAtFiles Z` of the public files `Z`.

That the two statements name the same verifier does not yet say: (1) `ServedRequest i x → relationAtFiles Z i x`: the relation of
completeness lies in the relation of soundness; (2) `extractIndex (encodeIndex i r) (recOf i r e) = some i`: soundness's extractor, at the
honest table and its out-of-domain sample, finds the honest index; (3) `¬ hasCollisionAt (encodeIndex i r) e`: the honest table has no collision at
the point of its sample.

What this file proves.
* `relation_is_the_objects`: `relationAtFiles Z` is `AtPublicFiles.Committed.RyesZ Z`, by unfolding (the configuration's `Ryes` and `Rno` are
  one text: `OnBytes.Flat.relationsAndEncodingOfClaims`). So the largest of the three nested relations of `E2E/CompleteAsIOPAtFiles.lean` is soundness's
  own.
* `served_in_relation`: (1), for `Z` in scope and read.
* `no_collision_at_honest`: (3), for every matrix `i`, in range or not, all encoding randomness `r` and every point `e`.
* `extract_honest_iff`: (2) holds if and only if `i` is in range. `extract_inRange`: at every table and sample, the extractor
  answers matrices in range alone; so out of range (2) fails at all `r`, `e`. `extract_honest`: (2) where `i` is in range.
  `inRange_of_relation`: a pair in soundness's relation has its matrix in range.
* `extract_at_served`, `oneIndexOneRelation`: (1), (2) and (3) together at every served request, and some request is served
  (`OneIndexOneRelationAt Z`), for `Z` in scope.
* `honest_tables_conclude`: for `Z` in scope and read and every served request `(i, x)`: at the honest first table and an honest
  copy (other randomness, other point), each with its honest sample, the three clauses behind "∃ index" in soundness's conclusion
  `WholeRun.Concludes` hold at `index := i`. `only_the_honest_index`: for `i` in range, the extractor answers no other index there.
* `sound_and_tied`: `OneIndexOneRelationAt Z` beside the soundness theorem's own conclusion at `protocolAtFiles Z`, in one proposition, for `Z`
  in scope, read, and passing the public test `protocolDataWellFormed`.
* `oneIndexOneRelation_zFull`, `zFull_is_read`: at `VerifierAndGoals.storedPublicFiles`, the library's written copy of the full-size public files, with no
  premise. With the soundness theorem's conclusion beside it, which needs the side library:
  `AtFullSide/E2E/ExtractorAtHonestTablesAtWritten.lean`.
* `object_decoder_in_range`, `object_has_no_collision`: the two general statements beneath, at any stored table with an
  out-of-domain sample; the second under the premise that the radius is below the code's distance.
* `wholeRun_concludes_at_honest`: soundness's conclusion at a whole run on honest tables, under a strong premise: every accepted
  request with the named one's early part is served at `i`. The premise assumes most of what one would wish to conclude, so the
  statement says little.

What this file does not say.
* Nothing here says that any prover is accepted: this is not completeness. Nothing is said on zero knowledge.
* The scope is a premise of (1) (`servedRequest_below` uses it); (2) and (3) have no premise on `Z`.
* (1) is an inclusion, not an equation: the relation also holds of outputs that the files' policy accepts and that are not the
  model's own.
* "No collision" rests on this: the radius is below the code's distance (`OnBytes.K.Oracle.full_dist`), so within that radius of a
  table of code words lies that table alone. Of tables that are not code words nothing is said here; there soundness's clause
  `samplePoint` counts.
* `encodeIndex` and `honestOutOfDomainAnswer` are the honest fields of the protocol object (`OnBytes.Flat.codingCells`). That a program writes its tables so is
  not said.
-/
import E2E.SoundAsIOPAtFilesProofs
import E2E.CompleteAsIOPAtFiles
import E2E.CompleteAsIOPServedLaws
import Johnson.Goal.Files.ScopeExample

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.AtHonestTables
open Iop Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice
open OnBytes.Flat (Files relationsAndEncodingOfClaims codingHonest rowWords tailWords)

/-! ## 1. General statements -/

section General

/-- **The index decoder of a stored table with an out-of-domain sample answers matrices in range alone**: at every table and every sample. -/
theorem object_decoder_in_range {D : DecR} {X : Type} (A : D.Claims X) (R : D.RelationsAndEncoding A) (F : Files (DecR.configurationOfStoredTable A R))
    (P : F.Provers) (y : (F.withProvers P).Table) (rec : (F.withProvers P).Sample) (M : A.Mat)
    (h : (F.withProvers P).decodeIndex y rec = some M) : A.inRange M := by
  classical
  have h' : (DecR.configurationOfStoredTable A R).D y rec = some M := h
  rw [DecR.conf_D] at h'
  by_cases hc : D.coll y rec.1
  · rw [if_pos hc] at h'
    cases h'
  · rw [if_neg hc] at h'
    obtain ⟨u, -, hu⟩ := Option.bind_eq_some_iff.1 h'
    have hu' : (if A.inRange (A.mat u) then some (A.mat u) else none) = some M := hu
    by_cases g : A.inRange (A.mat u)
    · rw [if_pos g] at hu'
      exact Option.some.inj hu' ▸ g
    · rw [if_neg g] at hu'
      cases hu'

variable (S : Sz) (Z : Sample GE S.En) (cut : ℕ) {X : Type} (A : (S.toDecR Z cut).Claims X)
  (Pad : Type) [Fintype Pad] [Nonempty Pad] (holdW : A.Mat → Pad → ℕ → List UInt64) {d : ℕ}

/-- **The honest table has no collision, at any point**: for every matrix, in range or not, if the radius is below the code's distance. -/
theorem object_has_no_collision (hd : HasDist S.ix.G d) (he : S.eM < d)
    (F : Files (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A (codingHonest S Z cut A Pad holdW)))) (P : F.Provers)
    (M : A.Mat) (r : (F.withProvers P).EncodingRandomness) (s : (F.withProvers P).OutOfDomainSeed) :
    ¬ (F.withProvers P).hasCollisionAt ((F.withProvers P).encodeIndex M r) s :=
  OnBytes.K.Oracle.not_coll_words (S.toDecR Z cut) hd he _
    (honestPolys S (rowWords S (honestMsgs S (holdW M r.1))) (tailWords S r.2))
    (tab_honestTab S _ _) s

end General

/-! ## 2. At the public files Z -/

open AtPublicFiles.AtFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (committerCoinCountLessOne protocolDataWellFormed)

/- Among all that this file imports, the search for this instance runs out of its budget (as in E2E/BridgeJoinAtFiles.lean). It is a proposition,
so whichever proof is found, the statements below are the same. -/
local instance (priority := high) padsNonemptyAtHonestTables : Nonempty (OnBytes.Flat.PadsOf frS 402653181) :=
  AtPublicFiles.Committed.pads_nonempty frS 402653181

/-- **Soundness's relation is the protocol object's relation**, the largest of the three that completeness nests: by unfolding. -/
theorem relation_is_the_objects (Z : PublicFiles) : relationAtFiles Z = AtPublicFiles.Committed.RyesZ Z := rfl

/-- **(1) A served request is in soundness's relation.** -/
theorem served_in_relation (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (i : FullSizeMatrix) (x : XF) (h : ServedRequest committerCoinCountLessOne Z hr i x) : relationAtFiles Z i x :=
  servedRequest_below committerCoinCountLessOne Z scope hr h

/-- What is in soundness's relation has its matrix in range. -/
theorem inRange_of_relation (Z : PublicFiles) (i : FullSizeMatrix) (x : XF) (h : relationAtFiles Z i x) : inRange i := h.1

/-- **(3) No collision at the honest table**: every matrix, all randomness, every point. -/
theorem no_collision_at_honest (Z : PublicFiles) (i : FullSizeMatrix) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) :
    ¬ (protocolAtFiles Z).hasCollisionAt ((protocolAtFiles Z).encodeIndex i r) e :=
  object_has_no_collision frS frZ 402653181 _ _ _ OnBytes.K.Oracle.full_dist.1 OnBytes.K.Oracle.full_dist.2
    (filesAt Z) _ i r e

/-- The extractor answers matrices in range alone: at every table and sample. -/
theorem extract_inRange (Z : PublicFiles) (table : (protocolAtFiles Z).Table) (sample : (protocolAtFiles Z).Sample) (i : FullSizeMatrix)
    (h : (protocolAtFiles Z).extractIndex table sample = some i) : inRange i :=
  object_decoder_in_range _ _ (filesAt Z) _ table sample i h

/-- **(2) At the honest table and its honest sample the extractor answers the honest index**, if it is in range. -/
theorem extract_honest (Z : PublicFiles) (i : FullSizeMatrix) (hi : inRange i) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) :
    (protocolAtFiles Z).extractIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) = some i :=
  OnBytes.Flat.obj_decodes_cells_full _ _ (filesAt Z) _ i hi r e

/-- **(2), exactly**: if and only if the index is in range. -/
theorem extract_honest_iff (Z : PublicFiles) (i : FullSizeMatrix) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) :
    (protocolAtFiles Z).extractIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) = some i ↔ inRange i :=
  ⟨extract_inRange Z _ _ i, fun hi => extract_honest Z i hi r e⟩

/-- (2) at a served request. -/
theorem extract_at_served (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (i : FullSizeMatrix) (x : XF) (h : ServedRequest committerCoinCountLessOne Z hr i x) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) :
    (protocolAtFiles Z).extractIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) = some i :=
  extract_honest Z i (inRange_of_relation Z i x (served_in_relation Z scope hr i x h)) r e

/-- **One index, one relation, at Z**: some request is served; and at every served request (i, x): (1) it is in soundness's relation; at all
encoding randomness and every point, (3) the honest table has no collision and (2) the extractor answers i. -/
def OneIndexOneRelationAt (Z : PublicFiles) : Prop :=
  ∀ {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp),
    (∃ (i : FullSizeMatrix) (x : XF), ServedRequest committerCoinCountLessOne Z hr i x) ∧
    ∀ (i : FullSizeMatrix) (x : XF), ServedRequest committerCoinCountLessOne Z hr i x →
      relationAtFiles Z i x ∧
      ∀ (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed),
        ¬ (protocolAtFiles Z).hasCollisionAt ((protocolAtFiles Z).encodeIndex i r) e ∧
        (protocolAtFiles Z).extractIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) = some i

theorem oneIndexOneRelation (Z : PublicFiles) (scope : InScope Z = true) : OneIndexOneRelationAt Z :=
  fun hr => ⟨servedRequest_met committerCoinCountLessOne Z scope hr, fun i x h =>
    ⟨served_in_relation Z scope hr i x h, fun r e =>
      ⟨no_collision_at_honest Z i r e, extract_at_served Z scope hr i x h r e⟩⟩⟩

/-- **At honest tables, what soundness concludes holds at the honest index**: the three clauses behind "∃ index" in
WholeRun.Concludes, at index := i, for the honest first table and an honest copy with randomness and point of its own. -/
theorem honest_tables_conclude (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (i : FullSizeMatrix) (x : XF) (h : ServedRequest committerCoinCountLessOne Z hr i x) (r r' : (protocolAtFiles Z).EncodingRandomness) (e e' : (protocolAtFiles Z).OutOfDomainSeed) :
    (protocolAtFiles Z).extractIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) = some i ∧
      (protocolAtFiles Z).decodeIndex ((protocolAtFiles Z).encodeIndex i r') ((protocolAtFiles Z).recOf i r' e') = some i ∧ relationAtFiles Z i x :=
  ⟨extract_at_served Z scope hr i x h r e, extract_at_served Z scope hr i x h r' e', served_in_relation Z scope hr i x h⟩

/-- **And at no other**: whichever index the extractor answers at the honest table and sample of a matrix in range, it is that matrix. -/
theorem only_the_honest_index (Z : PublicFiles) (i : FullSizeMatrix) (hi : inRange i) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (index : FullSizeMatrix)
    (h : (protocolAtFiles Z).extractIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) = some index) : index = i :=
  (Option.some.inj ((extract_honest Z i hi r e).symm.trans h)).symm

/-- **A whole run on honest tables concludes, at the honest index**: soundness's own conclusion (WholeRun.Concludes, at soundness's relation), for
every whole run whose two tables and samples are the honest ones of i, where every request with the named one's early part that the three verifiers
accept is served at i. -/
theorem wholeRun_concludes_at_honest (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (i : FullSizeMatrix) (r r' : (protocolAtFiles Z).EncodingRandomness) (e e' : (protocolAtFiles Z).OutOfDomainSeed) (run : (protocolAtFiles Z).WholeRun)
    (h1 : run.firstTable = (protocolAtFiles Z).encodeIndex i r) (h2 : run.firstSample = (protocolAtFiles Z).recOf i r e)
    (h3 : run.copy = (protocolAtFiles Z).encodeIndex i r') (h4 : run.copySample = (protocolAtFiles Z).recOf i r' e')
    (hs : ∀ request, (protocolAtFiles Z).early request = (protocolAtFiles Z).early run.named → run.Accepted request →
      ServedRequest committerCoinCountLessOne Z hr i request) :
    run.Concludes (relationAtFiles Z) := by
  intro request he ha
  have h := honest_tables_conclude Z scope hr i request (hs request he ha) r r' e e'
  refine ⟨i, ?_, ?_, h.2.2⟩
  · rw [h1, h2]
    exact h.1
  · rw [h3, h4]
    exact h.2.1

/-- **Beside the soundness theorem's own conclusion**, in one proposition, at one constant protocolAtFiles Z and one relation relationAtFiles Z. -/
theorem sound_and_tied (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (protocolAtFiles Z).IndexKnowledgeSoundIOP (relationAtFiles Z) (filesAt Z).annT (offlinePlaces Z) (filesAt Z).annL 1
      ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧ OneIndexOneRelationAt Z :=
  ⟨soundAsIOPAtTheProtocol Z pp scope hr live, oneIndexOneRelation Z scope⟩

/-! ## 3. At the library's written copy of the full-size public files: no premise is left -/

/-- The written files are read: the "for every reading" of OneIndexOneRelationAt is not vacuous there. -/
theorem zFull_is_read : ∃ pp, readFiles VerifierAndGoals.storedPublicFiles = .ok pp :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨pp, hr⟩

/-- **One index, one relation, at the written files.** No premise. -/
theorem oneIndexOneRelation_zFull : OneIndexOneRelationAt VerifierAndGoals.storedPublicFiles :=
  oneIndexOneRelation VerifierAndGoals.storedPublicFiles VerifierAndGoals.inScope_full

end AtPublicFiles.AtFiles.AtHonestTables
end

#print axioms AtPublicFiles.AtFiles.AtHonestTables.object_decoder_in_range
#print axioms AtPublicFiles.AtFiles.AtHonestTables.object_has_no_collision
#print axioms AtPublicFiles.AtFiles.AtHonestTables.relation_is_the_objects
#print axioms AtPublicFiles.AtFiles.AtHonestTables.served_in_relation
#print axioms AtPublicFiles.AtFiles.AtHonestTables.inRange_of_relation
#print axioms AtPublicFiles.AtFiles.AtHonestTables.no_collision_at_honest
#print axioms AtPublicFiles.AtFiles.AtHonestTables.extract_inRange
#print axioms AtPublicFiles.AtFiles.AtHonestTables.extract_honest
#print axioms AtPublicFiles.AtFiles.AtHonestTables.extract_honest_iff
#print axioms AtPublicFiles.AtFiles.AtHonestTables.extract_at_served
#print axioms AtPublicFiles.AtFiles.AtHonestTables.oneIndexOneRelation
#print axioms AtPublicFiles.AtFiles.AtHonestTables.honest_tables_conclude
#print axioms AtPublicFiles.AtFiles.AtHonestTables.only_the_honest_index
#print axioms AtPublicFiles.AtFiles.AtHonestTables.wholeRun_concludes_at_honest
#print axioms AtPublicFiles.AtFiles.AtHonestTables.sound_and_tied
#print axioms AtPublicFiles.AtFiles.AtHonestTables.zFull_is_read
#print axioms AtPublicFiles.AtFiles.AtHonestTables.oneIndexOneRelation_zFull
#check @AtPublicFiles.AtFiles.AtHonestTables.oneIndexOneRelation
#check @AtPublicFiles.AtFiles.AtHonestTables.zFull_is_read
#check @AtPublicFiles.AtFiles.AtHonestTables.oneIndexOneRelation_zFull
#check @AtPublicFiles.AtFiles.AtHonestTables.sound_and_tied
