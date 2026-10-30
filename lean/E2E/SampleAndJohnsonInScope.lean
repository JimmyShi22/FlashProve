-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`E2E/SampleAndJohnsonInScope.lean`: for public files in scope, the committed table's out-of-domain sample has one answer for each
row, and the decoding radius that is derived for the table lies within the Johnson bound at, and beyond half of, the library's
distance of the table's code.

`OneAnswerAndTarget l` says of the first 32 lines `l` of a parameter file: `answers = 1` (each out-of-domain sample has one answer)
and `sec = 128`.

What this file proves.
* `in_scope`, `in_scope_every`: for all `Z` with `VerifierAndGoals.InScope Z = true`, the Lean reader `readLines` returns at `Z.pol`, and
  whatever it returns satisfies `OneAnswerAndTarget`. `typed_lines_say`: the library's lines `Params.recordLines` satisfy it. (In
  scope the reader returns `recordLines` entire: `Johnson.G.ScopeLines.inScope_reads`. `OneAnswerAndTarget` names two of their
  values.)
* `table_in_scope`: in scope, `deriveTable` returns `Params.recordTable`, whose sample has one answer for each row.
* `plan_in_scope`: in scope, every plan that the verifier's planner `Model.Verify.planned` returns is configured from lines that
  satisfy `OneAnswerAndTarget`, its setting is `settingOf` of these lines, and the table in its link is `recordTable`.
* `radius_of_the_lines`: the radius derived from these lines for the table's one-time proximity test, in whole positions at length
  2^32, is 2,852,142,980, rounded down or up.
* `decoder_at_that_radius`, `collision_is_the_decoders`: the index decoder `frS.toDecR frZ 402653181` has that radius, and `(protocolAtFiles
  Z).hasCollisionAt`, the collision predicate of the protocol object, is that decoder's.
* `distance_is_the_codes`, `beyond_half_the_distance`, `within_johnson`, `below_distance`: `Blocks.HasDist` holds of the table's
  code at 3,848,273,922; twice the radius exceeds that number; the radius meets the library's Johnson condition `Cb.InJohnson` at
  length 2^32 and that number; and it is below that number.
* `sample_and_johnson_in_scope`: these in one proposition, but for `plan_in_scope`, `below_distance` and the table's `answers = 1`,
  for all `Z` in scope.
* `radius_of_the_lines`, `within_johnson`, `below_distance` and `distance_is_the_codes` restate the library's `rr_radius`,
  `record_radius_inJohnson` and `full_dist`; `decoder_at_that_radius` and `collision_is_the_decoders` hold by unfolding.
  This file adds `plan_in_scope`, and that these hold together for all `Z` in scope.

What this file does not say.
* "Distance" is the library's number for the table's Reed-Solomon code, length less dimension plus 1 = 3,848,273,922. `HasDist`
  proves that the minimum distance is at least that number; that it is no more is not proved here.
* `sec = 128` is the value of a line: the target at which the parameters are sized. It is no statement on a soundness error.
* That the radius meets the Johnson condition is a fact on a number. It says nothing on which theorem bounds the soundness error of
  a proximity round.
* No group's derived radius is evaluated here but the table's. For the stages of the nine proximity tests see
  `E2E/StagesAtOrBeyondHalfTheDistance.lean`; for the sampled messages of the full-size list, a literal, see
  `Johnson/G/PackLitArms.lean`.
* The plan is that of `Model.Verify.planned`. That the protocol object `protocolAtFiles Z`, or `verify`, is built from that plan is not shown
  here. The object's decoder is tied to the files by its radius alone, a number written in the text of `frS`, not by a derivation
  from the files.
* Beyond the number of answers, the out-of-domain samples of oracle messages inside the proximity tests, of either phase, are not
  treated: "sample" here is the committed table's own (the first table's and a copy's).
* Facts evaluated by `decide +kernel` lie beneath these statements: the library's `lines_at32`, `record_table`, `rr_radius`.
-/
import Johnson.Goal.Conditions.LinkTypedAtLines
import OnBytes.Params.RecordRound
import OnBytes.Flat.EntryRecord
import E2E.BridgeJoinAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.AtFiles.InScopeSetting
open OnBytes OnBytes.Params

/-! ## 1. The lines -/

/-- **What the lines say**: each out-of-domain sample has one answer; the target at which the parameters are sized is 128. -/
structure OneAnswerAndTarget (l : Lines) : Prop where
  answers : l.answers = 1
  target : l.sec = 128

/-- The library's lines `recordLines` say so. -/
theorem typed_lines_say : OneAnswerAndTarget recordLines :=
  ⟨rfl, rfl⟩

/-- **In scope the reader returns, and what it returns says so.** -/
theorem in_scope {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true) :
    ∃ l b, readLines Z.pol = .ok (l, b) ∧ OneAnswerAndTarget l := by
  obtain ⟨b, hb⟩ := Johnson.G.ScopeLines.inScope_reads scope
  exact ⟨recordLines, b, hb, typed_lines_say⟩

/-- Whatever the reader returns at a parameter file in scope says so. -/
theorem in_scope_every {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true) {l : Lines} {b : ByteArray}
    (h : readLines Z.pol = .ok (l, b)) : OneAnswerAndTarget l := by
  obtain ⟨b', hb⟩ := Johnson.G.ScopeLines.inScope_reads scope
  rw [hb] at h
  injection h with h
  injection h with h1 _
  exact h1 ▸ typed_lines_say

/-! ## 2. The table -/

/-- **In scope the table is `recordTable`, with one answer for each row to its out-of-domain sample.** -/
theorem table_in_scope {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true) {l : Lines} {b : ByteArray}
    (h : readLines Z.pol = .ok (l, b)) :
    deriveTable (settingOf l) l = some recordTable ∧ recordTable.answers = 1 := by
  obtain ⟨b', hb⟩ := Johnson.G.ScopeLines.inScope_reads scope
  rw [hb] at h
  injection h with h
  injection h with h1 _
  subst h1
  exact ⟨record_table, rfl⟩

/-! ## 3. The verifier's plan -/

/-- **Every plan that the verifier's planner returns at files in scope is configured from lines that say so, and the table in its link is
`recordTable`.** -/
theorem plan_in_scope {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true) {p : Model.Verify.Planned}
    (h : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    ∃ l rest shapes, readLines Z.pol = .ok (l, rest) ∧
      configure l shapes p.cfg 0 = .ok p.chains.made ∧ OneAnswerAndTarget l ∧
      p.chains.made.sized.set = settingOf l ∧
      p.chains.made.sized.link.table = recordTable := by
  obtain ⟨l, rest, shapes, hl, hm⟩ := Model.Verify.planned_madeKey h
  have hsay := in_scope_every scope hl
  obtain ⟨hs, T, hT, hL⟩ := sized_link (configure_sized hm)
  obtain ⟨b', hb⟩ := Johnson.G.ScopeLines.inScope_reads scope
  have e : l = recordLines := by
    rw [hb] at hl
    injection hl with hl
    injection hl with h1 _
    exact h1.symm
  subst e
  obtain rfl : T = recordTable := Option.some.inj (hT.symm.trans record_table)
  have hq := Option.some.inj (hL.symm.trans record_link)
  have q1 : p.chains.made.sized.link = ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩ :=
    congrArg Prod.fst hq
  exact ⟨recordLines, rest, shapes, hl, hm, hsay, hs, by rw [q1]⟩

/-! ## 4. The radius -/

/-- **The radius that is derived from these lines for the table's one-time test, in whole positions.** -/
theorem radius_of_the_lines :
    lowerRadius (tableAnalysis (settingOf recordLines) recordTable).once.delta (2 ^ 32) = 2852142980 ∧
      upperRadius (tableAnalysis (settingOf recordLines) recordTable).once.delta (2 ^ 32) = 2852142980 :=
  ⟨rr_radius.1, rr_radius.2.1⟩

open OnBytes.Slice (frS frZ) in
/-- **The protocol object's index decoder works at that radius.** -/
theorem decoder_at_that_radius : (frS.toDecR frZ 402653181).eM = 2852142980 := rfl

open OnBytes.Slice (frS frZ) in
/-- The protocol object's collisions are that decoder's: by unfolding. -/
theorem collision_is_the_decoders (Z : VerifierAndGoals.PublicFiles) :
    (AtPublicFiles.AtFiles.protocolAtFiles Z).hasCollisionAt = (frS.toDecR frZ 402653181).coll := rfl

/-- **Beyond half the distance**: twice the radius exceeds the library's distance of the table's code. -/
theorem beyond_half_the_distance : 3848273922 < 2 * 2852142980 := by decide

/-- **Within the Johnson bound**, in the library's form, at length 2^32 and the code's distance. -/
theorem within_johnson : Cb.InJohnson (2 ^ 32) 3848273922 2852142980 :=
  record_radius_inJohnson.1

/-- Below the distance. -/
theorem below_distance : 2852142980 < 3848273922 := by decide

open OnBytes.Slice (frS) in
/-- `HasDist` holds of the table's code at 3,848,273,922: its minimum distance is at least that number (the library's full_dist). -/
theorem distance_is_the_codes : Blocks.HasDist frS.ix.G 3848273922 := OnBytes.K.Oracle.full_dist.1

/-! ## 5. Together -/

open OnBytes.Slice (frS frZ) in
/-- **In scope: the lines, the table, the radius, the decoder and the two comparisons in one proposition.** -/
theorem sample_and_johnson_in_scope {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true) :
    (∃ l b, readLines Z.pol = .ok (l, b) ∧ OneAnswerAndTarget l ∧
      deriveTable (settingOf l) l = some recordTable ∧
      lowerRadius (tableAnalysis (settingOf l) recordTable).once.delta (2 ^ 32) = 2852142980 ∧
      upperRadius (tableAnalysis (settingOf l) recordTable).once.delta (2 ^ 32) = 2852142980) ∧
    (AtPublicFiles.AtFiles.protocolAtFiles Z).hasCollisionAt = (frS.toDecR frZ 402653181).coll ∧
    (frS.toDecR frZ 402653181).eM = 2852142980 ∧
    Blocks.HasDist frS.ix.G 3848273922 ∧
    3848273922 < 2 * 2852142980 ∧ Cb.InJohnson (2 ^ 32) 3848273922 2852142980 := by
  obtain ⟨b, hb⟩ := Johnson.G.ScopeLines.inScope_reads scope
  exact ⟨⟨recordLines, b, hb, typed_lines_say, record_table, radius_of_the_lines.1,
    radius_of_the_lines.2⟩, rfl, rfl, distance_is_the_codes, beyond_half_the_distance, within_johnson⟩

end AtPublicFiles.AtFiles.InScopeSetting

#print axioms AtPublicFiles.AtFiles.InScopeSetting.typed_lines_say
#print axioms AtPublicFiles.AtFiles.InScopeSetting.in_scope
#print axioms AtPublicFiles.AtFiles.InScopeSetting.in_scope_every
#print axioms AtPublicFiles.AtFiles.InScopeSetting.table_in_scope
#print axioms AtPublicFiles.AtFiles.InScopeSetting.plan_in_scope
#print axioms AtPublicFiles.AtFiles.InScopeSetting.radius_of_the_lines
#print axioms AtPublicFiles.AtFiles.InScopeSetting.decoder_at_that_radius
#print axioms AtPublicFiles.AtFiles.InScopeSetting.collision_is_the_decoders
#print axioms AtPublicFiles.AtFiles.InScopeSetting.beyond_half_the_distance
#print axioms AtPublicFiles.AtFiles.InScopeSetting.within_johnson
#print axioms AtPublicFiles.AtFiles.InScopeSetting.below_distance
#print axioms AtPublicFiles.AtFiles.InScopeSetting.distance_is_the_codes
#print axioms AtPublicFiles.AtFiles.InScopeSetting.sample_and_johnson_in_scope
#check @AtPublicFiles.AtFiles.InScopeSetting.sample_and_johnson_in_scope
#check @AtPublicFiles.AtFiles.InScopeSetting.plan_in_scope
