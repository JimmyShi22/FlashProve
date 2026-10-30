-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/ProofSizesAtScope.lean: at public files in the goals' scope, three fields of
the sizes of a proof's chains in what the planner's text at o returns are written values: the
setting, the list of codes, and the first group of the request's own test. Statements and proofs;
no definition.

Why. The law of the kind "the code switch" is stated at records that are computed of these sizes
(`rowOf`, Johnson/Top/H0/K2Caller/Table.lean), and its premises are theorems at 25 written records
(`tableFullLit`, K2Caller/LitRows.lean). To carry them over one needs that the sizes are the written
ones. This file is the half on the sizes; the half on the frames, and the joining, are not here.

How. `Params.proofSized` makes the list of codes by four calls of `ioppStages`, on the stages of the
last test, of the folded row's test, of Omega's test and of the request's own test, beginning at the
empty lists. The four lists of stages in scope are typed lists by
Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean and LastAtScope.lean. The rest is evaluated by
Lean's kernel at these typed lists.

Main statements.
  `proofSized_codes`, `linFinish_codes`: the text of the two makers as far as the codes go.
  `codes_written`, `set_written`, `ownFirst_written`: three closed facts, by the kernel.
  `codes_of_public`, `sizes_of_public`: from `H2K.Sizes.PubFull X`, configure's yes, and the last
    test's stages.
  `set_ownFirst_of_plannedO`: from `plannedAtO o` at files in scope, at every o and every digest:
    the setting and the first group of the request's own test: no further premise.
  `sizes_of_plannedO`: all three fields, UNDER THE PREMISE that the last test's stages are the typed
    list `szLFull`.
  `last_of_plannedO`: that premise, from the closed premise `H2K.Sizes.LayoutGroupsAre`.
  `sizes_at_scope`: so all three fields under that closed premise.

Limits. THE CODES STAND UNDER A PREMISE: that the stages of the first chain's last test are the
typed list. LastAtScope.lean has that from one closed statement on the stored layout file
(`LayoutGroupsAre`), WHICH IS PROVED IN AtFullSide/LayoutRead/GroupsPaid.lean. The setting and the
first group of the request's own test stand under no premise but the scope
(`set_ownFirst_of_plannedO`). Nothing on `request`, on `link` or on the frames. Nothing says that a
description takes its numbers from `plannedAtO o`. Nothing on soundness.

-/
import Johnson.Desc.K12.Law.Sizes.LastAtScope
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope
import Johnson.G.SwitchPricesLit
import OnBytes.Model.Fit.PlannedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifierAndGoals.Sizes
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify OnBytes.Tie
open VerifiableInference.PlanWritten (plannedAtO publicOfO)
open H2K.Sizes H2K.Member Lk6.AtPlan Johnson.G

/-! ## 1. The two makers' text, as far as the codes go -/

/-- `proofSized` hands `linSized` the codes that `ioppStages` makes of the last test's stages,
beginning at the empty lists. -/
theorem proofSized_codes {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    ∃ T : TableSize, linSized (settingOf l) (linLines l sub.matrixRows
        (Send.maskRowsFor
          (sub.pendingRows + (if 1 < sub.pendingRows then Batt.masksOf l.blockLog else 0))
          (2 ^ l.own.maskLogL) l.answers) false) T (ioppStages z.last.stages {}).2 =
      some (z.batch, z.codes) := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, hl, h⟩ := opt_bind h
  obtain ⟨stages, hs, h⟩ := opt_bind h
  obtain ⟨T, hT, h⟩ := opt_bind h
  split at h
  rename_i last codes1 he
  replace h := opt_guard h
  obtain ⟨⟨batch, codes2⟩, hb, h⟩ := opt_bind h
  cases h
  refine ⟨T, ?_⟩
  show linSized _ _ T (ioppStages stages {}).2 = _
  rw [he]
  exact hb

/-- `linSized`'s closing text makes its codes by three more calls of `ioppStages`. -/
theorem linFinish_codes {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x y z : Sizing} {stU stO stW : List StageSize} {r : LinSized}
    (h : linFinish s L T codes x y z stU stO stW = some (r, c)) :
    c = (ioppStages stW (ioppStages stO (ioppStages stU codes).2).2).2 := by
  unfold linFinish at h
  dsimp only at h
  split at h
  · exact ((Prod.mk.inj (Option.some.inj h)).2).symm
  · cases h

/-! ## 2. Three closed facts -/

/-- The four typed lists of stages give the written list of codes. -/
theorem codes_written :
    (ioppStages szWFull (ioppStages szOFull (ioppStages szUFull
      (ioppStages szLFull {}).2).2).2).2 = codesFull2 := by decide +kernel

/-- The typed setting is the written one. -/
theorem set_written : setAt = setLit := by decide +kernel

/-- The first group of a test whose stages are the typed list of the request's own test. -/
theorem ownFirst_written (t : TestSizes) (h : t.stages = szWFull) :
    t.first = { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
                slots := 1, rule := .johnson, m := 159 } := by
  unfold TestSizes.first
  rw [h]
  rfl

/-! ## 3. From configure's yes -/

section
variable {X : Public} (hP0 : PubFull X) {shapes : Shapes} {cfg : ByteArray} {bits : Nat}
  {made : Configured} (hc : configure X.P.frame shapes cfg bits = .ok made) {rl : List ReqLink}
  (he : shapes.sub = subproofsWith X rl)
include hP0 hc he

/-- **The codes**, from the last test's stages. -/
theorem codes_of_public (hL : made.sized.proof.last.stages = szLFull) :
    made.sized.proof.codes = codesFull2 := by
  have hP := (configure_proof_sizes hc).1
  obtain ⟨T, hS⟩ := proofSized_codes hP
  obtain ⟨_, _, _, stU, stO, stW, _, _, _, _, hF⟩ := linSized_named hS
  obtain ⟨u1, u2, u3⟩ := linFinish_stages hF
  have A := atFull_of_public hP0 hc he
  rw [linFinish_codes hF, ← u1, ← u2, ← u3, A.U, A.O, A.W, hL]
  exact codes_written

/-- **The three fields.** -/
theorem sizes_of_public (hL : made.sized.proof.last.stages = szLFull) :
    made.sized.proof.set = setLit ∧ made.sized.proof.codes = codesFull2 ∧
      made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } :=
  ⟨(atFull_of_public hP0 hc he).setP.trans set_written, codes_of_public hP0 hc he hL,
    ownFirst_written _ (atFull_of_public hP0 hc he).W⟩

end

/-! ## 4. At the scope, from the planner's text at o -/

section
variable {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {c : ByteArray}
  {p : Verify.Planned} (hp : plannedAtO o Z.pol Z.KL (some Z.lay) c = .ok p)
include hZ hp

/-- **The setting and the first group of the request's own test: under the scope alone.** -/
theorem set_ownFirst_of_plannedO :
    p.chains.made.sized.proof.set = setLit ∧
      p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } := by
  unfold plannedAtO at hp
  obtain ⟨X, hX, hp⟩ := exc_bind hp
  obtain ⟨chains, hch, hp⟩ := exc_bind hp
  obtain ⟨built, hbu, hp⟩ := exc_bind hp
  cases hp
  obtain ⟨links, shapes, hs, hc, -, -⟩ := chainsOf_parts hch
  obtain ⟨_, _, rl, _, _, he⟩ := shapesOf_sub hs
  have A := atFull_of_publicO hZ hX hc he
  exact ⟨A.setP.trans set_written, ownFirst_written _ A.W⟩

/-- **The three fields, under the premise on the last test's stages.** -/
theorem sizes_of_plannedO (hL : p.chains.made.sized.proof.last.stages = szLFull) :
    p.chains.made.sized.proof.set = setLit ∧ p.chains.made.sized.proof.codes = codesFull2 ∧
      p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } := by
  unfold plannedAtO at hp
  obtain ⟨X, hX, hp⟩ := exc_bind hp
  obtain ⟨chains, hch, hp⟩ := exc_bind hp
  obtain ⟨built, hbu, hp⟩ := exc_bind hp
  cases hp
  obtain ⟨links, shapes, hs, hc, -, -⟩ := chainsOf_parts hch
  obtain ⟨_, _, rl, _, _, he⟩ := shapesOf_sub hs
  exact sizes_of_public (publicO_at_scope hZ hX) hc he hL

/-- **The last test's stages, under the closed premise on the stored layout file.** -/
theorem last_of_plannedO (hG : LayoutGroupsAre) :
    p.chains.made.sized.proof.last.stages = szLFull := by
  unfold plannedAtO at hp
  obtain ⟨X, hX, hp⟩ := exc_bind hp
  obtain ⟨chains, hch, hp⟩ := exc_bind hp
  obtain ⟨built, hbu, hp⟩ := exc_bind hp
  cases hp
  obtain ⟨links, shapes, hs, hc, -, -⟩ := chainsOf_parts hch
  obtain ⟨rl, lay, _, declared, file, _, _, hf, hr, hw⟩ := Fo.shapesOf_cut hs
  obtain ⟨hn0, he⟩ := shapesWith_count hw
  have hg : file.groups = groupsFull := by
    have e : Plan.layoutRead Z.lay = some file := hf
    have hG' : (Plan.layoutRead Z.lay).map (·.groups) = some groupsFull := by
      rw [(Johnson.G.ScopeLines.inScope_files hZ).2]
      exact hG
    rw [e] at hG'
    exact Option.some.inj hG'
  exact last_of_public (publicO_at_scope hZ hX) hc he hr hn0 hg

/-- **The three fields, under the closed premise.** -/
theorem sizes_at_scope (hG : LayoutGroupsAre) :
    p.chains.made.sized.proof.set = setLit ∧ p.chains.made.sized.proof.codes = codesFull2 ∧
      p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } :=
  sizes_of_plannedO hZ hp (last_of_plannedO hZ hp hG)

end

end VerifierAndGoals.Sizes

#print axioms VerifierAndGoals.Sizes.proofSized_codes
#print axioms VerifierAndGoals.Sizes.linFinish_codes
#print axioms VerifierAndGoals.Sizes.codes_written
#print axioms VerifierAndGoals.Sizes.set_written
#print axioms VerifierAndGoals.Sizes.ownFirst_written
#print axioms VerifierAndGoals.Sizes.codes_of_public
#print axioms VerifierAndGoals.Sizes.sizes_of_public
#print axioms VerifierAndGoals.Sizes.set_ownFirst_of_plannedO
#print axioms VerifierAndGoals.Sizes.sizes_of_plannedO
#print axioms VerifierAndGoals.Sizes.last_of_plannedO
#print axioms VerifierAndGoals.Sizes.sizes_at_scope
