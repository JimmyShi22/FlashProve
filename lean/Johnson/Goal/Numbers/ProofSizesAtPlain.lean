-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/ProofSizesAtPlain.lean: the three fields of ProofSizesAtScope.lean (the
setting, the list of codes, the first group of the request's own test) at what the proof file's
description plans with: `ProofFile.Plain.planned o` and `ProofFile.PlainG.madeOf o`
(Johnson/Desc/ProofFile/PlanPlain.lean). Statements and proofs; no definition.

Why. The proof file's description does not call `plannedAtO o`: it has a text of its own for the
plan, with records of the segments that hold no routine. Its public part is `publicOfO o`'s, and it
calls the same `Params.configure` on shapes that the same `shapesWith` makes. ProofSizesAtScope.lean
states the three fields from these alone (`sizes_of_public`), so they carry over.

Main statements.
  `plainShapesOf_cut`, `plainChainsOf_cut`, `plain_parts`: a run of the plain texts, taken apart.
  `atFull_of_plain`: in scope its sizes are as at the full size (`H2K.Sizes.AtFull`: ten fields, the
    table's shape `fold.index` among them).
  `set_ownFirst_of_plain`: in scope: the setting and the first group of the request's own test.
  `sizes_of_plain`: all three, UNDER THE PREMISE that the last test's stages are `szLFull`.
  `last_of_plain`: that premise, from the closed premise `H2K.Sizes.LayoutGroupsAre`.
  `sizes_of_plain_scope`: all three under that closed premise.
  `made_planned`: what `ProofFile.PlainG.madeOf o` returns holds what `ProofFile.Plain.planned o` returns.
  `atFull_of_made`, `set_ownFirst_of_made`, `sizes_of_made`, `sizes_of_made_scope`: the same at
    `madeOf`'s value.

Limits. As in ProofSizesAtScope.lean: THE CODES STAND UNDER A PREMISE, whose closed form is proved
nowhere. Nothing on `request`, `link` or the frames. That the description's public part holds
`madeOf`'s value is not said here. Nothing on soundness.

-/
import Johnson.Goal.Numbers.ProofSizesAtScope
import Johnson.Desc.ProofFile.PlanPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifierAndGoals.Sizes
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Tie
open VerifiableInference.PlanWritten (publicOfO)
open H2K.Sizes H2K.Member Lk6.AtPlan Johnson.G

/-! ## 1. A run of the plain texts, taken apart -/

/-- A run of the plain `shapesOf`: the layout file as read, the frame's links, the shapes. -/
theorem plainShapesOf_cut {X : Public} {lf : Option ByteArray} {links : Array LinkH} {x : Shapes}
    (h : ProofFile.Plain.shapesOf X lf = .ok (links, x)) :
    ∃ rl lay declared file,
      lf.bind Plan.layoutRead = some file ∧
      Plan.reqFrame declared file X.P.frame.answers = some (rl, lay) ∧
      shapesWith X rl lay (links.toList.map (·.gid)) = .ok x := by
  unfold ProofFile.Plain.shapesOf at h
  obtain ⟨links0, h0, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨links1, declared⟩, h1, h⟩ := exc_bind h
  dsimp only at h
  cases hf : lf.bind Plan.layoutRead with
  | none =>
    rw [hf] at h
    cases h
  | some file =>
    rw [hf] at h
    dsimp only at h
    obtain ⟨file', e1, h⟩ := exc_bind h
    obtain rfl : file = file' := Except.ok.inj e1
    cases hr : Plan.reqFrame declared file X.P.frame.answers with
    | none =>
      rw [hr] at h
      cases h
    | some y =>
      rw [hr] at h
      dsimp only at h
      obtain ⟨y', e2, h⟩ := exc_bind h
      obtain rfl : y = y' := Except.ok.inj e2
      obtain ⟨x', h4, h⟩ := exc_bind h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      exact ⟨y.1, y.2, declared, file, rfl, hr, h4⟩

/-- A run of the plain `chainsOf`: the shapes, and configure's yes. -/
theorem plainChainsOf_cut {X : Public} {lf : Option ByteArray} {cfg : ByteArray} {c : Chains}
    (h : ProofFile.Plain.chainsOf X lf cfg = .ok c) :
    ∃ links x, ProofFile.Plain.shapesOf X lf = .ok (links, x) ∧
      configure X.P.frame x cfg 0 = .ok c.made := by
  unfold ProofFile.Plain.chainsOf at h
  obtain ⟨⟨links, x⟩, hs, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨made, hm, h⟩ := exc_bind h
  split at h
  · cases h
    exact ⟨links, x, hs, hm⟩
  · cases h

/-- **A run of the plain `planned`, taken apart.** -/
theorem plain_parts {o : VerifierAndGoals.SecondHashFunctionType} {pol KL lay : ByteArray} {p : Verify.Planned}
    (hp : ProofFile.Plain.planned o pol KL (some lay) = .ok p) :
    ∃ X shapes rl lay' declared file,
      publicOfO o pol KL (some lay) = .ok X ∧
      configure X.P.frame shapes VerifiableInference.Desc.fixedConfigurationDigest 0 = .ok p.chains.made ∧
      shapes.sub = subproofsWith X rl ∧
      Plan.reqFrame declared file X.P.frame.answers = some (rl, lay') ∧
      rl.length = (if X.p4 then 2 else 1) * X.NGr + 1 ∧
      Plan.layoutRead lay = some file := by
  unfold ProofFile.Plain.planned at hp
  obtain ⟨X, hX, hp⟩ := exc_bind hp
  dsimp only at hp
  obtain ⟨chains, hch, hp⟩ := exc_bind hp
  obtain ⟨built, hbu, hp⟩ := exc_bind hp
  cases hp
  obtain ⟨links, x, hs, hc⟩ := plainChainsOf_cut hch
  obtain ⟨rl, lay', declared, file, hf, hr, hw⟩ := plainShapesOf_cut hs
  obtain ⟨hn0, he⟩ := shapesWith_count hw
  exact ⟨X, x, rl, lay', declared, file, hX, hc, he, hr, hn0, hf⟩

/-! ## 2. At the scope, from the plain `planned` -/

section
variable {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Verify.Planned}
  (hp : ProofFile.Plain.planned o Z.pol Z.KL (some Z.lay) = .ok p)
include hZ hp

/-- **In scope the plain road's sizes are as at the full size.** -/
theorem atFull_of_plain : AtFull p.chains.made := by
  obtain ⟨X, shapes, rl, _, _, _, hX, hc, he, _, _, _⟩ := plain_parts hp
  exact atFull_of_publicO hZ hX hc he

/-- **The setting and the first group of the request's own test: under the scope alone.** -/
theorem set_ownFirst_of_plain :
    p.chains.made.sized.proof.set = setLit ∧
      p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } := by
  obtain ⟨X, shapes, rl, _, _, _, hX, hc, he, _, _, _⟩ := plain_parts hp
  have A := atFull_of_publicO hZ hX hc he
  exact ⟨A.setP.trans set_written, ownFirst_written _ A.W⟩

/-- **The three fields, under the premise on the last test's stages.** -/
theorem sizes_of_plain (hL : p.chains.made.sized.proof.last.stages = szLFull) :
    p.chains.made.sized.proof.set = setLit ∧ p.chains.made.sized.proof.codes = codesFull2 ∧
      p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } := by
  obtain ⟨X, shapes, rl, _, _, _, hX, hc, he, _, _, _⟩ := plain_parts hp
  exact sizes_of_public (publicO_at_scope hZ hX) hc he hL

/-- **The last test's stages, under the closed premise on the stored layout file.** -/
theorem last_of_plain (hG : LayoutGroupsAre) :
    p.chains.made.sized.proof.last.stages = szLFull := by
  obtain ⟨X, shapes, rl, lay', declared, file, hX, hc, he, hr, hn0, hf⟩ := plain_parts hp
  have hg : file.groups = groupsFull := by
    have hG' : (Plan.layoutRead Z.lay).map (·.groups) = some groupsFull := by
      rw [(Johnson.G.ScopeLines.inScope_files hZ).2]
      exact hG
    rw [hf] at hG'
    exact Option.some.inj hG'
  exact last_of_public (publicO_at_scope hZ hX) hc he hr hn0 hg

/-- **The three fields, under the closed premise.** -/
theorem sizes_of_plain_scope (hG : LayoutGroupsAre) :
    p.chains.made.sized.proof.set = setLit ∧ p.chains.made.sized.proof.codes = codesFull2 ∧
      p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } :=
  sizes_of_plain hZ hp (last_of_plain hZ hp hG)

end

/-! ## 3. The same at what `madeOf` returns -/

/-- What the plain `madeOf` returns holds what the plain `planned` returns. -/
theorem made_planned {o : VerifierAndGoals.SecondHashFunctionType} {pol lay KL : ByteArray} {m : Johnson.G.OfPlan.Made}
    (h : ProofFile.PlainG.madeOf o pol lay KL = .ok m) :
    ProofFile.Plain.planned o pol KL (some lay) = .ok m.p := by
  unfold ProofFile.PlainG.madeOf at h
  obtain ⟨p, hp, h⟩ := exc_bind h
  obtain ⟨l, hl, h⟩ := exc_bind h
  split at h
  · obtain rfl : _ = m := Except.ok.inj h
    exact hp
  · cases h

section
variable {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
  {m : Johnson.G.OfPlan.Made} (h : ProofFile.PlainG.madeOf o Z.pol Z.lay Z.KL = .ok m)
include hZ h

theorem atFull_of_made : AtFull m.p.chains.made := atFull_of_plain hZ (made_planned h)

theorem set_ownFirst_of_made :
    m.p.chains.made.sized.proof.set = setLit ∧
      m.p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } :=
  set_ownFirst_of_plain hZ (made_planned h)

theorem sizes_of_made (hL : m.p.chains.made.sized.proof.last.stages = szLFull) :
    m.p.chains.made.sized.proof.set = setLit ∧ m.p.chains.made.sized.proof.codes = codesFull2 ∧
      m.p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } :=
  sizes_of_plain hZ (made_planned h) hL

theorem sizes_of_made_scope (hG : LayoutGroupsAre) :
    m.p.chains.made.sized.proof.set = setLit ∧ m.p.chains.made.sized.proof.codes = codesFull2 ∧
      m.p.chains.made.sized.proof.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } :=
  sizes_of_plain_scope hZ (made_planned h) hG

end

end VerifierAndGoals.Sizes

#print axioms VerifierAndGoals.Sizes.plain_parts
#print axioms VerifierAndGoals.Sizes.atFull_of_plain
#print axioms VerifierAndGoals.Sizes.set_ownFirst_of_plain
#print axioms VerifierAndGoals.Sizes.sizes_of_plain
#print axioms VerifierAndGoals.Sizes.last_of_plain
#print axioms VerifierAndGoals.Sizes.sizes_of_plain_scope
#print axioms VerifierAndGoals.Sizes.made_planned
#print axioms VerifierAndGoals.Sizes.atFull_of_made
#print axioms VerifierAndGoals.Sizes.set_ownFirst_of_made
#print axioms VerifierAndGoals.Sizes.sizes_of_made
#print axioms VerifierAndGoals.Sizes.sizes_of_made_scope
