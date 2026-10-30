-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/PlainMade.lean: where the public part of the proof file's description is
computed, its fields come from one call of the planner. Theorems only; no file of the description
imports this one.
Why. Tests such as `everyOk` (Johnson/Desc/Ok/FormRules.lean) and `proofOk`
(Johnson/Desc/MadeOk.lean) read the planner's record `Z.p.chains.made`, while the blocks follow the
plans that were read back from that record's byte strings (`Z.p.chains.proof`) and the declared
rounds `Z.D`. A law that joins the two needs to know that they come from one call. FormRules.lean
asks for just that premise: `configure l x cfg bits = .ok M`.
  `chainsOf_made`    `chainsOf X layout cfg = .ok C` gives the shapes, `configure ... = .ok C.made`,
                     and that `C.key`, `C.link`, `C.proof` are read back from its byte strings
  `chainsOf_sized`   the same premise gives `sized ... = .ok z` at these shapes, and that
                     `linksFit` says yes
  `planned_chains`   `planned o pol KL layout = .ok p` gives `chainsOf p.X layout fixedConfigurationDigest = .ok`
                     `p.chains`, `p.cfg = fixedConfigurationDigest` and `builtOf p.X p.chains = .ok p.built`
  `pubBy_fields`     `pubBy made st pol lay KL = .ok Z` gives each further field of `Z` as the value
                     of the function that computes it, at `Z.made`
  `pub_configure`    the first two, for `pureRoad.pub`
  `descPure_configure`   the same, for `onlineDescription`
All are unfoldings: they say how the value was computed, and nothing about whether any test passes.
`chainsOf`, `planned`, `builtOf` and `shapesOf` are PlanPlain.lean's copies. Nothing here ties them
to the functions that they were copied from.

-/
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.Desc (FileDescription fixedConfigurationDigest)

theorem chainsOf_made {X : Public} {layout : Option ByteArray} {cfg : ByteArray} {C : Chains}
    (h : ProofFile.Plain.chainsOf X layout cfg = .ok C) :
    ∃ ls, ProofFile.Plain.shapesOf X layout = .ok ls ∧
      Params.configure X.P.frame ls.2 cfg 0 = .ok C.made ∧
      Params.KeyChains.read C.made.keyOneTime C.made.keyShared C.made.keySecond = some C.key ∧
      Params.Link.read C.made.entryLink = some C.link ∧
      Params.ProofChains.read C.made.first C.made.shared C.made.second = some C.proof := by
  unfold ProofFile.Plain.chainsOf at h
  obtain ⟨⟨links, shapes⟩, hs, h⟩ := bind_ok h
  obtain ⟨z, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨made, hm, h⟩ := bind_ok h
  split at h
  · rename_i key link proof hk hl hp
    cases h
    exact ⟨(links, shapes), hs, hm, hk, hl, hp⟩
  · exact (error_ne_ok h).elim

/-- The two steps of `chainsOf` that `chainsOf_made` passes over: at the same shapes `Params.sized`
returns a value, and `linksFit` says yes of the segments' records at that value's sizes. That
`C.made.sized` is this value is not said here: it is a matter of the text of `Params.configure`. -/
theorem chainsOf_sized {X : Public} {layout : Option ByteArray} {cfg : ByteArray} {C : Chains}
    (h : ProofFile.Plain.chainsOf X layout cfg = .ok C) :
    ∃ ls z, ProofFile.Plain.shapesOf X layout = .ok ls ∧ Params.sized X.P.frame ls.2 = .ok z ∧
      Stages.linksFit ls.1 z.proof.codes z.proof.request ls.2.layout
        z.proof.batch.shape.kCol = .ok () := by
  unfold ProofFile.Plain.chainsOf at h
  obtain ⟨⟨links, shapes⟩, hs, h⟩ := bind_ok h
  obtain ⟨z, hz, h⟩ := bind_ok h
  obtain ⟨_, hf, _⟩ := bind_ok h
  exact ⟨(links, shapes), z, hs, hz, hf⟩

theorem planned_chains {o : SecondHashFunctionArgument} {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Planned} (h : ProofFile.Plain.planned o pol KL layout = .ok p) :
    ProofFile.Plain.chainsOf p.X layout fixedConfigurationDigest = .ok p.chains ∧ p.cfg = fixedConfigurationDigest ∧
      ProofFile.Plain.builtOf p.X p.chains = .ok p.built := by
  unfold ProofFile.Plain.planned at h
  obtain ⟨X, _, h⟩ := bind_ok h
  obtain ⟨c, hc, h⟩ := bind_ok h
  obtain ⟨b, hb, h⟩ := bind_ok h
  cases h
  exact ⟨hc, rfl, hb⟩

theorem pubBy_fields
    {made : ByteArray → ByteArray → ByteArray → Except String Johnson.G.OfPlan.Made} {st : Starts}
    {pol lay KL : ByteArray} {Z : Pub} (h : pubBy made st pol lay KL = .ok Z) :
    Johnson.G.OfPlan.declPOf Z.made = .ok Z.D ∧ toldOf Z.made = .ok Z.told ∧
      Johnson.G.OfPlan.depthOf Z.made = .ok Z.depth ∧
      VerifiableInference.Desc.First.cutOf Z.first.given.rounds = some Z.cuts ∧
      Z.P = st.par Z.first ∧ Z.pol = pol ∧ Z.KL = KL := by
  unfold pubBy at h
  obtain ⟨m, _, h⟩ := bind_ok h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h
       exact ⟨atCall_ok (by assumption), by assumption, atCall_ok (by assumption),
         orSay_ok (by assumption), rfl, rfl, rfl⟩)

theorem pub_planned {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pureRoad.pub o pol lay KL = .ok Z) : ProofFile.Plain.planned o pol KL (some lay) = .ok Z.p :=
  madeOf_planned (pubBy_made
    (show pubBy (ProofFile.PlainG.madeOf o) plainStarts pol lay KL = .ok Z from h))

/-- Where the public part `Z` is computed: the planner's record in it is the value of one call of
`Params.configure`, at the constant `fixedConfigurationDigest` and at 0 for the bits that the caller asks; the three
files' chains in it are read back from that record's byte strings; and the declared rounds `Z.D` are
`declPOf`'s value at `Z.made`, which holds both. -/
theorem pub_configure {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pureRoad.pub o pol lay KL = .ok Z) :
    ∃ ls, ProofFile.Plain.shapesOf Z.p.X (some lay) = .ok ls ∧
      Params.configure Z.p.X.P.frame ls.2 fixedConfigurationDigest 0 = .ok Z.p.chains.made ∧
      Params.ProofChains.read Z.p.chains.made.first Z.p.chains.made.shared
        Z.p.chains.made.second = some Z.p.chains.proof ∧
      Johnson.G.OfPlan.declPOf Z.made = .ok Z.D := by
  obtain ⟨ls, hs, hm, _, _, hp⟩ := chainsOf_made (planned_chains (pub_planned h)).1
  exact ⟨ls, hs, hm, hp, (pubBy_fields
    (show pubBy (ProofFile.PlainG.madeOf o) plainStarts pol lay KL = .ok Z from h)).1⟩

theorem descPure_configure {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst}
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ Z ls, pureRoad.pub o pol lay KL = .ok Z ∧ onlineDescriptionFromPublicPart Z (pureSeat o Z) = .ok F ∧
      ProofFile.Plain.shapesOf Z.p.X (some lay) = .ok ls ∧
      Params.configure Z.p.X.P.frame ls.2 fixedConfigurationDigest 0 = .ok Z.p.chains.made ∧
      Params.ProofChains.read Z.p.chains.made.first Z.p.chains.made.shared
        Z.p.chains.made.second = some Z.p.chains.proof ∧
      Johnson.G.OfPlan.declPOf Z.made = .ok Z.D := by
  obtain ⟨Z, hZ, hF⟩ := descPure_made h
  obtain ⟨ls, hs, hm, hp, hD⟩ := pub_configure hZ
  exact ⟨Z, ls, hZ, hF, hs, hm, hp, hD⟩

end ProofFile.Law

#print axioms ProofFile.Law.chainsOf_made
#print axioms ProofFile.Law.chainsOf_sized
#print axioms ProofFile.Law.pubBy_fields
#print axioms ProofFile.Law.descPure_configure
