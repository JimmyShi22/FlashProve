-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/HeadNs.lean: where the public part of the proof file's IOP as written in
Lean is computed, the segments' structures in it (`Z.p.built.links`) have passed `linksFit` at the
first chain's parameters as they were read back (`Z.first`), and the last of them has the output
head's number of scalars (`Z.p.X.H.ns`). Theorems only; no file of that IOP imports this one.
Why. The output head's sub-protocols want to know that the head's scalars and the answers' pads have
room in the segment's mask row: `Z.p.X.H.ns + Z.first.shape.answers ≤ zk.ell`. `linkLaid`
(OnBytes/Model/StagesLinks.lean) tests just that of every segment, inside `linksFit`. What was
missing is that the planner has run that test on these structures at these parameters, and that the
head's is one of them.
  `buildLinksH_fits`   `buildLinksH links NGr p4 wsLay p = .ok B` gives `linksFit B.links` at `p`'s
                       codes, shape, layout and column bits
  `linksPlain_last`    the value of `linksPlain X` ends in a structure whose `ns` is `X.H.ns`
  `built_head_ns`      both, for `pureRoad.pub`
  `built_head_of g`    the last of them agrees with the head's structure as `linksPlain` makes it,
                       in whatever `g` reads, for every `g` that does not read the field `arrayOf`
  `built_head_Fp`      so one and the same last structure has the head's `ns` and its planned state
                       `Fp`
The walks through the two loops are laws of OnBytes/TieK/LinksEnd.lean (`listLinksH_kinds`,
`buildLinksH_keeps`); the proof of `buildLinksH_fits` follows that of `buildLinksH_keeps` there.
All are unfoldings: they say how the value was computed. What `linksFit` gives for one segment is
not said here. `linksPlain` and `builtOf` are PlanPlain.lean's copies.

-/
import Johnson.Desc.ProofFile.Law.PlainMade
import OnBytes.TieK.LinksEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Model.Stages (LinkH LinksH)
open OnBytes.TieK (ok_of_bind ok_of_jp)

/-- The public tests on the segments' structures end in `linksFit`, asked of the structures that are
returned, at the parameters that were handed in. -/
theorem buildLinksH_fits {links : Array LinkH} {NGr : Nat} {p4 : Bool} {wsLay : Model.WsLay}
    {p : Params.First} {B : LinksH} (h : Stages.buildLinksH links NGr p4 wsLay p = .ok B) :
    Stages.linksFit B.links p.codes p.shape p.layout p.lin.kCol = .ok () := by
  unfold Stages.buildLinksH at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨⟨links', declared⟩, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨u, hf, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  cases h
  cases u
  exact hf

/-- The list of the segments' structures ends in the output head's. -/
theorem linksPlain_last {X : Public} {ls : Array LinkH} (h : ProofFile.Plain.linksPlain X = .ok ls) :
    ∃ pre : Array LinkH,
      ls.toList.map (fun Y => Y.ns) = pre.toList.map (fun Y => Y.ns) ++ [X.H.ns] := by
  unfold ProofFile.Plain.linksPlain at h
  obtain ⟨pre, e, -⟩ := OnBytes.TieK.listLinksH_kinds h
  refine ⟨pre, ?_⟩
  rw [e, OnBytes.TieK.map_push]
  rfl

/-- **The segments' structures in the public part have passed `linksFit` at the parameters read
back, and the last of them has the output head's number of scalars.** -/
theorem built_head_ns {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pureRoad.pub o pol lay KL = .ok Z) :
    Stages.linksFit Z.p.built.links Z.first.codes Z.first.shape Z.first.layout
        Z.first.lin.kCol = .ok () ∧
      ∃ (pre : List LinkH) (L : LinkH),
        Z.p.built.links.toList = pre ++ [L] ∧ L.ns = Z.p.X.H.ns := by
  have hb : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    (planned_chains (pub_planned h)).2.2
  unfold ProofFile.Plain.builtOf at hb
  obtain ⟨ls, h0, hb⟩ := ok_of_bind hb
  refine ⟨buildLinksH_fits hb, ?_⟩
  obtain ⟨pre, e⟩ := linksPlain_last h0
  have hk := OnBytes.TieK.buildLinksH_keeps (fun Y : LinkH => Y.ns) (fun _ _ => rfl) hb
  rw [e] at hk
  obtain ⟨as, a, e1, -, e3⟩ := OnBytes.TieK.snoc_of_map _ _ _ _ hk
  exact ⟨as, a, e1, e3⟩

/-- `linksPlain_last`, for whatever is read off a structure. -/
theorem linksPlain_last_of {β : Type} (g : LinkH → β) {X : Public} {ls : Array LinkH}
    (h : ProofFile.Plain.linksPlain X = .ok ls) :
    ∃ pre : Array LinkH, ls.toList.map g = pre.toList.map g ++
      [g (({ tl := X.H.tl, Fp := X.H.Fp, Tp := X.H.Tp, ns := X.H.ns, NCL := X.H.NCL,
             run := ProofFile.Plain.notToBeRun } : Stages.SubPlanH).link "H" (1 + X.NGr) 2 0 true)] := by
  unfold ProofFile.Plain.linksPlain at h
  obtain ⟨pre, e, -⟩ := OnBytes.TieK.listLinksH_kinds h
  refine ⟨pre, ?_⟩
  rw [e]
  exact OnBytes.TieK.map_push g pre _

/-- **The last of the segments' structures in the public part is the output head's, but for the
field `arrayOf`.** g: any function of a structure that does not read that field. -/
theorem built_head_of {β : Type} (g : LinkH → β)
    (hg : ∀ (Y : LinkH) (a : Array (Nat × String)), g { Y with arrayOf := a } = g Y)
    {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub} (h : pureRoad.pub o pol lay KL = .ok Z) :
    ∃ (pre : List LinkH) (L : LinkH), Z.p.built.links.toList = pre ++ [L] ∧
      g L = g (({ tl := Z.p.X.H.tl, Fp := Z.p.X.H.Fp, Tp := Z.p.X.H.Tp, ns := Z.p.X.H.ns,
                  NCL := Z.p.X.H.NCL, run := ProofFile.Plain.notToBeRun } : Stages.SubPlanH).link
                "H" (1 + Z.p.X.NGr) 2 0 true) := by
  have hb : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    (planned_chains (pub_planned h)).2.2
  unfold ProofFile.Plain.builtOf at hb
  obtain ⟨ls, h0, hb⟩ := ok_of_bind hb
  obtain ⟨pre, e⟩ := linksPlain_last_of g h0
  have hk := OnBytes.TieK.buildLinksH_keeps g hg hb
  rw [e] at hk
  obtain ⟨as, a, e1, -, e3⟩ := OnBytes.TieK.snoc_of_map _ _ _ _ hk
  exact ⟨as, a, e1, e3⟩

/-- One and the same last structure has the output head's number of scalars and its planned
state. -/
theorem built_head_Fp {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pureRoad.pub o pol lay KL = .ok Z) :
    ∃ (pre : List LinkH) (L : LinkH), Z.p.built.links.toList = pre ++ [L] ∧
      L.ns = Z.p.X.H.ns ∧ L.Fp = Z.p.X.H.Fp := by
  obtain ⟨pre, L, e, hL⟩ := built_head_of (fun Y : LinkH => (Y.ns, Y.Fp)) (fun _ _ => rfl) h
  exact ⟨pre, L, e, congrArg Prod.fst hL, congrArg Prod.snd hL⟩

end ProofFile.Law

#print axioms ProofFile.Law.buildLinksH_fits
#print axioms ProofFile.Law.linksPlain_last
#print axioms ProofFile.Law.built_head_ns
#print axioms ProofFile.Law.built_head_of
#print axioms ProofFile.Law.built_head_Fp
