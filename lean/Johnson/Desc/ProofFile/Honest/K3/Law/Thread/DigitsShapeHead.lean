-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsShapeHead.lean: the shape of a site on the digits
is the field f9 of the plan's own structure of the link's smallness test; so what
Honest/K3/Law/Thread/DigitsHeardLink.lean says at the site's shape holds at that field. Theorems:
each joins earlier ones; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: `tlAt X l` (Johnson/Desc/First/Look/Laid.lean) is the
plan's structure of link l's smallness test.

What is shown.
  `site_f9_public`: at every size, where the library's `ShapeZAll`
    (Johnson/Desc/First/Look/DigitsShapeAt.lean) holds of the program's public data: the plan has
    a structure of the link's smallness test (`tlAt`), and the site's shape is its field f9.
  `site_f9_head`: the same under the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean),
    from which `ShapeZAll` follows: no public test is left.
  `digits_heard_plan`: `digits_heard_site` (DigitsHeardLink.lean) written at the plan's own f9.

Hypotheses that remain.
  `hZ`: (in `site_f9_public`) `ShapeZAll` at the public structure.
  `h`: (in the two others) the library's hypothesis `P5J.AtMgA`.
  `hs`, `hd`, `hl`: s is a site of the public part; it is on the digits; in `digits_heard_plan` its
    link is below 25 (that follows from `h` and `hs`: `link_lt_head`,
    Honest/K3/Law/Thread/LinkLtHead.lean).
  For the clause on eps alone: `Good.Ok rs` (Honest/K3/Good/Levels.lean).
What then remains of "the state's own f9": that the field f9 of the structure in the state behind
the step is the plan's. The step at the digits sets four fields of that structure anew
(Johnson/Desc/First/Look/K3Seat.lean: foldDrawn, slotA, slotB, heard) and names f9 nowhere: this is
by a reading of that file; it is not shown here. It is shown in `digits_tl_site`
(Honest/K3/Law/Thread/DigitsTlKept.lean).

How the proof goes. The theorems call `place_digits`, `digits_shape_at` and `shapeZAll_of_public`
(Johnson/Desc/First/Look/DigitsShapeAt.lean), `site_facts` (Honest/K3/Law/MemberSite.lean) and
`digits_heard_site`.

Users. Honest/K3/Law/Thread/DigitsTlKept.lean calls `digits_heard_plan`;
Honest/K3/Good/MarksLooks.lean imports this file.

Limits. Those of DigitsHeardLink.lean. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsHeardLink
import Johnson.Desc.First.Look.DigitsShapeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.First.Look (tlAt placeAt lookAt ShapeZAll shapeZAll_of_public
  digits_shape_at)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- **The shape of a site on the digits is the plan's own f9.** Conditional on the library's
`ShapeZAll` at the public structure, and the site. -/
theorem site_f9_public (Z : Pub) (hZ : ShapeZAll Z.p.X) (s : Site) (hs : s ∈ lookSites Z)
    (hd : s.digits = true) : ∃ tlP, tlAt Z.p.X s.link = some tlP ∧ s.shape = tlP.f9 := by
  unfold lookSites at hs
  obtain ⟨y, _, hsy⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, f2, f3, f4, _, _, _, _⟩ := site_facts _ _ y s hsy
  rw [← f3, ← f4, hd] at f1
  unfold placeAt at f1
  obtain ⟨pl, hpl, e⟩ := Option.map_eq_some_iff.1 f1
  obtain ⟨tlP, ht, _⟩ := VerifiableInference.Desc.First.Look.place_digits hpl
  refine ⟨tlP, ht, ?_⟩
  have h1 := digits_shape_at hZ hpl ht (OnBytes.Params.settingOf Z.p.X.P.frame)
  rw [e, f2] at h1
  exact Option.some.inj h1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The same under `P5J.AtMgA`: no public test is left. -/
theorem site_f9_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = true) :
    ∃ tlP, tlAt Zp.p.X s.link = some tlP ∧ s.shape = tlP.f9 :=
  site_f9_public Zp (shapeZAll_of_public h.pubOne) s hs hd

/-- **`digits_heard_site` at the plan's own f9.** Conditional on `P5J.AtMgA` and the site; the
clause on eps also on `Good.Ok rs`. No instance of these hypotheses is exhibited in this file. -/
theorem digits_heard_plan (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link < 25) (hd : s.digits = true) :
    ∃ tlP, tlAt Zp.p.X s.link = some tlP ∧
      ∀ blk, cF.blocksInOrder[borderOf s.link true]? = some blk →
        ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
          blk.step ft sj rs c = .ok (sj', n) →
          ∃ tl g, sj'.tl? = some tl ∧ tl.heard = some g ∧
            OpenSame g (lookHeardAt tlP.f9 0 (rs.map (·.drawn))) ∧
            g.cEnd.ents.isEmpty = true ∧ g.leaves.start.ents.isEmpty = true ∧
            (Good.Ok rs → g.leaves.eps = one rs (firstRound (faceOf tlP.f9) .leaves)) := by
  obtain ⟨tlP, ht, e⟩ := site_f9_head h s hs hd
  refine ⟨tlP, ht, fun blk hblk ft sj sj' n rs c hstep => ?_⟩
  obtain ⟨tl, g, t1, t2, W, c1, l1, l2⟩ :=
    digits_heard_site h s hs hl hd blk hblk ft sj sj' n rs c hstep
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨y, _, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, _, _, _, _, f6, _, _⟩ := site_facts _ _ y s hsy
  refine ⟨tl, g, t1, t2, ?_, c1, l1, ?_⟩
  · rw [← e]
    exact W
  · rw [← e, ← f6]
    exact l2

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.site_f9_public
#print axioms ProofFile.Honest.K3.Law.AtThr.site_f9_head
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_heard_plan
