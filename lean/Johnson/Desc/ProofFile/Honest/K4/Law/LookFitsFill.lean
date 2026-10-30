-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LookFitsFill.lean: CONDITIONAL.

What is here. THE PUBLIC TEST ON WHAT THE LOOKUP HAS SAMPLED (`k4LookFits`, Honest/K4/Part.lean: the
shape's numbers and the sizes of the fields zx, e and zk) ACCEPTS AT THE TEXT `lookOfK3` of the
authors of the kind "lookup" (Honest/K3/Law/Thread/LayersTieHead.lean), at the public data of the
member of the feed-forward layers' own rounds (sub-protocol K4), AT EVERY LIST OF CHALLENGES,
fitting or not: the text reads the challenges by number and lays zeros where they lack, so its sizes
hang on the shape alone. That is the hypothesis hLk of `k4Seated_member` (Law/SeatedMember.lean) at
`look Qp := fun hd => lookOfK3 Zp cF Qp.g ξ₀ hd`, at which `look_fill` (Law/LookOpenHead.lean) has
`LookIsK3`. The sizes: the key tree's last point has a coordinate a variable (the authors'
`size_keyPt`); it is cut at dT; each call's point is the last iota coordinates of the rest, then the
first dT; the library's test on the shape (`FoNums.ok`) has each call's number of variables as iota
+ dT and iota at most rK; the library's `pub_ok` has that test at the public parameters' shape. And
the text's shape IS the public parameters' (`callsShape_head`): by the authors' `site_facts`, the
library's `place_lay` and `nine_head` (Law/ElevenHead.lean). Each proof unfolds sizes or is a chain
of calls.

  `keyPtsOf_sizes`   the sizes of the cut, at a point of dT + rK coordinates.
  `lookFits_at`   the test at `lookHeardAt` of the public data's own shape, at every number of
      rounds in front and every list of challenges.
  `callsShape_head`   the shape of the site on the calls at link 2 g is the public parameters'.
  `lookFits_fill`   **the test at the member's own public data, at the text `lookOfK3`.**

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. Lh (`LaidK4`, Law/SeatedHead.lean):
on public lists and numbers. THE SIZES AND THE SHAPE's NUMBERS ALONE: nothing on any element of a
point. THAT ANY PROVER's HALF IS LAID OVER THIS TEXT is not shown: the lot takes `look` as a
parameter, and THE FRAME's FILLING `widerFill` (Honest/AtPureWider.lean) LAYS K4's LOT OVER ANOTHER
TEXT, `k4LookAt` (Honest/K4/Look.lean), which is not that text as a whole structure wherever the
shape has a call (`lookOf_ne`, Law/LookAtFill.lean): so `lookFits_fill` does not pay hLk at that
filling; the test there is `lookFits_lookAt`'s (the same file), which rests on `lookFits_at` here.
The test's other three companions in `k4Fits` are other files'. The side library AtFullSide proves,
with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). Of h together with hp,
hok, hla and Lh no example is known to us. No test that can fail stands beside them. `lookFits_fill`
and `callsShape_head`: THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`).
Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 81 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 89 is not counted: all the numbers are floors. It
imports files of the authors of the kind "lookup". A LAW, NOT A PART: no file that defines a part of
the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MakersFitMember
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LayersTieHead
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecCourse
import Johnson.Desc.First.Look.K3PlaceLetters
import Johnson.Road.K4.RefPub
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinAt
import OnBytes.Tie.Pv.Lookup.Forest.FoHole

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4.C (light_head)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.K3 (faceOf)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K3 (keyPtsOf ptsOf lookHeardAt lookSites)
open ProofFile.Honest.K3.Law.AtThr (lookOfK3 callsShape calls_site_found)

/-! ## 1 The sizes -/

/-- CONDITIONAL: on hp. **The sizes of the cut.** pt: a point of dT + rK coordinates. -/
theorem keyPtsOf_sizes (h : Forest.Shape) (pt : Array E) (hp : pt.size = h.dT + h.rK) :
    (keyPtsOf h pt).zx.size = h.dT ∧ (keyPtsOf h pt).zk.size = h.NC ∧
      ∀ c, c < h.NC → h.iota.getD c 0 ≤ h.rK →
        ((keyPtsOf h pt).zk.getD c #[]).size = h.iota.getD c 0 + h.dT := by
  refine ⟨?_, ?_, fun c hc hio => ?_⟩
  · show (pt.extract 0 h.dT).size = h.dT
    rw [Array.size_extract]
    omega
  · show ((Array.range h.NC).map _).size = h.NC
    rw [Array.size_map, Array.size_range]
  · have e : (keyPtsOf h pt).zk.getD c #[] =
        (pt.extract h.dT pt.size).extract (h.rK - h.iota.getD c 0)
          (pt.extract h.dT pt.size).size ++ pt.extract 0 h.dT := by
      show ((Array.range h.NC).map fun c =>
        (pt.extract h.dT pt.size).extract (h.rK - h.iota.getD c 0)
          (pt.extract h.dT pt.size).size ++ pt.extract 0 h.dT).getD c #[] = _
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_eq_getElem (by rw [Array.size_range]; exact hc), Array.getElem_range]
      rfl
    rw [e]
    simp only [Array.size_append, Array.size_extract]
    omega

/-- CONDITIONAL: on hok and hla. **THE TEST AT `lookHeardAt` OF THE PUBLIC DATA's OWN SHAPE**, at
every number base of rounds in front and every list hd of challenges. -/
theorem lookFits_at (Q : K4Pub) (hok : FoNums.ok Q.P.y.fo = true)
    (hla : Q.P.y.h.la ≤ Q.P.y.fo.dT) (base : ℕ) (hd : List Fmt.Drawn) :
    k4LookFits Q (lookHeardAt Q.P.y.fo base hd) = true := by
  obtain ⟨_, _, c3, _⟩ := Cb.Fo.ok_parts hok
  obtain ⟨s1, s2, s3⟩ := keyPtsOf_sizes Q.P.y.fo
    ((ptsOf (faceOf Q.P.y.fo) base hd).keyPt 0 Q.P.y.fo.v)
    (ProofFile.Honest.K3.Law.Spec.size_keyPt _ _ _ _ _)
  unfold k4LookFits
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, decide_eq_true hla⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold OnBytes.Desc.First.K4.shapeFits lookHeardAt
    simp
  · rw [beq_iff_eq]
    exact s1
  · rw [beq_iff_eq]
    show ((Array.range Q.P.y.fo.NC).map _).size = Q.P.y.fo.NC
    rw [Array.size_map, Array.size_range]
  · rw [beq_iff_eq]
    exact s2
  · rw [List.all_eq_true]
    intro c hc
    rw [List.mem_range] at hc
    rw [beq_iff_eq]
    have e1 := s3 c hc ((_root_.Fo.ok_prem hok).le c hc)
    have e2 : FoNums.nOf Q.P.y.fo c = FoNums.io Q.P.y.fo c + Q.P.y.fo.dT := (c3 c hc).2.2.1
    exact e1.trans e2.symm

/-! ## 2 At the member -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h and Lh. **The text's shape is the public parameters'.** -/
theorem callsShape_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) :
    callsShape Zp g = (P5J.At.X Zp).y.fo := by
  obtain ⟨s, hs, e1, e2, eS⟩ := calls_site_found h g Lh.lt
  have N := nine_head h Lh
  unfold lookSites at hs
  obtain ⟨a, _, hsa⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, f2, f3, f4, _⟩ := ProofFile.Honest.K3.Law.site_facts _ _ a s hsa
  rw [← f3, ← f4, e1, e2, ← Lh.seg] at f1
  obtain ⟨_, _, f5, _⟩ := VerifiableInference.Desc.First.Look.place_lay N.Sx.pubOf f1 N.Sx.notHead
    N.Sx.step
  rw [eS]
  exact Option.some.inj (f2.symm.trans f5)

/-- CONDITIONAL: on h and Lh. **THE TEST AT THE MEMBER's OWN PUBLIC DATA, AT THE TEXT `lookOfK3`**,
at every list fr of challenges. ξ₀: an instance; the text does not read it. -/
theorem lookFits_fill (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) (ξ₀ : ProofFile.Inst)
    (fr : List Fmt.Drawn) :
    k4LookFits (k4PubAt cF k x) (lookOfK3 Zp cF (k4PubAt cF k x).g ξ₀ fr) = true := by
  have N := nine_head h Lh
  rw [pubAt_is Lh]
  show k4LookFits (k4PubAtX (P5J.At.X Zp) x.2.hp g (roundsTo cF.blocksInOrder k))
    (lookHeardAt (callsShape Zp g) _ fr) = true
  rw [callsShape_head h Lh]
  exact lookFits_at (k4PubAtX (P5J.At.X Zp) x.2.hp g (roundsTo cF.blocksInOrder k))
    (OnBytes.Road.K4.pub_ok N.Sx.pubOf) (light_head h Lh.lt Lh.hp).2.1 _ fr

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.keyPtsOf_sizes
#print axioms ProofFile.Honest.K4.W.lookFits_at
#print axioms ProofFile.Honest.K4.W.callsShape_head
#print axioms ProofFile.Honest.K4.W.lookFits_fill
