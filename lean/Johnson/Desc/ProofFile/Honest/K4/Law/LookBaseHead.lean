-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LookBaseHead.lean: CONDITIONAL.

What is here. WHERE THE LOOKUP ON THE CALLS BEGINS, COUNTED BACK FROM THE MEMBER OF THE FEED-FORWARD
LAYERS' OWN ROUNDS (sub-protocol K4). Under the library's hypothesis h the member number 28 g + 3
(from 0) of the first chain's flat list, the lookup on the calls of link 2 g, has as many rounds as
the stages of the authors of the kind "lookup" add up to at the public parameters' shape
(`lookMember_rounds`). K4's member is the next one. So the count of rounds in front of K4's member
(the field r0 of `k4PubAt`, Law/DearTop.lean: by definition the chain's own count) is the number of
rounds in front of the lookup's member plus that sum (`lookBase_add`), and less that sum it is that
number (`lookBase_head`: the subtraction does not stop at 0); and the authors' text `lookOfK3`
(Honest/K3/Law/Thread/LayersTieHead.lean), which reads the chain for that number alone, is their
`lookHeardAt` at the public data's own shape and at that difference. THE SUM, written out as
((stages f).map (Stage.rounds f)).sum, IS THE BODY OF `k4LookRounds` (Honest/K4/Look.lean): so
`lookBase_head` is the first of the two hypotheses on which `k4LookAt` (the same file) says that it
stands, at `k4PubAt`, and `pubShape_head` is the second; Law/LookAtHead.lean joins them. That the
public data which the lot hands to `look` are `k4PubAt`'s is `k4Pub_head` (Law/FrontCount.lean).
Each proof is a chain of calls, over the authors' `member_plan_site`
(Honest/K3/Law/Thread/SitePays.lean) and `rounds_stages` (Honest/K3/RowLaw.lean) and
`callsShape_head` (Law/LookFitsFill.lean).

  `lookMember_rounds`   the lookup's member has as many rounds as the stages add up to.
  `pubShape_head`   the public data's shape of the lookup is the shape of the site on the calls.
  `lookBase_add`, `lookBase_head`   **r0 is the number of rounds in front of the lookup's member
      plus the sum; less the sum it is that number.**
  `lookOfK3_pub`   **the authors' text, in the public data's own letters.**

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. Lh (`LaidK4`, Law/SeatedHead.lean):
on public lists and numbers; h gives one at each of the twelve groups (`laid_head`, the same file,
with the library's `atK4_full`). NUMBERS OF ROUNDS AND THE SHAPE ALONE: nothing on any sampled
value, on any sent value, or on what any part sends. THAT ANY PROVER's HALF IS LAID OVER ANY TEXT
FOR `look` is not shown. At a description in which other rounds stand between the lookup and K4's
first round the statements do not speak: they stand under h, so AT THE FULL SIZE ALONE, and at the
format's second hash function alone (`OnBytes.secondHashFunction`). Beneath `callsShape_head` stands `nine_head`
(Law/ElevenHead.lean), which rests on a comparison by Lean's own kernel (`decide +kernel`) that no
independent checker has replayed. The side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). h gives Lh (`laid_at`, Law/LaidAtGroup.lean): Lh asks nothing
beyond h; `lookMember_rounds` asks hg (g < 12) and hb besides. No test that can fail stands beside
them. Nothing on soundness, on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 81 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 89 is not counted: all the numbers are floors. It
imports files of the authors of the kind "lookup". A LAW, NOT A PART: no file that defines a part of
the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LookFitsFill
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitePays

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K3 (lookHeardAt lookSites)
open ProofFile.Honest.K3.Law.AtThr (lookOfK3 callsShape calls_site_found site_hub member_at_link
  border_even member_plan_site)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, hg and hb. **The lookup's member has as many rounds as the stages add up
to**, at the shape of the site on the calls of link 2 g. -/
theorem lookMember_rounds (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {b : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[28 * g + 3]? = some b) :
    b.rounds.length =
      ((ProofFile.Honest.K3.stages (faceOf (callsShape Zp g))).map
        (ProofFile.Honest.K3.Stage.rounds (faceOf (callsShape Zp g)))).sum := by
  obtain ⟨s, hs, e1, e2, eS⟩ := calls_site_found h g hg
  have hl : s.link < 25 := by omega
  obtain ⟨Fd, Bs, base, A, B, lot, O, hlot, hbs, hm⟩ := site_hub h s hs hl
  have hb' : cF.blocksInOrder[borderOf s.link s.digits]? = some b := by
    rw [e1, e2, border_even g hg]
    exact hb
  obtain ⟨m1, m2, m3⟩ := hm b hb'
  obtain ⟨hr, _, hfit⟩ :=
    member_plan_site _ _ _ _ Fd Zp Bs base cF A B O s hs lot b hlot hbs m1 m2 m3
  have hf : s.at_.face = faceOf s.shape := by
    have hs' := hs
    unfold lookSites at hs'
    obtain ⟨a, _, hsa⟩ := List.mem_filterMap.1 hs'
    exact (ProofFile.Honest.K3.Law.site_facts _ _ a s hsa).2.2.2.2.2.1
  have h2 : 2 ≤ (faceOf s.shape).planes := by
    show 2 ≤ 32
    omega
  rw [eS, hr, List.length_map, ProofFile.Honest.K3.Law.fit_length _ _ hfit, hf]
  exact (ProofFile.Honest.K3.rounds_stages (faceOf s.shape) h2).symm

variable {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}

/-- CONDITIONAL: on h and Lh. **The public data's shape of the lookup is the shape of the site on
the calls.** -/
theorem pubShape_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (Lh : LaidK4 Zp cF k m g x blk) : (k4PubAt cF k x).P.y.fo = callsShape Zp g := by
  exact (congrArg (fun P : Layer.Pub => P.y.fo) Lh.P).trans (callsShape_head h Lh).symm

/-- CONDITIONAL: on h and Lh. **THE COUNT OF ROUNDS IN FRONT OF K4's MEMBER IS THE NUMBER OF ROUNDS
IN FRONT OF THE LOOKUP's MEMBER PLUS THE SUM OF THE STAGES' ROUNDS.** -/
theorem lookBase_add (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (Lh : LaidK4 Zp cF k m g x blk) :
    (k4PubAt cF k x).r0 =
      ((cF.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length +
        ((ProofFile.Honest.K3.stages (faceOf (k4PubAt cF k x).P.y.fo)).map
          (ProofFile.Honest.K3.Stage.rounds (faceOf (k4PubAt cF k x).P.y.fo))).sum := by
  have hg := Lh.lt
  obtain ⟨b, hb, _⟩ := member_at_link h (2 * g) (by omega) false
  rw [border_even g hg] at hb
  have e1 := lookMember_rounds h hg hb
  have eA : (k4PubAt cF k x).r0 =
      ((cF.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length + b.rounds.length := by
    show ((cF.blocksInOrder.take k).flatMap (·.rounds)).length = _
    rw [Lh.num, show 28 * g + 4 = 28 * g + 3 + 1 from rfl, List.take_add_one, hb]
    simp
  rw [pubShape_head h Lh, ← e1]
  exact eA

/-- CONDITIONAL: on h and Lh. **LESS THAT SUM IT IS THE NUMBER OF ROUNDS IN FRONT OF THE LOOKUP's
MEMBER.** -/
theorem lookBase_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (Lh : LaidK4 Zp cF k m g x blk) :
    (k4PubAt cF k x).r0 -
        ((ProofFile.Honest.K3.stages (faceOf (k4PubAt cF k x).P.y.fo)).map
          (ProofFile.Honest.K3.Stage.rounds (faceOf (k4PubAt cF k x).P.y.fo))).sum =
      ((cF.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length :=
  Nat.sub_eq_of_eq_add (lookBase_add h Lh)

/-- CONDITIONAL: on h and Lh. **THE AUTHORS' TEXT, IN THE PUBLIC DATA's OWN LETTERS**: at every
list hd of challenges. ξ₀: an instance; the text does not read it. -/
theorem lookOfK3_pub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (Lh : LaidK4 Zp cF k m g x blk) (ξ₀ : ProofFile.Inst) (hd : List Fmt.Drawn) :
    lookOfK3 Zp cF (k4PubAt cF k x).g ξ₀ hd =
      lookHeardAt (k4PubAt cF k x).P.y.fo
        ((k4PubAt cF k x).r0 -
          ((ProofFile.Honest.K3.stages (faceOf (k4PubAt cF k x).P.y.fo)).map
            (ProofFile.Honest.K3.Stage.rounds (faceOf (k4PubAt cF k x).P.y.fo))).sum) hd := by
  rw [lookBase_head h Lh, pubShape_head h Lh]
  show lookHeardAt (callsShape Zp x.2.g)
    ((cF.blocksInOrder.take (28 * x.2.g + 3)).flatMap (·.rounds)).length hd = _
  rw [Lh.grp]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.lookMember_rounds
#print axioms ProofFile.Honest.K4.W.pubShape_head
#print axioms ProofFile.Honest.K4.W.lookBase_add
#print axioms ProofFile.Honest.K4.W.lookBase_head
#print axioms ProofFile.Honest.K4.W.lookOfK3_pub
