-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MakersFitHead.lean: CONDITIONAL. A statement with its proof.

What is here: UNDER THE LIBRARY's HYPOTHESIS ON THE PUBLIC FILES (h: `P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean), at each of the twelve groups of layers and its plan, THE CLAUSE ON THE
MAKERS OF THE PUBLIC TEST ON THE PARTS OF THE FEED-FORWARD LAYERS' OWN ROUNDS (`k4MakersFit`,
Honest/K4/Part.lean; the sub-protocol K4) IS TRUE at the public structure that h fixes
(`P5J.At.X Zp`), at every number r0 of rounds in front and at every value fo of what the lookup has
sampled that passes the test on its sizes (`k4LookFits`). The public data are `k4PubAtX`
(Law/FitsX.lean): link and segment 2 g, piece 3, any r0.
How. `makersFit_plan` (Law/MakersFitPlan.lean), each premise paid under h: `K4Plan` and the weights'
layout (Law/W/PlanHead.lean); profile 4 and what the heads' weights read (the library's `PubLines`;
`qkRd_of`, Johnson/Road/K4/C/ClaimRdOf.lean); the two tests with code (`claimsB_head`, `pansB_head`,
Law/DearX.lean); that the plan names the reads' array and the tables are placed (`light_head`,
Johnson/Road/K4/C/PublicLight.lean); the two facts on that array (`freeReads`,
Johnson/Road/K4/C/Free/FreeReads.lean); the vocabulary's size (`vocab_at_head`,
Johnson/P5J/VocabAtHead.lean).

Not shown here. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). BESIDE h: hg and hG (the group has a plan), and hL (`k4LookFits`
at fo), which has a member under h (`lookFits_head`, Law/MakersFitMember.lean). THE FULL SIZE ALONE,
and the format's second hash function alone. That `k4PubAtX` is the member's own public data (`pubAt_is`,
Law/MakersFitMember.lean, has it under `LaidK4`). That any fo passes `k4LookFits` (`lookFits_head`,
there, has one), or that it holds at what a run's lookup samples. RETURNS, SHAPES AND SIZES AT THE
ZERO INPUT: nothing on what any maker's table is worth. The other tests of `k4Fits` are not here.
Beneath it stand uses of kernel_rfl, comparisons by Lean's own kernel: one in each of the seven
facts of Johnson/Road/K4/C/Free/ that it calls, and seven that these share
(Johnson/Road/K4/RowHead/ClosedAt.lean, ClosedTies.lean), five of them with the parameter file's
eight free numbers as a variable. No independent checker has replayed them. Its imports reach files
under Johnson/Goal/: a program's walk from import to import, which reads import lines alone and
stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at
23 modules under Johnson/Goal/ and at 5 under Johnson/Bridge/, and saw 46 whose name holds
RecCompile: the numbers are floors (with h; with Johnson/Road/K4/RefInScope.lean, whose
`refPub_in_scope` calls a statement of such a file): A LAW, NOT A PART: no file that defines a part
of the proof file's description may import this one. Nothing on soundness, on completeness or on any
other property. No property is claimed.

  `makersFit_head`   **`k4MakersFit` is true under h**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MakersFitPlan
import Johnson.Desc.ProofFile.Honest.K4.Law.DearX
import Johnson.Desc.ProofFile.Honest.K4.Law.FitsX
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PlanHead
import Johnson.Road.K4.C.ClaimRdOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Road.K4 (refPub_in_scope)
open OnBytes.Road.K4.C (light_head twins_head_all qkRd_of)
open OnBytes.Desc.First.K4.RtPub (tablesB)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h and on every other hypothesis named. **THE CLAUSE ON THE MAKERS IS TRUE UNDER
h**, at each group and its plan. -/
theorem makersFit_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) (r0 : ℕ) {fo : Forest.Heard}
    (hL : k4LookFits (k4PubAtX (P5J.At.X Zp) hp g r0) fo = true) :
    k4MakersFit (k4PubAtX (P5J.At.X Zp) hp g r0) fo = true := by
  obtain ⟨s0, HL, -⟩ := (refPub_in_scope h.scope h.reads h.pubOne hg).lines hp hG
  have L := HL (P5J.At.X Zp).layers.tokv
  have A := W.k4Plan_head h hg hG (P5J.At.X Zp).layers.tokv
  obtain ⟨_, _, _, _, _, _, _, hUs, hTB, _⟩ := light_head h hg hG
  obtain ⟨iU3, hu⟩ := Option.isSome_iff_exists.mp hUs
  unfold tablesB at hTB
  obtain ⟨rr, ht, _⟩ := OnBytes.Desc.First.K4.RtPub.any_some hTB
  have f := twins_head_all h _ OnBytes.Road.K4.C.Free.freeReads hg hG
  rw [hu, ht, Option.any_some, Option.any_some, Bool.and_eq_true, bne_iff_ne,
    decide_eq_true_eq] at f
  have v := P5J.vocab_at_head h.toAtMg
  have hV : k4TokensFit (k4PubAtX (P5J.At.X Zp) hp g r0)
      (Array.replicate (P5J.At.X Zp).layers.y.T 0) = true := by
    have hv0 : 0 < (P5J.At.X Zp).layers.V := by
      rw [v.2.2]
      decide
    unfold k4TokensFit
    rw [Bool.or_eq_true]
    refine Or.inr ?_
    rw [Bool.and_eq_true]
    refine ⟨by simp [k4PubAtX], ?_⟩
    rw [Array.all_eq_true]
    intro i hi
    simpa [k4PubAtX] using hv0
  exact makersFit_plan (Q := k4PubAtX (P5J.At.X Zp) hp g r0) A L.h4 hu ht f.1 f.2
    (claimsB_head h hg hG) (pansB_head h hg hG hu ht) (W.wsLay_head h hg hG)
    (qkRd_of L.hy L.S L.hN L.Z L.Zw) hL hV

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.makersFit_head
