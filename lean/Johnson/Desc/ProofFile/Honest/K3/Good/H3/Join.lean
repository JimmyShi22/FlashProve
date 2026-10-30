-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/Join.lean: the kind "lookup" (K3): the lookups' share of
the field on marks of the frame's bound on the first chain's falls: the hypothesis h₃ of
`marksHead_hM` (Honest/Law/MarksHead.lean: the frame's bound on
falls), at the kit `Run.ckP .two` (strings of hash blocks). Conditional. One theorem.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), site, member, share and kit.

What is shown.
  `k3Marks_hM_blocks`: that hypothesis's own text, with `(_root_.Run.ckP .two)` for its letter C.

Whose text stands here. The theorem's end is the text of that hypothesis, laid in by program; it is
the statement asked for. The binders pre₁, e₁, cut and PM follow those of
`marksHead_hM_blocks6` (Honest/Law/MarksHeadK6Blocks.lean): the names pre₁ and PM, and all four
types, are fixed by the end. Neither file is imported here: that the end fits is shown only by a
call of `marksHead_hM`, which is not made in this folder. Honest/K3/Good/H3/JoinForm.lean
[not in this library] holds the end against a copy of the text.

Hypotheses that remain.
  `hcap`: `KitCap (Run.ckP .two) cap` (Honest/K3/Good/H3/Defs.lean): it can be had by one call of
    `P1K8.kit_count_blocks` (Johnson/P1K8R/KitCount.lean).
  `h`: `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): the library's hypothesis at the full size.
  `hkap`: every listed round's bound, at every site, is at most kap₃; the listed rounds are the
    events' rounds of both marks, and alpha's. Shown by nobody.
  `cut`: the flat list is pre₁ and one sub-protocol behind it.

Meant for whoever calls `marksHead_hM`.

Limits. All limits of Honest/K3/Good/H3/Member.lean hold here. At one kit. cap and kap₃ are letters:
no number is named or evaluated. The stated shares are not shown to be held: their numerators alone
are spent. The uniform law on the rounds' messages is named, not derived. What a mark's silence
gives is not treated. The list runs over the sites that could be made of the public part
(`lookSites`): under `P5J.AtMgA` there are fifty (`sites_fifty`, Honest/K3/Good/MarksHead.lean).
That the theorem speaks at every one of them is `site_has_behind` (Honest/K3/Good/H3/Guards.lean).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.Member

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open scoped ENNReal
open VerifiableInference.Desc (Block Chain)
open OnBytes.Maker (RDT WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE HYPOTHESIS h₃ OF marksHead_hM (Honest/Law/MarksHead.lean: the frame's
bound on falls), AT THE KIT Run.ckP .two. CONDITIONAL on KitCap at that kit, on
P5J.AtMgA, on the cut and on hkap: every listed round's bound, at every site, is at most kap₃; the
listed rounds are the events' rounds of both marks, and alpha's.** cap and kap₃ are letters. The
uniform law on the rounds' messages is named, not derived. The stated shares are not shown to be
held: their numerators alone are spent. The end is that hypothesis's own text, laid in by program;
the binders pre₁, e₁, cut and PM follow those of marksHead_hM_blocks6
(Honest/Law/MarksHeadK6Blocks.lean). That none of the defaults in the two marks' tests is met at
what the kit's messages show is `fence_all` (Honest/K3/Good/H3/Fence.lean [not in this library]): a
law beside this one, no clause of it. -/
theorem k3Marks_hM_blocks (cap : Fmt.Entry → Fmt.Kind → ℝ≥0∞)
    (hcap : KitCap (_root_.Run.ckP .two) cap) (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {G₀ : ProofFile.Ground} (kap₃ : ℝ≥0∞)
    (hkap : ∀ s ∈ lookSites Zp, CapsUnder cap s.at_.face (s.p.entries.getD []) kap₃)
    {pre₁ : List (Block P5J.TS ProofFile.Cl)} {e₁ : Block P5J.TS ProofFile.Cl} (cut : cF.blocksInOrder = pre₁ ++ [e₁])
    {PM : Block P5J.TS ProofFile.Cl → List Fmt.Drawn → Prop} :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K3.Good.k3Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) ((mk.share.num : ℝ≥0∞) * kap₃) := by
  intro A b b' B hpre mk hmk dsb hf
  obtain ⟨hm, hpl⟩ := List.mem_filter.1 hmk
  have hb : b ∈ cF.blocksInOrder := by
    rw [cut, hpre]
    exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
  exact k3Marks_debt_blocks cap hcap h G₀ kap₃ hkap hm hb (eq_of_beq hpl) dsb hf (PM b)

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.k3Marks_hM_blocks
