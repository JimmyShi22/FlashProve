-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/BuiltAtName.lean: in the goals' scope, where the proof file's value is laid, the
list of built segments has 25 entries: one for each written segment.

Why. The composed meaning's parameters read that list by a segment's number and lay a default where
it answers nothing. The named test `builtB` (Johnson/P5J/OptsOk.lean) asks that it answers at every
written segment. The list holds a function in each entry, so no comparison with a written value can
hold it. But its length follows from the maker's own text.

What is shown.
  `built_size`: **`Zp.made.p.built.links.size = 25`**, from the scope and `LaidAt` at the second
    hash function. No written value is compared. A chain of calls: the public part is made by the
    plain planner (`ProofFile.Law.pubBy_made`, `madeOf_planned`); its built list is `buildLinksH` of the
    plain list (`IM.planned_built`, `IM.plain_built`); the plain list has 2 * NGr + 1 entries where
    attention is covered (`listLinksH_with`); `buildLinksH` keeps the length (`buildLinksH_keeps`);
    in scope attention is covered and there are 12 groups (`publicO_at_scope`).
  `built_at_name`: **the body of `builtB Zp`, written out, is true.** That file is not imported
    here; where it lies, the statement is `builtB Zp = true` by unfolding.

Limits. The length alone: nothing on what an entry holds. The full size alone. The premise on the
scale file's reading is not spent. Nothing on soundness.


-/
import Johnson.P5J.LettersAt4
import Johnson.P5J.LaidOpens
import Johnson.IMR.PureJoin
import OnBytes.TieK.LinksEnd
import OnBytes.Tie.Pv.Keeps.LinksOrder
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J

open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)

/-- **The list of built segments has 25 entries.** -/
theorem built_size {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    Zp.made.p.built.links.size = 25 := by
  have hp := ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
          (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts Z.pol Z.lay Z.KL = .ok Zp
            from L.pub))
  obtain ⟨l₀, h1, h2⟩ := IM.plain_built (IM.planned_built hp)
  have F := H2K.Sizes.publicO_at_scope hZ L.publicO
  have F4 : Zp.made.p.X.p4 = true := F.p4
  have FG : Zp.made.p.X.NGr = 12 := F.groups
  unfold ProofFile.Plain.linksPlain at h1
  rw [F4] at h1
  obtain ⟨_, _, h3, _⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h1
  have h4 := congrArg List.length
    (OnBytes.TieK.buildLinksH_keeps (fun _ => ()) (fun _ _ => rfl) h2)
  rw [List.length_map, List.length_map, Array.length_toList, Array.length_toList] at h4
  rw [h4, h3, FG]

/-- **The list of built segments answers at every written segment.** -/
theorem built_at_name {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (_ : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ((List.range At.links.length).all fun l => (Zp.made.p.built.links[l]?).isSome) = true := by
  have hs := built_size hZ L
  have hl : At.links.length = 25 := rfl
  refine List.all_eq_true.2 fun l hm => ?_
  have hlt : l < Zp.made.p.built.links.size := by
    rw [hs, ← hl]
    exact List.mem_range.1 hm
  rw [Array.getElem?_eq_getElem hlt]
  rfl

end P5J

#print axioms P5J.built_size
#print axioms P5J.built_at_name
