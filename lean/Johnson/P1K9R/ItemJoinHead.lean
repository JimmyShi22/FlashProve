-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/ItemJoinHead.lean: the batching kind's law (K9), AT THE CLOSED CONSTANT:
WHAT IS LEFT OF hitems (the structure HitemsLeft, Johnson/LPFE1R/HitemsAtConst.lean), ITS FIELD
k3i AT THE OUTPUT HEAD's LINK's ENTRY (3, "join"). THE ENTRY. It is the output head's own run: the
lookup's run "join" fed with the head's key vectors. The table of terms tmH answers it by plainTm
(valsStill (fsJoin ..)) (Johnson/Desc/First/Link/Law/PayHead.lean), not by the lookups' table t3.

  join_in_head · join3_not_in_attention  the entry is of the head's order, and not of attention's:
                    by decide +kernel
  k3i_join_head_at  THE CLAUSE, at the field's own letters. ITS BINDERS ARE AMONG THOSE OF
                    hitems_head_at (LPFE1R/): the head · z · hlk · hL · A : HeadTake .. · rdW · ok
HOW. A CARRY, NO MORE: item_head_join (Johnson/Desc/First/Link/Law/HitemsMarks.lean: the
clause at the readers of the link itself, from HeadTake), had at the empty second hole and carried
to the constant's readers by forms_of_run, formsIn_congr, itemIn_congr
(Johnson/Desc/First/Link/Law/HitemsHead.lean) with hrun_any_at
(Johnson/LPFE1R/HrunAnyAt.lean), as other files do at "objects".
LIMITS. An implication: HeadTake's fields are premises. No state is shown to meet on0At. The full
size alone. From the head (with the fourteen entry tests): a verifier whose entry tests lack the two
pins' rows gives no such head. No example of the head by Lean's kernel. No soundness is claimed.

-/
import Johnson.Desc.First.Link.Law.HitemsMarks
import Johnson.LPFE1R.HitemsAtConst
import Johnson.LPFE1R.HrunAnyAt
import Johnson.Desc.First.Link.Law.SortLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart orderOf)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open IM (subAt)

/-- "join" is of the head's order. -/
theorem join_in_head : ((3 : ℕ), "join") ∈ orderOf ModelPart.head := by decide +kernel

/-- A negative test: at that number it is not of attention's order. -/
theorem join3_not_in_attention : ¬ ((3 : ℕ), "join") ∈ orderOf ModelPart.attention := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
variable {W : Type} {L : Link S Claim} {u : HTailF2} {Ok : Q BetaAll → Prop} {Fu : S → Prop}
  {hS : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Kinds.Head.Par}
  {kap : Phi BetaAll → Option Kinds.Head.Law.Seen} {nU : Array ℕ}
  {tm4 : ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q BetaAll → ℕ}

/-- **AT THE OUTPUT HEAD's LINK: THE FIELD k3i's CLAUSE AT (3, "join").** -/
theorem k3i_join_head_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub)
    (hlk : h.𝔇.lk 24 = some L) (hL : SegAt 24 .head L)
    (A : HeadTake L u psiAll Ok Fu hS iU3 l' piece p kap nU entUnit tm4 t3 l3)
    (rdW : W → ℕ × ℕ → MsgQ) (ok : ∀ a, on0At h z 24 a → Ok (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z 24 a →
      ItemIn L (phiAll u psiAll) (tmH hS iU3 p kap entUnit tm4 t3) (lenH hS iU3 p kap l3)
        (h.𝔇.Rd 24) (h.𝔇.N.group 24) rdW a w (3, "join") := by
  intro a w ha
  have hm : 24 < 25 := by omega
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (part_at h z hm a ha)
  have he : ((3 : ℕ), "join") ∈ orderOf (subAt 24) := join_in_head
  have hin := hin_at h hm z _ a ha he rfl
  have hrun := hrun_any_at h z hlk a ha (3, "join") (by decide) rfl
  rw [readers_at24 h 24, K9.readersAt_some _ _ _ _ L hlk] at hin ⊢
  have e0 := forms_of_run (K9.withSmall K9.LinkHoles.none) (K9.holesAt (P5J.At.X Zp) 24 24 L) L
    3 "join" a.1 rfl hrun
  have hin0 := (formsIn_congr (h.𝔇.N.group 24) 3 "join" a.1 e0).trans hin
  have hq2 : (fixed9 (phiAll u psiAll) a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  have hf : Fx9 (phiAll u psiAll) Ok (fixed9 (phiAll u psiAll) a.1) a.1 :=
    ⟨ok a ha, rfl, pubOf b, b, hq2, hb, goesOn_refl b⟩
  exact itemIn_congr (e := (3, "join")) e0.symm
    (item_head_join (K9.withSmall K9.LinkHoles.none) hL A _ rdW a w b ⟨hb, hf⟩ rfl hin0).toIn

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.join_in_head
#print axioms VerifiableInference.Desc.LinkJoin.join3_not_in_attention
#print axioms VerifiableInference.Desc.LinkJoin.k3i_join_head_at
