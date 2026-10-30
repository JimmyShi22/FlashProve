-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/ReplyStonesLaid.lean: WHERE THE PROOF FILE's VALUE IS LAID (`LaidAt`,
Johnson/P5J/LaidOpens.lean), IN THE GOALS' SCOPE, THE THREE PREMISES ON THE DRIVER's STRUCTURE OF
THE FRAME FACT ON THE REPLY (`eachRep_at_driver`, Johnson/P5J/ReplyAtDriver.lean) HOLD AT ONE H.
For the field reply_leaves of the proof file's rows. A joining.

  `vocabulary_in_scope`: in scope the plan's vocabulary is no larger than the reference's.
  `reply_stones`: ∃ H, (R1) `firstChain H fullLinks true = some cF` ∧ (R2) what `H.same` lets pass
    leaves `heardV` ∧ (R3) what `H.block` gives at a place of the kind K7 hears once.
What is called: `reply_stones_open` (Johnson/P5J/ReplyStones.lean) at `LaidAt.opened` ·
`P4.base_k7_hearsOnce` (Johnson/P4R/BaseK7HearsOnce.lean) ·
`InScope.numbers_in_scope` (Johnson/Goal/Meaning/HeadCondScope.lean).
Limits. At OnBytes.secondHashFunction alone, and with "the reader returns pp" beside the scope: the stones stand
there. THAT ANY FILES MEET THE THREE PREMISES IS NOT SHOWN HERE. Nothing on soundness. On hiding
nothing.

-/
import Johnson.P5J.ReplyStones
import Johnson.P5J.LaidOpens
import Johnson.P4R.BaseK7HearsOnce
import Johnson.Goal.Meaning.HeadCondScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (Blocks firstChain)
open OnBytes.Maker (WholeD)

/-- In scope the plan's vocabulary is no larger than the reference's. -/
theorem vocabulary_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) : X.hS.V ≤ Inst.Model.ppref.V := by
  rw [(VerifiableInference.Desc.Kinds.Head.Law.InScope.numbers_in_scope hZ hR h).V]
  decide

/-- **THE THREE AT ONE H, WHERE THE VALUE IS LAID.** -/
theorem reply_stones {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∃ H : Blocks TS ProofFile.Cl, firstChain H fullLinks true = some cF ∧
      (∀ t s, H.same t s = true → heardV (fun s : TS => s) s = heardV (fun s : TS => s) t) ∧
      ∀ a b, H.block a = some b → a.kind = KindName.K7 →
        b.HearsOnce (heardV fun s : TS => s) := by
  obtain ⟨Bs, base, O⟩ := L.opened
  exact reply_stones_open hZ hR O
    (P4.base_k7_hearsOnce O (vocabulary_in_scope hZ hR O.public))

end P5J

#print axioms P5J.vocabulary_in_scope
#print axioms P5J.reply_stones
