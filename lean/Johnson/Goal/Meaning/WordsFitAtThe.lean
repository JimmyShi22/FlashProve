-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/WordsFitAtThe.lean: THE TEST wordsFitAt
(Johnson/Goal/Meaning/PublicSizesAt.lean) SAYS YES AT ALL PUBLIC FILES IN SCOPE WHERE protocolDataWellFormed SAYS
YES. A theorem: so whoever asks both tests asks protocolDataWellFormed alone. This file states no goal. It turns
none.

Main names.
  chainsOf_key_binding   in what chainsOf returns at the release's lines the key's binding tree is
    ⟨0, 40⟩: one leaf, a salt of 40 bytes.
  chainsOf_key_salt_at   there the plan of the key's one-time chain has a leaf salt of 40 bytes.
  rounds_keyFull, rounds_proofFull   roundsB at the two files' written lists: every round has fewer
    than 2^64 items and every tree a width below 2^64: by evaluation in Lean's kernel, list by list.
  wordsFitAt_the         THE END: InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    wordsFitAt (asDescriptionFiles Z) = true.
  sizesSay_the           so SizesSay of what verify()'s description lays at Z.

By: key_written_of_liveAt, proof_written_of_live (Johnson/Goal/Description/KeyWritten.lean,
ProofWritten.lean): in scope, under protocolDataWellFormed, both files' data ARE the written lists ·
writtenKFull_eq, writtenPFull_eq (Johnson/Flat/Dec/FitAtWritten.lean): the twins that the kernel
evaluates · thePlan_key (Johnson/Goal/Description/PlanKey.lean) · chainsOf_proof_binding
(Johnson/Goal/Numbers/DepthAtThe.lean): ⟨6, 40⟩ · configure_salts
(OnBytes/Maker/Page/OnePlan.lean) · configure_oneTime_salt, Given.read_salt
(OnBytes/K/KeySalt.lean).

Not shown here: that protocolDataWellFormed says yes at any public files: that is proved in Lean, in the side
library (outside the main library and with that library's own limits), at the written copy of the
full-size example's files under every acceptance policy in scope (theLive_zAt,
AtFullSide/Top/LiveAtPolicies.lean; owner: Johnson/Goal/Conditions/HomeLast.lean, limit 4). The
scope is wider than these files; elsewhere in it that protocolDataWellFormed accepts stays a premise. Nothing at
files out of scope. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Meaning.PublicSizesAt
import Johnson.Goal.Description.KeyWritten
import Johnson.Goal.Description.ProofWritten
import Johnson.Goal.Numbers.DepthAtThe
import OnBytes.K.KeySalt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Verify
open OnBytes.Params

/-- **The key's binding tree in what chainsOf returns at the release's lines.** -/
theorem chainsOf_key_binding {X : Public} {layout : Option ByteArray} {c : ByteArray}
    {ch : Chains} (h : chainsOf X layout c = .ok ch) (hl : X.P.frame = recordLines)
    (h32 : c.size = 32) (hb : (ch.bytes .keyOneTime).size < 2 ^ 64) :
    ch.key.oneTime.binding = ⟨0, 40⟩ := by
  obtain ⟨r1, -, -⟩ := OnBytes.TieK.G.chainsOf_read h
  obtain ⟨shapes, hm⟩ := chainsOf_made h
  rw [hl] at hm
  obtain ⟨P1, F', e1, -, -, -, sk, -⟩ := Maker.Page.configure_salts hm
  obtain ⟨m, r, t, c', ll, F⟩ := TieK.oneTime_read_open (Params.KeyChains.read_parts r1).1
  have g1 := F.given
  have b1 : ch.bytes .keyOneTime = ch.made.keyOneTime := rfl
  rw [b1, e1] at g1 hb
  have t1 := Params.Given.read_items hb h32 (by
    intro y hy
    simp only [Plan.oneTimeItems, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)) g1
  have q1 := F.items
  rw [t1] at q1
  simp only [Plan.oneTimeItems, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at q1
  have w := F.binding
  rw [← q1.2.2.1] at w
  have hk : readBinding (spellBinding ⟨0, (settingOf recordLines).saltBytes⟩) = some ⟨0, 40⟩ := by
    decide +kernel
  have hz : ch.made.sized.key.binding = ⟨0, (settingOf recordLines).saltBytes⟩ := by
    show (⟨0, ch.made.sized.key.set.saltBytes⟩ : LinBindingShape) = _
    rw [sk]
  rw [hz] at w
  exact Option.some.inj (w.symm.trans hk)

/-- **The leaf salt's bytes in the plan of the key's one-time chain, at the release's lines.** -/
theorem chainsOf_key_salt_at {X : Public} {layout : Option ByteArray} {c : ByteArray}
    {ch : Chains} (h : chainsOf X layout c = .ok ch) (hl : X.P.frame = recordLines) :
    ch.key.oneTime.given.plan.salt = 40 := by
  obtain ⟨r1, -, -⟩ := OnBytes.TieK.G.chainsOf_read h
  obtain ⟨shapes, hm⟩ := chainsOf_made h
  rw [hl] at hm
  obtain ⟨P, I, e1, hs⟩ := Params.configure_oneTime_salt hm
  obtain ⟨m, r, t, c', ll, F⟩ := TieK.oneTime_read_open (Params.KeyChains.read_parts r1).1
  have g1 := F.given
  have b1 : ch.bytes .keyOneTime = ch.made.keyOneTime := rfl
  rw [b1, e1] at g1
  rw [Params.Given.read_salt g1, hs]
  decide +kernel

end OnBytes.Model.Verify

namespace Meaning
open OnBytes.Maker OnBytes.Flat
open VerifierAndGoals FlashProve FlashProve
open LPFD.Full (XF sBG sTG saltG)
open Johnson.G (writtenKFull writtenPFull dKeyFull dProofFull writtenKFull_eq writtenPFull_eq)

/-- one round's test -/
def roundB (d : RDT) : Bool :=
  decide (d.items.length < 2 ^ 64) && d.trees.all fun t => decide (t.W < 2 ^ 64)

theorem roundsB_of (D : WholeD) (h₁ : D.ds₁.all roundB = true) (h₂ : D.ds₂.all roundB = true)
    (h₃ : D.ds₃.all roundB = true) : roundsB D = true := by
  show (D.ds₁ ++ (D.ds₂ ++ D.ds₃)).all roundB = true
  rw [List.all_append, List.all_append, h₁, h₂, h₃]
  rfl

set_option maxRecDepth 1000000 in
theorem key1 : dKeyFull.ds₁.all roundB = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem key2 : dKeyFull.ds₂.all roundB = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem key3 : dKeyFull.ds₃.all roundB = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem proof1 : dProofFull.ds₁.all roundB = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem proof2 : dProofFull.ds₂.all roundB = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem proof3 : dProofFull.ds₃.all roundB = true := by decide +kernel

theorem rounds_keyFull : roundsB writtenKFull = true := by
  rw [writtenKFull_eq]
  exact roundsB_of _ key1 key2 key3

theorem rounds_proofFull : roundsB writtenPFull = true := by
  rw [writtenPFull_eq]
  exact roundsB_of _ proof1 proof2 proof3

/-- **IN SCOPE, WHERE protocolDataWellFormed SAYS YES, wordsFitAt SAYS YES.** -/
theorem wordsFitAt_the (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) : wordsFitAt (asDescriptionFiles Z) = true := by
  have hK : theKeyData (asDescriptionFiles Z) = writtenKFull :=
    key_written_of_liveAt OnBytes.secondHashFunction Z scope live
  have hP : theProofData (asDescriptionFiles Z) = writtenPFull := proof_written_of_live Z scope live
  obtain ⟨X₀, m, hX, _, hG, hc, hb⟩ := thePlan_key Z live
  have hf := (H2K.Sizes.publicO_at_scope scope hX).frame
  have bK : (sTG (thePlan (asDescriptionFiles Z))) = ⟨0, 40⟩ := by
    rw [hG]
    exact OnBytes.Model.Verify.chainsOf_key_binding hc hf VerifiableInference.Desc.theCfg_size
      (hb .keyOneTime)
  have bP : (sBG (thePlan (asDescriptionFiles Z))) = ⟨6, 40⟩ := by
    rw [hG]
    exact OnBytes.Model.Verify.chainsOf_proof_binding hc hf VerifiableInference.Desc.theCfg_size
      (hb .proofFirst)
  have sK : saltG (thePlan (asDescriptionFiles Z)) = 40 := by
    rw [hG]
    exact OnBytes.Model.Verify.chainsOf_key_salt_at hc hf
  unfold wordsFitAt sizesB
  rw [hK, hP, rounds_keyFull, rounds_proofFull, bK, bP, sK]
  decide

/-- So what the test's yes says holds of what verify()'s description lays at Z. -/
theorem sizesSay_the (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    SizesSay (dataAtFiles flashProveData Z).G (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP :=
  wordsFitAt_says live (wordsFitAt_the Z scope live)

end Meaning

#print axioms OnBytes.Model.Verify.chainsOf_key_binding
#print axioms OnBytes.Model.Verify.chainsOf_key_salt_at
#print axioms Meaning.roundB
#print axioms Meaning.roundsB_of
#print axioms Meaning.key1
#print axioms Meaning.key2
#print axioms Meaning.key3
#print axioms Meaning.proof1
#print axioms Meaning.proof2
#print axioms Meaning.proof3
#print axioms Meaning.rounds_keyFull
#print axioms Meaning.rounds_proofFull
#print axioms Meaning.wordsFitAt_the
#print axioms Meaning.sizesSay_the
