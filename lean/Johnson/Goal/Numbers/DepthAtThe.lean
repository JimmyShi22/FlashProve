-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/DepthAtThe.lean: at the closed term VerifierAndGoals.theDescription, in the goals' scope and where the
gate protocolDataWellFormed is open, the binding tree of a batch's requests has depth 6: so the number 2 ^ depthReq
of requests behind one key, which the shared chain's field of the proof file's soundness
(shared_joint_count: EachLawsBN … (2 ^ depthReq) …) bears, is 64. K14's files' bound for the shared
chain's round "LIN point" is proved for at most 64 requests (their top's premise slots ≤ 64). The
like for the key file's tree (depth 0) is depthReqT_the
(Johnson/Goal/Conditions/KeyDepthAtThe.lean), whose road this file follows.
  chainsOf_proof_binding: in what chainsOf returns at the release's lines and a digest of 32 bytes,
      the proof file's first chain's parameters, as read back, have the binding tree ⟨6, 40⟩ (depth,
      salt bytes), if that chain's parameter bytes are fewer than 2 ^ 64
  depth_the: (sBG (dataAtFiles flashProveData Z).G).logLeaves = 6, from InScope Z and protocolDataWellFormed's accept: the term
      that Johnson/Goal/Skeleton/ProofAtName.lean abbreviates as depthZ Z
  slots_the: 2 ^ that depth = 64; slots_le_the: ≤ 64

How. Under protocolDataWellFormed's accept the frame's list of rounds is the one of which the key file's IOP as
written in Lean is made, and each of its seven strings of parameter bytes is shorter than 2 ^ 64
(thePlan_key, PlanKey.lean: the key's door asks it: of all seven, the proof's first among them).
In scope the lines are the release's (publicO_at_scope, PublicOAtScope.lean).

What is not claimed. That protocolDataWellFormed accepts at any files: at files as bytes an evaluation alone says so. That the public
part of the proof file's IOP as written in Lean (ProofFile.Pub) has this binding tree: that is Written's
clause slots, at another term. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Description.PlanKey
import Johnson.Goal.Conditions.LiveAtThe
import Johnson.Goal.Conditions.DepthsAtDescriptionDataAtFiles
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope
import OnBytes.Maker.Page.OnePlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Verify
open OnBytes.Params

/-- **The proof file's binding tree in what chainsOf returns at the release's lines.** -/
theorem chainsOf_proof_binding {X : Public} {layout : Option ByteArray} {c : ByteArray}
    {ch : Chains} (h : chainsOf X layout c = .ok ch) (hl : X.P.frame = recordLines)
    (h32 : c.size = 32) (hb : (ch.bytes .proofFirst).size < 2 ^ 64) :
    ch.proof.first.binding = ⟨6, 40⟩ := by
  obtain ⟨-, -, r3⟩ := OnBytes.TieK.G.chainsOf_read h
  obtain ⟨shapes, hm⟩ := chainsOf_made h
  rw [hl] at hm
  obtain ⟨P1, F, e1, e5, -, -, sk, sz⟩ := Maker.Page.configure_salts hm
  obtain ⟨_, _, _, _, _, _, t3, B⟩ := TieK.first_read_open (Params.ProofChains.read_parts r3).1
  have g3 := B.given
  have b3 : ch.bytes .proofFirst = ch.made.first := rfl
  rw [b3, e5] at g3 hb
  have i3 := (Given.read_items hb h32 (madeFirstItems_names _ _ _) g3).symm.trans B.items
  simp only [madeFirstItems, madeLinItems, List.cons_append, List.nil_append, List.cons.injEq,
    Prod.mk.injEq, true_and] at i3
  have hbd := B.binding
  rw [← i3.2.2.2.2.2.2.1, sz] at hbd
  have hk : readBinding (spellBinding ⟨clog2 recordLines.slots,
      (settingOf recordLines).saltBytes⟩) = some ⟨6, 40⟩ := by decide +kernel
  exact Option.some.inj (hbd.symm.trans hk)

end OnBytes.Model.Verify

namespace FlashProve
open VerifierAndGoals FlashProve VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat

/-- **At the name the binding tree of a batch's requests has depth 6**, in scope, where the gate is
open. -/
theorem depth_the (Z : PublicFiles) (hZ : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves = 6 := by
  rw [g_built_live Z hl]
  obtain ⟨X₀, m, hX, _, hG, hc, hb⟩ := thePlan_key Z hl
  rw [hG]
  show m.p.chains.proof.first.binding.logLeaves = 6
  rw [OnBytes.Model.Verify.chainsOf_proof_binding hc (H2K.Sizes.publicO_at_scope hZ hX).frame
    VerifiableInference.Desc.theCfg_size (hb .proofFirst)]

theorem slots_the (Z : PublicFiles) (hZ : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    2 ^ (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves = 64 := by
  rw [depth_the Z hZ hl]
  rfl

theorem slots_le_the (Z : PublicFiles) (hZ : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    2 ^ (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves ≤ 64 :=
  le_of_eq (slots_the Z hZ hl)

end FlashProve

#print axioms OnBytes.Model.Verify.chainsOf_proof_binding
#print axioms FlashProve.depth_the
#print axioms FlashProve.slots_the
#print axioms FlashProve.slots_le_the
