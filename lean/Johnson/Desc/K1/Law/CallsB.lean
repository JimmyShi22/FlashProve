-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/CallsB.lean: K01_law: CALLS, EACH TO THE LETTER OF A BINDER OF THE TOP (k01_law, Johnson/Desc/K1/Law/K01Law.lean) OR OF AN ARM OF hgo (Johnson/Desc/K1/Law/GoAtLater.lean), FROM WHAT LIES.
  tiedAllForms_full   [kernel] every tied public item that comes at a reads' place is a «formsIn»
  pubP_true        where Mg's pubP is the lookups' layer's over a base that says True (FillsK1.pubP; as reported: Mg₀.pubP := fun _ _ => True): pubP holds at every item but left | leftOn
  hpubP_of         **hpubP: PAID**: what comes at (l, d) is a «formsIn» or a named item of the door: neither is left | leftOn
  hPubP_of         **hPubP ⟸ ONE ARM**: pubP at left m | leftOn m (k3LeftItemAt | k3LeftOnItemAt) goes over the block's own yes (by a look «left» is open at none of the fifty: the arm is idle there; no fact on the door is asked)
  aPinW_of         hgo's arm pinW ⟸ DecBlind decT (pinW_back_blind, K13/Law/SigDecodes.lean)
  aPin_of | aPinI_of   hgo's arms pin | pinI ⟸ hbase · SmpLeft (pin_arms, Johnson/Desc/K1/Law/PinsGoBack.lean)
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.MgK1
import Johnson.Desc.K1.Law.FillsK1
import Johnson.Desc.K1.Law.PinsGoBack
import Johnson.Desc.K13.Law.SigDecodes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Maker Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More PubData flatPlacesOf)
open VerifiableInference.Desc.Sound (Mem MsgT linksFull SitsAt)
open VerifiableInference.Desc.K13.Law (DecBlind openAt)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads)

variable {Pp Xi Cells Tok : Type}

/-- The item is a «formsIn». -/
def isFormsIn : Pub → Bool
  | .formsIn _ _ _ => true
  | _ => false

theorem tiedAllForms_full : ((List.range 25).all fun l =>
    (tiedAt linksFull (flatPlacesOf linksFull true) (noR l)).all isFormsIn) = true := by
  decide +kernel

section
variable {D : PubData} {G : FileDescription Xi} {arr : ℕ → ℕ → ℕ}
  {smp : Pp × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf D.cs s.l).om i).Smp}
  {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
  {shape : Params.ReqShape} {layout : Params.ReqLayout} {io0 : Pp × S → Bool}
  {base : Pub → Pp × S → Bool} {X3 : OnBytes.Model.Verify.Public} {D3 : First.Look.Sent}
  {MgP Mg : Meaning Pp (Wit Cells Tok MsgT)}

/-- The item is the lookups' «left» or «leftOn»: the two at which their layer lays pubP. -/
def isLeft : Pub → Bool
  | .left _ | .leftOn _ => true
  | _ => false

theorem isLeft_false (q : Pub) (h1 : ∀ m, q ≠ .left m) (h2 : ∀ m, q ≠ .leftOn m) :
    isLeft q = false := by
  cases q with
  | left m => exact absurd rfl (h1 m)
  | leftOn m => exact absurd rfl (h2 m)
  | _ => rfl

/-- **What is asked of the base meaning Mg₀** (by report, not checked here: Mg₀.inOrder := fun _ => true · Mg₀.pubP := fun _ _ => True: each field then by rfl). -/
structure BaseK1 (M : More) (MgP : Meaning Pp (Wit Cells Tok MsgT)) : Prop where
  /-- AT THE ITEMS THAT ARE OPEN BEHIND ONE OF THE FIFTY PLACES ALONE: asked of EVERY item it is FALSE at the base meaning (mgBase, Johnson/Desc/Sound/MgBase.lean: pubP q _ := (First.saysNone q).isSome = true) at an item which no part names:
  the law above it would be empty there. -/
  pubP : ∀ l, l < 25 → ∀ d : Bool,
    ∀ q ∈ (First.pubSets M linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [], isLeft q = false → ∀ a, MgP.pubP q a

theorem pubP_true (h : FillsK1 D G arr smp ms decT shape layout io0 base X3 D3 MgP Mg)
    (q : Pub) (a : Pp × S) (hBaseP : MgP.pubP q a) (h1 : ∀ m, q ≠ .left m)
    (h2 : ∀ m, q ≠ .leftOn m) : Mg.pubP q a := by
  rw [h.pubP, First.Look.fill_pubP_other _ _ _ q a h1 h2]
  exact hBaseP

/-- What comes at (l, d) is neither «left» nor «leftOn». -/
theorem tiedL_other (M : More) (l : ℕ) (hl : l < 25) (d : Bool) (q : Pub) (hq : q ∈ tiedL M l d) :
    (∀ m, q ≠ .left m) ∧ ∀ m, q ≠ .leftOn m := by
  have made : ∀ k, q ∈ madeAt M linksFull (flatPlacesOf linksFull true) k →
      (∀ m, q ≠ .left m) ∧ ∀ m, q ≠ .leftOn m := by
    intro k hk
    unfold madeAt at hk
    split at hk
    · obtain ⟨n, _, rfl⟩ := List.mem_map.1 hk
      exact ⟨fun m e => by simp [First.moreItem] at e, fun m e => by simp [First.moreItem] at e⟩
    · exact nomatch hk
  cases d with
  | true =>
    exact made _ (by simpa [tiedL] using hq)
  | false =>
    rcases List.mem_append.1 (show q ∈ tiedAt linksFull (flatPlacesOf linksFull true) (noR l) ++
      madeAt M linksFull (flatPlacesOf linksFull true) (noR l) from hq) with h | h
    · have a := List.all_eq_true.1 (List.all_eq_true.1 tiedAllForms_full l (List.mem_range.2 hl)) q h
      cases q with
      | formsIn _ _ _ => exact ⟨fun m e => (by cases e), fun m e => (by cases e)⟩
      | _ => simp [isFormsIn] at a
    · exact made _ h

/-- **hpubP: PAID** (the binder's last two lines; its other premises are not spent). -/
theorem hpubP_of (h : FillsK1 D G arr smp ms decT shape layout io0 base X3 D3 MgP Mg)
    (l : ℕ) (hl : l < 25) (d : Bool)
    (hBaseP : ∀ q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [],
      isLeft q = false → ∀ a, MgP.pubP q a) (a : Pp × S) :
    ∀ q ∈ tiedL Mg.more l d,
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] →
      Mg.pubP q a :=
  fun q hq hq' => pubP_true h q a
    (hBaseP q hq' (isLeft_false q (tiedL_other _ l hl d q hq).1 (tiedL_other _ l hl d q hq).2) a)
    (tiedL_other _ l hl d q hq).1 (tiedL_other _ l hl d q hq).2

/-- **hPubP ⟸ the arm at left | leftOn.** -/
theorem hPubP_of (h : FillsK1 D G arr smp ms decT shape layout io0 base X3 D3 MgP Mg)
    (N : Numbers) (B : Block S Unit) (l : ℕ) (d : Bool)
    (hBaseP : ∀ q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [],
      isLeft q = false → ∀ a, MgP.pubP q a)
    (aLeft : ∀ (x x' : Pp × S) y q, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → isLeft q = true →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] →
      Mg.pubP q x') :
    ∀ (x x' : Pp × S) y q, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] →
      Mg.pubP q x' := by
  intro x x' y q hy hIn hq hq'
  by_cases e : isLeft q = true
  · exact aLeft x x' y q hy hIn e hq
  · exact pubP_true h q x' (hBaseP q hq' (Bool.eq_false_iff.2 e) x') (fun m c => e (by rw [c]; rfl))
      (fun m c => e (by rw [c]; rfl))

/-- hgo's arm at pinW. -/
theorem aPinW_of (h : FillsK1 D G arr smp ms decT shape layout io0 base X3 D3 MgP Mg)
    (hBlind : DecBlind decT) (B : Block S Unit) (base : ℕ) (x x' : Pp × S) (y y' : Strs)
    (w : Wit Cells Tok MsgT) (hy : YesOf B x x') (hK : KeptBelow base y y')
    (h0 : Mg.pinW x' y' w) : Mg.pinW x y w := by
  rw [h.pinW] at h0 ⊢
  exact K13.Law.pinW_back_blind hBlind hy.1 hK.1 h0

/-- hgo's arms at the pins that ride. O: what is open in front. In: the promise in front (SmpLeft's letter: without it SmpLeft is false at smpNamed (Johnson/Desc/Sound/SmpNamed.lean)). -/
theorem aPins_of (h : FillsK1 D G arr smp ms decT shape layout io0 base X3 D3 MgP Mg) (N : Numbers)
    (B : Block S Unit) (In : Pp × S → Strs → Prop) (O : List Item) (base : ℕ)
    (hbase : ∀ u ∈ First.sampledIn N O, u.1 < base)
    (hSmp : SmpLeft D.cs B In smp ms (First.sampledIn N O)) (x x' : Pp × S) (y y' : Strs)
    (w : Wit Cells Tok MsgT) (hy : YesOf B x x') (hIn : In x y) (hK : KeptBelow base y y')
    (i : Item) (hi : i ∈ O) (hp : IsPin i) (h0 : i.holds N Mg x' y' w) : i.holds N Mg x y w :=
  pin_arms D.cs G arr smp ms N Mg h.pin O base x x' y y' w hbase hK.2
    (fun u hu m hm hs => hSmp x x' y hy hIn u hu m hm hs) i hi hp h0

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.tiedAllForms_full
#print axioms VerifiableInference.Desc.K1.hpubP_of
#print axioms VerifiableInference.Desc.K1.hPubP_of
#print axioms VerifiableInference.Desc.K1.aPinW_of
#print axioms VerifiableInference.Desc.K1.aPins_of
