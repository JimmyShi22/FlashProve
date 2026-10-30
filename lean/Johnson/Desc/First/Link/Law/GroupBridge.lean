-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/GroupBridge.lean: THE BRIDGE FROM THE FACT ALONG THE VERIFIER's RUN «in
front of a sub-protocol of segment m, where a segment's link context is in use, the group that it
names is the plan's group of the segment» TO THE PREMISE hg OF THE ONE EQUATION's HAND-ON
(RidesAtMgR.lean: `hon3_mgR`). Theorems.

What is said.
  `GroupFact Rch pl g`: the fact, written out: to the letter the field groupIs of the structure of
    facts that the laws take from «reached» (Johnson/Desc/First/FoldFacts.lean),
    at the reading «the public part z and the state» of
    a statement. `hg_of_group`: **hg, at the conditions of the second form.** `hon3_mgF`: `hon3_mgR`
    with `GroupFact` in the place of hg.

Limits. `GroupFact` is a premise: Johnson/IMR/GroupField.lean has it along the fold at all 25
segments.
That the plan's numbers name the group as that fact does (`Nm.groupAt m = g m`) is a premise
too. This file does not import the structure: it restates one field. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.RidesAtMgR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers rowsAtFit)
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame}

/-- **The fact along the run**, written out. -/
def GroupFact (Rch : ℕ → S × F.E.Str → Prop) (pl : List Place) (g : ℕ → ℕ) : Prop :=
  ∀ k (a : S × F.E.Str) p m L, Rch k a → a.1.failed = none → pl[k]? = some p → p.link = some m →
    a.1.link? = some L → L.check.group = g m ∧ L.check.frame.group = g m

/-- **hg, at the conditions of the second form.** -/
theorem hg_of_group {P W : Type} (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (pl : List Place) (z : P) (Rch : ℕ → S × F.E.Str → Prop) (g : ℕ → ℕ)
    (G : GroupFact Rch pl g) (k m : ℕ) (p : Place) (hp : pl[k]? = some p) (hl : p.link = some m)
    (hN : Nm.groupAt m = g m) :
    ∀ a : S × F.E.Str, onTR Nm Mg links pl (fun s : S => (z, s)) Rch k a →
      ∀ x, atS.get? a.1 = some x → Nm.groupAt m = x.L.check.group := by
  intro a ha x hx
  have hf : a.1.failed = none := Classical.not_not.1 ha.1.2
  rw [hN, (G k a p m x.L ha.2 hf hp hl (part_reads a.1 x hx).1).1]

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

local notation "WT" => Wit (CellsQ rows cols) Tok MsgT

/-- **hon3, SECOND FORM, WITH THE FACT ALONG THE RUN IN THE PLACE OF hg.** -/
theorem hon3_mgF (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P)
    (Rch : ℕ → S × F.E.Str → Prop) (k m : ℕ) (p p' : Place) (hfit : linkFit links pl = true)
    (hlf : listFit links pl = true) (hpf : pubFitE moreAll links pl = true)
    (hN : rowsAtFit Nm links.length = true) (hml : m < links.length) (hp : pl[k]? = some p)
    (hp' : pl[k + 1]? = some p') (hl : p.link = some m) (hpc : p.piece = hearN links m + 3)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece C F S Claim WT) (hpe : pe.b = below b₃) (H : HandsOn Rch k pe) (g : ℕ → ℕ)
    (G : GroupFact Rch pl g) (hg : Nm.groupAt m = g m)
    (A : ∀ a τ b, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      pe.ior.red.out a τ = some b → EqAsks 𝔇 Nm links pl z k pe.base a.1 b.1) :
    ∀ a τ b, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      pe.ior.red.out a τ = some b →
      onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch (k + 1) b :=
  hon3_mgR 𝔇 Nm links pl z Rch k m p p' hfit hlf hpf hN hml hp hp' hl hpc ht hm pw b₃ hb₃ pe hpe H
    (hg_of_group Nm (mgAll 𝔇 mgBase) links pl z Rch g G k m p hp hl hg) A

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.hg_of_group
#print axioms VerifiableInference.Desc.LinkJoin.hon3_mgF
