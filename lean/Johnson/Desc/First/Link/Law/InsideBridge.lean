-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/InsideBridge.lean: THE BRIDGE FROM THE FACT ALONG THE VERIFIER's RUN
«the live state of the calls holds the plan's layout» AND A TEST ON THAT LAYOUT TO THE LINK LAW's
PREMISE inside (`OwesConds`, LinkOwes.lean: in front of the one equation's piece every block of a
required array lies inside it). Definitions and a theorem.

What is said.
  `LayoutFact Rch lay`: the fact, written out: to the letter the field liveLayout of the structure
    of facts that the laws take from «reached» (Johnson/Desc/First/FoldFacts.lean),
    at the reading «the
    public part z and the state» of a statement. `LayoutInside lay`: every block of every array that
    the layout names lies inside it. `inside_of_fact`: **the premise inside, at the conditions of
    the second form (`onTR`).**

Limits. `LayoutFact` is a premise. `LayoutInside` at the release's
layout is a premise: a sentence on the plan alone: it has been shown of no layout here. This file
does not import the structure: it restates one field. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTiedR
import Johnson.Desc.First.Link.Law.RbRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers)

variable {F : Frame}

/-- **The fact along the run**, written out. -/
def LayoutFact (Rch : ℕ → S × F.E.Str → Prop) (lay : Params.ReqLayout) : Prop :=
  ∀ k (a : S × F.E.Str), Rch k a → a.1.failed = none → a.1.live.rows.layout = lay

/-- Every block of every array that the layout names lies inside it. -/
def LayoutInside (lay : Params.ReqLayout) : Prop :=
  ∀ born name r, reqArray lay born name = some r → ∀ bl ∈ r.blocks, Inside r bl

/-- **THE PREMISE inside, AT THE CONDITIONS OF THE SECOND FORM.** -/
theorem inside_of_fact {P W : Type} (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (pl : List Place) (z : P) (Rch : ℕ → S × F.E.Str → Prop) (lay : Params.ReqLayout)
    (G : LayoutFact Rch lay) (hI : LayoutInside lay) (k : ℕ) :
    ∀ s : S × F.E.Str, onTR Nm Mg links pl (fun s : S => (z, s)) Rch k s →
      ∀ a, atS.get? s.1 = some a → ∀ born name r,
        reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl := by
  intro s hs a ha born name r hr
  have hf : s.1.failed = none := Classical.not_not.1 hs.1.2
  have h1 := G k s hs.2 hf
  have hl : s.1.live = a.L.check := by
    unfold S.live
    rw [(part_reads s.1 a ha).1]
  rw [hl] at h1
  rw [h1] at hr
  exact hI born name r hr

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.inside_of_fact
