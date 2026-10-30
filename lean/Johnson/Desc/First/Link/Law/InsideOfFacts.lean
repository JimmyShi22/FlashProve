-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/InsideOfFacts.lean (kind K9): THE FIELD Ainside OF A LINK's «REST» (`CoreRest2`, LinkRestAtSort2.lean; `OwesConds`' inside, LinkOwes.lean): «in front of the one equation's piece every block of a
required array lies inside it»: FROM THE FACTS THAT THE LAWS TAKE FROM «REACHED» (`FoldFacts`) AND THE PROGRAMS' OWN TEST ON THE LAYOUT. A theorem: a join of three that lie.

THE SEARCH FIRST. Nobody held the field by name. But all its stones lie: `inside_of_fact` (InsideBridge.lean beside this file): the field's text from «the live copy of the calls' state holds the layout lay» (`LayoutFact`) and
«every block of every array that lay names lies inside it» (`LayoutInside`): both premises there · `FoldFacts.liveLayout` IS the first, to the letter · `K9L.inside_of_layoutOk` (Johnson/Desc/First/Batch/Law/Layout.lean)
gives the second from `reqLayoutOk codes shape lay = true`.

What is said.
  `layoutFact_of_facts`: FF : FoldFacts Rch (fun a => a.1) fd reqW links' ps' ⊢ `LayoutFact (RchAt Rch z) fd.sent.layout`, at every public part z.
  `layoutInside_of_ok`: `reqLayoutOk codes shape lay = true` ⊢ `LayoutInside lay`.
  `ainside_of_facts`: **FF · reqLayoutOk fd.sent.codes fd.sent.shape fd.sent.layout = true ⊢ THE FIELD's TEXT, TO THE LETTER, at the conditions onTR Nm Mg links pl (fun s => (z, s)) (RchAt Rch z) k, every k.** General in the
    numbers, the meaning, the lists and the frame.

Limits. FoldFacts is a premise. The test's yes is a premise here: at the constant's letters: Johnson/P5J/InsideAtMg.lean. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.InsideBridge
import Johnson.Desc.First.Link.Law.LinkTiedPubR
import Johnson.Desc.First.Batch.Law.Layout
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers FoldFacts FoldData)

variable {F : Frame} {P : Type}

/-- The fact along the run is the structure's own field. -/
theorem layoutFact_of_facts {Rch : ℕ → (P × S) × F.E.Str → Prop} {fd : FoldData}
    {reqW : P → Array UInt32} {links' : List ModelPart} {ps' : List Place}
    (FF : FoldFacts Rch (fun a => a.1) fd reqW links' ps') (z : P) :
    LayoutFact (RchAt Rch z) fd.sent.layout :=
  fun k a hr hu => FF.liveLayout k ((z, a.1), a.2) hr hu

/-- The programs' own test on a layout gives the sentence on it. -/
theorem layoutInside_of_ok {codes : Codes} {shape : Params.ReqShape} {lay : Params.ReqLayout}
    (h : reqLayoutOk codes shape lay = true) : LayoutInside lay :=
  fun born name r hr => inside_of_layoutOk codes shape lay h born name r hr

/-- **THE FIELD Ainside, TO THE LETTER.** -/
theorem ainside_of_facts {W : Type} {Rch : ℕ → (P × S) × F.E.Str → Prop} {fd : FoldData}
    {reqW : P → Array UInt32} {links' : List ModelPart} {ps' : List Place}
    (FF : FoldFacts Rch (fun a => a.1) fd reqW links' ps')
    (hOk : reqLayoutOk fd.sent.codes fd.sent.shape fd.sent.layout = true)
    (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P) (k : ℕ) :
    ∀ s : S × F.E.Str, onTR Nm Mg links pl (fun s : S => (z, s)) (RchAt Rch z) k s →
      ∀ a, atS.get? s.1 = some a → ∀ born name r,
        reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl :=
  inside_of_fact Nm Mg links pl z (RchAt Rch z) fd.sent.layout (layoutFact_of_facts FF z)
    (layoutInside_of_ok hOk) k

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.layoutFact_of_facts
#print axioms VerifiableInference.Desc.LinkJoin.layoutInside_of_ok
#print axioms VerifiableInference.Desc.LinkJoin.ainside_of_facts
