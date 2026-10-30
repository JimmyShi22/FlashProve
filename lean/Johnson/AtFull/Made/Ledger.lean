-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/Ledger.lean: THE LEDGER of the planner's second half: where each step of
`VerifiableInference.Desc.Key.madeAt` (Johnson/Desc/Key/Road.lean) returns, `madeAt` returns, and at
which value. Every step's return is a NAMED PREMISE, in the step's own terms, so that whoever shows
one part has its statement to the letter.

The premises' letters go by the step: a: the segments; b: the layout; c: the shapes and sizes; d:
the key file's and the copy's plans; e: the proof file's plans; f: the gates; g: the reads back; h:
the built segments; s: the sendings.
  `shapesOf_of_parts`: a₁ `linksOf`, a₂ `headLast`, a₃ `linksCount`, a₄ `declareLinks`;
    b₁ `Plan.layoutRead`, b₂ `Plan.reqFrame`; c₁ `shapesWith`.
  `madeOfParts`: the value that `Params.configure` returns, from its parts: its text.
  `configure_of_parts`: c₂ `Params.sized`; e₁ to e₃ and d₁ to d₄: the seven plans; f₁ to f₅: the
    five gates; f₆: the four small conditions.
  `chainsOf_of_parts`: hs `shapesOf`, c₂ `sized`, c₃ `linksFit`, hc `configure`; g₁ to g₃: the
    three reads back.
  `madeAt_of_parts`: hch `chainsOf`, a₁ `linksOf`, h₁ `buildLinksH`; s₁: `Johnson.G.sendsFrom`
    gives seven.

This is the KEY file's road (`Key.madeAt`: `linksOf X default`). The proof file's public part goes
by copies of these routines; what joins the two is `FlashProve.madeOf_of_madeAt`
(Johnson/AtFull/Top/OnePlanner.lean).

X, lay and cfg are letters: nothing is asked of them here.

Limits. A JOINING: each proof unfolds one definition and rewrites by the premises. IT PAYS NO
PREMISE: none of them is shown here. No soundness is claimed.
-/
import Johnson.Desc.Key.Road

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params

/-- **Where each of its seven steps returns (a₁ to a₄, b₁, b₂, c₁: premises), `shapesOf`
returns.** -/
theorem shapesOf_of_parts {X : Public} {lay : ByteArray} {links₀ links : Array LinkH}
    {declared : Array FrameLink} {file : Plan.LayoutLines} {reqLinks : List ReqLink}
    {layout : ReqLayout} {shapes : Shapes}
    (a₁ : linksOf X default = .ok links₀) (a₂ : headLast links₀ = .ok ())
    (a₃ : linksCount links₀ = .ok ())
    (a₄ : declareLinks links₀ X.NGr X.p4 = .ok (links, declared))
    (b₁ : Plan.layoutRead lay = some file)
    (b₂ : Plan.reqFrame declared file X.P.frame.answers = some (reqLinks, layout))
    (c₁ : shapesWith X reqLinks layout (links.toList.map (·.gid)) = .ok shapes) :
    shapesOf X (some lay) = .ok (links, shapes) := by
  unfold shapesOf
  simp only [a₁, a₂, a₃, a₄, b₁, b₂, c₁, Option.bind_some, bind, Except.bind, pure, Except.pure]

/-- The record that `Params.configure` returns, from its parts: the text of its last step. -/
def madeOfParts (l : Lines) (x : Shapes) (cfg : ByteArray) (z : Sized)
    (first shared second oneTime keyShared keySecond entry : Params.Planned) : Configured :=
  let lin := fun (codes : Codes) (S : LinShape) =>
    [("codes", spellCodes codes), ("the test on the table", spellLin S)]
  { sized := z, configuration := cfg, proof := [first, shared, second],
    key := [oneTime, keyShared, keySecond], entry := entry,
    keyOneTime := Fmt.paramsBytes oneTime.plan cfg (Plan.oneTimeItems z.key),
    keyShared := Fmt.paramsBytes keyShared.plan cfg (lin z.key.codes z.key.once.shape),
    keySecond := Fmt.paramsBytes keySecond.plan cfg [],
    entryLink := Fmt.paramsBytes entry.plan cfg
      [("codes", spellCodes z.entryCodes), ("the link", spellLink z.link.shape)],
    first := Fmt.paramsBytes first.plan cfg
      (lin z.proof.codes z.proof.batch.shape ++
       [("request's shape", spellReq z.proof.request), ("layout", spellLayout x.layout),
        ("links' identifiers", spellWords x.identifiers),
        ("pending rows", spellWord x.sub.pendingRows),
        ("binding tree", spellBinding ⟨Params.clog2 l.slots, z.set.saltBytes⟩)]),
    shared := Fmt.paramsBytes shared.plan cfg (lin z.proof.codes z.proof.batch.shape),
    second := Fmt.paramsBytes second.plan cfg [] }

/-- **Where `sized` and the seven plans return, the five gates let it pass and the four small
conditions hold (c₂, e₁ to e₃, d₁ to d₄, f₁ to f₆: premises), `Params.configure` returns**, at 0
requested bits. -/
theorem configure_of_parts {l : Lines} {x : Shapes} {cfg : ByteArray} {z : Sized}
    {first shared second oneTime keyShared keySecond entry : Params.Planned}
    (c₂ : sized l x = .ok z)
    (e₁ : firstPlan z.proof x.sub = .ok first)
    (e₂ : sharedPlan z.proof.set z.proof.codes z.proof.batch = .ok shared)
    (e₃ : secondPlan z.proof.set z.proof.batch = .ok second)
    (d₁ : Plan.oneTimePlan z.key = .ok oneTime)
    (d₂ : sharedPlan z.set z.key.codes z.key.once = .ok keyShared)
    (d₃ : secondPlan z.set z.key.once = .ok keySecond)
    (d₄ : finishHeld z.set .once (linkPlan z.link) = .ok entry)
    (f₁ : missedInTheLinks l z.proof x.sub first = .ok false)
    (f₂ : Plan.missedInTheRanges z.key = false)
    (f₃ : missedOnTheTable l ⟨z.proof.batch, z.proof.codes, shared, second, x.sub.pendingRows, 0⟩
        ⟨z.key.once, z.key.codes, keyShared, keySecond,
          if sumT (z.key.ranges.x.lookups.map (·.parts.length)) != 0 then
            sumT (z.key.ranges.x.lookups.map (·.parts.length)) else 1,
          sumT (z.key.ranges.x.lookups.map (·.parts.length))⟩
        z.link z.entryCodes entry = false)
    (f₄ : missedInTheChecks l x.rangeChecks z.key.once.shape.fold.columns
        z.link.shape.columnsFirst z.proof.batch.batches = false)
    (f₅ : Plan.keyOk z.key = true)
    (f₆ : (x.identifiers.length != z.proof.request.link.length ||
        z.proof.request.atStart.length != 1 || x.sub.pendingRows == 0 ||
        z.proof.request.link.map (·.plain) !=
          List.replicate (z.proof.request.link.length - 1) 0 ++ [1]) = false) :
    configure l x cfg 0 =
      .ok (madeOfParts l x cfg z first shared second oneTime keyShared keySecond entry) := by
  unfold configure proofPlans madeOfParts
  simp only [c₂, e₁, e₂, e₃, d₁, d₂, d₃, d₄, f₁, f₂, f₃, f₄, f₅, f₆, bind, Except.bind, pure,
    Except.pure, Bool.false_eq_true, if_false, Bool.not_true, Nat.not_lt_zero]

/-- **Where each of its seven steps returns (hs, c₂, c₃, hc, g₁ to g₃: premises), `chainsOf`
returns.** -/
theorem chainsOf_of_parts {X : Public} {lay cfg : ByteArray} {links : Array LinkH}
    {shapes : Shapes} {z : Sized} {made : Configured} {key : KeyChains} {link : Params.Link}
    {proof : ProofChains}
    (hs : shapesOf X (some lay) = .ok (links, shapes))
    (c₂ : sized X.P.frame shapes = .ok z)
    (c₃ : linksFit links z.proof.codes z.proof.request shapes.layout z.proof.batch.shape.kCol =
      .ok ())
    (hc : configure X.P.frame shapes cfg 0 = .ok made)
    (g₁ : KeyChains.read made.keyOneTime made.keyShared made.keySecond = some key)
    (g₂ : Params.Link.read made.entryLink = some link)
    (g₃ : ProofChains.read made.first made.shared made.second = some proof) :
    chainsOf X (some lay) cfg = .ok { made := made, key := key, link := link, proof := proof } := by
  unfold chainsOf
  simp only [hs, c₂, c₃, hc, g₁, g₂, g₃, bind, Except.bind, pure, Except.pure]

/-- **Where each of its four steps returns (hch, a₁, h₁, s₁: premises), `madeAt` returns.** -/
theorem madeAt_of_parts {X : Public} {lay cfg : ByteArray} {links₀ : Array LinkH}
    {chains : Chains} {built : LinksH} {k0 k1 k2 en p0 p1 p2 : Johnson.G.ChainSends}
    (hch : chainsOf X (some lay) cfg = .ok chains)
    (a₁ : linksOf X default = .ok links₀)
    (h₁ : buildLinksH links₀ X.NGr X.p4 X.layers.wsLay chains.proof.first = .ok built)
    (s₁ : Johnson.G.sendsFrom chains.made = .ok [k0, k1, k2, en, p0, p1, p2]) :
    VerifiableInference.Desc.Key.madeAt X lay cfg =
      .ok ⟨{ X := X, cfg := cfg, chains := chains, built := built }, (k0, k1, k2),
        (p0, p1, p2)⟩ := by
  unfold VerifiableInference.Desc.Key.madeAt builtOf
  simp only [hch, a₁, h₁, s₁, bind, Except.bind, pure, Except.pure]

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.shapesOf_of_parts
#print axioms Johnson.AtFull.Made.configure_of_parts
#print axioms Johnson.AtFull.Made.chainsOf_of_parts
#print axioms Johnson.AtFull.Made.madeAt_of_parts
