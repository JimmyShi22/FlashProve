-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/PlainRoads.lean: roads from a law without an extractor to the form that the table
of joints asks of a block. Six theorems. Rules over letters: no block of any
description occurs.

What these rules do not do. THEY MEET NOTHING: each moves a debt into a named premise. At a
proximity test, (agree) and the second premise of `goodIn_of_leads` are the step from "a witness
within the radius at which the sample's rows hold" to "what the committed word decodes to with its
sample": shown by nobody. At `Agree := fun _ _ => True` (agree) is free and (cong) says that the
closed items read nothing of the witness. A law at a condition that holds of nothing, or of a block
that refuses all, passes through every rule here, true and empty. No member is shown. No soundness
of any verifier follows from this file.

Why. The ties of the chain of promises (`TiedAt`, Johnson/Desc/Sound/ChainOfPromises.lean) take a
kind's law as `Piece.GoodIn`. Several kinds have their law in the plain form (`Reduction.Leads`,
Johnson/Desc/Plain/Leads.lean), which names no witness. The way back that the library has,
`OwnOfPlain` (Johnson/Desc/Sound/SpinePlain.lean), asks that the block's extractor is the identity
and that the row's context pins what the row closes. By an evaluation of the table's own functions
12 of the 78 rows of the small list's first chain, and 52 of the 358 of the full one, lay a
component of the witness; each of the twelve has an empty context.

What is said.
  `plain_iff_keeps`: `Piece.Plain` is `Reduction.Keeps` of the piece's reduction at its errors.
  `leads_withExt`: a law in the plain form does not read the extractor: it holds of the same piece
    with any other (`{ p with ext := e }`).
  `goodIn_of_leads`: from `Leads` to `GoodIn`, at whatever extractor, under two premises that hold
    for certain: what the law's relation says gives the promise behind; and, with a witness behind,
    it gives the relation in front at the extractor's value.
  `own_of_plain_lays`: `OwnOfPlain` with its four premises on the context and the identity replaced
    by one: (agree) where the block says yes, the extractor's value agrees with EVERY witness of
    what the row closes.
  `ownOfPlain_again`: the library's `OwnOfPlain`, to the letter, from `own_of_plain_lays`: so the
    new rule is at least as wide.
  `frames_of_free`: items of a set `free` that go back over a yes of the block (they read nothing
    that the block turns), and that the extractor leaves, ride; only the others are owed one by one.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.SpinePlain
import Johnson.Desc.Plain.Leads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)

variable {S Cl W ι : Type} {C : CK} {F : Frame}

/-- The plain law of a piece is the plain form's "keeps" of its reduction, at its errors. -/
theorem plain_iff_keeps (p : Piece C F S Cl W) (on on' T T' : S × F.E.Str → Prop) :
    p.Plain on on' T T' ↔ p.ior.red.Keeps on on' T T' p.err := Iff.rfl

/-- A law in the plain form does not read the extractor. -/
theorem leads_withExt (p : Piece C F S Cl W) (e : S × F.E.Str → Iop.Tr (uLT C p.ds) → W → W)
    (on : S × F.E.Str → Prop) (Q : S × F.E.Str → S × F.E.Str → Prop)
    (h : p.ior.red.Leads on Q p.err) :
    ({ p with ext := e } : Piece C F S Cl W).ior.red.Leads on Q p.err := h

/-- **From the plain form to the form with a witness, at whatever extractor.** -/
theorem goodIn_of_leads (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (Q : S × F.E.Str → S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (h : p.ior.red.Leads on Q p.err)
    (hon : ∀ a τ b, on a → p.ior.red.out a τ = some b → Q a b → on' b)
    (hR : ∀ a τ b w, on a → p.ior.red.out a τ = some b → Q a b → R' b w → R a (p.ext a τ w)) :
    p.GoodIn on on' R R' := fun a ha =>
  Doomed.mono _ _
    (fun τ hτ b hb => ⟨hon a τ b ha hb (hτ b hb), fun w hw => hR a τ b w ha hb (hτ b hb) hw⟩)
    (h a ha)

/-- **The way back for a row that lays.** Agree: two witnesses agree on what the closed items read.
-/
theorem own_of_plain_lays (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ι → Prop) (Agree : W → W → Prop)
    (cong : ∀ i, In i → ∀ a w w', Agree w w' → means i a w' → means i a w)
    (agree : ∀ a τ b w w₀, on a → p.ior.red.out a τ = some b → on' b → relAt means Out b w →
      relAt means In a w₀ → Agree (p.ext a τ w) w₀)
    (h : p.Plain on on' (shadow (relAt means In)) (shadow (relAt means Out))) :
    p.Own on on' means In Out := by
  intro a ha
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b hb
  obtain ⟨hon, hT⟩ := hτ b hb
  refine ⟨hon, fun w hw i hi => ?_⟩
  obtain ⟨w₀, hw₀⟩ := hT ⟨w, hw⟩
  exact cong i hi a _ _ (agree a τ b w w₀ ha hb hon hw hw₀) (hw₀ i hi)

/-- The library's rule, to the letter, from the wider one. -/
theorem ownOfPlain_again : OwnOfPlain := by
  intro S Cl W ι C F p on on' means In Out Ctx Agree hIn hOut pins cong back hid h
  refine own_of_plain_lays p on on' means In Out Agree cong ?_ h
  intro a τ b w w₀ ha hb hon hw hw₀
  rw [hid a τ w]
  exact pins a w w₀ ha (fun i hi => back a τ b w i ha hb hon hi (hw i (hOut i hi)))
    fun i hi => hw₀ i (hIn i hi)

/-- **Items that go back over a yes of the block, and that the extractor leaves, ride.** The first
premise is asked at the two statements of one yes alone, inside the two promises; the second inside
the promise in front. -/
theorem frames_of_free (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (O In free : ι → Prop)
    (hf : ∀ i, free i → ∀ a τ b w, on a → p.ior.red.out a τ = some b → on' b → means i b w →
      means i a w)
    (he : ∀ i, free i → ∀ a τ w, on a → means i a w → means i a (p.ext a τ w))
    (rest : p.Frames on on' means (fun i => O i ∧ ¬ free i) In) :
    p.Frames on on' means O In := by
  intro a τ b w i ha hb hon hO hIn hm
  by_cases hfi : free i
  · exact he i hfi a τ w ha (hf i hfi a τ b w ha hb hon hm)
  · exact rest a τ b w i ha hb hon ⟨hO, hfi⟩ hIn hm

end VerifiableInference.Desc.Sound
