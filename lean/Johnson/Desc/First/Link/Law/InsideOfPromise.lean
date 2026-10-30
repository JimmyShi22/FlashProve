-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/InsideOfPromise.lean (kind K9): `InsideAt` AT EVERY STATE WITH THE TABLE's PROMISE, «NO MARK» AND «REACHED» AT ONE BORDER: IN THE FORM OF THE FIELDS inTot · inSeg · inRun OF A LINK's «REST» (`CoreLeft`, CoreLeft.lean). Theorems: calls of InsideAtTied.lean and InRunOfKeeps.lean (beside this file).

Why. `insideAt_tied` (InsideAtTied.lean) takes the promise's two Bools (bookAt · shapeAt), «reached» and «no mark» one by one, at a statement of the facts' own type. The fields speak of `onTR` at a public part z. Here the one is drawn out of the other.

What is said. FF : FoldFacts Rch (fun a => a.1) fd reqW links pl; the border k has the place p of segment m, p.piece ≤ 11 + 2 · shift; nsOf m = (ns, ns); SlotsInv nsOf at every state reached at k; PlanFits … ns.
  `bools_of_onTR`: the promise with «no mark» gives shapeAt and bookAt.
  `inTot_of_promise`: **∀ b, onTR … k b → ∀ a, atS.get? b.1 = some a → InsideAt fd.sent.codes ms (Nm.group m) a: inTot's FORM (and the premise hin of `inRun_of_keeps`).**
  `inSeg_of_promise`: the same at `segAt?`, where kind K9's lens gives a part at that border.
  `inRun_of_promise`: with «every run behind the batching keeps insF»: **inRun's FORM.**

Limits. IMPLICATIONS. FoldFacts · SlotsInv at «reached» · nsOf m = (ns, ns) · PlanFits · «a part is there» are premises. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.InsideAtTied
import Johnson.Desc.First.Link.Law.InRunOfKeeps
import Johnson.Desc.First.Link.Law.LinkTiedPubR
import Johnson.Desc.First.Batch.FormsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS segAt? segAt_of_atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers FoldFacts FoldData momentAt shiftAt
  bookAt shapeAt)

variable {F : Frame} {P W : Type}

/-- The promise with «no mark» gives the two Bools. -/
theorem bools_of_onTR {Nm : Numbers} {Mg : Meaning P W} {links : List ModelPart} {pl : List Place}
    {z : P} {Rz : ℕ → S × F.E.Str → Prop} {k : ℕ} {b : S × F.E.Str}
    (h : onTR Nm Mg links pl (fun s : S => (z, s)) Rz k b) :
    b.1.failed = none ∧ shapeAt links pl[k]? b.1 = true ∧ bookAt Nm pl[k]? b.1 = true ∧ Rz k b := by
  obtain ⟨⟨hq, hm⟩, hr⟩ := h
  have hu : b.1.failed = none := Classical.not_not.1 hm
  rcases hq.2 with hf | ⟨hB, -, -, -⟩
  · exact absurd hf hm
  · simp only [Bool.and_eq_true] at hB
    exact ⟨hu, hB.1.1.1.1.1, hB.2, hr⟩

section
variable {Rch : ℕ → (P × S) × F.E.Str → Prop} {fd : FoldData} {reqW : P → Array UInt32}
  {links : List ModelPart} {pl : List Place} (FF : FoldFacts Rch (fun a => a.1) fd reqW links pl)
  (Nm : Numbers) (Mg : Meaning P W) (ms : List Mem) (nsOf : ℕ → ℕ × ℕ) (z : P) {k : ℕ} {p : Place}
  {m ns : ℕ} (hp : pl[k]? = some p) (hl : p.link = some m)
  (hpc : p.piece ≤ 11 + 2 * shiftAt links m)
  (hSl : ∀ b : S × F.E.Str, Rch k ((z, b.1), b.2) → SlotsInv nsOf b.1) (hn : nsOf m = (ns, ns))
  (T : PlanFits fd ms (Nm.group m) m (momentAt (shiftAt links m) p.piece) (Nm.msgsAt pl[k]?) ns)
include FF hp hl hpc hSl hn T

/-- **inTot's FORM.** -/
theorem inTot_of_promise :
    ∀ b : S × F.E.Str, onTR Nm Mg links pl (fun s : S => (z, s)) (RchAt Rch z) k b →
      ∀ a, atS.get? b.1 = some a → InsideAt fd.sent.codes ms (Nm.group m) a := by
  intro b hb a ha
  obtain ⟨hu, hSh, hB, hr⟩ := bools_of_onTR hb
  exact insideAt_tied FF Nm ms (Nm.group m) nsOf (a := ((z, b.1), b.2)) hr hu hp hl hpc ha hB hSh
    (hSl b hr) hn T

/-- **inSeg's FORM**, where kind K9's lens gives a part at that border. -/
theorem inSeg_of_promise
    (hs : ∀ b : S × F.E.Str, onTR Nm Mg links pl (fun s : S => (z, s)) (RchAt Rch z) k b →
      (atS.get? b.1).isSome = true) :
    ∀ b : S × F.E.Str, onTR Nm Mg links pl (fun s : S => (z, s)) (RchAt Rch z) k b →
      ∀ x, segAt? b.1 = some x → InsideAt fd.sent.codes ms (Nm.group m) x := by
  intro b hb x hx
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (hs b hb)
  obtain rfl : a = x := Option.some.inj ((segAt_of_atS b.1 a ha).symm.trans hx)
  exact inTot_of_promise FF Nm Mg ms nsOf z hp hl hpc hSl hn T b hb a ha

/-- **inRun's FORM.** -/
theorem inRun_of_promise (L : Link S Claim)
    (hq : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      insF e₁ = insF e)
    (hs : ∀ b : S × F.E.Str, onTR Nm Mg links pl (fun s : S => (z, s)) (RchAt Rch z) k b →
      (atS.get? b.1).isSome = true) :
    ∀ b : S × F.E.Str, onTR Nm Mg links pl (fun s : S => (z, s)) (RchAt Rch z) k b →
      ∀ s' a, L.runBehind b.1 = .ok s' → atS.get? s' = some a →
        InsideAt fd.sent.codes ms (Nm.group m) a :=
  inRun_of_keeps fd.sent.codes ms (Nm.group m) L hq _ hs
    (inTot_of_promise FF Nm Mg ms nsOf z hp hl hpc hSl hn T)

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.bools_of_onTR
#print axioms VerifiableInference.Desc.LinkJoin.inTot_of_promise
#print axioms VerifiableInference.Desc.LinkJoin.inSeg_of_promise
#print axioms VerifiableInference.Desc.LinkJoin.inRun_of_promise
