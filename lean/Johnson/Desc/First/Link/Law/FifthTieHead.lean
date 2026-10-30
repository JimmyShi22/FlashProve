-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FifthTieHead.lean: THE PREMISE `HeadOpen` OF `t5_quiet` (FifthTie.lean)
AND OF `t5_eq` (FifthTieEq.lean) AT K9's FOUR PLACES: paid, where 𝔇's parameter headPart is
`headPartK6`, by `headOpen_of` (HeadOpenOf.lean, over
`headPartK6_goesBack`). A joining: four short theorems.

What is said.
  `out_quiet9`: two states with `Quiet9` have one field out. `out_eq`: so have the states in front
of
    and behind an accepting step of the one equation's sub-protocol.
  `headOpen_quiet9`: **`HeadOpen 𝔇 Op (StepRel rel base In)` at every rel that gives `Quiet9`** (the
    batching; the frame's sub-protocol behind it; the shutting).
  `headOpen_eq`: **the same at the one equation.**

Limits. Three premises on the letters: 𝔇.headPart is `headPartK6` at them; its reader of the request
reads the public part alone; its reader of the token reads, beside the public part, the heard reply
alone (the state's field out.reply). Shown here of no 𝔇. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.FifthTieEq
import Johnson.Desc.First.Link.Law.HeadOpenOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item Numbers)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6)
open Johnson.Desc.First.Walk.Tied

theorem out_quiet9 {s t : S} (h : Quiet9 s t) : t.out = s.out := by
  obtain ⟨L₀, F₀, t₀, e⟩ := h
  exact congrArg (·.out) e

theorem out_eq {Cl : Type} (pw : Where) (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    {s t : S} (h : BlockYes b₃ s t) : t.out = s.out := by
  obtain ⟨ft, rs, cols, k, h⟩ := h
  obtain ⟨a0, out, ha0, _, hs'⟩ := oneEquation_inv atS pw _ _ _ _ _ k (hb₃ _ _ _ _ _ h)
  rw [hs']
  exact out_set s _

/-- The joining, at every relation on states that leaves the field out. -/
theorem headOpen_out {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ}
    {msR : List Mem} {N : Numbers} {sz : ℕ → Cb.Pv.Tail.Size}
    {seat : ∀ k, Fin (sz k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {pl : ℕ → ℕ × Bool × ℕ × ℕ} {tab : ℕ → ℕ}
    {put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq}
    {H : P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols}
    {tokH : P × S → Fin Inst.Model.ppref.V}
    (h𝔇 : 𝔇.headPart = headPartK6 cs arr msR N sz seat X pl tab put H tokH)
    (hreq : ∀ p s t, H.req (p, s) = H.req (p, t))
    (htok : ∀ p s t, t.out.reply = s.out.reply → tokH (p, s) = tokH (p, t))
    (Op : Item → Prop) (rel : S → S → Prop) (hrel : ∀ s t, rel s t → t.out = s.out) (base : ℕ)
    (In : P × S → Strs → Prop) : HeadOpen 𝔇 Op (StepRel rel base In) := by
  refine headOpen_of 𝔇 h𝔇 Op _ ?_ ?_
  · rintro ⟨p, s⟩ y ⟨p', t⟩ y' h
    obtain rfl : p' = p := h.1
    exact hreq p' s t
  · rintro ⟨p, s⟩ y ⟨p', t⟩ y' h
    obtain rfl : p' = p := h.1
    exact htok p' s t (by rw [hrel s t h.2.1])

/-- **AT THE THREE QUIET SUB-PROTOCOLS.** -/
theorem headOpen_quiet9 {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ}
    {msR : List Mem} {N : Numbers} {sz : ℕ → Cb.Pv.Tail.Size}
    {seat : ∀ k, Fin (sz k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {pl : ℕ → ℕ × Bool × ℕ × ℕ} {tab : ℕ → ℕ}
    {put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq}
    {H : P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols}
    {tokH : P × S → Fin Inst.Model.ppref.V}
    (h𝔇 : 𝔇.headPart = headPartK6 cs arr msR N sz seat X pl tab put H tokH)
    (hreq : ∀ p s t, H.req (p, s) = H.req (p, t))
    (htok : ∀ p s t, t.out.reply = s.out.reply → tokH (p, s) = tokH (p, t))
    (Op : Item → Prop) (rel : S → S → Prop) (hrel : ∀ s t, rel s t → Quiet9 s t) (base : ℕ)
    (In : P × S → Strs → Prop) : HeadOpen 𝔇 Op (StepRel rel base In) :=
  headOpen_out 𝔇 h𝔇 hreq htok Op rel (fun s t h => out_quiet9 (hrel s t h)) base In

/-- **AT THE ONE EQUATION.** -/
theorem headOpen_eq {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ}
    {msR : List Mem} {N : Numbers} {sz : ℕ → Cb.Pv.Tail.Size}
    {seat : ∀ k, Fin (sz k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {pl : ℕ → ℕ × Bool × ℕ × ℕ} {tab : ℕ → ℕ}
    {put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq}
    {H : P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols}
    {tokH : P × S → Fin Inst.Model.ppref.V}
    (h𝔇 : 𝔇.headPart = headPartK6 cs arr msR N sz seat X pl tab put H tokH)
    (hreq : ∀ p s t, H.req (p, s) = H.req (p, t))
    (htok : ∀ p s t, t.out.reply = s.out.reply → tokH (p, s) = tokH (p, t))
    (Op : Item → Prop) {Cl : Type} (pw : Where) (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (base : ℕ) (In : P × S → Strs → Prop) : HeadOpen 𝔇 Op (StepRel (BlockYes b₃) base In) :=
  headOpen_out 𝔇 h𝔇 hreq htok Op _ (fun _ _ h => out_eq pw b₃ hb₃ h) base In

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.headOpen_out
#print axioms VerifiableInference.Desc.LinkJoin.headOpen_quiet9
#print axioms VerifiableInference.Desc.LinkJoin.headOpen_eq
