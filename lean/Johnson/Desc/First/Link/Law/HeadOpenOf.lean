-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HeadOpenOf.lean: HeadOpen (Johnson/Top/H0/Walk/FrameItemsOpen.lean) FROM
headPartK6_goesBack (Johnson/Desc/Kinds/Law/HeadPartsGoBack.lean): ONCE, GENERAL IN THE
STRUCTURE OF LETTERS 𝔇, IN THE SET Op OF OPEN ITEMS AND IN THE RELATION R. One theorem with its
proof.

  headOpen_of      𝔇.headPart is headPartK6 at some letters · over R the request's reader H.req and
                   the heard token's reader tokH answer alike ⊢ HeadOpen 𝔇 Op R

For whom. K10's place (Johnson/LPFE1R/K10HeadOpenAt.lean has it at the closed constant and K10's own
relation, typed before this file); K9's four places (t5_quiet | t5_eq, in files beside this one).

Limits. The three premises are the caller's. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameItemsOpen
import Johnson.Desc.Kinds.Law.HeadPartsGoBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes.Maker
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item Numbers)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6 headPartK6_goesBack)
open Johnson.Desc.First.Walk.Tied (HeadOpen)

/-- **HeadOpen, from headPartK6_goesBack (Johnson/Desc/Kinds/Law/HeadPartsGoBack.lean).** -/
theorem headOpen_of {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ}
    {msR : List Mem} {N : Numbers} {s : ℕ → Cb.Pv.Tail.Size}
    {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {pl : ℕ → ℕ × Bool × ℕ × ℕ} {tab : ℕ → ℕ}
    {put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq}
    {H : P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols}
    {tokH : P × S → Fin Inst.Model.ppref.V}
    (h𝔇 : 𝔇.headPart = headPartK6 cs arr msR N s seat X pl tab put H tokH)
    (Op : Item → Prop) (R : P × S → Strs → P × S → Strs → Prop)
    (hreq : ∀ a y b y', R a y b y' → H.req a = H.req b)
    (htok : ∀ a y b y', R a y b y' → tokH a = tokH b) : HeadOpen 𝔇 Op R := by
  intro p _ i
  rw [h𝔇]
  exact headPartK6_goesBack cs arr msR N s seat X pl tab put H tokH R hreq p (fun _ => htok) i

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.headOpen_of
