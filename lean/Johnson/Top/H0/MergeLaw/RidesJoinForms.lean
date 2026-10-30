-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RidesJoinForms.lean: THE MERGE's FIFTH TIE AT THE COMPOSED MEANING
`mgAll 𝔇 Mg`, AT THE WRITTEN LIST AT THE FULL SIZE, AT NUMBER 346: CUT DOWN FROM EIGHT ITEMS TO TWO.
A join: `t5_cut` (RidesJoin.lean) with its premise hRest paid at the six names of
"forms" by `six_forms_back` (FormsBackAtMerge.lean).

  worthAtMerge     the two that are left: worth 24 8 "planes", worth 24 8 "keys"
  rest_is          the eight of `restAtMerge` are the six names of "forms" and these two
  t5_cut_forms     **`merge_tiedAtR`'s premise t5** at Mg := mgAll 𝔇 Mg, links := linksFull, ps :=
                   flatPlacesOf linksFull true, k := 346: from `t5_cut`'s own premises with hRest
                   asked at the two alone; `Fwd` at each run under the six names; the six public
                   tests "formsIn" in front

Limits. `Fwd` (ten runs at the output head's sort: `six_are_ten`), the six public tests in front and
"each of the two goes back" are premises. Shown at no real state. No soundness statement.

-/
import Johnson.Top.H0.MergeLaw.RidesJoin
import Johnson.Top.H0.MergeLaw.FormsBackAtMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn Item Meaning Numbers start flatPlacesOf)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- The two that are left. -/
def worthAtMerge : List Item := [.worth 24 8 "planes", .worth 24 8 "keys"]

/-- The eight are the six names of "forms" and the two. -/
theorem rest_is : restAtMerge = sixForms ++ worthAtMerge := rfl

/-- **THE FIFTH TIE, CUT DOWN TO THE TWO.** -/
theorem t5_cut_forms {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    {Fr : Frame} (Nn : Numbers) (Pm : HeadMergeP) (base : ℕ) (ds : List RDT)
    (hF : ∀ t, t = 1 ∨ t = 2 → ∀ p ∈ Nn.sent 24 t, ∀ x ∈ 𝔇.ms, SitsAt x p.1 p.2 →
      Fenced base [x])
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      𝔇.smp (z, { s with rowsOwed := none, here := .head a' }) = 𝔇.smp (z, s))
    (z : P) (a b : S × Fr.E.Str) (w : Wit (CellsQ rows cols) Tok MsgT) (i : Item)
    (hy : ∃ rs, headMergeDecide Pm a.1 rs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ)
    (hrel : relQ Nn (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s))
      (346 + 1) b w)
    (hf : ∀ x ∈ sixNames, ∀ p ∈ 𝔇.runs 24 x.1 x.2, Fwd (𝔇.Rd 24) p.1 p.2 a.1 b.1)
    (hin : ∀ x ∈ sixNames, (mgAll 𝔇 Mg).pub (.formsIn 24 x.1 x.2) (z, a.1) = true)
    (hW : ∀ j ∈ worthAtMerge, meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) j b w →
      meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) j a w)
    (hi : openAfter (insQ linksFull (flatPlacesOf linksFull true))
      (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) 346 i)
    (hn : ¬ insQ linksFull (flatPlacesOf linksFull true) 346 i) :
    meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) i a w := by
  refine t5_cut 𝔇 Mg Nn Pm base ds hF hsmp z a b w i hy hb hrel (fun j hj => ?_) hi hn
  rw [rest_is] at hj
  rcases List.mem_append.1 hj with h6 | h2
  · exact six_forms_back 𝔇 Mg Nn Pm z a b w hy hf
      (fun x hx => formsTest_of_pub 𝔇 Mg 24 x.1 x.2 z a.1 (hin x hx)) j h6
  · exact hW j h2

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.rest_is
#print axioms VerifiableInference.Desc.First.MergeLaw.t5_cut_forms
