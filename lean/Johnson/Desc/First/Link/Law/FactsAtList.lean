-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FactsAtList.lean: TWO PREMISES OF A LINK's TIES, IN THEIR VERY FORM AT
THE TABLE's OWN CONDITION (`onTR`), FROM ONE FIELD: ANOTHER FILE's LIST OF FACTS ON REACHED STATES
(`FoldFacts`, Johnson/Desc/First/FoldFacts.lean) AT THE CONDITION's OWN SECOND CONJUNCT. Theorems.

What is said. FF : FoldFacts Rz (fun a => (z, a.1)) d reqW links pl: the list, at Rch := the letter
Rz of the condition and at_ := "the public part z with the statement's state".
  `full_of_facts`: **"full"**: at every state that meets the condition at border k, a border in
    front of a sub-protocol of segment m at a piece from 7 + shift to 11 + 2 shift: the frame of the
    open link's check is full (FrameFull, TieFronts.lean): frameFull_of_facts (FrameFullOf.lean).
  `link_of_atS`: the part that kind K9's lens reads holds the state's open link.
  `grp_of_facts`: **"hg"** (t3_eq_front | t3_eq_rows): at every state that meets the condition at
    border k, in front of a sub-protocol of segment m: the group that the link's check names is the
    plan's: the list's field groupIs, where the list's number is the table's (hgr).

Limits. PREMISES: FF itself · closed: hp · hl · h7 · h11 · hall ·
hgr (d.groupAt m = 𝔇.N.groupAt m). Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FrameFullOf
import Johnson.Desc.First.Link.Law.TieThreeFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS segAt?)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning FoldFacts FoldData shiftAt)

/-- The part that kind K9's lens reads holds the state's open link. -/
theorem link_of_atS (s : S) (x : K9.Part) (h : atS.get? s = some x) : s.link? = some x.L :=
  link_of_seg s x (K9.segAt_of_atS s x h)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz

/-- **"full", IN ITS VERY FORM.** -/
theorem full_of_facts {d : FoldData} {reqW : P → Array UInt32}
    (FF : FoldFacts Rz (fun a : S × F.E.Str => (z, a.1)) d reqW links pl) (p : Place)
    (hp : pl[k]? = some p) (hl : p.link = some m) (h7 : 7 + shiftAt links m ≤ p.piece)
    (h11 : p.piece ≤ 11 + 2 * shiftAt links m)
    (hall : ∀ ms, (d.sent.shape.link[m]?).map (·.messages) = some ms →
      ms.length ≤ (d.ownAt m 3).size) :
    ∀ a, onK k a → ∀ x, segAt? a.1 = some x → FrameFull x.L.check.frame :=
  fun a ha x hx => frameFull_of_facts FF k a p m x ha.2 (Classical.not_not.1 ha.1.2) hp hl hx h7
    h11 hall

/-- **"hg", IN ITS VERY FORM.** -/
theorem grp_of_facts {d : FoldData} {reqW : P → Array UInt32}
    (FF : FoldFacts Rz (fun a : S × F.E.Str => (z, a.1)) d reqW links pl) (p : Place)
    (hp : pl[k]? = some p) (hl : p.link = some m) (hgr : d.groupAt m = 𝔇.N.groupAt m) :
    ∀ a, onK k a → ∀ x, atS.get? a.1 = some x → x.L.check.group = 𝔇.N.groupAt m :=
  fun a ha x hx => ((FF.groupIs k a p m x.L ha.2 (Classical.not_not.1 ha.1.2) hp hl
    (link_of_atS a.1 x hx)).1).trans hgr

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.full_of_facts
#print axioms VerifiableInference.Desc.LinkJoin.grp_of_facts
