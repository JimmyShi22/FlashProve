-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorAtTexts.lean: SH₃ (the premise on `PL.shape 0` of the joint between the
shared and the last chain: `OnZero₃OfEnd₂`, Johnson/Desc/Sound/BordersLastQ.lean) STATED WITH TEXTS
IN THE PLACE OF ITS TWO LETTERS, AND PROVED UNDER SIX NAMED PREMISES. Statements and proofs; no
definition. THE SIX ARE PAID NOWHERE.

Main names (namespace `VerifiableInference.Desc.Last`).
  `doorFirstL_eq`, `doorSharedL_eq` (by the make): the texts' lists
    (Johnson/Desc/Last/DoorTexts.lean) are `firstSixClauses` and `sharedDoorClauses`
    (ShapeDoorLess.lean, ShapeDoor.lean). `firstSix_of_text`, `sharedDoor_of_text`: what a yes of a
    text gives where something is handed, or the chain has ended.
  **`sh₃_at_texts`**: at PLm := `fillZ p R fun q => (get q).2` and Oc := `ocEnd get N₁ Mg₁ links ps`
    (the first chain's whole last promise: Johnson/Desc/Sound/TieEnd.lean): inside `onQ₂ N Pm Oc
    split T.p₂ T.l₂ (1 + T.l₂.length)` the start's yes gives `PLm.shape 0`. ITS SIX PREMISES: hPm:
    `Pm.shape` at the last border bears `doorSharedB p` · hitem: `Mg₁.pub` at "K13.doorFirst" is
    `doorFirstB` (at `fillDoor`: by the make) · hopen: that item is open at the first chain's last
    border (a test on the table) · hmark: the start's yes gives "no mark" at the first chain's last
    record · hstart: the start's yes is a yes of `startAtEnds p` at K14's end · ahead:
    `p.S.masksAhead = true`.

Every "there is": e in hstart: tied by `ended d = some e`.
WHO COULD PAY, BY KIND (others' words; nothing of it is held here). hPm: whoever fills the shared
table's `shape` lays `doorX p K` beside it; then every block of that chain owes it at K alone: the
last block earns it, from what rides in front (in order; the book fits; Omega's place, shape and
sample row). hitem: `fillDoor_door`. hopen: an evaluation of the table's open sets at the real
lists, or a law on `More.merge`. hmark, hstart: the seated description's own text of the start (it
tests `First.S.fin`, goes by `ended`, then by the second seat's start). ahead:
`masksAhead_of_linSized` at what the planner has sized.
Limits. (1) A REDUCTION: six premises; a start₃ that never says yes pays hmark and hstart for
nothing. (2) NO MEMBER. (3) Those of DoorTexts.lean and ShapeAt.lean. (4) N, split, T, R are
letters; the last border is written as the table writes it. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorAtTable
import Johnson.Desc.Last.ShapeDoorLess
import Johnson.Desc.First.FillDoor
import Johnson.Desc.Sound.TieEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Last
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.First (Meaning Numbers ModelPart moreItem nDoor pubSets)
open _root_.Desc.K14 (St)

/-! ## 1 The two texts are the door's own tests -/

/-- The six of the text are `firstSixClauses`. -/
theorem doorFirstL_eq (f : FirstEnd₃) : doorFirstL f = firstSixClauses f := rfl

/-- The five of the text are `sharedDoorClauses`. -/
theorem doorSharedL_eq (p : P₁₄) (o : SharedOut) : doorSharedL p o = sharedDoorClauses p o := rfl

theorem firstSix_of_text {s : First.S} {f : FirstEnd₃} (h : doorFirstB s = true)
    (hf : firstOfS s = some f) : firstSixB f = true := by
  unfold doorFirstB at h
  rw [hf] at h
  exact h

theorem sharedDoor_of_text {p : P₁₄} {d : St} {e : OnBytes.Proof.SharedEnd}
    (h : doorSharedB p d = true) (he : _root_.Desc.K14.ended d = some e) :
    sharedDoorB p (sharedOfEnd e) = true := by
  unfold doorSharedB at h
  rw [he] at h
  exact h

/-! ## 2 SH₃ at the two texts -/

/-- **SH₃ AT THE TWO TEXTS, UNDER SIX PREMISES.** PLm := `fillZ p R fun q => (get q).2`; Oc := the
first chain's whole last promise (`ocEnd`). hPm: the shared table's `shape` at its last border bears
`doorSharedB p`. hitem, hopen: the first table's named item "K13.doorFirst" is `doorFirstB`, and is
open at that chain's last border. hmark: the start's yes gives "no mark" at the first chain's last
record. hstart: the start's yes is a yes of `startAtEnds p` at K14's end. ahead: the plan's shape
sends the masks ahead. -/
theorem sh₃_at_texts {C : CK} {D : WholeD} {all : List LeftT} {Y P S₁ P₀ X₁ X₂ Cl Wt W₁ : Type}
    (p : P₁₄) (R : List Fmt.DeclaredRound) (get : P × S₁ → P₀ × First.S)
    (start₃ : P → S₁ → St → Option S₃)
    (T : Three C D all Y (P × S₁) ((P × S₁) × St) ((P × S₁ × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm : PromMeaning St) (split : Bool)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W₁) (links : List ModelPart) (ps : List Place)
    (hPm : ∀ d, Pm.shape (1 + T.l₂.length) d = true → doorSharedB p d = true)
    (hitem : ∀ a, Mg₁.pub (moreItem nDoor) a = doorFirstB a.2)
    (hopen : moreItem nDoor ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hmark : ∀ q s₁ d s, start₃ q s₁ d = some s → (get (q, s₁)).2.failed = none)
    (hstart : ∀ q s₁ d s, start₃ q s₁ d = some s →
      ∃ e, _root_.Desc.K14.ended d = some e ∧ startAtEnds p q (get (q, s₁)).2 e = .ok s)
    (ahead : p.S.masksAhead = true)
    (b : ((P × S₁) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N Pm (ocEnd get N₁ Mg₁ links ps) split T.p₂ T.l₂ (1 + T.l₂.length) b)
    (hs : start₃ b.1.1.1 b.1.1.2 b.1.2 = some s) :
    (fillZ p R fun q => (get q).2).shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true := by
  refine door_fillZ_less (On₂ := onQ₂ N Pm (ocEnd get N₁ Mg₁ links ps) split T.p₂ T.l₂
    (1 + T.l₂.length)) (start₃ := start₃) ⟨?_, ?_, hstart, ahead⟩ b s hb hs
  · intro b s hb hs f hf
    have hm : (get b.1.1).2.failed = none := hmark b.1.1.1 b.1.1.2 b.1.2 s hs
    have h1 := ocEnd_pub get N₁ Mg₁ links ps b.1.1 _ hb.2 hm (moreItem nDoor) hopen
    rw [hitem] at h1
    exact firstSix_of_text h1 hf
  · intro b s hb _ e he
    have hmem : PromS.shape (1 + T.l₂.length) ∈ promsAt split (1 + T.l₂.length) := by
      unfold promsAt
      simp
    exact sharedDoor_of_text (hPm _ (hb.1 _ hmem)) he

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.doorFirstL_eq
#print axioms VerifiableInference.Desc.Last.doorSharedL_eq
#print axioms VerifiableInference.Desc.Last.firstSix_of_text
#print axioms VerifiableInference.Desc.Last.sharedDoor_of_text
#print axioms VerifiableInference.Desc.Last.sh₃_at_texts
