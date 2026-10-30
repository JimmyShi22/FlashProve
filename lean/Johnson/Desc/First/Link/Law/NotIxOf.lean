-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/NotIxOf.lean: BENEATH THE LINK's NAMED LIST: TWO OF ITS FIELDS ON
STATES, EACH TO THE LETTER, from what lies: notIx («in front of the one equation no message of the
link's own is the index masks' message») and, of the law's premise A, conds.hN («in front of the one
equation at most N oracle messages»; in LinkRest.lean: AhN). Theorems, evaluations.

What is said.
  `notIx_of`: **the field notIx** from: the facts along the fold at the list's own «reached»; an
    elder Bool on the written list (`idxFitE`, OwnBridge.lean: the promise asks the index's number
    there); the place's facts; and ONE TEST WITH CODE on the fold's data and the plan's numbers: no
    number of the link's own messages at that moment is the index masks' (`ownNotIndexB`). Calls of
    `ownNotIndex_reached` (FifthTieLow.lean) and of `index_of_promise`. `ahN_of`:
    **the field AhN** from the promise (`hN_of_onT`, FromPromise.lean) and one inequality on the
    plan's numbers: the number of messages at the place is at most N. `idxFitE_links`: the elder
    Bool at `P5J.fullLinks`, by the kernel. `piece_le_links`: at each of the 25 links the one
    equation's piece lies within the bound that the facts along the fold ask.

Limits. BOOK-KEEPING OVER THEOREMS THAT LAY. LEFT BY NAME: the facts along the fold (shown whole in
Johnson/P5J/MaskLettersAtMg.lean (`AtMgA.fold_full`), from the standing hypotheses (P5J.AtMgA),
which stay premises there, at the second hash function (OnBytes.secondHashFunction) alone, at that theorem's
own letters; nothing here ties the letters Rz, fd, reqW, links, pl of `notIx_of` to these);
the test `ownNotIndexB`; the inequality on N. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OwnBridge
import Johnson.Desc.First.Link.Law.FifthTieLow
import Johnson.Desc.First.Link.Law.FromPromise
import Johnson.Desc.First.Link.Law.K09Cond

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf FoldData FoldFacts momentAt shiftAt)

variable {F : Frame}
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (links : List ModelPart) (pl : List Place) (z : P)
  (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "onK" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz

/-- **THE FIELD notIx** (k: the one equation's border). -/
theorem notIx_of (p : Place) {fd : FoldData} {reqW : P → Array UInt32}
    (FF : FoldFacts Rz (fun a : S × F.E.Str => (z, a.1)) fd reqW links pl)
    (hidx : idxFitE moreAll links pl = true) (hp : pl[k]? = some p) (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 3) (hle : p.piece ≤ 11 + 2 * shiftAt links m)
    (T : ownNotIndexB fd m (momentAt (shiftAt links m) p.piece) 𝔇.pubD.N.indexNo = true) :
    ∀ a, onK k a → OwnNotIndex a.1 :=
  fun a ha => ownNotIndex_reached FF ha.2 (Classical.not_not.1 ha.1.2) hp hl hle
    (index_of_promise 𝔇 𝔇.N links pl z k m p hidx hp hl hpc a ha.1) T

/-- **THE FIELD AhN** (k: the one equation's border). -/
theorem ahN_of (N : ℕ) (hN : 𝔇.N.msgsAt pl[k]? ≤ N) :
    ∀ s, onK k s → ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ N :=
  fun s hs a ha => Nat.le_trans (hN_of_onT 𝔇.N (mgAll 𝔇 mgBase) links pl z k s hs.1 a ha) hN

set_option maxRecDepth 1000000 in
/-- An elder Bool on the written list, at P5J.fullLinks (Johnson/P5J/MeansQ.lean), by the kernel. -/
theorem idxFitE_links :
    idxFitE moreAll P5J.fullLinks (flatPlacesOf P5J.fullLinks true) = true := by
  decide +kernel

/-- The one equation's piece lies within the bound, at each of the 25 links. -/
theorem piece_le_links : ∀ m, m < 25 →
    hearN P5J.fullLinks m + 3 ≤ 11 + 2 * shiftAt P5J.fullLinks m := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.notIx_of
#print axioms VerifiableInference.Desc.LinkJoin.ahN_of
#print axioms VerifiableInference.Desc.LinkJoin.idxFitE_links
#print axioms VerifiableInference.Desc.LinkJoin.piece_le_links
