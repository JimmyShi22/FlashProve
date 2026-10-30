-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09Core.lean: AT THE CLOSED CONSTANT: THE LIST OF THE FIELDS OF A LINK's REST
THAT NO CHOICE OF THE LETTERS LAYS IN (`CoreRest2`,
Johnson/Desc/First/Link/Law/LinkRestAtSort2.lean) FROM WHAT IS LEFT OF IT (`CoreLeft`,
CoreLeft.lean) WHEN THE PAYERS THAT LIE ARE LAID IN: twelve fields. General in the
link's sort and in the law's other letters. One theorem.

What is said.
  `coreRest2_at`: **`CoreRest2` at the constant's letters, at link m < 25, at every public part z,
    from `CoreLeft` there**, under: the tower's own three equations on the flat lists' heads; the
    facts along the fold at `At.foldD Zp cF Ld`; letters that sit at the link, with p the plan's
    own; the runs' share of the link (`LinkShare L p`: it comes off the sort's own fields); the
    row's piece at the batching's number; (xx, tlD) is what `digAt` answers at the link; THE LETTER
    N IS LAID AT THE NUMBER OF THE FOLD's MESSAGES (`(At.foldD Zp cF Ld).M.length`). LAID IN: Ahds,
    Ahbk (`ahds_ahbk_at`) and mh (`meantEx_at`, `headIs_at`): Johnson/LPFE1R/K9RestLight.lean; hN
    (by that choice); AhN (`ahN_of`, with `AtMg.msgs_le`, Johnson/P5T/MsgsLeAtMg.lean)
    and notIx (`notIx_of`): NotIxOf.lean, the latter with `AtMg.notIx`
    (Johnson/P5T/NotIxAtMg.lean: the test on the link's own messages' numbers, from the head (which
    stands with fourteen entry tests)); Ainside (`AtMgA.ainside`): InsideAtMg.lean; HD and hdig
    (`AtMgA.k9_dig`): Johnson/P5T/DigAtHead.lean, at set := the frame's setting and pp := the
    field's prime; tot (`tot_of`): TotOfPromise.lean; Ahs1 (`ahs1_at`): K09Ahs1.lean; hbook₂
    (`hbook2_of_share`): SortShare.lean.

Limits. BOOK-KEEPING: A JOIN OF THEOREMS THAT LAY: its worth is that Lean holds each payer against
the field's own type. `CoreLeft` (10 fields) and the facts along the fold (a premise here; the
caller has them from another file's theorem) ARE THE DEBT. AT THE SECOND HASH FUNCTION ALONE.
Nothing on soundness.

-/
import Johnson.P5J.K09Rest
import Johnson.P5J.InsideAtMg
import Johnson.P5T.DigAtHead
import Johnson.P5T.NotIxAtMg
import Johnson.P5T.MsgsLeAtMg
import Johnson.LPFE1R.K9RestLight
import Johnson.P5J.K09Ahs1
import Johnson.Desc.First.Link.Law.SortShare
import Johnson.Desc.First.Link.Law.CoreLeft
import Johnson.Desc.First.Link.Law.TotOfPromise
import Johnson.Desc.First.Link.Law.NotIxOf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Link claimsInBy)
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf FoldFacts momentAt shiftAt)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS Where)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.LinkJoin (batchAt atRec CoreLeft CoreRest2 coreRest2_of_left hearN
  ownNotIndexB mid_eq midFit_links tot_of totFitE_links notIx_of ahN_of idxFitE_links
  piece_le_links foldFacts_at LinkShare hbook2_of_share)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

local notation "FD" => F0T OnBytes.secondHashFunction Zp Np cF
local notation "kAt" => batchAt fullLinks At.ps
set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **THE ELDER LIST AT THE CONSTANT, FROM WHAT IS LEFT.** -/
theorem coreRest2_at {β : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (m : ℕ) (hm : m < 25) {L : _} {p : _} {Q : _} {b₃ b₅ : _} (St : h.Sits m L p Q b₃ b₅)
    (kp : IM.k9At Zp m = some p) (share : LinkShare L p)
    (qb : _) (hb : (h.toAtMg.row 𝔏)[kAt m]? = some qb) (xx : _) (tlD : _)
    (hdig : VerifiableInference.Desc.First.Look.digAt (At.X Zp) m = some (xx, tlD)) (sub : ModelPart)
    (u : _) (ψ : S → β) (Ok : _) (nU : _) (tmOf : _) (lenOf : _) (d : ℕ) (items : _) (o : _)
    (run : _)
    (z : ProofFile.InstPub)
    (H : CoreLeft (F := FrK) h.𝔇 fullLinks At.ps z
      (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m sub L u ψ Ok nU p tmOf
      lenOf d (At.foldD Zp cF Ld).M.length (atRec qb (below L.batchB)) items o run xx tlD
      (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
      (At.foldD Zp cF Ld)) :
    CoreRest2 (F := FrK) h.𝔇 fullLinks At.ps z
      (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m sub L u ψ Ok nU p tmOf
      lenOf d (At.foldD Zp cF Ld).M.length (atRec qb (below L.batchB)) items o run xx tlD
      (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
      (At.foldD Zp cF Ld) := by
  obtain ⟨L', p', Q', hlk', hp', _, hs⟩ := LPFK9.sits_at_constant h.toAtMg m hm
  obtain rfl : L' = L := Option.some.inj (hlk'.symm.trans St.lk)
  obtain rfl : p' = p := Option.some.inj (hp'.symm.trans kp)
  obtain ⟨pE, pE1, hpE, hpE1, hlE, hpcE⟩ := mid_eq fullLinks At.ps midFit_links m hm
  obtain ⟨y, tl', hd', HD⟩ := h.k9_dig m hm h.𝔇.l3.rad
  obtain ⟨rfl, rfl⟩ : y = xx ∧ tl' = tlD := Prod.mk.inj (Option.some.inj (hd'.symm.trans hdig))
  have ad := ahds_ahbk_at h 𝔏 q₁ q₂ q₃ m hm hs qb hb (below L'.batchB)
  exact coreRest2_of_left h.𝔇 fullLinks At.ps z _ (kAt m) m sub L' u ψ Ok nU p' tmOf lenOf d _ _
    items o run y tl' _ _ _ _ ad.1 ad.2 (ahs1_at h m hm St share z)
    (ahN_of h.𝔇 fullLinks At.ps z _ (kAt m + 1 + 1) _ (h.toAtMg.msgs_le Ld _))
    (h.ainside Ld Fo z (kAt m)) (hbook2_of_share share) HD hdig (Nat.le_refl _)
    (tot_of h.𝔇 fullLinks At.ps z _ (kAt m + 1 + 1) m pE totFitE_links hpE hlE hpcE)
    ⟨meantEx_at h, headIs_at h⟩
    (notIx_of h.𝔇 fullLinks At.ps z _ (kAt m + 1 + 1) m pE (foldFacts_at Fo z) idxFitE_links hpE
      hlE hpcE (by rw [hpcE]; exact piece_le_links m hm) (h.toAtMg.notIx Ld hm _))
    H

end P5J

#print axioms P5J.coreRest2_at
