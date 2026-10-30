-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsObjInFits.lean: the lookup on the digits of a segment's approximate
range proof: TWO JOINS FOR THE ONE NEW PUBLIC TEST formsIn l (7 + shift sub) "objects": (1) IT
CROSSES THE STEP WITHOUT A ROUND: «no heard row names the slot of the merge's end value» (hmerge, in
the text of objects_formsIn, Johnson/Top/H/Keep/FormsInObjects.lean) AT THE STATE BEHIND THE WHOLE
SEATED SUB-PROTOCOL (K3's own rounds AND THEN the step without a round), where
Johnson/Top/H/Keep/MergeApart.lean has it behind the lookup's own rounds alone; (2) so the item's
test itself (objIn_dig, MgAt/K3DigitsObjIn.lean) with hmerge struck for one test on the state in
front. Joinings. NO RESULT ON THE PROTOCOL.

Main names.
  k3_digits_step_hmerge: from an .ok of the seated sub-protocol's decide, the ledger in front with
    its sizes, and sFvFitsB s = true (the merge's slot lies below the ledger's next slot:
    Johnson/Desc/First/Look/MergeSlotFits.lean): hmerge at s₂. The step without a round leaves the
    merge's slot (K3Pass.merge of quietAt_pass) and what was heard (quietAt_tlFuns).
  objIn_dig_fits: (mgAll Dm Mg).pub (.formsIn l k "objects") (z, s₂) = true.
WHAT IS LEFT. ON THE STATE IN FRONT: hfits (sFvFitsB s: no public item says it; a fact along the
fold, shown by nobody at every place) (Where this
and lean/THEOREM.md differ, the page holds.) · hF, hS. AT THE STATE BEHIND, WITH A FACT ALONG THE
FOLD: hmask. TERMS OF Dm: as in objIn_dig.
OBJECT. Desc.K3.theStated's value at the digits' address; the composed public test at formsIn.
USER. objIn_dig_fits: hForms_dig_mgAll (MgAt/K3DigitsFormsJoin.lean). Meant: hForms at the new item.
LETTERS. Those of MgAt/K3DigitsObjIn.lean.


Compiled with the whole library.


Limits. At Cl := Desc.Claim for the second.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.MergeApart
import Johnson.Desc.Sound.MgAt.K3DigitsObjIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub Meaning runsOf)
open VerifiableInference.Desc.K9 (segAt? readersOfLink statesOfLink LinkHoles maskSeat mergeOf)

/-- **hmerge BEHIND THE WHOLE SEATED SUB-PROTOCOL.** -/
theorem k3_digits_step_hmerge {Cl : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) (hfits : Desc.K3.sFvFitsB s = true) :
    ∀ g, (Desc.K3.seatDigits claim).heard s₂ = some g →
      ∀ f ∈ g.rows.toList, ∀ x ∈ f.slots.toList, mergeOf s₂ ≠ some x.1 := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  have H0 := k3_digits_hmerge claim a.piece laid sent P' [] s s' _ gs' hyes hF hS hfits
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact H0
  · obtain ⟨G0, Q0⟩ := k3_digits_pass claim a.piece laid sent P' [] s s' _ gs' hyes hF hS
    obtain ⟨G₂, Q₂⟩ := quietAt_pass X i f hf s' s₂ hfs Q0.behind Q0.sizedG
    obtain ⟨et, -⟩ := quietAt_tlFuns X i f hf s' s₂ hfs
    intro g hg
    have hg' : (Desc.K3.seatDigits claim).heard s' = some g := by
      have h1 : s₂.tl?.bind (·.heard) = some g := hg
      rw [et] at h1
      exact h1
    rw [Q₂.merge]
    exact H0 g hg'

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **THE NEW ITEM, hmerge PAID.** -/
theorem objIn_dig_fits (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Desc.Claim)
    (claim : Aff → Desc.Claim)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hlinks : Dm.links = linksFull) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    (hRd : Dm.Rd l = readersOfLink H lk) (hA : AtS2 (Desc.K3.seatDigits claim))
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) {k B₀ : ℕ}
    (he : runsOf sub k "objects" = [(B₀, "objects"), (B₀, "guests")])
    (pass : Desc.First.S → Desc.First.S → Prop) (hpass : ∀ t G, pass t (t.putFork G))
    (hsame : ∀ t, pass t t)
    (hfO : ∃ n r, (statesOfLink lk B₀).find? (fun x => x.1 == "objects") = some (n, r) ∧
      RunOver pass r (objectsRun (Desc.K3.seatDigits claim)))
    (hfG : ∃ n r, (statesOfLink lk B₀).find? (fun x => x.1 == "guests") = some (n, r) ∧
      RunOver pass r (guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim))))
    (hmask : ∀ c, segAt? s₂ = some c → (maskSeat (Dm.N.group l) c).isSome = true)
    (hfits : Desc.K3.sFvFitsB s = true) :
    (mgAll Dm Mg).pub (.formsIn l k "objects") (z, s₂) = true :=
  objIn_dig Dm Mg H lk readers codes shape a B claim h hOk hi hpc hlinks hsub hRd hA z s s₂ rs gs hd
    hF hS he pass hpass hsame hfO hfG hmask
    (k3_digits_step_hmerge claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd hF hS hfits)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_hmerge
#print axioms VerifiableInference.OnPublicFiles.objIn_dig_fits
