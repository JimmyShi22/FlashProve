-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsFormsKeptFound.lean: the lookup on the digits of a segment's
approximate range proof: A PAYER, HELD BY LEAN AGAINST THE PREMISES' OWN TEXTS, FOR FOUR PREMISES OF
objects_kept_dig (MgAt/K3DigitsFormsKept.lean): hrawO, hrawG («what the link states under "objects",
"guests" is the lookup's own run»: k03_objects_raw, k03_guests_raw,
Johnson/Desc/First/Look/K03StatesRaw.lean: in the goals' scope, at the description
as it is opened), hA (the calls' seat at the kind's own letter) and hB₀ (the run's number). So that
these four are known to be meetable together. A joining. NO RESULT ON THE PROTOCOL.

Main names.
  atS2_calls_ofForm: AtS2 (seatCalls K3Lot.ofForm). k3Ix_calls_shift: IM.k3Ix l false = 1 + shift
    sub at l < 25.
  objects_kept_dig_found: objects_kept_dig at claim := K3Lot.ofForm, B₀ := IM.k3Ix l false, lk :=
    the opened description's own link l, with the four struck.
WHAT IS LEFT. THE GOALS' SCOPE AND THE OPENING (hS, hR, O) · hlkc (the term's chain is the opened
description's: Dm.lk l = c.links[l]?) · hlinks · the seated sub-protocol's and hF, hS.
OBJECT. K9.statesOfLink at the description's own links; the composed public test at formsIn.
Its two small lemmas are used by K3DigitsFormsJoin.lean (Johnson/Desc/Sound/MgAt/) and 5 more;
objects_kept_dig_found is called by no other file.
LETTERS. Those of K03StatesRaw.lean and of objects_kept_dig.


Compiled with the whole library.


Limits. No segment is shown at which what is left holds.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsFormsKept
import Johnson.Desc.First.Look.K03StatesRaw
import Johnson.Desc.First.Look.K3Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub Meaning shift)

/-- The calls' seat at the kind's own letter. -/
theorem atS2_calls_ofForm : AtS2 (Desc.K3.seatCalls K3Lot.ofForm) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The run's number. -/
theorem k3Ix_calls_shift {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) :
    IM.k3Ix l false = 1 + shift sub := by
  obtain ⟨sub', hsub', h2, -⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
  have h3 : IM.k3Ix l false + 1 = 2 + shift sub' := h2
  omega

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F₀ : Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Desc.Block Desc.First.S ProofFile.Cl)} {c : Desc.Chain Desc.First.S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}
  {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **THE PAYER SPENT.** -/
theorem objects_kept_dig_found (hSc : VerifierAndGoals.InScope Pf = true)
    (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F₀ Z Bs base c A B₂) {l : ℕ} (hl : l < 25)
    (hlkc : Dm.lk l = c.links[l]?)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Desc.Claim)
    (h : Desc.K3.theStated K3Lot.ofForm readers X codes shape a = some B)
    (hOk : B.planOk = true) (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hlinks : Dm.links = linksFull) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F)
    (ht : (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "objects") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "objects") (z, s₂) = true := by
  obtain ⟨lk, hlk, hO⟩ := k03_objects_raw hSc hR O l hl false
  obtain ⟨lk', hlk', hG⟩ := k03_guests_raw hSc hR O l hl false
  obtain rfl : lk = lk' := Option.some.inj (hlk.symm.trans hlk')
  exact objects_kept_dig Dm Mg lk readers codes shape a B K3Lot.ofForm h hOk hi hpc hlinks hsub
    (hlkc.trans hlk) atS2_calls_ofForm z s s₂ rs gs hd hF hS (k3Ix_calls_shift hl hsub) hO hG ht

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.atS2_calls_ofForm
#print axioms VerifiableInference.OnPublicFiles.k3Ix_calls_shift
#print axioms VerifiableInference.OnPublicFiles.objects_kept_dig_found
