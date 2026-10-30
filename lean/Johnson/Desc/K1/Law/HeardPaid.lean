-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/HeardPaid.lean: K01_law: THE TWO BINDERS hheard (344) AND hheard2 (342) OF k01_fifty_paid («inside the wider promise in front of the output head's two later sendings the head has heard»), FROM THE SCOPE AND THREE EQUATIONS ON LETTERS (hDlk · hlk · hWX):
hheard_344_mw1 | hheard_342_mw1 (HeardAtSendings.lean; heard_of_own | heard_of_ownT behind them) ask three things, none on a state: the readers at segment 24 are the link's with K6's silent reader (rd24 · silent24: by the make of the composed meaning's data) · the claim «own» at (24, 4) has K6's
three runs (the kernel, at the written links) · K6States (k6States_seated: from the scope): the last three names stand in ArmHeadPaid.lean. They stand at the elder mw1: called through inAt_drop.
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.HeardAtSendings
import Johnson.Desc.K1.Law.ArmHeadPaid
import Johnson.Desc.K1.Law.ReadersPaid
import Johnson.Desc.K1.Law.MemberMw1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13 mgBase)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (statesOfLink readersOfLink holesAt)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (k6Silent K6States readsOf p8K6)
open ProofFile (Cl)

/-- The claim «own» of segment 24's fourth piece has K6's three runs, at the written links. -/
theorem own_runs_24 : runsAt linksFull 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")] := by
  decide +kernel

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}

/-- **hheard and hheard2, from the scope.** -/
theorem hheard_paid (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (xb : S → Bool)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (d : Bool) :
    ∀ x y, InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase) xb) linksFull (flatPlacesOf linksFull true) (noL 24 d) x y →
      ∃ H, (seatAt XV.hS (readsOf XV)).heard x.2 = some H := by
  intro x y hIn
  obtain ⟨lk, _, _, _, eL, -⟩ := IM.k6_of hS hR O
  have hX : headLink XV = 24 := hWX ▸ headLink_open hS hR O
  have hreaders : Dm.Rd 24 =
      readersOfLink ⟨(holesAt XV 24 24 lk).small, k6Silent (p8K6 XV 24) (statesOfLink lk)⟩ lk := by
    rw [rd24 Dm hX lk ((hlk 24 (by decide)).trans eL), ← silent24 lk]
  have hown : Dm.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")] := by
    show runsAt Dm.links 24 4 "own" = _
    rw [hDlk]
    exact own_runs_24
  have K := k6States_seated hS hR O lk eL
  rw [hWX] at K
  cases d with
  | true => exact hheard_344_mw1 Dm mgBase hreaders hown K Dm.N Dm.N (d13 Dm) dk x y (inAt_drop hIn).1
  | false => exact hheard_342_mw1 Dm mgBase hreaders hown K Dm.N Dm.N (d13 Dm) dk x y (inAt_drop hIn).1

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.own_runs_24
#print axioms VerifiableInference.Desc.K1.hheard_paid
