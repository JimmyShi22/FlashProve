-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsFormsJoinAtt.lean: the lookup on the digits of a segment's
approximate range proof: THE COMPOSED MEANING's PUBLIC TEST AT THE KEPT ITEM formsIn l 2 "join" OF
AN ATTENTION SEGMENT PASSES AN ACCEPT OF THE WHOLE SEATED DIGITS' SUB-PROTOCOL, UNDER ONE TERM, IN
THE SHAPE IN WHICH K5's FILES HAVE IT (K05_join_of_open, Johnson/H2K5R/JoinAtOpen.lean:
not imported here). A joining. NO RESULT ON THE PROTOCOL.

Why. "join" is the lookup's run (K3.joinRun, K3Runs.lean), but at an attention segment THE CALLER's
block states it (Johnson/Desc/First/Att/SeatO.lean: at forms, with the claim's maker id;
Johnson/Desc/First/Att/SeatN.lean: runN lays each form as a claim behind it). K3's files' theorems
on the run ask it at a maker of claims. That the two are one function is the calling kind's files'
join_runN_keys, join_runN_eq (Johnson/Desc/First/Att/K05JoinRunN.lean).

Main name.
  join_kept_dig_att: by join_formsIn_pass_r (Johnson/Top/H/Keep/FormsPassRun.lean); hkeys by
    k3_digits_step_attKeys (K3DigitsCallersStay.lean); «the run itself answers» by
    hr_of_formsIn_quiet (MgAt/K3DigitsFormsPlanes.lean).
WHAT IS LEFT. TERMS: hrawJ (what lk states under "join" at the caller's piece: find? = some ("join",
joinRun (seatCalls claimC) (keysOfO A)): K05_join_of_open's own conclusion at claimC :=
K3Lot.ofForm; no payer has typechecked against it here) · hlinks, hlk, hne. ON THE STATE IN FRONT:
hF, hS, hatt.
OBJECT. The composed public test at formsIn; Desc.K3.theStated's value at the digits' address.
USER. hJoinIt_dig (MgAt/K3DigitsJoinIt.lean) · k03_join_kept_att (Johnson/P5J/K03JoinRawAt.lean).
Meant: hJoinIt of hForms_dig_mgAll at an attention segment.
LETTERS. Those of planes_kept_dig_att; claimC.


Compiled with the whole library.


Limits. Attention alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsFormsPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub Meaning runsOf shift joinAt)
open VerifiableInference.Desc.K9 (readerOf readersOfLink statesOfLink LinkHoles formsIn holesAt)
open VerifiableInference.Desc.K3 (joinRun)
open VerifiableInference.Desc.First.Att.P (keysOfO)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **THE KEPT "join" AT AN ATTENTION SEGMENT.** -/
theorem join_kept_dig_att (lk : Desc.Link Desc.First.S Desc.Claim)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Desc.Claim)
    (claim : Aff → Desc.Claim)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hlinks : Dm.links = linksFull) (hsub : linksFull[l]? = some .attention)
    (hlk : Dm.lk l = some lk) (claimC : Aff → Desc.Claim)
    (hA : AtS2 (Desc.K3.seatCalls claimC))
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) (hne : (l == headLink X) = false) (A : Attention.Plan)
    {u : Desc.First.AttOwn} (hatt : s.here = .att u)
    (hrawJ : (statesOfLink lk 2).find? (fun x => x.1 == "join") =
      some ("join", joinRun (Desc.K3.seatCalls claimC) (keysOfO A)))
    (ht : (mgAll Dm Mg).pub (.formsIn l 2 "join") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l 2 "join") (z, s₂) = true := by
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hF hS
  obtain ⟨-, -, -, -, hLk, -, -⟩ :=
    k3_digits_step_leaves claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
  have eF : u.F = F := by simpa [Desc.First.S.fork?, hatt] using hF
  refine formsIn_pass_mgAll Dm Mg hlinks hsub z s s₂ (fun p hpm => ?_) ht
  have he : runsOf .attention 2 "join" = [(2, "join")] := he_join .attention (by decide)
  rw [he] at hpm
  rw [rd_holesAt Dm hlk]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  obtain rfl := hpm
  exact ⟨(by decide : ("join" == "K8.equations") = false), fun hin =>
    join_formsIn_pass_r (holesAt X (headLink X) l lk) lk 2 _ (Desc.K3.seatCalls claimC) hA Q hLk
      (keysOfO A)
      (k3_digits_step_attKeys claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd hatt
        (eF ▸ hS) A)
      (hr_of_formsIn_quiet _ lk 2 _ (by decide : ("join" == "K8.equations") = false)
        (holesAt_silent_none X hne lk 2 "join" s) hin)
      (find_eq_of_raw hrawJ) hin⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.join_kept_dig_att
