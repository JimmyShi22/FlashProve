-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsFormsOurs.lean: the lookup on the digits of a segment's approximate
range proof: THE COMPOSED MEANING's PUBLIC TEST AT formsIn, UNFOLDED ONCE, KIND-FREE; and so: the
tests formsIn at THE LOOKUP ON THE CALLS' OWN RUNS ("objects" with "guests", "planes", "join") pass
an accept of the whole seated digits' sub-protocol. At the sub-protocol's own decide, whatever the
rounds' words. Joinings. NO RESULT ON THE PROTOCOL.

Main names.
  formsIn_pass_mgAll: KIND-FREE: where each run that the table's name stands for is none of the
    approximate range proof's own and its test formsIn at the term's reader goes from s to s', the
    composed test at formsIn l k r goes from s to s'.
  objects_pass_dig, planes_pass_dig, join_pass_dig: at the names "objects", "planes", "join" whose
    runs stand at the pieces B₀ (and B₁ for "join"): by objects_formsIn_pass, guests_formsIn_pass,
    planes_formsIn_pass, join_formsIn_pass (Johnson/Top/H/Keep/FormsPassOurs.lean) over
    k3_digits_step_pass (K3DigitsPass.lean) and DigLeft's clause «what was heard at the calls' seat
    is one» (k3_digits_step_leaves).
WHAT EACH STILL CARRIES, BOOKED.
  TERMS OF Dm: hlinks · hRd (Dm.Rd l = readersOfLink H lk) · he… (what the table's name lists:
    Johnson/Desc/Sound/MgAt/Runs.lean has the lists) · hs… (the link's second hole is silent at the
    run) · hf… (the run that the link states under the name is the lookup's own).
  THE CALLING KIND's, AT THE TWO STATES: hkeys, hread (its keys, its readers answer the same).
  ON THE STATE IN FRONT: hwin ("planes": the window of the sumcheck over the leaves is free, ends at
    or below the ledger's next slot) · hF, hS (the ledger, with its sizes: had from the promise in
    front).
OBJECT. The composed public test at formsIn; Desc.K3.theStated's value at the digits' address.
Used by K3DigitsFormsJoinAtt.lean and K3DigitsFormsKept.lean (Johnson/Desc/Sound/MgAt/) and 4 more.
LETTERS. Dm, Mg; H, lk; l, sub; the seated sub-protocol's; z, s, s₂.


Compiled with the whole library.


Limits. Nothing on "own", "small", "weights", nor on the new item "objects" at the digits' own
piece.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.FormsPassOurs
import Johnson.Desc.First.Look.K3DigitsPass
import Johnson.Desc.Sound.MgAt.Runs
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub Meaning runsOf pubAll_formsIn)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles formsIn)
open VerifiableInference.Desc.K3 (planesRun joinRun)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **THE COMPOSED TEST AT formsIn GOES WHERE ITS RUNS' TESTS GO.** -/
theorem formsIn_pass_mgAll (hlinks : Dm.links = linksFull) {l : ℕ} {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) {k : ℕ} {r : String} (z : P) (s s' : Desc.First.S)
    (hp : ∀ p ∈ runsOf sub k r, (p.2 == "K8.equations") = false ∧
      (formsIn (Dm.Rd l) (Dm.N.group l) p.1 p.2 s = true →
        formsIn (Dm.Rd l) (Dm.N.group l) p.1 p.2 s' = true))
    (ht : (mgAll Dm Mg).pub (.formsIn l k r) (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l k r) (z, s') = true := by
  rw [mgAll_pub, pubAll_formsIn] at ht ⊢
  have e : Dm.pubD.runs l k r = runsOf sub k r := by
    show runsAt Dm.links l k r = runsOf sub k r
    rw [hlinks]
    exact runsAt_of linksFull l sub hsub k r
  rw [e, List.all_eq_true] at ht ⊢
  intro p hpm
  have h0 := ht p hpm
  obtain ⟨ha, hq⟩ := hp p hpm
  have ea : Dm.pubD.ah p.1 p.2 = false := ha
  rw [ea] at h0 ⊢
  simp only [Bool.false_eq_true, if_false] at h0 ⊢
  exact hq h0

variable (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim)
  (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
  (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Desc.Claim)
  (claim : Aff → Desc.Claim)
  (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
  {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
  (hlinks : Dm.links = linksFull) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
  (hRd : Dm.Rd l = readersOfLink H lk)
  (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
  (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
  (hS : OnBytes.PscRun.Sized F)
include h hOk hi hpc hlinks hsub hRd hd hF hS

/-- **"objects" (with "guests") at the calls' piece.** -/
theorem objects_pass_dig (hA : AtS2 (Desc.K3.seatCalls claim)) {k B₀ : ℕ}
    (he : runsOf sub k "objects" = [(B₀, "objects"), (B₀, "guests")])
    (hsO : H.silent B₀ "objects" s = none) (hsG : H.silent B₀ "guests" s = none)
    (hfO : ∀ n r, (statesOfLink lk B₀).find? (fun x => x.1 == "objects") = some (n, r) →
      r = objectsRun (Desc.K3.seatCalls claim))
    (hfG : ∀ n r, (statesOfLink lk B₀).find? (fun x => x.1 == "guests") = some (n, r) →
      r = guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim)))
    (ht : (mgAll Dm Mg).pub (.formsIn l k "objects") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l k "objects") (z, s₂) = true := by
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hF hS
  obtain ⟨-, -, -, -, hLk, -, -⟩ :=
    k3_digits_step_leaves claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
  refine formsIn_pass_mgAll Dm Mg hlinks hsub z s s₂ (fun p hpm => ?_) ht
  rw [he] at hpm
  rw [hRd]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  rcases hpm with rfl | rfl
  · exact ⟨(by decide : ("objects" == "K8.equations") = false),
      objects_formsIn_pass H lk B₀ _ (Desc.K3.seatCalls claim) hA Q hLk hsO hfO⟩
  · exact ⟨(by decide : ("guests" == "K8.equations") = false),
      guests_formsIn_pass H lk B₀ _ Q hsG hfG⟩

/-- **"planes" at the calls' piece.** -/
theorem planes_pass_dig (hA : AtS2 (Desc.K3.seatCalls claim)) {k B₀ : ℕ}
    (he : runsOf sub k "planes" = [(B₀, "planes")]) (lm : ℕ)
    (rd : Desc.K3.Readers Desc.First.S) (hread : rd s₂ = rd s)
    (hwin : ∀ g, (Desc.K3.seatCalls claim).heard s = some g →
      g.leaves.first + lvLen g ≤ F.next ∧ F.next ≤ F.ns ∧
        ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ OnBytes.PscRun.Filled F j)
    (hsP : H.silent B₀ "planes" s = none)
    (hfP : ∀ n r, (statesOfLink lk B₀).find? (fun x => x.1 == "planes") = some (n, r) →
      r = planesRun (Desc.K3.seatCalls claim) lm rd)
    (ht : (mgAll Dm Mg).pub (.formsIn l k "planes") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l k "planes") (z, s₂) = true := by
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hF hS
  obtain ⟨-, -, -, -, hLk, -, -⟩ :=
    k3_digits_step_leaves claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
  refine formsIn_pass_mgAll Dm Mg hlinks hsub z s s₂ (fun p hpm => ?_) ht
  rw [he] at hpm
  rw [hRd]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  obtain rfl := hpm
  exact ⟨(by decide : ("planes" == "K8.equations") = false),
    planes_formsIn_pass H lk B₀ _ (Desc.K3.seatCalls claim) hA Q hLk lm rd hread hwin hsP hfP⟩

/-- **"join".** -/
theorem join_pass_dig (hA : AtS2 (Desc.K3.seatCalls claim)) {k B₀ : ℕ}
    (he : runsOf sub k "join" = [(B₀, "join")])
    (keys : Desc.First.S → Option (Array Aff)) (hkeys : keys s₂ = keys s)
    (hsJ : H.silent B₀ "join" s = none)
    (hfJ : ∀ n r, (statesOfLink lk B₀).find? (fun x => x.1 == "join") = some (n, r) →
      r = joinRun (Desc.K3.seatCalls claim) keys)
    (ht : (mgAll Dm Mg).pub (.formsIn l k "join") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l k "join") (z, s₂) = true := by
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hF hS
  obtain ⟨-, -, -, -, hLk, -, -⟩ :=
    k3_digits_step_leaves claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
  refine formsIn_pass_mgAll Dm Mg hlinks hsub z s s₂ (fun p hpm => ?_) ht
  rw [he] at hpm
  rw [hRd]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  obtain rfl := hpm
  exact ⟨(by decide : ("join" == "K8.equations") = false),
    join_formsIn_pass H lk B₀ _ (Desc.K3.seatCalls claim) hA Q hLk keys hkeys hsJ hfJ⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.formsIn_pass_mgAll
#print axioms VerifiableInference.OnPublicFiles.objects_pass_dig
#print axioms VerifiableInference.OnPublicFiles.planes_pass_dig
#print axioms VerifiableInference.OnPublicFiles.join_pass_dig
