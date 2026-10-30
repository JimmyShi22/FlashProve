-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsFormsKept.lean: the lookup on the digits of a segment's approximate
range proof: THE COMPOSED MEANING's PUBLIC TEST AT THE KEPT ITEM formsIn l (2 + shift sub) "objects"
(the runs "objects" and "guests" of the lookup on the calls) PASSES AN ACCEPT OF THE WHOLE SEATED
DIGITS' SUB-PROTOCOL: AT EVERY SORT OF SEGMENT, THE OUTPUT HEAD's TOO, WIRED TO ITS PAYERS: no word
on the link's second hole, no fact on the state but the kept test itself and the ledger in front. It
overtakes objects_pass_dig (MgAt/K3DigitsFormsOurs.lean), whose premise «the hole is silent» is, by
a reading of the hole's text there (not evaluated), false in front of the output
head's digits. Joinings. NO RESULT ON THE PROTOCOL.

Main names.
  rd_holesAt: where the term's chain has the link lk at l, the term's reader at l is readersOfLink
    (holesAt X (headLink X) l lk) lk (readersAt_some, Johnson/Desc/First/Batch/ReadersAt.lean).
  find_eq_of_raw: from «find? = some (name, r₀)» the form «∀ nm r, find? = some (nm, r) → r = r₀».
  objects_kept_dig: THE END: by objects_formsIn_pass_r, guests_formsIn_pass_r
    (Johnson/Top/H/Keep/FormsPassRun.lean), «the run itself answers in front» by
    objects_hr_of_formsIn, guests_hr (Johnson/Top/H/Keep/RunAnswers.lean), over k3_digits_step_pass
    and DigLeft's clause on what was heard at the calls' seat.
WHAT IT STILL CARRIES. TERMS: hlinks · hlk (Dm.lk l = some lk) · hA · hrawO, hrawG (what the link
states under the two names is the lookup's own run: in the form of k03_objects_raw, k03_guests_raw,
Johnson/Desc/First/Look/K03StatesRaw.lean). ON THE STATE IN FRONT: hF, hS (the
ledger with its sizes: off the promise's lookIn).
OBJECT. The composed public test at formsIn; Desc.K3.theStated's value at the digits' address.
USER. objects_kept_dig: hForms_dig_mgAll (MgAt/K3DigitsFormsJoin.lean) · objects_kept_dig_found
(MgAt/K3DigitsFormsKeptFound.lean). rd_holesAt, find_eq_of_raw: MgAt/K3DigitsFormsJoin.lean ·
K3DigitsFormsPlanes.lean · K3DigitsFormsJoinAtt.lean · K3DigitsPlanesHead.lean. Meant: hForms at
this item.
LETTERS. Those of MgAt/K3DigitsFormsOurs.lean; lk.


Compiled with the whole library.


Limits. "objects" alone. At Cl := Desc.Claim.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunAnswers
import Johnson.Desc.Sound.MgAt.K3DigitsFormsOurs
import Johnson.Desc.Sound.MgAt.K3DigitsRunsHe

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub Meaning runsOf shift)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles formsIn holesAt
  readersAt_some)

/-- From the raw form to the form with two letters. -/
theorem find_eq_of_raw {α : Type} {L : List (String × α)} {p : String × α → Bool} {nm₀ : String}
    {r₀ : α} (h : L.find? p = some (nm₀, r₀)) : ∀ nm r, L.find? p = some (nm, r) → r = r₀ := by
  intro nm r h'
  rw [h] at h'
  exact (congrArg Prod.snd (Option.some.inj h')).symm

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- The term's reader at a link of its chain. -/
theorem rd_holesAt {l : ℕ} {lk : Desc.Link Desc.First.S Desc.Claim} (hlk : Dm.lk l = some lk) :
    Dm.Rd l = readersOfLink (holesAt X (headLink X) l lk) lk :=
  readersAt_some Dm.lk X (headLink X) l lk hlk

/-- **THE KEPT "objects", AT EVERY SORT.** -/
theorem objects_kept_dig (lk : Desc.Link Desc.First.S Desc.Claim)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Desc.Claim)
    (claim : Aff → Desc.Claim)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hlinks : Dm.links = linksFull) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    (hlk : Dm.lk l = some lk) (hA : AtS2 (Desc.K3.seatCalls claim))
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) {B₀ : ℕ} (hB₀ : B₀ = 1 + shift sub)
    (hrawO : (statesOfLink lk B₀).find? (fun x => x.1 == "objects") =
      some ("objects", objectsRun (Desc.K3.seatCalls claim)))
    (hrawG : (statesOfLink lk B₀).find? (fun x => x.1 == "guests") =
      some ("guests", guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim))))
    (ht : (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "objects") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "objects") (z, s₂) = true := by
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hF hS
  obtain ⟨-, -, -, -, hLk, -, -⟩ :=
    k3_digits_step_leaves claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
  refine formsIn_pass_mgAll Dm Mg hlinks hsub z s s₂ (fun p hpm => ?_) ht
  rw [he_objects_calls sub, ← hB₀] at hpm
  rw [rd_holesAt Dm hlk]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  rcases hpm with rfl | rfl
  · exact ⟨(by decide : ("objects" == "K8.equations") = false), fun hin =>
      objects_formsIn_pass_r (holesAt X (headLink X) l lk) lk B₀ _ (Desc.K3.seatCalls claim) hA Q
        hLk
        (objects_hr_of_formsIn X (headLink X) l lk B₀ _ claim hA (find_eq_of_raw hrawO) hin)
        (find_eq_of_raw hrawO) hin⟩
  · exact ⟨(by decide : ("guests" == "K8.equations") = false), fun hin =>
      guests_formsIn_pass_r (holesAt X (headLink X) l lk) lk B₀ _ Q
        (guests_hr lk B₀ (fun _ _ => True) (fun _ => trivial) ⟨_, _, hrawG, runOver_refl _ _⟩ hF)
        (find_eq_of_raw hrawG) hin⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.find_eq_of_raw
#print axioms VerifiableInference.OnPublicFiles.rd_holesAt
#print axioms VerifiableInference.OnPublicFiles.objects_kept_dig
