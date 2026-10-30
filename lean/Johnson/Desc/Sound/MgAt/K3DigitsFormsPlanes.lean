-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsFormsPlanes.lean: the lookup on the digits of a segment's
approximate range proof: THE COMPOSED MEANING's PUBLIC TEST AT THE KEPT ITEM formsIn l (2 + shift
sub) "planes" (a run of the lookup on the calls; idle at a layers' segment) PASSES AN ACCEPT OF THE
WHOLE SEATED DIGITS' SUB-PROTOCOL, WIRED TO ITS PAYERS AS FAR AS THEY LIE. It overtakes
planes_pass_dig (MgAt/K3DigitsFormsOurs.lean), of whose premises hread (an equation) has no payer at
an attention segment, and hs (the hole is silent) none at the output head's. Joinings. NO RESULT ON
THE PROTOCOL.

Main names.
  holesAt_silent_none: off the output head's segment the description's second hole answers nothing.
    hr_of_formsIn_quiet: where the hole answers nothing and the test formsIn is true, the run itself
    answers.
  planes_kept_dig: GENERAL IN THE SORT (not the layers'): by planes_formsIn_pass_r
    (Johnson/Top/H/Keep/FormsPassRun.lean); the window of the sumcheck over the leaves by
    hwin_of_onOut (Johnson/Top/H/Keep/CallersStay.lean) from the two items on the lookup on the
    calls in front.
  planes_kept_dig_att: at an attention segment: hread by k3_digits_step_attReaders
    (K3DigitsCallersStay.lean), hr by hr_of_formsIn_quiet.
  planes_kept_dig_head: at the output head's segment: hread by k3_digits_step_headReaders; hr STAYS
    A PREMISE.
WHAT IS LEFT, BOOKED. TERMS: hlinks · hlk · hA · hrawP (what the link states under "planes" is the
lookup's own run at the calling kind's readers: the shape of k03_planes_raw,
Johnson/Desc/First/Look/K03StatesRaw.lean) · hne (l is not the output head's segment). ON THE STATE
IN FRONT: hF, hS · hO (the calls' test lookOut) · hLf (the sentence at leftOn) · hatt | hhead (which
sort of segment is open) · AT THE OUTPUT HEAD's: hr (the run itself answers): NOBODY PAYS IT.
OBJECT. The composed public test at formsIn; Desc.K3.theStated's value at the digits' address.
Used by K3DigitsFormsJoinAtt.lean and K3DigitsPlanesHead.lean (Johnson/Desc/Sound/MgAt/) and 3 more.
LETTERS. Those of MgAt/K3DigitsFormsKept.lean; pc, lm, rd, A, iU3.


Compiled with the whole library.


Limits. "planes" alone. Of "join" nothing: what the link states under that name is the calling
kind's run: no payer.
(Where this and lean/THEOREM.md differ, the page
holds.)
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsFormsKept
import Johnson.Desc.First.Look.K3DigitsCallersStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub Meaning runsOf shift)
open VerifiableInference.Desc.K9 (readerOf readersOfLink statesOfLink LinkHoles formsIn holesAt)
open VerifiableInference.Desc.K3 (planesRun)
open VerifiableInference.Desc.First.Att.P (readersOfO)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)

/-- Off the output head's segment the second hole answers nothing. -/
theorem holesAt_silent_none (X : Verify.Public) {mH m : ℕ} (hne : (m == mH) = false)
    (lk : Desc.Link Desc.First.S Desc.Claim) (b : ℕ) (nm : String) (s : Desc.First.S) :
    (holesAt X mH m lk).silent b nm s = none := by
  show (if m == mH then _ else fun _ _ _ => none : ℕ → String → Desc.First.S → _) b nm s = none
  rw [hne]
  rfl

/-- Where the hole answers nothing and the test is true, the run itself answers. -/
theorem hr_of_formsIn_quiet (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim) (b : ℕ)
    (own : List (ℕ × ℕ)) {nm : String} {s : Desc.First.S}
    (hn : (nm == "K8.equations") = false) (hsil : H.silent b nm s = none)
    (hin : formsIn (readersOfLink H lk) own b nm s = true) :
    (readerOf (statesOfLink lk) b nm s).isSome = true := by
  obtain ⟨R, hR⟩ := formsIn_some hin
  cases hq : readerOf (statesOfLink lk) b nm s with
  | some _ => rfl
  | none =>
    have e : (readersOfLink H lk).forms b nm s = H.silent b nm s := by
      show (if nm == "K8.equations" then H.small s
        else match readerOf (statesOfLink lk) b nm s with
          | some R => some R
          | Option.none => H.silent b nm s) = H.silent b nm s
      rw [hn, hq]
      rfl
    rw [e, hsil] at hR
    cases hR

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **THE KEPT "planes", GENERAL IN THE SORT.** -/
theorem planes_kept_dig (lk : Desc.Link Desc.First.S Desc.Claim)
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
    (hnl : sub ≠ .layers) (lm : ℕ) (rd : Desc.K3.Readers Desc.First.S)
    (hread : ∀ r, rd s = some r → rd s₂ = some r)
    {pc : Desc.First.Look.P} (hdc : pc.digits = false) (hO : Desc.K3.k3OnOut pc s = true)
    (hLf : k3LeftOnItem pc s)
    (hr : formsIn (readersOfLink (holesAt X (headLink X) l lk) lk) (Dm.N.group l) B₀ "planes" s =
      true → (readerOf (statesOfLink lk) B₀ "planes" s).isSome = true)
    (hrawP : (statesOfLink lk B₀).find? (fun x => x.1 == "planes") =
      some ("planes", planesRun (Desc.K3.seatCalls claim) lm rd))
    (ht : (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "planes") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "planes") (z, s₂) = true := by
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hF hS
  obtain ⟨-, -, -, -, hLk, -, -⟩ :=
    k3_digits_step_leaves claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
  refine formsIn_pass_mgAll Dm Mg hlinks hsub z s s₂ (fun p hpm => ?_) ht
  rw [he_planes sub hnl, ← hB₀] at hpm
  rw [rd_holesAt Dm hlk]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  obtain rfl := hpm
  exact ⟨(by decide : ("planes" == "K8.equations") = false), fun hin =>
    planes_formsIn_pass_r (holesAt X (headLink X) l lk) lk B₀ _ (Desc.K3.seatCalls claim) hA Q hLk
      lm rd hread (hwin_of_onOut hdc hF hO hLf) (hr hin) (find_eq_of_raw hrawP) hin⟩

/-- **AT AN ATTENTION SEGMENT.** -/
theorem planes_kept_dig_att (lk : Desc.Link Desc.First.S Desc.Claim)
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
    (hnl : sub ≠ .layers) (hne : (l == headLink X) = false) (lm : ℕ) (A : Attention.Plan)
    {u : Desc.First.AttOwn} (hatt : s.here = .att u)
    {pc : Desc.First.Look.P} (hdc : pc.digits = false) (hO : Desc.K3.k3OnOut pc s = true)
    (hLf : k3LeftOnItem pc s)
    (hrawP : (statesOfLink lk B₀).find? (fun x => x.1 == "planes") =
      some ("planes", planesRun (Desc.K3.seatCalls claim) lm (readersOfO A)))
    (ht : (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "planes") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "planes") (z, s₂) = true := by
  have eF : u.F = F := by simpa [Desc.First.S.fork?, hatt] using hF
  exact planes_kept_dig Dm Mg lk readers codes shape a B claim h hOk hi hpc hlinks hsub hlk hA z s
    s₂ rs gs hd hF hS hB₀ hnl lm (readersOfO A)
    (k3_digits_step_attReaders claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd hatt
      (eF ▸ hS) A)
    hdc hO hLf
    (hr_of_formsIn_quiet _ lk B₀ _ (by decide : ("planes" == "K8.equations") = false)
      (holesAt_silent_none X hne lk B₀ "planes" s))
    hrawP ht

/-- **AT THE OUTPUT HEAD's SEGMENT.** -/
theorem planes_kept_dig_head (lk : Desc.Link Desc.First.S Desc.Claim)
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
    (hnl : sub ≠ .layers) (lm iU3 : ℕ) {o : Desc.First.HeadOwn} (hhead : s.here = .head o)
    {pc : Desc.First.Look.P} (hdc : pc.digits = false) (hO : Desc.K3.k3OnOut pc s = true)
    (hLf : k3LeftOnItem pc s)
    (hr : (readerOf (statesOfLink lk) B₀ "planes" s).isSome = true)
    (hrawP : (statesOfLink lk B₀).find? (fun x => x.1 == "planes") =
      some ("planes", planesRun (Desc.K3.seatCalls claim) lm (callerReaders (planesAt iU3))))
    (ht : (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "planes") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "planes") (z, s₂) = true :=
  planes_kept_dig Dm Mg lk readers codes shape a B claim h hOk hi hpc hlinks hsub hlk hA z s
    s₂ rs gs hd hF hS hB₀ hnl lm (callerReaders (planesAt iU3))
    (fun r hr0 => by
      rw [k3_digits_step_headReaders claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
        hhead hF hS iU3]
      exact hr0)
    hdc hO hLf (fun _ => hr) hrawP ht

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.holesAt_silent_none
#print axioms VerifiableInference.OnPublicFiles.hr_of_formsIn_quiet
#print axioms VerifiableInference.OnPublicFiles.planes_kept_dig
#print axioms VerifiableInference.OnPublicFiles.planes_kept_dig_att
#print axioms VerifiableInference.OnPublicFiles.planes_kept_dig_head
