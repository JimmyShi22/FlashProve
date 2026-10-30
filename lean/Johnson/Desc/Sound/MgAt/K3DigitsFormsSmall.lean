-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsFormsSmall.lean: the lookup on the digits of a segment's approximate
range proof: THE COMPOSED MEANING's PUBLIC TEST AT formsIn l k "small" (the approximate range
proof's own run "K8.equations", whose forms may name what is ahead) PASSES AN ACCEPT OF THE WHOLE
SEATED DIGITS' SUB-PROTOCOL, the step without a round among it. At the sub-protocol's own decide,
whatever the rounds' words. The like across the lookup's own rounds alone:
Johnson/Top/H/Keep/SmallPassDigits.lean. Joinings. NO RESULT ON THE PROTOCOL.

Main names.
  quietAt_tlFuns: the step without a round leaves what the first hole's reader reads (S.tl?,
    S.funs?).
  k3_digits_step_smallReader: smallReader s₂ = smallReader s (k3_digits_smallReader;
    smallReader_same, Johnson/Desc/First/Batch/ReadersAt.lean).
  formsInA_pass_mgAll: KIND-FREE: the sister of formsIn_pass_mgAll (MgAt/K3DigitsFormsOurs.lean)
    where each run that the table's name stands for IS the approximate range proof's own.
  small_pass_dig: THE END: by small_formsInA_pass (Johnson/Top/H/Keep/FormsAheadPassK3.lean) over
    k3_digits_step_pass.
WHAT IT STILL CARRIES. TERMS OF Dm: hlinks · hRd (Dm.Rd l = readersOfLink H lk) · hHs (the link's
first hole is smallReader) · he (what the table's name lists). ON THE STATE IN FRONT: hF, hS (the
ledger with its sizes: had from the promise in front). NO FACT ALONG THE FOLD.
OBJECT. The composed public test at formsIn; Desc.K3.theStated's value at the digits' address.
Used by K3DigitsFormsJoin.lean and K3DigitsObjIn.lean (Johnson/Desc/Sound/MgAt/) and 4 more.
LETTERS. Those of MgAt/K3DigitsFormsOurs.lean.


Compiled with the whole library.


Limits. One way.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.SmallPassDigits
import Johnson.Desc.First.Batch.ReadersAt
import Johnson.Desc.First.Batch.Law.Keeps
import Johnson.Desc.Sound.MgAt.K3DigitsFormsOurs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub Meaning runsOf pubAll_formsIn)
open VerifiableInference.Desc.K9 (readersOfLink LinkHoles formsInA smallReader smallReader_same)

/-- The step without a round leaves what the first hole's reader reads. -/
theorem quietAt_tlFuns (X : Verify.Public) (i : ℕ)
    (f : Desc.First.S → Except String Desc.First.S) (hf : Desc.K3.quietAt X i true = some f)
    (s t : Desc.First.S) (h : f s = .ok t) : t.tl? = s.tl? ∧ t.funs? = s.funs? := by
  unfold Desc.K3.quietAt at hf
  simp only [if_true] at hf
  split at hf
  · obtain rfl := Option.some.inj hf
    obtain ⟨ah, c', ha, ho, e⟩ := Desc.K3.quietHead_ok X s t h
    rw [e]
    exact ⟨by simp [Desc.First.S.tl?, ha], by simp [Desc.First.S.funs?, ha]⟩
  · split at hf <;> split at hf <;>
      (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
       obtain ⟨F', hF', -, e⟩ := Desc.K3.quietDigits_ok _ _ s t h
       rw [e]
       exact ⟨tl_putFork s _, Desc.K9.funs_putFork s _⟩)

/-- **The reader's answer is the same across the whole seated accept.** -/
theorem k3_digits_step_smallReader {Cl : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) : smallReader s₂ = smallReader s := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  have e0 := k3_digits_smallReader claim a.piece laid sent P' [] s s' _ gs' hyes
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact e0
  · obtain ⟨e1, e2⟩ := quietAt_tlFuns X i f hf s' s₂ hfs
    exact (smallReader_same s' s₂ e1 e2).trans e0

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **THE COMPOSED TEST AT formsIn, WHERE THE RUNS ARE THE APPROXIMATE RANGE PROOF's OWN.** -/
theorem formsInA_pass_mgAll (hlinks : Dm.links = linksFull) {l : ℕ} {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) {k : ℕ} {r : String} (z : P) (s s' : Desc.First.S)
    (hp : ∀ p ∈ runsOf sub k r, (p.2 == "K8.equations") = true ∧
      (formsInA (Dm.Rd l) (Dm.N.sent l) (Dm.N.group l) p.1 p.2 s = true →
        formsInA (Dm.Rd l) (Dm.N.sent l) (Dm.N.group l) p.1 p.2 s' = true))
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
  have ea : Dm.pubD.ah p.1 p.2 = true := ha
  rw [ea, if_pos rfl] at h0 ⊢
  exact hq h0

/-- **"small".** -/
theorem small_pass_dig (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Desc.Claim)
    (claim : Aff → Desc.Claim)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hlinks : Dm.links = linksFull) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    (hRd : Dm.Rd l = readersOfLink H lk) (hHs : H.small = smallReader)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) {k B₀ : ℕ}
    (he : runsOf sub k "small" = [(B₀, "K8.equations")])
    (ht : (mgAll Dm Mg).pub (.formsIn l k "small") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l k "small") (z, s₂) = true := by
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hF hS
  have eS := k3_digits_step_smallReader claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
  refine formsInA_pass_mgAll Dm Mg hlinks hsub z s s₂ (fun p hpm => ?_) ht
  rw [he] at hpm
  rw [hRd]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  obtain rfl := hpm
  refine ⟨(by decide : ("K8.equations" == "K8.equations") = true),
    small_formsInA_pass Q H lk _ _ B₀ (fun R hR => ?_) (fun R hR x hx => ?_)⟩
  · rw [hHs] at hR ⊢
    rw [eS]
    exact hR
  · rw [hHs] at hR
    rw [smallReader_late hR] at hx
    exact absurd hx List.not_mem_nil

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.quietAt_tlFuns
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_smallReader
#print axioms VerifiableInference.OnPublicFiles.formsInA_pass_mgAll
#print axioms VerifiableInference.OnPublicFiles.small_pass_dig
