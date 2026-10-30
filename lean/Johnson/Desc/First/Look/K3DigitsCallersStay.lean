-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsCallersStay.lean: the lookup on the digits of a segment's
approximate range proof: WHAT THE CALLING KINDS' READERS AND KEYS OF THE LOOKUP ON THE CALLS ANSWER
IN FRONT OF AN ACCEPT OF THE WHOLE SEATED DIGITS' SUB-PROTOCOL (the step without a round among it)
THEY ANSWER BEHIND IT: at an attention segment and at the output head's. At the sub-protocol's own
decide, whatever the rounds' words. The like across the lookup's own rounds alone:
Johnson/Top/H/Keep/AttCallersStay.lean, CallersStay.lean. NO SOUNDNESS IS CLAIMED.

Main names.
  k3_digits_step_attSame: at an attention segment: the own part behind has the same g and heard5,
    its ledger shows what was shown and has the same widths (AttStays: K3DigitsOwnStays.lean;
    K3Pass: K3DigitsPass.lean).
  k3_digits_step_attReaders, k3_digits_step_attKeys: so readersOfO A and keysOfO A answer behind
    what they answered in front (attReaders_fwd, attKeys_fwd).
  headClaim_samePlanes; k3_digits_step_samePlanes: SamePlanes s s₂
    (Johnson/Desc/Kinds/Law/PlanesStay.lean) at every sort of segment.
  k3_digits_step_headReaders: at the output head's segment: callerReaders (planesAt iU3) has one
    value (headReaders_same).
OBJECT. Desc.K3.theStated's value at the digits' address; the callers' readers.
USER. Whoever pays hread, hkeys of planes_formsIn_pass', join_formsIn_pass', planes_formsIn_pass at
the digits' seated accept. K3RidesDigFwd2.lean, K3DigitsFormsPlanes.lean and
K3DigitsFormsJoinAtt.lean (Johnson/Desc/Sound/MgAt/) call the theorems on readers and keys.
LETTERS. Those of k3_digits_step_turns; u, o; A, iU3.
IS IT EMPTY? The premises are an .ok of decide, the sort of the open segment and a ledger with its
sizes.
Compiled with the whole library.




Limits. Nothing on the output head's keys ("join" there).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.AttCallersStay
import Johnson.Top.H.Keep.CallersStay
import Johnson.Desc.First.Look.K3DigitsPass
import Johnson.Desc.First.Look.K3DigitsOwnStays

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Att.P (readersOfO keysOfO)
open K5Law (ShownLe shownLe_of_later widths)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)
open VerifiableInference.Desc.Kinds.Head.Law (SamePlanes same_putFork)

/-- The claim on the weights is none of what the law on "planes" reads. -/
theorem headClaim_samePlanes (s : Desc.First.S) (a : Desc.First.HeadOwn) (c : WsClaim)
    (ha : s.here = .head a) :
    SamePlanes s { s with here := .head { a with claim := some c } } := by
  refine ⟨rfl, rfl, fun o h => ?_⟩
  rw [ha] at h
  cases h
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {Cl : Type}

/-- **At an attention segment.** -/
theorem k3_digits_step_attSame (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {u : Desc.First.AttOwn} (hs : s.here = .att u)
    (hS : OnBytes.PscRun.Sized u.F) :
    ∃ w, s₂.here = .att w ∧ w.g = u.g ∧ w.heard5 = u.heard5 ∧ ShownLe u.F w.F ∧
      widths w.F = widths u.F := by
  have hF : s.fork? = some u.F := by simp [Desc.First.S.fork?, hs]
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
    hF hS
  obtain ⟨w, hw, k⟩ :=
    k3_digits_step_attStays claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd u hs
  have eG : w.F = G := by simpa [Desc.First.S.fork?, hw] using Q.behind
  refine ⟨w, hw, congrArg (·.g) (k u.tl u.F), congrArg (·.heard5) (k u.tl u.F), ?_, ?_⟩
  · rw [eG]
    exact shownLe_of_later ⟨Q.later.next, Q.later.ns, fun _ => Q.sizedG, Q.later.keep⟩
  · rw [eG]
    unfold widths
    rw [Q.trees]

/-- **The attention kind's readers.** -/
theorem k3_digits_step_attReaders (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {u : Desc.First.AttOwn} (hs : s.here = .att u)
    (hS : OnBytes.PscRun.Sized u.F) (A : Attention.Plan) :
    ∀ r, readersOfO A s = some r → readersOfO A s₂ = some r := by
  obtain ⟨w, h1, h2, h3, h4, h5⟩ :=
    k3_digits_step_attSame claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd hs hS
  exact attReaders_fwd A hs h1 h2 h3 h4 h5

/-- **Its key forms.** -/
theorem k3_digits_step_attKeys (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {u : Desc.First.AttOwn} (hs : s.here = .att u)
    (hS : OnBytes.PscRun.Sized u.F) (A : Attention.Plan) :
    ∀ KF, keysOfO A s = some KF → keysOfO A s₂ = some KF := by
  obtain ⟨w, h1, h2, h3, h4, h5⟩ :=
    k3_digits_step_attSame claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd hs hS
  exact attKeys_fwd A hs h1 h2 h3 h4 h5

/-- **What the law on "planes" reads.** -/
theorem k3_digits_step_samePlanes (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) : SamePlanes s s₂ := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  have hS := k3_digits_samePlanes claim a.piece laid sent _ [] s s' _ gs' hyes
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact hS
  · unfold Desc.K3.quietAt at hf
    simp only [if_true] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨ah, c, ha, -, e⟩ := Desc.K3.quietHead_ok X s' s₂ hfs
      rw [e]
      exact hS.trans (headClaim_samePlanes s' ah c ha)
    · split at hf <;> split at hf <;>
        (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
         obtain ⟨F, -, -, e⟩ := Desc.K3.quietDigits_ok _ _ s' s₂ hfs
         exact hS.trans (e ▸ same_putFork s' _))

/-- **The output head's readers.** -/
theorem k3_digits_step_headReaders (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {o : Desc.First.HeadOwn} (ho : s.here = .head o)
    {F : Fork} (hF : s.fork? = some F) (hS : OnBytes.PscRun.Sized F) (iU3 : ℕ) :
    callerReaders (planesAt iU3) s₂ = callerReaders (planesAt iU3) s := by
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
    hF hS
  exact headReaders_same
    (k3_digits_step_samePlanes claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd) ho hF
    Q.behind Q.trees iU3

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.headClaim_samePlanes
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_attSame
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_attReaders
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_attKeys
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_samePlanes
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_headReaders
