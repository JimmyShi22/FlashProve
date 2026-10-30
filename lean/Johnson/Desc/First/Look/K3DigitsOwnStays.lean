-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsOwnStays.lean: the lookup on the digits of a segment's approximate
range proof: WHICH FIELDS OF THE OPEN SEGMENT's OWN PART OF THE VERIFIER's STATE AN ACCEPT OF THE
WHOLE SEATED SUB-PROTOCOL WRITES, AT A LAYERS' AND AT AN ATTENTION SEGMENT: TWO: tl, F (at the
output head's segment: K3DigitsHeadStays.lean); and what follows for four readers of the state. At
the sub-protocol's own decide, whatever the rounds' words. NO SOUNDNESS IS CLAIMED.

Main names.
  LayKept, LayStays, AttKept, AttStays: as HeadKept, HeadStays. k3_digits_step_layStays,
    k3_digits_step_attStays: at an .ok of decide of K3.theStated's value at the digits' address.
  digits_step_heard5: what attention's own rounds handed on is one (S.heard5?).
  digits_step_leftOf: what the open segment's sub-proof has left for its row is one
    (Walk.Law.leftOf). digits_step_hasRow: so «can the pending claim on the weights be made» has one
    value, at every parameter (Walk.Law.hasRow, Johnson/Top/H0/Walk/FrameRow.lean).
  digits_step_reply: the heard reply is one (out.reply).
OBJECT. Desc.K3.seatDigits' put, quietHead, quietDigits, through their laws; readers of the state.
USER. Whoever keeps hasRow, tokenSmall and attention's named items over the digits' sub-protocol.
K3DigitsMadeMore.lean, K3DigitsMadeTrees.lean and K3DigitsCallersStay.lean call its theorems; so do
K3DigitsStaysBelow.lean, K3RidesDig.lean and K3RidesDigStep.lean (Johnson/Desc/Sound/MgAt/).
LETTERS. Those of k3_digits_step_turns.
IS IT EMPTY? The premise is an .ok of decide.



Compiled with the whole library.
Limits. Nothing on the fields that are written.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsStep
import Johnson.Top.H0.Walk.FrameRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- The two are one but for tl, F. -/
def LayKept (a a' : Desc.First.LayOwn) : Prop :=
  ∀ (tl : HTailF2) (F : Fork),
    ({ a' with tl := tl, F := F } : Desc.First.LayOwn) = { a with tl := tl, F := F }

/-- Where s stands in such a segment, s' does, and the part is kept but for the two. -/
def LayStays (s s' : Desc.First.S) : Prop :=
  ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ LayKept a a'

theorem LayStays.trans {s t u : Desc.First.S} (h : LayStays s t) (h' : LayStays t u) :
    LayStays s u := by
  intro a ha
  obtain ⟨a', h1, k1⟩ := h a ha
  obtain ⟨a'', h2, k2⟩ := h' a' h1
  exact ⟨a'', h2, fun tl F => (k2 tl F).trans (k1 tl F)⟩

theorem putFork_layStays (s : Desc.First.S) (G : Fork) : LayStays s (s.putFork G) := by
  intro a ha
  exact ⟨{ a with F := G }, by simp [Desc.First.S.putFork, ha], fun _ _ => rfl⟩

theorem putTl_layStays (s : Desc.First.S) (tl : HTailF2) : LayStays s (s.putTl tl) := by
  intro a ha
  exact ⟨{ a with tl := tl }, by simp [Desc.First.S.putTl, ha], fun _ _ => rfl⟩

theorem headClaim_layStays (s : Desc.First.S) (a : Desc.First.HeadOwn) (c : WsClaim)
    (ha : s.here = .head a) :
    LayStays s { s with here := .head { a with claim := some c } } := by
  intro a₀ h₀
  rw [ha] at h₀
  cases h₀

theorem putDigits_layStays {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) (g : Forest.Heard)
    (F Gk : Fork) (hF : (Desc.K3.seatDigits claim).fork s = some F) :
    LayStays s ((Desc.K3.seatDigits claim).put s g Gk) := by
  intro a ha
  have hF' : s.fork? = some F := hF
  have htl : s.tl? = some a.tl := by simp [Desc.First.S.tl?, ha]
  have e : (Desc.K3.seatDigits claim).put s g Gk =
      (s.putTl { a.tl with
        foldDrawn := a.tl.foldDrawn + 1, slotA := F.next, slotB := Gk.next,
        heard := some g }).putFork Gk := by
    simp only [Desc.K3.seatDigits, htl, hF']
  rw [e]
  exact (putTl_layStays s _).trans (putFork_layStays _ _) a ha

theorem k3_digits_layStays {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') : LayStays s s' := by
  obtain ⟨F, y, hF, -, -, rfl⟩ := decide_ok _ piece laid before p guests s s' rs cols h
  exact putDigits_layStays claim s y.1 F y.2 hF

/-- **An accept of the whole seated sub-protocol.** -/
theorem k3_digits_step_layStays {Cl : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) : LayStays s s₂ := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  have hS := k3_digits_layStays claim a.piece laid sent _ [] s s' _ gs' hyes
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact hS
  · unfold Desc.K3.quietAt at hf
    simp only [if_true] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨ah, c, ha, -, e⟩ := Desc.K3.quietHead_ok X s' s₂ hfs
      rw [e]
      exact hS.trans (headClaim_layStays s' ah c ha)
    · split at hf <;> split at hf <;>
        (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
         obtain ⟨F, -, -, e⟩ := Desc.K3.quietDigits_ok _ _ s' s₂ hfs
         exact hS.trans (e ▸ putFork_layStays s' _))

/-- The two are one but for tl, F. -/
def AttKept (a a' : Desc.First.AttOwn) : Prop :=
  ∀ (tl : HTailF2) (F : Fork),
    ({ a' with tl := tl, F := F } : Desc.First.AttOwn) = { a with tl := tl, F := F }

/-- Where s stands in such a segment, s' does, and the part is kept but for the two. -/
def AttStays (s s' : Desc.First.S) : Prop :=
  ∀ a, s.here = .att a → ∃ a', s'.here = .att a' ∧ AttKept a a'

theorem AttStays.trans {s t u : Desc.First.S} (h : AttStays s t) (h' : AttStays t u) :
    AttStays s u := by
  intro a ha
  obtain ⟨a', h1, k1⟩ := h a ha
  obtain ⟨a'', h2, k2⟩ := h' a' h1
  exact ⟨a'', h2, fun tl F => (k2 tl F).trans (k1 tl F)⟩

theorem putFork_attStays (s : Desc.First.S) (G : Fork) : AttStays s (s.putFork G) := by
  intro a ha
  exact ⟨{ a with F := G }, by simp [Desc.First.S.putFork, ha], fun _ _ => rfl⟩

theorem putTl_attStays (s : Desc.First.S) (tl : HTailF2) : AttStays s (s.putTl tl) := by
  intro a ha
  exact ⟨{ a with tl := tl }, by simp [Desc.First.S.putTl, ha], fun _ _ => rfl⟩

theorem headClaim_attStays (s : Desc.First.S) (a : Desc.First.HeadOwn) (c : WsClaim)
    (ha : s.here = .head a) :
    AttStays s { s with here := .head { a with claim := some c } } := by
  intro a₀ h₀
  rw [ha] at h₀
  cases h₀

theorem putDigits_attStays {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) (g : Forest.Heard)
    (F Gk : Fork) (hF : (Desc.K3.seatDigits claim).fork s = some F) :
    AttStays s ((Desc.K3.seatDigits claim).put s g Gk) := by
  intro a ha
  have hF' : s.fork? = some F := hF
  have htl : s.tl? = some a.tl := by simp [Desc.First.S.tl?, ha]
  have e : (Desc.K3.seatDigits claim).put s g Gk =
      (s.putTl { a.tl with
        foldDrawn := a.tl.foldDrawn + 1, slotA := F.next, slotB := Gk.next,
        heard := some g }).putFork Gk := by
    simp only [Desc.K3.seatDigits, htl, hF']
  rw [e]
  exact (putTl_attStays s _).trans (putFork_attStays _ _) a ha

theorem k3_digits_attStays {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') : AttStays s s' := by
  obtain ⟨F, y, hF, -, -, rfl⟩ := decide_ok _ piece laid before p guests s s' rs cols h
  exact putDigits_attStays claim s y.1 F y.2 hF

/-- **An accept of the whole seated sub-protocol.** -/
theorem k3_digits_step_attStays {Cl : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) : AttStays s s₂ := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  have hS := k3_digits_attStays claim a.piece laid sent _ [] s s' _ gs' hyes
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact hS
  · unfold Desc.K3.quietAt at hf
    simp only [if_true] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨ah, c, ha, -, e⟩ := Desc.K3.quietHead_ok X s' s₂ hfs
      rw [e]
      exact hS.trans (headClaim_attStays s' ah c ha)
    · split at hf <;> split at hf <;>
        (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
         obtain ⟨F, -, -, e⟩ := Desc.K3.quietDigits_ok _ _ s' s₂ hfs
         exact hS.trans (e ▸ putFork_attStays s' _))

section
variable {Cl : Type}

/-- **What attention's own rounds handed on is one.** -/
theorem digits_step_heard5 (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    {x : Desc.First.Look.Place} (hlook : lookAt X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) : s₂.heard5? = s.heard5? := by
  have T := (k3_digits_step_turns claim readers X codes shape a B h hOk i hi hpc hlook hsh s s₂ rs
    gs hd).1
  have A := k3_digits_step_attStays claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  unfold Desc.First.S.heard5?
  rcases T.sort with ⟨u, u', e, e'⟩ | ⟨u, u', e, e'⟩ | ⟨u, u', e, e', -, -⟩
  · rw [e, e']
  · obtain ⟨w, hw, k⟩ := A u e
    rw [e, hw]
    exact congrArg (·.heard5) (k u.tl u.F)
  · rw [e, e']

/-- **What the sub-proof has left for its row is one.** -/
theorem digits_step_leftOf (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    {x : Desc.First.Look.Place} (hlook : lookAt X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) :
    Johnson.Desc.First.Walk.Law.leftOf s₂ = Johnson.Desc.First.Walk.Law.leftOf s := by
  have T := (k3_digits_step_turns claim readers X codes shape a B h hOk i hi hpc hlook hsh s s₂ rs
    gs hd).1
  have Ly := k3_digits_step_layStays claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  have Hd := k3_digits_step_headStays claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  unfold Johnson.Desc.First.Walk.Law.leftOf Johnson.Desc.First.Walk.leftLay
    Desc.First.Close.leftHead
  rcases T.sort with ⟨u, u', e, e'⟩ | ⟨u, u', e, e'⟩ | ⟨u, u', e, e', -, -⟩
  · obtain ⟨w, hw, k⟩ := Ly u e
    rw [e, hw]
    have eo : w.own = u.own := congrArg (·.own) (k u.tl u.F)
    simp only [eo]
  · rw [e, e']
  · obtain ⟨w, hw, k⟩ := Hd u e
    rw [e, hw]
    have eo : w.wo = u.wo := congrArg (·.wo) (k u.tl u.F u.claim)
    simp only [eo]

/-- **«Can the pending claim be made» has one value.** -/
theorem digits_step_hasRow (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    {x : Desc.First.Look.Place} (hlook : lookAt X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) (lay : WsLay) (n : ℕ) (lin : Params.LinShape) :
    Johnson.Desc.First.Walk.Law.hasRow lay n lin s₂ =
      Johnson.Desc.First.Walk.Law.hasRow lay n lin s := by
  have T := (k3_digits_step_turns claim readers X codes shape a B h hOk i hi hpc hlook hsh s s₂ rs
    gs hd).1
  unfold Johnson.Desc.First.Walk.Law.hasRow Johnson.Desc.First.Walk.Law.rowAt
    Johnson.Desc.First.Walk.Law.rowBy
  rw [digits_step_leftOf claim readers X codes shape a B h hOk i hi hpc hlook hsh s s₂ rs gs hd,
    T.out, T.st]

/-- **The heard reply is one.** -/
theorem digits_step_reply (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    {x : Desc.First.Look.Place} (hlook : lookAt X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) : s₂.out.reply = s.out.reply := by
  rw [(k3_digits_step_turns claim readers X codes shape a B h hOk i hi hpc hlook hsh s s₂ rs gs
    hd).1.out]

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_layStays
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_attStays
#print axioms VerifiableInference.OnPublicFiles.digits_step_heard5
#print axioms VerifiableInference.OnPublicFiles.digits_step_leftOf
#print axioms VerifiableInference.OnPublicFiles.digits_step_hasRow
#print axioms VerifiableInference.OnPublicFiles.digits_step_reply
