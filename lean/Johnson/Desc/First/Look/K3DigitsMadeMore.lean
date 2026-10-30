-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsMadeMore.lean: the lookup on the digits of a segment's approximate
range proof: THREE SORTS MORE OF THE COMPOSED MEANING's PUBLIC TESTS (pubAll D base) THAT AN ACCEPT
OF THE WHOLE SEATED SUB-PROTOCOL KEEPS (the first four: K3DigitsMade.lean): hasRow · tokenSmall ·
the name "K5.okAt". At the sub-protocol's own decide, whatever the rounds' words. NO SOUNDNESS IS
CLAIMED.

Main names.
  digits_keeps_hasRow: hasRow m: by digits_step_hasRow (K3DigitsOwnStays.lean).
    digits_keeps_tokenSmall: tokenSmall: it reads the heard reply alone (digits_step_reply).
  stretchB_mono, formB_mono, sumB_mono, heardSlotsB_mono: attention's files' tests «these slots
    are filled» (Johnson/Desc/First/Att/Door/OkThereB.lean) go from a ledger to one in which every
    slot that was filled is filled.
  digits_keeps_okAt: "K5.okAt" at an attention segment: the ledger behind has its sizes and is a
    later one (DigLeft: k3_digits_step_leaves) · what attention's own rounds handed on is one
    (digits_step_heard5).
NOT HERE, BY NAME: "K5.plain", "K5.readsThere" (each reads the ledger's list of arrays: that the
accept leaves it is a lemma of another file, not shown here) (Where this and
lean/THEOREM.md differ, the page holds.) · formsIn.
NO FACT ALONG THE FOLD IS SPENT BY ANY LEMMA OF THIS FILE.
OBJECT. Desc.K3.theStated's value at the digits' address; pubAll D base.
USER. Johnson/Desc/Sound/MgAt/K3DigitsOthers.lean calls digits_keeps_hasRow, digits_keeps_okAt.
LETTERS. D, base; claim, readers, codes, shape, a, B, i; z, s, s₂, rs, gs; x, hs; m.
IS IT EMPTY? The premises are an .ok of decide, the place and a test in front.



Compiled with the whole library.
Limits. One way each.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsOwnStays
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Pub PubData pubAll pubAll_hasRow pubAll_tokenSmall
  pubAll_more_okAt)
open H2K5.Door (stretchB formB sumB heardSlotsB okThereB)

section
variable {U G : Fork} (hk : ∀ j, U.gotF.getD j false = true → G.gotF.getD j false = true)
include hk

theorem stretchB_mono (a n : ℕ) (h : stretchB U a n = true) : stretchB G a n = true := by
  unfold stretchB at h ⊢
  exact List.all_eq_true.2 fun i hi => hk _ (List.all_eq_true.1 h i hi)

theorem formB_mono (f : Aff) (h : formB U f = true) : formB G f = true := by
  unfold formB at h ⊢
  exact List.all_eq_true.2 fun i hi => hk _ (List.all_eq_true.1 h i hi)

theorem sumB_mono (hh : Desc.Part.MaskedSum.Heard) (n : ℕ) (h : sumB U hh n = true) :
    sumB G hh n = true := by
  unfold sumB at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨formB_mono hk _ h.1.1, stretchB_mono hk _ _ h.1.2⟩, stretchB_mono hk _ _ h.2⟩

theorem heardSlotsB_mono (g : Desc.First.Att.P.Geo) (e : Desc.First.Att.P.Heard)
    (h : heardSlotsB U g e = true) : heardSlotsB G g e = true := by
  unfold heardSlotsB at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩,
    c15⟩, c16⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨
    List.all_eq_true.2 fun j hj => stretchB_mono hk _ _ (List.all_eq_true.1 c1 j hj),
    List.all_eq_true.2 fun j hj => stretchB_mono hk _ _ (List.all_eq_true.1 c2 j hj)⟩,
    List.all_eq_true.2 fun j hj => sumB_mono hk _ _ (List.all_eq_true.1 c3 j hj)⟩,
    stretchB_mono hk _ _ c4⟩, stretchB_mono hk _ _ c5⟩, stretchB_mono hk _ _ c6⟩,
    stretchB_mono hk _ _ c7⟩, stretchB_mono hk _ _ c8⟩, sumB_mono hk _ _ c9⟩,
    sumB_mono hk _ _ c10⟩, sumB_mono hk _ _ c11⟩, sumB_mono hk _ _ c12⟩, sumB_mono hk _ _ c13⟩,
    sumB_mono hk _ _ c14⟩, c15⟩, c16⟩

end

section
variable {P Cl : Type} (D : PubData) (base : Pub → P × Desc.First.S → Bool)

/-- **hasRow: kept.** -/
theorem digits_keeps_hasRow (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers D.d3.X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt D.d3.X i true)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂)
    {x : Desc.First.Look.Place} (hlook : lookAt D.d3.X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf D.d3.X.P.frame) true x).shape = some hs)
    (m : ℕ) (hin : pubAll D base (.hasRow m) (z, s) = true) :
    pubAll D base (.hasRow m) (z, s₂) = true := by
  rw [pubAll_hasRow] at hin ⊢
  show Johnson.Desc.First.Walk.Law.hasRow D.d1.lay (D.d1.ncl m) D.d1.lin s₂ = true
  rw [digits_step_hasRow claim readers D.d3.X codes shape a B h hOk i hi hpc hlook hsh s s₂ rs gs
    hd]
  exact hin

/-- **tokenSmall: kept.** -/
theorem digits_keeps_tokenSmall (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers D.d3.X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt D.d3.X i true)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂)
    {x : Desc.First.Look.Place} (hlook : lookAt D.d3.X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf D.d3.X.P.frame) true x).shape = some hs)
    (hin : pubAll D base .tokenSmall (z, s) = true) :
    pubAll D base .tokenSmall (z, s₂) = true := by
  have e : s₂.out.reply = s.out.reply :=
    digits_step_reply claim readers D.d3.X codes shape a B h hOk i hi hpc hlook hsh s s₂ rs gs hd
  have e2 : Desc.Kinds.Reply.token (Desc.Kinds.Head.seatAt D.hShape D.iU3).toSeat s₂ =
      Desc.Kinds.Reply.token (Desc.Kinds.Head.seatAt D.hShape D.iU3).toSeat s := by
    unfold Desc.Kinds.Reply.token
    show Option.map _ s₂.out.reply = Option.map _ s.out.reply
    rw [e]
  rw [pubAll_tokenSmall] at hin ⊢
  have h0 : Desc.Kinds.Head.tokenHeardB D.hShape D.iU3 s = true := hin
  show Desc.Kinds.Head.tokenHeardB D.hShape D.iU3 s₂ = true
  unfold Desc.Kinds.Head.tokenHeardB at h0 ⊢
  rw [e2]
  exact h0

/-- **"K5.okAt": kept.** -/
theorem digits_keeps_okAt (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers D.d3.X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt D.d3.X i true)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂)
    {x : Desc.First.Look.Place} (hlook : lookAt D.d3.X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf D.d3.X.P.frame) true x).shape = some hs)
    (m : ℕ) (hm : D.d5.isAtt m = true)
    (hin : pubAll D base (.more (some m) "K5.okAt") (z, s) = true) :
    pubAll D base (.more (some m) "K5.okAt") (z, s₂) = true := by
  obtain ⟨F, Gk, hF, hG, -, hZ, -⟩ :=
    k3_digits_step_leaves claim readers D.d3.X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  have e5 := digits_step_heard5 claim readers D.d3.X codes shape a B h hOk i hi hpc hlook hsh s s₂
    rs gs hd
  rw [pubAll_more_okAt D base m hm] at hin ⊢
  cases hA : D.d5.W.A[m / 2]? with
  | none =>
    rw [hA] at hin
    cases hin
  | some p =>
    rw [hA] at hin
    have h1 : okThereB (Desc.First.Att.P.geoOf p.S) s = true := hin
    show okThereB (Desc.First.Att.P.geoOf p.S) s₂ = true
    unfold okThereB at h1 ⊢
    rw [hG, e5]
    rw [hF] at h1
    cases h5 : s.heard5? with
    | none =>
      rw [h5] at h1
      cases h1
    | some e =>
      rw [h5] at h1
      have h2 : (H2K5.Door.sizedB F && heardSlotsB F (Desc.First.Att.P.geoOf p.S) e) = true := h1
      obtain ⟨z1, z2⟩ := Eq.mp (Bool.and_eq_true _ _) h2
      have hS : OnBytes.PscRun.Sized F := by
        simp only [H2K5.Door.sizedB, Bool.and_eq_true, beq_iff_eq] at z1
        exact ⟨z1.1.1, z1.1.2, z1.2⟩
      obtain ⟨hLat, ⟨y1, y2, y3⟩, -⟩ := hZ hS
      show (H2K5.Door.sizedB Gk && heardSlotsB Gk (Desc.First.Att.P.geoOf p.S) e) = true
      refine Eq.mpr (Bool.and_eq_true _ _)
        ⟨?_, heardSlotsB_mono (fun j hj => (hLat.keep j hj).1) _ _ z2⟩
      simp [H2K5.Door.sizedB, y1, y2, y3]

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.heardSlotsB_mono
#print axioms VerifiableInference.OnPublicFiles.digits_keeps_hasRow
#print axioms VerifiableInference.OnPublicFiles.digits_keeps_tokenSmall
#print axioms VerifiableInference.OnPublicFiles.digits_keeps_okAt
