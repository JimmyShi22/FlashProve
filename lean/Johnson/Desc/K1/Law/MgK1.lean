-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/MgK1.lean: K01_law: K1's OWN PREMISES ON THE MEANING, GATHERED IN ONE STRUCTURE OVER A LETTER Mg (the discipline: a kind's files prove KindTied under their own premises over a letter Mg, gathered in one
structure; the composed meaning's files are to give, for each kind, one lemma "these premises hold at mgAll"), AND WHAT OF FillL (Johnson/Desc/K1/Law/KeepAtLater.lean) FOLLOWS FROM THEM.
  MgK1 cs G arr smp ms decT Mg     six equations on Mg's fields: held · shown · noColl · pin · decodes · pinW: each is mgAll's own field lemma's right side (mgAll_held | _shown | _noColl | _pin | _decodes | _pinW, all by rfl)
  LaterFacts B                     what is asked of a later block's text beside block_tied's four: a yes keeps every sampled message (SmpStay) and lets the book grow at its end alone
  SmpLeft B smp ms O | DecLeft B decT    what is asked of the two letters smp and decT: the block's own yes leaves the sample of every member that sits at a tenant open in front; and the stored table's decoding
  fill_held      PAID from MgK1.held · LaterFacts · smpHeldStays (K1/Law/SmpHeldStays.lean)
  fill_shown     PAID from MgK1.shown · shownJT_col (Johnson/Desc/Sound/ReadsTreeAt.lean)
  fill_noColl    BROUGHT DOWN TO SmpLeft, by MgK1.noColl · noCollJT_col
  fill_decodes   BROUGHT DOWN TO DecLeft, by MgK1.decodes
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.KeepAtLater
import Johnson.Desc.K1.Law.SmpHeldStays
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Sound.ReadsTreeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open VerifiableInference.Desc.Sound (Sending Mem SitsAt MsgT shownJT noCollJT pinJT decodesOf
  pinWOf shownJT_col noCollJT_col)
open Cb Johnson.Pack
open VerifiableInference.Desc.K13.Law (OldKept)

variable {Pp Xi Cells Tok : Type}

/-- **K1's premises on the meaning.** -/
structure MgK1 (cs : Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) : Prop where
  held : Mg.held = fun j t a => smpHeld a.2.st a.2.book j t
  shown : Mg.shown = shownJT cs G ms
  noColl : Mg.noColl = noCollJT cs G smp ms
  pin : Mg.pin = pinJT cs G arr smp ms
  decodes : Mg.decodes = decodesOf decT
  pinW : Mg.pinW = pinWOf decT

/-- What is asked of a later block's text, beside block_tied's four facts. -/
structure LaterFacts (B : Block S Unit) : Prop where
  rounds : B.rounds.length = 2
  smpStay : ∀ s s' r₁ r₂ gs, B.decide s [r₁, r₂] gs = .ok s' → SmpStay s.st s'.st
  grows : ∀ s s' r₁ r₂ gs, B.decide s [r₁, r₂] gs = .ok s' →
    ∃ more, s'.book.place = s.book.place ++ more

/-- The block's own yes, where it declares two rounds, is a yes on two rounds. -/
theorem YesOf.two {B : Block S Unit} {x x' : Pp × S} (h : YesOf B x x') (hl : B.rounds.length = 2) :
    ∃ r₁ r₂ gs, B.decide x.2 [r₁, r₂] gs = .ok x'.2 := by
  obtain ⟨_, rs, gs, hf, hd⟩ := h
  have hl' : (rs.map noDigest).length = 2 := by
    rw [List.length_map, K13.Law.roundsFit_length _ _ hf, hl]
  obtain ⟨r₁, r₂, e⟩ : ∃ r₁ r₂, rs.map noDigest = [r₁, r₂] := by
    match rs.map noDigest, hl' with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [e] at hd
  exact ⟨r₁, r₂, gs, hd⟩

/-- The block's own yes, FROM INSIDE In (the promise in front: it says where the book and the statement stand), leaves the sample of every member that sits at a tenant of the list T. (Without In it cannot be met at the
named reader smpNamed (Johnson/Desc/Sound/SmpNamed.lean): «the member's number lies below the number of messages in front» wants bookAt.) -/
def SmpLeft (cs : Codes) (B : Block S Unit) (In : Pp × S → Strs → Prop)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (T : List (ℕ × ℕ)) : Prop :=
  ∀ x x' y, YesOf B x x' → In x y → ∀ u ∈ T, ∀ m ∈ ms, SitsAt m u.1 u.2 →
    smp x' m.1 m.2 = smp x m.1 m.2

/-- The block's own yes leaves the stored table's decoding. -/
def DecLeft (B : Block S Unit) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) :
    Prop :=
  ∀ x x' c, YesOf B x x' → decT c x' = decT c x

section
variable {cs : Codes} {G : FileDescription Xi} {arr : ℕ → ℕ → ℕ}
  {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
  {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
  {Mg : Meaning Pp (Wit Cells Tok MsgT)}

theorem fill_held (h : MgK1 cs G arr smp ms decT Mg) {B : Block S Unit} (hB : LaterFacts B)
    (x x' : Pp × S) (hy : YesOf B x x') (u : ℕ × ℕ) (h0 : Mg.held u.1 u.2 x = true) :
    Mg.held u.1 u.2 x' = true := by
  rw [h.held] at h0 ⊢
  obtain ⟨r₁, r₂, gs, hd⟩ := hy.two hB.rounds
  obtain ⟨more, hm⟩ := hB.grows _ _ _ _ _ hd
  exact (smpHeldStays _ _ _ _ more u.1 u.2 (hB.smpStay _ _ _ _ _ hd) hm h0).2.2.2

theorem fill_shown (h : MgK1 cs G arr smp ms decT Mg) (y y' : Strs) (u : ℕ × ℕ)
    (hk : OldKept u.1 y y') (h0 : Mg.shown u.1 u.2 y) : Mg.shown u.1 u.2 y' := by
  rw [h.shown] at h0 ⊢
  exact shownJT_col cs G ms u.1 u.2 y y' hk.2 h0

theorem fill_noColl (h : MgK1 cs G arr smp ms decT Mg) {B : Block S Unit} {T : List (ℕ × ℕ)}
    {In : Pp × S → Strs → Prop} (hS : SmpLeft cs B In smp ms T) (x x' : Pp × S)
    (hy : YesOf B x x') (y y' : Strs) (hIn : In x y) (u : ℕ × ℕ)
    (hu : u ∈ T) (hk : OldKept u.1 y y') (h0 : Mg.noColl u.1 u.2 x y) :
    Mg.noColl u.1 u.2 x' y' := by
  rw [h.noColl] at h0 ⊢
  have h1 := noCollJT_col cs G smp ms u.1 u.2 x y y' hk.2 h0
  intro m hm hs
  obtain ⟨z, hz, a, b⟩ := h1 m hm hs
  exact ⟨z, (hS x x' y hy hIn u hu m hm hs).trans hz, a, b⟩

theorem fill_decodes (h : MgK1 cs G arr smp ms decT Mg) {B : Block S Unit} (hD : DecLeft B decT)
    (x x' : Pp × S) (hy : YesOf B x x') (y y' : Strs) (hc : y'.cell = y.cell)
    (h0 : Mg.decodes x y) : Mg.decodes x' y' := by
  rw [h.decodes] at h0 ⊢
  unfold decodesOf at h0 ⊢
  rw [hc, hD x x' _ hy]
  exact h0

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.fill_held
#print axioms VerifiableInference.Desc.K1.fill_shown
#print axioms VerifiableInference.Desc.K1.fill_noColl
#print axioms VerifiableInference.Desc.K1.fill_decodes
