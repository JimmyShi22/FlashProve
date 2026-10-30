-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3At.lean (IN TWO: K3At HAS EIGHT FIELDS; the two on the
door's name «frame.liveIs» stand apart in K3AtLive: with them the structure could be met at no
filling whose door lacks that name): the kind "lookup" (K3): WHAT THE LOOKUPS' THEOREMS AT THE TABLE
OF JOINTS SPEND OF THEIR OWN LAYER OF THE FILLING, AS ONE STRUCTURE OVER A LETTER Mg: K3At X D L Mg:
at K3's own items and fields Mg says what the lookups' layer says (fillK3All, K3FillWorth.lean). So
the theorems meet a composed meaning in which other layers stand over the lookups' one. Definitions,
statements, proofs. NO SOUNDNESS IS CLAIMED.

Main names.
  K3At X D L Mg: eight fields: pub at lookIn, lookOut (at K3.pieceAt's two pieces of every segment),
    linkFresh, left, leftOn · pubP at left, leftOn · worth is worthK3 X D L f for some f.
  worthK3_digits: the field's term at the digits' piece. k3At_fill: K3At holds at fillK3All X D L
    Mg₀, for every Mg₀; k3At_wide: and at fillK3Wide X D L Mg₀.
  K3AtLive D Mg: two fields: pub at liveItem is liveIsB D · the door's rows at both lookups' places
    ask liveName. k3AtLive_fill: it holds at fillK3Wide X D L Mg₀. fLive_at: under it.
  THE ROWS' PREMISES UNDER IT: fLook_at, fOut_at (both sorts) · fPl_at, fKe_at · THE WAY BACK, for
    whoever closes the two items: fPl_back, fKe_back (the sentence gives worth "planes", "keys" at
    the digits' piece).
OBJECT. No sub-protocol's text: Meaning (Johnson/Desc/First/Borders.lean).
USER. k3_digits_seatLaws_at (K3DigitsAtFill.lean), k3_digits_behind_at (K3DigitsBehind.lean) and
what stands on them. At a composed term: k3At_mgAll (Johnson/Desc/Sound/MgAt/K3At.lean).
LETTERS. X, D, L, Mg.
IS IT EMPTY? No: k3At_fill.

Compiled with the whole library.
Limits. That a composed term meets it is other files' to show (each field: «the layers above hand
the item on»).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3FillWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning ModelPart shift)
open VerifiableInference.Desc (Strs)

section
variable {P Cells Tok : Type} (X : Verify.Public) (D : Desc.First.Look.Sent)
  (L : K3Letters Cells Tok)

/-- **AT K3's OWN ITEMS AND FIELDS Mg SAYS WHAT THE LOOKUPS' LAYER SAYS.** -/
structure K3At (Mg : Meaning P (Desc.Wit Cells Tok MsgT)) : Prop where
  lookIn : ∀ m dg a, Mg.pub (.lookIn m (Desc.K3.pieceAt X m dg)) a = k3LookInAt X D m dg a.2
  lookOut : ∀ m dg a, Mg.pub (.lookOut m (Desc.K3.pieceAt X m dg)) a = k3OnOutAt X m dg a.2
  linkFresh : ∀ m a, Mg.pub (.linkFresh m) a = linkFreshB (D.arrayOf.getD m #[]) a.2
  left : ∀ m a, Mg.pub (.left m) a = true
  leftOn : ∀ m a, Mg.pub (.leftOn m) a = true
  pLeft : ∀ m a, Mg.pubP (.left m) a = k3LeftItemAt X m a.2
  pLeftOn : ∀ m a, Mg.pubP (.leftOn m) a = k3LeftOnItemAt X m a.2
  worth : ∃ f, Mg.worth = worthK3 X D L f

/-- **WHAT IS SAID OF THE DOOR's NAME "frame.liveIs"**: apart, because a filling whose door lacks
the name cannot meet it. -/
structure K3AtLive (Mg : Meaning P (Desc.Wit Cells Tok MsgT)) : Prop where
  live : ∀ m a, Mg.pub (liveItem m) a = liveIsB D a.2
  asks : ∀ (links : List ModelPart) (a : Desc.Place) (i : ℕ) (sub : ModelPart), a.link = some i →
    links[i]? = some sub → (a.piece = 2 + shift sub ∨ a.piece = 7 + shift sub) →
    liveName i ∈ (Mg.more.rows links a).asks

/-- The field's term at the digits' piece of a segment. -/
theorem worthK3_digits
    (f : ℕ → ℕ → String → P × Desc.First.S → Strs → Desc.Wit Cells Tok MsgT → Prop) (m : ℕ)
    {x : Desc.First.Look.Place} {tl : HTailF2} (hx : digAt X m = some (x, tl)) (r : String)
    (a : P × Desc.First.S) (y : Strs) (w : Desc.Wit Cells Tok MsgT) :
    worthK3 X D L f m (Desc.K3.pieceAt X m true) r a y w =
      worthDig D L x tl r a.2 w (f m (Desc.K3.pieceAt X m true) r a y w) := by
  unfold worthK3
  rw [sort_digits, hx]

/-- **It holds at the lookups' own layer.** -/
theorem k3At_fill (Mg₀ : Meaning P (Desc.Wit Cells Tok MsgT)) :
    K3At X D L (fillK3All X D L Mg₀) :=
  ⟨fun m dg a => fill_lookIn X D Mg₀ m dg a, fun m dg a => fill_lookOut X D Mg₀ m dg a,
    fun m a => fill_linkFresh X D Mg₀ m a, fun m a => fill_left X D Mg₀ m a,
    fun m a => fill_leftOn X D Mg₀ m a,
    fun m a => fill_pubP_left X D Mg₀ m a, fun m a => fill_pubP_leftOn X D Mg₀ m a, ⟨_, rfl⟩⟩

/-- And at the wider term, with the thin layer for the name over it. -/
theorem k3At_wide (Mg₀ : Meaning P (Desc.Wit Cells Tok MsgT)) :
    K3At X D L (fillK3Wide X D L Mg₀) :=
  ⟨fun m dg a => fill_lookIn X D Mg₀ m dg a, fun m dg a => fill_lookOut X D Mg₀ m dg a,
    fun m a => fill_linkFresh X D Mg₀ m a, fun m a => fill_left X D Mg₀ m a,
    fun m a => fill_leftOn X D Mg₀ m a,
    fun m a => fill_pubP_left X D Mg₀ m a, fun m a => fill_pubP_leftOn X D Mg₀ m a, ⟨_, rfl⟩⟩

/-- **The two on the name hold at the wider term.** -/
theorem k3AtLive_fill (Mg₀ : Meaning P (Desc.Wit Cells Tok MsgT)) :
    K3AtLive D (fillK3Wide X D L Mg₀) :=
  ⟨fun m a => fill_live X D (fillK3All X D L Mg₀) m a,
    fun links a i sub hl hs hp => hAsk_fill X D (fillK3All X D L Mg₀) links a i sub hl hs hp⟩

/-- **fLive.** -/
theorem fLive_at {D : Desc.First.Look.Sent} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)}
    (hV : K3AtLive D Mg) (m : ℕ) (z : P) (s : Desc.First.S) :
    Mg.pub (liveItem m) (z, s) = true ↔ LiveIs D s := by
  rw [hV.live]
  exact liveIsB_iff D s

variable {X D L} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} (hK : K3At X D L Mg)
include hK

/-- **fLook | pubIn.** -/
theorem fLook_at (m : ℕ) (dg : Bool) {x : Desc.First.Look.Place} (hlook : lookAt X m dg = some x)
    (z : P) (s : Desc.First.S)
    (h : Mg.pub (.lookIn m (Desc.K3.pieceAt X m dg)) (z, s) = true) :
    k3LookIn (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) dg x)
      (D.arrayOf.getD x.link #[]) s = true := by
  rw [hK.lookIn] at h
  unfold k3LookInAt placeAt at h
  rw [hlook] at h
  rw [lookAt_link hlook]
  exact h

/-- **fOut.** -/
theorem fOut_at (m : ℕ) (dg : Bool) {x : Desc.First.Look.Place} (hlook : lookAt X m dg = some x)
    (z : P) (s : Desc.First.S)
    (h : Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) dg x) s = true) :
    Mg.pub (.lookOut m (Desc.K3.pieceAt X m dg)) (z, s) = true := by
  rw [hK.lookOut]
  unfold k3OnOutAt placeAt
  rw [hlook]
  exact h

/-- **fPl.** -/
theorem fPl_at {Cl : Type} (claim : Aff → Cl) (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : Mg.worth m (Desc.K3.pieceAt X m true) "planes" (z, s) y w) :
    ∀ g F', (Desc.K3.seatDigits claim).fork s = some F' →
      (Desc.K3.seatDigits claim).heard s = some g →
      K3OutPlanes tl.f9 5 x.F.next
        (digNu x tl D L.rad (fun j => L.seat x.link true j.1) L.arr w) Reading.gl g F' := by
  obtain ⟨f, hf⟩ := hK.worth
  rw [hf, worthK3_digits X D L f m hx] at h
  unfold worthDig at h
  rw [if_pos rfl] at h
  exact h

/-- **fPl, the way back.** -/
theorem fPl_back {Cl : Type} (claim : Aff → Cl) (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : ∀ g F', (Desc.K3.seatDigits claim).fork s = some F' →
      (Desc.K3.seatDigits claim).heard s = some g →
      K3OutPlanes tl.f9 5 x.F.next
        (digNu x tl D L.rad (fun j => L.seat x.link true j.1) L.arr w) Reading.gl g F') :
    Mg.worth m (Desc.K3.pieceAt X m true) "planes" (z, s) y w := by
  obtain ⟨f, hf⟩ := hK.worth
  rw [hf, worthK3_digits X D L f m hx]
  unfold worthDig
  rw [if_pos rfl]
  exact h

/-- **fKe.** -/
theorem fKe_at {Cl : Type} (claim : Aff → Cl) (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : Mg.worth m (Desc.K3.pieceAt X m true) "keys" (z, s) y w) :
    ∀ g F', (Desc.K3.seatDigits claim).fork s = some F' →
      (Desc.K3.seatDigits claim).heard s = some g →
      K3OutKeys tl.f9 5 x.F.next
        (digNu x tl D L.rad (fun j => L.seat x.link true j.1) L.arr w)
        (forK Cb.Gl.E (DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
          (zext (digMu x D L.rad (fun j => L.seat x.link true j.1) L.arr w))) Reading.gl g F' := by
  obtain ⟨f, hf⟩ := hK.worth
  rw [hf, worthK3_digits X D L f m hx] at h
  unfold worthDig at h
  rw [if_neg (by decide), if_pos rfl] at h
  exact h

/-- **fKe, the way back.** -/
theorem fKe_back {Cl : Type} (claim : Aff → Cl) (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : ∀ g F', (Desc.K3.seatDigits claim).fork s = some F' →
      (Desc.K3.seatDigits claim).heard s = some g →
      K3OutKeys tl.f9 5 x.F.next
        (digNu x tl D L.rad (fun j => L.seat x.link true j.1) L.arr w)
        (forK Cb.Gl.E (DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
          (zext (digMu x D L.rad (fun j => L.seat x.link true j.1) L.arr w))) Reading.gl g F') :
    Mg.worth m (Desc.K3.pieceAt X m true) "keys" (z, s) y w := by
  obtain ⟨f, hf⟩ := hK.worth
  rw [hf, worthK3_digits X D L f m hx]
  unfold worthDig
  rw [if_neg (by decide), if_pos rfl]
  exact h

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.worthK3_digits
#print axioms VerifiableInference.OnPublicFiles.k3At_fill
#print axioms VerifiableInference.OnPublicFiles.k3At_wide
#print axioms VerifiableInference.OnPublicFiles.k3AtLive_fill
#print axioms VerifiableInference.OnPublicFiles.fLive_at
#print axioms VerifiableInference.OnPublicFiles.fLook_at
#print axioms VerifiableInference.OnPublicFiles.fOut_at
#print axioms VerifiableInference.OnPublicFiles.fPl_at
#print axioms VerifiableInference.OnPublicFiles.fKe_at
#print axioms VerifiableInference.OnPublicFiles.fPl_back
#print axioms VerifiableInference.OnPublicFiles.fKe_back
