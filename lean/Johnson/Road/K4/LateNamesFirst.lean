-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/LateNamesFirst.lean: names, late entries and forms at which the library's four
records of the first group, NormsOkF, TermsOkF, GatedOkF and EmbOkF
(Cb/Pv/Lay/End/LayFirst.lean), hold, but for their clauses on sizes.

Johnson/Road/K4/LateNames.lean fills the free letters of the theorem on the end of the chain of a
later group. The first group's chain has one share more: the claim on the stream that comes in, with
names of its own (EmbNm). Here the letters of that theorem are filled alike: the three shares' names
with the embedding's beside them.

Main names:
  `Nm4`: the four shares' names, side by side. `J4 N`: J3 N, and two numbers up to N.
  `lateF N`: which late entry has which name; good: the name's numbers are at most N.
  `fmOfF`: the form of each name: what the late entry is meant to be.
  `roomF`: a number N that has room for all names in range.
  `normsOkF_of`, `termsOkF_of`, `gatedOkF_of`, `embOkF_of`: the four records, from their clauses on
    sizes alone.
Limits. A filling of letters: the forms are the library's own by definition, so the clauses hfm hold
by definition. The clauses on sizes stay premises. Nothing on a program's reads, on a run, on
soundness or on hiding.


-/
import Johnson.Road.K4.LateNames
import Cb.Pv.Lay.End.LayFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Arr lDd lF lFe)

/-- The names of the four shares, side by side. -/
abbrev Nm4 : Type := Nm3 ⊕ EmbNm

/-- The late entries: those of the three shares, and two numbers up to N for the embedding's. -/
abbrev J4 (N : ℕ) : Type := J3 N ⊕ (Fin (N + 1) × Fin (N + 1))

/-- The name of a late entry. -/
def nmF (N : ℕ) : J4 N → Nm4
  | .inl j => .inl (nmOf N j)
  | .inr p => .inr (.x0 p.1 p.2)

/-- The late entry of a name. -/
def atF (N : ℕ) : Nm4 → J4 N
  | .inl x => .inl (atOf N x)
  | .inr (.x0 l kh) => .inr (clamp N l, clamp N kh)

/-- The name's numbers are at most N. -/
def goodF (N : ℕ) : Nm4 → Prop
  | .inl x => goodOf N x
  | .inr (.x0 l kh) => l ≤ N ∧ kh ≤ N

theorem nm_atF (N : ℕ) : ∀ x : Nm4, goodF N x → nmF N (atF N x) = x
  | .inl x, h => congrArg Sum.inl (nm_at N x h)
  | .inr (.x0 l kh), h => by
    show Sum.inr (EmbNm.x0 (clamp N l).val (clamp N kh).val) = _
    rw [clamp_val h.1, clamp_val h.2]

/-- Which late entry has which name. -/
def lateF (N : ℕ) : LateLay Nm4 (J4 N) where
  nm := nmF N
  at' := atF N
  good := goodF N
  ok := nm_atF N

/-- A number with room for all names in range. nb: the blocks of the stream that comes in. -/
def roomF (D : Dim) (B sG nb : ℕ) : ℕ := roomFor D B sG + nb + Arr.x0.nCell

theorem good_mono {N N' : ℕ} (h : N ≤ N') : ∀ x : Nm3, goodOf N x → goodOf N' x
  | .inl (.xi _ _ _), g => ⟨g.1.trans h, g.2.1.trans h, g.2.2.trans h⟩
  | .inl (.atP _ _), g => ⟨g.1.trans h, g.2.trans h⟩
  | .inl (.atR _ _), g => ⟨g.1.trans h, g.2.trans h⟩
  | .inl (.sel _ _), g => ⟨g.1.trans h, g.2.trans h⟩
  | .inr (.inl (.row _ _)), g => ⟨g.1.trans h, g.2.trans h⟩
  | .inr (.inl (.sc _ _)), g => ⟨g.1.trans h, g.2.trans h⟩
  | .inr (.inl (.sel _ _ _)), g => ⟨g.1.trans h, g.2.1.trans h, g.2.2.trans h⟩
  | .inr (.inr (.s5 _ _ _)), g => ⟨g.1.trans h, g.2.1.trans h, g.2.2.trans h⟩
  | .inr (.inr (.u5 _ _ _)), g => ⟨g.1.trans h, g.2.1.trans h, g.2.2.trans h⟩
  | .inr (.inr (.s6 _ _ _)), g => ⟨g.1.trans h, g.2.1.trans h, g.2.2.trans h⟩
  | .inr (.inr (.u6 _ _ _)), g => ⟨g.1.trans h, g.2.1.trans h, g.2.2.trans h⟩

theorem room_le (D : Dim) (B sG nb : ℕ) : roomFor D B sG ≤ roomF D B sG nb := by
  unfold roomF
  omega

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullFPar E M X)

/-- The form of each name: what the late entry is meant to be. -/
noncomputable def fmOfF (zt : (tailW P).s7.Nx → ℕ → E) (b s sG : ℕ) (e : (tailW P).s7.Nx) :
    Nm4 → TWhole.Aff E P.J
  | .inl (.inl x) =>
    toAff (normsFm P.rd P.D (eAtF P.ofp P.wfPart e (zt e)) (P.D.lL + 1) b s x)
  | .inl (.inr (.inl x)) => toAff (termsFm P.rd P.D (termsEAt P.tp ((tailW P).b3 e).2).rt x)
  | .inl (.inr (.inr x)) => toAff (gatedFm P.rd P.D
      (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2) sG x)
  | .inr x => toAff (embFm P.rd P.D (stF P e).pa P.ls x)

variable (zt : (tailW P).s7.Nx → ℕ → E) (b s B sG : ℕ)

/-- NormsOkF, from its three clauses on sizes. -/
theorem normsOkF_of (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b) :
    NormsOkF P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x))
      (fmOfF P zt b s sG) zt b s B where
  hl := hl
  hd := hd
  hB := hB
  hfm := fun _ _ _ => rfl
  gXi := fun ν l kh h1 h2 h3 => by
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine good_mono (room_le P.D B sG P.nb) (.inl (.xi ν l kh)) ⟨?_, ?_, ?_⟩ <;> omega
  gP := fun ν n h1 h2 => by
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine good_mono (room_le P.D B sG P.nb) (.inl (.atP ν n)) ⟨?_, ?_⟩ <;> omega
  gR := fun ν n h1 h2 => by
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine good_mono (room_le P.D B sG P.nb) (.inl (.atR ν n)) ⟨?_, ?_⟩ <;> omega
  gS := fun l x h1 h2 => by
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine good_mono (room_le P.D B sG P.nb) (.inl (.sel l x)) ⟨?_, ?_⟩ <;> omega

/-- TermsOkF: no premise. -/
theorem termsOkF_of :
    TermsOkF P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inr (Sum.inl x)))
      (fmOfF P zt b s sG) where
  hfm := fun _ _ _ => rfl
  gR := fun ν n h1 h2 => by
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine good_mono (room_le P.D B sG P.nb) (.inr (.inl (.row ν n))) ⟨?_, ?_⟩ <;> omega
  gC := fun l k h1 h2 => by
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine good_mono (room_le P.D B sG P.nb) (.inr (.inl (.sc l k))) ⟨?_, ?_⟩ <;> omega
  gS := fun l x k h1 h2 h3 => by
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine good_mono (room_le P.D B sG P.nb) (.inr (.inl (.sel l x k))) ⟨?_, ?_, ?_⟩ <;> omega

/-- GatedOkF, from its four clauses on sizes. -/
theorem gatedOkF_of (h1 : 1 ≤ P.D.lL) (hs1 : sG ≤ lF P.D) (hs2 : sG ≤ lFe P.D)
    (hfe : P.D.fe = 2 ^ lFe P.D) :
    GatedOkF P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inr (Sum.inr x)))
      (fmOfF P zt b s sG) sG where
  h1 := h1
  hs1 := hs1
  hs2 := hs2
  hfe := hfe
  hfm := fun _ _ _ => rfl
  hY :=
    { s5 := fun l hl i hi c hc => by
        obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
        refine good_mono (room_le P.D B sG P.nb) (.inr (.inr (.s5 l i c))) ⟨?_, ?_, ?_⟩ <;> omega
      u5 := fun l hl i hi c hc => by
        obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
        refine good_mono (room_le P.D B sG P.nb) (.inr (.inr (.u5 l i c))) ⟨?_, ?_, ?_⟩ <;> omega
      s6 := fun l hl i hi c hc => by
        obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
        refine good_mono (room_le P.D B sG P.nb)
          (.inr (.inr (.s6 l (2 * i + 1) (2 ^ (lFe P.D - sG) + c)))) ⟨?_, ?_, ?_⟩ <;> omega
      u6 := fun l hl i hi c hc => by
        obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
        refine good_mono (room_le P.D B sG P.nb)
          (.inr (.inr (.u6 l (2 * i + 1) (2 ^ (lFe P.D - sG) + c)))) ⟨?_, ?_, ?_⟩ <;> omega }

/-- EmbOkF: no premise. -/
theorem embOkF_of :
    EmbOkF P (lateF (roomF P.D B sG P.nb)) Sum.inr (fmOfF P zt b s sG) where
  hfm := fun _ _ _ => rfl
  hY := fun l hl kh hk => by
    show l ≤ _ ∧ kh ≤ _
    unfold roomF
    refine ⟨?_, ?_⟩ <;> omega

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.normsOkF_of
#print axioms OnBytes.Road.K4.termsOkF_of
#print axioms OnBytes.Road.K4.gatedOkF_of
#print axioms OnBytes.Road.K4.embOkF_of
