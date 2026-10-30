-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RealLeads.lean: a law of K10 in the plain form is carried from the
three rounds as letters to the chain's own written stretch.

Why. K10's laws (Law/Leads.lean, Law/FrameLaw.lean) speak of a reduction over "rB, rE, k times rR"
whose decision reads the transcript through the six readings alone: out a τ := f a (ρ.V τ). A piece
of a description runs over `uLT (ckP .two) ds` and hands its block the view's rounds without the
sealed digest, behind the tests of work.
  `writtenRed ds f`: that decision over the written stretch ds: where all tests of work pass, f at
  the view's rounds (`rvT`), each without the sealed digest; else nothing.
  `leads_written`: at the real readings (`realRd`, Law/RealRounds.lean) a law `Leads on Q` at the
  cap over the three rounds gives the same law at the cap over the written stretch "dB, dE, k times
  dR". By `realRd_V`, `leads_sim` and `leads_cast` (Johnson/Desc/Plain/Moves.lean).
Limits. A carriage: it proves no law. From `writtenRed` to a piece's own reduction
(`Piece.out_decide`; the kind's decision under its seat) is not here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Close.Law.RealRounds
import Johnson.Desc.Plain.Moves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Iop Run
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt

theorem cast_cast_back {α β : Type} (h : α = β) (h' : β = α) (x : β) :
    cast h (cast h' x) = x := by
  cases h
  rfl

/-- A decision on the rounds that a kind is shown, over a written stretch. -/
def writtenRed {A B : Type} (ds : List RDT) (f : A → List Fmt.RoundView → Option B) : Reduction A B :=
  ⟨uLT (ckP .two) ds, fun a τ =>
    if passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true then
      f a ((rvT (ckP .two) ds τ).map noDigest)
    else none⟩

variable (c : BatFoldCaller GE) (dB dE dR : RDT) (rdZ : List E → Option c.s.Z.D)
  (rdCh : List E → Option (Yc c).Ch)

/-- **From the three rounds as letters to the written stretch, at the cap.** -/
theorem leads_written {A B : Type} (f : A → List Fmt.RoundView → Option B) (on : A → Prop)
    (Q : A → B → Prop)
    (h : (⟨wT dB :: wT dE :: List.replicate (Yc c).k (wT dR),
        fun a τ => f a ((realRd c dB dE dR rdZ rdCh).V τ)⟩ : Reduction A B).Leads on Q
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc c).k (wT dR)))) :
    (writtenRed (dB :: dE :: List.replicate (Yc c).k dR) f).Leads on Q
      (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc c).k dR))) := by
  have hs := shape_k10 dB dE dR (Yc c).k
  have k1 : (⟨wT dB :: wT dE :: List.replicate (Yc c).k (wT dR),
      fun a τ => (writtenRed (dB :: dE :: List.replicate (Yc c).k dR) f).out a
        (cast (congrArg Iop.Tr hs.symm) τ)⟩ : Reduction A B).Leads on Q
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc c).k (wT dR))) := by
    refine Reduction.leads_sim
      (⟨wT dB :: wT dE :: List.replicate (Yc c).k (wT dR),
        fun a τ => f a ((realRd c dB dE dR rdZ rdCh).V τ)⟩ : Reduction A B)
      _ on Q _ on Q (fun a ha => Or.inr ⟨a, ha, fun τ b' hb' => ?_⟩) h
    refine ⟨b', ?_, id⟩
    have hb2 : (if passT (ckP .two) (dB :: dE :: List.replicate (Yc c).k dR)
        (rhoT (ckP .two) (dB :: dE :: List.replicate (Yc c).k dR)
          (cast (congrArg Iop.Tr hs.symm) τ)) = true then
        f a ((rvT (ckP .two) (dB :: dE :: List.replicate (Yc c).k dR)
          (cast (congrArg Iop.Tr hs.symm) τ)).map noDigest)
      else none) = some b' := hb'
    by_cases hp : passT (ckP .two) (dB :: dE :: List.replicate (Yc c).k dR)
        (rhoT (ckP .two) (dB :: dE :: List.replicate (Yc c).k dR)
          (cast (congrArg Iop.Tr hs.symm) τ)) = true
    · rw [if_pos hp] at hb2
      have hV := realRd_V c dB dE dR rdZ rdCh (cast (congrArg Iop.Tr hs.symm) τ) hp
      rw [cast_cast_back] at hV
      show f a ((realRd c dB dE dR rdZ rdCh).V τ) = some b'
      rw [hV]
      exact hb2
    · rw [if_neg hp] at hb2
      cases hb2
  have k2 := Reduction.leads_cast hs.symm
    (writtenRed (dB :: dE :: List.replicate (Yc c).k dR) f).out on Q _ k1
  rw [cap_cast hs.symm 128] at k2
  exact k2

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.leads_written
