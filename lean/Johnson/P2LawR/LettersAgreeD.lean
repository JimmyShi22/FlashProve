-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/LettersAgreeD.lean: THE LETTERS OF row0B_at_head AGAINST THE LAST CHAIN's FIELD
AT THE VALUE, SECOND PART: THE TWO MAKES OF THE SHARED TABLE's OPEN LETTERS ARE ONE:
`Sh.openAll h (Sh.eCodes_at h)` (Johnson/Desc/K14/Law/SharedConstFirstAt.lean) and
`h.toAtMg.shOpen h.𝔇` (Johnson/P5J/FreeShared.lean). Eight theorems. No mathematics.

Both are `Sh.openAt` at the same nine letters and at a structure of the first table's five. Of the
five, three are one by unfolding (N₁ · links · ms₁). TWO ARE NOT:
  Mg₁: `P5J.mgAtAll h` | `h.toAtMg.mq h.𝔇`: one by `M₁_is` (Johnson/P2LawR/LettersAgreeC.lean).
  smp₁: `e ▸ P5J.At.smp Zp` | `smpNamed Q.codes (P5J.At.seats Zp)`: the first is carried along
    e : `P5J.At.cs Zp = Q.codes`, which is no rfl: one by `cast_smp`.

  `shPlan_is` (rfl) · `X_is` (rfl) · `cast_smp` · `open₁_ext` · `first_is` · `open_is` ·
  `MS_is`: `Sh.mg (planAt …) (openAll …) = Sh.mg h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)` ·
  `decT₂_is`: the like at `Sh.decT₂`.
Limits. Equations of terms. Nothing on soundness.
-/
import Johnson.P2LawR.LettersAgreeC
import Johnson.P5J.FreeShared

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P2Law.LettersC
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat Fo.Peel
    Cb Johnson.Pack
open Iop Prob _root_.Run
open LLT25
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K13.Law (vecAt)
open VerifiableInference.Desc.K1 (shapeAt)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotEq gLaid parO omegaShapes_pos)
open _root_.Desc.K14.Law.Sh (planAt)
open _root_.Desc.K14.Law (Sh.X Sh.sentU Sh.layU Sh.layO Sh.mem Sh.mg secondAt)
open _root_.Desc.K14.Law.Sh (seatF openAll eCodes_at)
open P5J (AtMgA colsAt)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)

open _root_.Desc.K14.Law.Sh (open₁At openAt)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain First.S ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA o Z D₀ r₀ Zp Np cF x₀)

theorem shPlan_is : h.toAtMg.shPlan = planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF) := rfl

theorem X_is : Sh.X h.toAtMg.shPlan 12 =
    Sh.X (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) 12 := rfl

/-- The reader of samples by name, carried along an equation of codes, is the reader at the other
codes. -/
theorem cast_smp {P : Type} {c' : OnBytes.Codes} (seats : List (ℕ × ℕ)) :
    ∀ (c : OnBytes.Codes) (e : c = c')
      (f : P × First.S → (s : Sending) → (i : Fin s.l.length) →
        Option ((Johnson.Pack.sigOf c s.l).om i).Smp),
      f = smpNamed (P := P) c seats →
      (Eq.rec (motive := fun x _ => P × First.S → (s : Sending) → (i : Fin s.l.length) →
        Option ((Johnson.Pack.sigOf x s.l).om i).Smp) f e) = smpNamed (P := P) c' seats := by
  intro c e f hf
  subst e
  exact hf

/-- Two structures of the first table's five are one where their five fields are. -/
theorem open₁_ext {Cells Tok : Type} {Q : _root_.Desc.K14.P14}
    (a b : _root_.Desc.K14.Law.Sh.Open₁ Cells Tok Q) (h1 : a.N₁ = b.N₁) (h2 : a.links = b.links)
    (h3 : a.Mg₁ = b.Mg₁) (h4 : a.smp₁ = b.smp₁) (h5 : a.ms₁ = b.ms₁) : a = b := by
  obtain ⟨n, l, m, s, ms⟩ := a
  obtain ⟨n', l', m', s', ms'⟩ := b
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

/-- **The first table's five are one.** -/
theorem first_is : open₁At h (eCodes_at h) = h.toAtMg.shFirst h.𝔇 :=
  open₁_ext _ _ rfl rfl (M₁_is h)
    (cast_smp (P5J.At.seats Zp) (P5J.At.cs Zp) (eCodes_at h) (P5J.At.smp Zp) rfl) rfl

/-- **The two makes are one.** -/
theorem open_is : openAll h (eCodes_at h) = h.toAtMg.shOpen h.𝔇 :=
  congrArg (openAt o Zp Np (secondAt Zp Np) cF h.plan.shape
    (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) (P5J.At.EAt Z)) (first_is h)

theorem MS_is : Sh.mg (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF))
      (openAll h (eCodes_at h)) =
    Sh.mg h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇) :=
  congrArg (Sh.mg (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF))) (open_is h)

theorem decT₂_is : _root_.Desc.K14.Law.Sh.decT₂ (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF))
      (openAll h (eCodes_at h)) =
    _root_.Desc.K14.Law.Sh.decT₂ h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇) :=
  congrArg (_root_.Desc.K14.Law.Sh.decT₂ (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)))
    (open_is h)

end P2Law.LettersC

#print axioms P2Law.LettersC.first_is
#print axioms P2Law.LettersC.open_is
#print axioms P2Law.LettersC.MS_is
