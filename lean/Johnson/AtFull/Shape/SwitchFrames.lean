-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SwitchFrames.lean: THE CODE SWITCH's 25 PLACES IN THE PROOF FILE's OWN FIRST
CHAIN (kind K2), IN THE FRAME's OWN FORM: ONE OF THE TWO PREMISES THAT THE RULE FOR ACCEPTANCE ASKS
AT A MEMBER: Carries (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), at the reader shA of
Johnson/AtFull/Shape/FrameForm.lean. A joining of laws (SwitchAtHead.lean); nothing is evaluated.

Carries ALONE. AT THESE STEPS Returns IS NOT STATED: THESE 25 DO NOT COUNT AS MEMBERS THAT ARE
PAID. (Both premises, at these steps with a guard in front: SwitchReturns.lean, the links 1 to 23,
and SwitchEndsBoth.lean, the two other places.)

Which dress stands at a link's place is not said here: the step switchU bears both and chooses by
the shape's own "here" (SwitchAtHead.lean's head).

  **`carries_of_strong`**: THE PATTERN: a member at whose every yes from s to t a step f on ShA
    returns shA t at shA s has Carries, for every table of steps G with G ‹number› = optE f.
  **`switch_att_frame`** (12) · **`switch_lay_frame`** (11): 1 ≤ l < 24, at 14 l + 0 + 2: f :=
    switchU …, then the frame's "opened" on the pair.
  **`switch_head_frame`** (1): at 14 · 24 + 1 + 2: f := switchU ….
  **`switch_finish_frame`** (1): at the first member behind the links: f := finFrontU, finU,
    finBehindU in a row, at the numeral 353 + 0.

Limits. As said above. G and vals are letters. No frame here says that a member stands at its
number. None of the four switch_…_frame laws has a caller. UNDER THE HEAD: that it has a member is
shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the earlier hash. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.SwitchAtHead
import Johnson.AtFull.Shape.FrameOpt
import Johnson.IMR.BackSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (HeadPar)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape
open OnBytes.Maker (WholeD)
open IM (subAt k2P k2PlaceF)
open P5J (AtMgA)
open ProofFile.Honest (Carries)

/-- **THE PATTERN.** -/
theorem carries_of_strong {Cl : Type} {bs : List (Block S Cl)} {i : Nat} {b : Block S Cl}
    {f : ShA → Option ShA} (hb : bs[i]? = some b)
    (hc : ∀ s rs gs t, b.decide s rs gs = .ok t → f (shA s) = some (shA t))
    (ft : Nat) (G : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hG : G i = optE f) : Carries bs ft (firstZA G vals) i := by
  refine carries_of_seat hb fun s rs gs t u _ hd hu => ?_
  rw [hG] at hu
  exact Option.some.inj ((optE_ok.1 hu).symm.trans (hc s _ gs t hd))

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem switch_att_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (h1 : 1 ≤ l)
    (h24 : l < 24) (hs : subAt l = .attention) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar) (Y : Stages.LinkH)
        (p : Attention.Plan),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some l) = some n ∧
      P1K2.pureLetters Bs.G₀ l = some HP ∧ Zp.p.built.links[l]? = some Y ∧
      Zp.p.X.A[Y.g]? = some p ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * l + 0 + 2) = optE (fun y =>
          (switchU Zp { chain := 1, link := some l, piece := 1, kind := .K2 } n HP y).bind
            (quietE (openAttG (attPar Y p l)))) →
        Carries cF.blocksInOrder ft (firstZA G vals) (14 * l + 0 + 2) := by
  obtain ⟨Bs, P, n, HP, Y, p, Lk, b, a1, a2, a3, a4, a5, a6, -, a8, hc⟩ :=
    switch_att_at h l h1 h24 hs
  exact ⟨Bs, P, n, HP, Y, p, a1, a2, a3, a4, a5, a6, fun ft G vals hG =>
    carries_of_strong a8 hc ft G vals hG⟩

theorem switch_lay_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (h1 : 1 ≤ l)
    (h24 : l < 24) (hs : subAt l = .layers) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar) (Y : Stages.LinkH)
        (hp : Layer.HPlan2),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some l) = some n ∧
      P1K2.pureLetters Bs.G₀ l = some HP ∧ Zp.p.built.links[l]? = some Y ∧
      Zp.p.X.G[Y.g]? = some hp ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * l + 0 + 2) = optE (fun y =>
          (switchU Zp { chain := 1, link := some l, piece := 1, kind := .K2 } n HP y).bind
            (quietE (openLayG (layPar Zp.p.X Y hp l)))) →
        Carries cF.blocksInOrder ft (firstZA G vals) (14 * l + 0 + 2) := by
  obtain ⟨Bs, P, n, HP, Y, hp, Lk, b, a1, a2, a3, a4, a5, a6, -, a8, hc⟩ :=
    switch_lay_at h l h1 h24 hs
  exact ⟨Bs, P, n, HP, Y, hp, a1, a2, a3, a4, a5, a6, fun ft G vals hG =>
    carries_of_strong a8 hc ft G vals hG⟩

theorem switch_head_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some 24) = some n ∧
      P1K2.pureLetters Bs.G₀ 24 = some HP ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * 24 + 1 + 2) =
          optE (switchU Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } n HP) →
        Carries cF.blocksInOrder ft (firstZA G vals) (14 * 24 + 1 + 2) := by
  obtain ⟨Bs, P, n, HP, Lk, b, a1, a2, a3, a4, -, -, a7, hc⟩ := switch_head_at h
  exact ⟨Bs, P, n, HP, a1, a2, a3, a4, fun ft G vals hG =>
    carries_of_strong a7 hc ft G vals hG⟩

theorem switch_finish_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P none = some n ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (353 + 0) = optE (fun y =>
          ((finFrontU y).bind (finU (k2P Zp k2PlaceF "" .finish n))).bind finBehindU) →
        Carries cF.blocksInOrder ft (firstZA G vals) (353 + 0) := by
  obtain ⟨Bs, P, n, b, a1, a2, a3, a4, hc⟩ := switch_finish_at h
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  have hf := (IM.back_numbers h.scope h.reads O).1 0 b a4
  exact ⟨Bs, P, n, a1, a2, a3, fun ft G vals hG =>
    carries_of_strong hf (fun s rs gs t hd => hc s rs gs t hd) ft G vals hG⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.switch_finish_frame
#print axioms Johnson.AtFull.Shape.carries_of_strong
#print axioms Johnson.AtFull.Shape.switch_att_frame
#print axioms Johnson.AtFull.Shape.switch_lay_frame
#print axioms Johnson.AtFull.Shape.switch_head_frame
