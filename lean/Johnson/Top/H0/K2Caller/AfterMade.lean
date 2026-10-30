-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/AfterMade.lean: the code switch: `LawAfter` AT THE PIECE's OWN SHOWN
COLUMNS, BROUGHT TO PUBLIC FACTS AND THE LIGHTER STRUCTURE ON THE FRONT. The oracles' columns are
    read
by make; that every shown column is the oracles' own holds at every transcript.

Main names:
  `orcsP`: the oracles' columns in front by make: by key and leaf off the statement's strings
    (`K2.orcS`, Johnson/Top/H0/K2Hears/ColsAtStage.lean).
  `KeysFit`: four facts on the plan's numbers at the piece's stage: the frame's first tree is the
    place's · below the base the first tree at hand with a tree's key is that tree · a read tree's
    key is below 2 ^ 16 · the two written rounds open only trees that were sent in front of them. (A
    first form asked that the keys of ALL trees at hand be one to one: at the frame of a whole file,
    which holds three chains' trees with the second chain's labelled from 0 again, that is false.)
  `cols_shownP`: every column that the law's text is shown is the oracles' own, AT EVERY TRANSCRIPT:
    where the step's own tests pass by `K2.colsOf_first`
    (Johnson/Top/H0/K2Hears/ColsAtStageFirst.lean); elsewhere `shownP` (PieceAt.lean) shows nothing.
  `lawAfter_light`: `LawAfter` from: the written rounds · `P2At` · the kind's test on the plan ·
    r.sizedB · `CallerAt` against a public frame W₀ · `FrontOnL`
    (Johnson/Top/H0/K2Hands/TieLight.lean: the structure on the front without `Slots`) where on
        holds ·
    `KeysFit`. By `afterAtYes_light`, `lin_at` and `yesAt_at`.
Limits. `CallerAt`, `FrontOnL` and `KeysFit` are premises; that `KeysFit` holds at a real frame is
shown by nobody yet.
(Where this and lean/THEOREM.md differ, the page
holds.) W₀ is meant as THE REAL FRAME OF THE PLACE, which numbers the old messages by
the statement's own numbers. No member. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.PlainGood
import Johnson.Top.H0.K2Caller.LinAt
import Johnson.Top.H0.K2Hands.TieLight
import Johnson.Top.H0.K2Hears.ColsAtStageFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open scoped ENNReal

variable {F : Frame} {W : Type}

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (p : K2.P2) (base : ℕ)
  (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)

/-- **The oracles' columns in front BY MAKE**: by key and leaf, off the statement's strings. -/
noncomputable def orcsP (a : Rec × F.E.Str) : ℕ → ℕ → List UInt64 :=
  K2.orcS (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).stage a.2

/-- Four facts on the plan's numbers at the piece's stage. -/
structure KeysFit : Prop where
  /-- the frame's first tree is the place's -/
  ft : F.ft = p.firstTree
  /-- below the base the first tree at hand with a tree's key is that tree -/
  first : ∀ j, j < (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).stage.base →
    ((k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).stage.Lin.find? fun L =>
      (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).stage.key L.no ==
        (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).stage.key j).map (·.no) = some j
  /-- a read tree's key is below 2 ^ 16 -/
  low : ∀ x ∈ p.read, x.1 < 2 ^ 16
  /-- the two written rounds open only trees that were sent in front of them -/
  old : ∀ d ∈ (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).stage.ds, ∀ j ∈ d.opens,
    j < (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).stage.base

/-- **Every column that the law's text is shown is the oracles' own, AT EVERY TRANSCRIPT.** -/
theorem cols_shownP (hk : KeysFit (W := W) X iJ iQ d₁ d₂ ρ p base ext) (a : Rec × F.E.Str)
    (τ : Tr [wT d₁, wT d₂]) :
    K2.ColsOf (orcsP X iJ iQ d₁ d₂ ρ p base ext a)
      (K2.flat p (shownP X iJ iQ d₁ d₂ ρ p base ext a τ)) := by
  classical
  unfold shownP
  split
  · rename_i hf
    rw [hk.ft] at hf ⊢
    exact K2.colsOf_first (ckP .two) (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).stage
      (below (K2.codeSwitchKind (Cl := Claim) p)) p rfl hk.first hk.low hk.old a.2 τ _ hf
  · intro c hc
    simp [K2.flat] at hc

variable (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)

set_option maxHeartbeats 1000000 in
/-- **`LawAfter` at the piece's own shown columns**, from: the written rounds · the place's numbers
    ·
the kind's test on the plan · the typed caller against a public frame · the stage sized · the
    lighter
structure on the front · the facts on the keys. -/
theorem lawAfter_light {Cl : Type} (w : K2Wr r d₁ d₂) (hp : P2At r p)
    (hpl : (K2.codeSwitchKind (Cl := Cl) p).planOk = true) (hz : r.sizedB = true)
    (W₀ : OnBytes.SwitchFrame) (mem row : (selR X).Kp → ℕ) (pl : (selR X).Kp → OnBytes.KeptPlace)
    (aOf : (selLoc X iJ iQ).hd.K → ℕ) (iOf : ∀ k, ((selLoc X iJ iQ).hd.o k).Z.S → ℕ)
    (on : Rec × F.E.Str → Prop) (C : CallerAt (selR X) r.cs r.l iJ iQ mem row pl W₀)
    (Fr : ∀ a, on a → FrontOnL (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l
      iJ iQ (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) p strs inX
      (orcsP X iJ iQ d₁ d₂ ρ p base ext) W₀ mem row pl aOf iOf a)
    (hk : KeysFit (W := W) X iJ iQ d₁ d₂ ρ p base ext) :
    LawAfter X iJ iQ d₁ d₂ ρ p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) on :=
  afterAtYes_light (selR X) (heldAt r H X.t₀ X.oM X.oZ X.kq) X.Sb X.sl X.Z X.A₀ r.cs r.l iJ iQ
    (baseCount r.set .request r.g) X.w₀ (portCode r.cs r.rider) (rdOf (X.withSel iJ iQ) d₁ d₂ ρ) p
    (vN d₁) (vN d₂) strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext)
    (orcsP X iJ iQ d₁ d₂ ρ p base ext) hpl W₀ mem row pl aOf iOf on C (lin_at hz X iJ iQ) Fr
    (yesAt_at X iJ iQ d₁ d₂ ρ p (shownP X iJ iQ d₁ d₂ ρ p base ext)
      (orcsP X iJ iQ d₁ d₂ ρ p base ext) w hp on
      (fun a τ _ => cols_shownP X iJ iQ d₁ d₂ ρ p base ext hk a τ))

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.cols_shownP
#print axioms VerifiableInference.Desc.First.K2Caller.lawAfter_light
