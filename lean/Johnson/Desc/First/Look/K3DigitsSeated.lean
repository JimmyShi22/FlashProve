-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsSeated.lean: the lookup on the digits of a link's smallness test:
THE END THEOREM AT WHAT IS SEATED: at the piece that holds «below B'», B' any block that narrows the
value of K3.theStated at the digits' address of link i of a public record X. By the carriage
k3_seated_goodIn (Johnson/Desc/Sound/K3Seated.lean). Definitions, statements and proofs. NO
SOUNDNESS OF THE PROTOCOL IS CLAIMED.

Main names.
  DigKeeps smp s t: what a step without a round behind the digits' lookup must keep: the ledger
    behind is a later one, with its sizes; what was heard, the record's own five and the samples do
    not turn.
  digOn'_keeps, digBehind_back: under DigKeeps the condition behind passes forward over the step and
    the relation behind passes back.
  pieceAt_neD: a link's two lookups stand at two pieces.
  k3_digits_seated: Piece.GoodIn between DigOn, DigOn', DigFront, DigBehind, with the cap as errors.
OBJECT. Desc.K3.theStated claim readers X codes shape a (Johnson/Desc/First/Look/K3Stated.lean), at
a.link = some i and a.piece = K3.pieceAt X i true; through it K3.Law.blockVia at K3.seatDigits.
USER. K3DigitsRowSeated.lean calls k3_digits_seated and hands it to k3_digits_row_of_law as its hG.
LETTERS. claim, readers, X, codes, shape, a, i, B, B'; p; G, seatT, arr, smp; D, rad, pp. The place
and the plan's record are digAt X i's.
(Where this and lean/THEOREM.md differ, the page holds.)
WHAT IS LEFT, BY NAME: hOk (the seated block's own
test on the plan says yes: a public Bool) · hN (B' narrows theStated's value: the seat's) · hB
(digB: one public Bool) · hback, hext, hR, hcap, hseat (on the piece) · hsmp (where blockVia's own
test on the plan says yes, its yes does not turn smp) · hKeep (each step that quietAt gives at the
address keeps what DigKeeps names).
Limits. Those of K3DigitsAny.lean and of K3Seated.lean: the lift over the public part is not joined;
GoodIn alone: nothing on what rides past. hKeep is shown of no step here. At smp := «no sample»
DigOn holds nowhere and the theorem says nothing.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsAny
import Johnson.Desc.Sound.K3Seated
import Johnson.Top.H.K3LeftLater
import Johnson.Top.H.K3Via.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- A link's two lookups stand at two pieces. -/
theorem pieceAt_neD (X : Verify.Public) (i : ℕ) :
    Desc.K3.pieceAt X i false ≠ Desc.K3.pieceAt X i true := by
  unfold Desc.K3.pieceAt
  split <;> decide

section
variable {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ}

variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)

/-- **What a step without a round behind the digits' lookup must keep.** -/
structure DigKeeps (s t : Desc.First.S) : Prop where
  fork : ∀ F', s.fork? = some F' → ∃ Gk, t.fork? = some Gk ∧ _root_.Fo.Later F' Gk ∧
    (OnBytes.PscRun.Sized F' → OnBytes.PscRun.Sized Gk)
  heard : t.tl?.bind (·.heard) = s.tl?.bind (·.heard)
  own : ownOf t = ownOf s
  smp : smp t = smp s

variable {smp}

/-- The condition behind passes forward over such a step. -/
theorem digOn'_keeps (claim : Aff → Cl) {s t : Desc.First.S} (y : Fr.E.Str)
    (K : DigKeeps smp s t)
    (h : DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
      (Desc.K3.seatDigits claim).heard (OwnIs D x.link) (s, y)) :
    DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
      (Desc.K3.seatDigits claim).heard (OwnIs D x.link) (t, y) := by
  obtain ⟨hO, hC, g, F', hf, hh, hz, hS⟩ := h
  obtain ⟨Gk, hG, hL, hZ⟩ := K.fork F' hf
  refine ⟨K.own.trans hO, fun i hi => ?_, g, Gk, hG, K.heard.trans hh, hZ hz,
    k3StandsLater _ Reading.gl _ _ _ g F' Gk hL hS⟩
  obtain ⟨z, h1, h2, h3⟩ := hC i hi
  exact ⟨z, (congrFun K.smp i).trans h1, h2, h3⟩

/-- The relation behind passes back over it. -/
theorem digBehind_back (claim : Aff → Cl) {s t : Desc.First.S} (y : Fr.E.Str)
    (K : DigKeeps smp s t)
    (ho : DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
      (Desc.K3.seatDigits claim).heard (OwnIs D x.link) (s, y))
    (w : Desc.Wit Cells Tok MsgT)
    (h : DigBehind G x tl D rad seatT arr smp (Desc.K3.seatDigits claim).fork
      (Desc.K3.seatDigits claim).heard (t, y) w) :
    DigBehind G x tl D rad seatT arr smp (Desc.K3.seatDigits claim).fork
      (Desc.K3.seatDigits claim).heard (s, y) w := by
  obtain ⟨-, -, g, F', hf, hh, -, -⟩ := ho
  obtain ⟨Gk, hG, hL, -⟩ := K.fork F' hf
  obtain ⟨⟨hSF, hP⟩, g₁, G₁, hf₁, hh₁, hK⟩ := h
  obtain rfl : Gk = G₁ := Option.some.inj (hG.symm.trans hf₁)
  obtain rfl : g = g₁ := Option.some.inj ((hh.symm.trans K.heard.symm).trans hh₁)
  refine ⟨⟨hSF, fun i hi => ?_⟩, g, F', hf, hh, k3OutBack _ Reading.gl _ _ _ _ _ g F' Gk hL hK⟩
  obtain ⟨z, h1, h2, h3⟩ := hP i hi
  exact ⟨z, (congrFun K.smp i).symm.trans h1, h2, h3⟩

end

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)

/-- **THE END THEOREM AT WHAT IS SEATED.** -/
theorem k3_digits_seated (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    {x : Desc.First.Look.Place} {tl : HTailF2} (hx : digAt X i = some (x, tl))
    (D : Desc.First.Look.Sent) (rad : OracleShape → ℕ) (pp : ℕ)
    (hB : digB (Params.settingOf X.P.frame) x tl D rad pp = true)
    (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (smp : Desc.First.S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hp : p.b = below B')
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (hR : List.Forall₂ SameAs p.ds
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).rounds)
    (hcap : p.err = Err.cap 128 (uLT (ckP .two) p.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim) a.piece laid sent
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) []).planOk = true →
      ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim) a.piece laid sent
        (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) []).decide s rs cols =
          .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (digSg x D rad).Smp)
    (hKeep : ∀ f, (a.link.bind fun j =>
        Desc.K3.quietAt X j (a.piece == Desc.K3.pieceAt X j true)) = some f →
      ∀ s t, f s = .ok t → DigKeeps smp s t) :
    p.GoodIn
      (DigOn G x D rad seatT smp (Desc.K3.seatDigits claim).fork (OwnIs D x.link))
      (DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard (OwnIs D x.link))
      (DigFront G x tl D rad seatT arr smp)
      (DigBehind G x tl D rad seatT arr smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard) := by
  have hlook : lookAt X i true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  refine k3_seated_goodIn claim readers X codes shape a B B' h hOk hN p hp _
    (DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
      (Desc.K3.seatDigits claim).heard (OwnIs D x.link)) _ _
    (DigBehind G x tl D rad seatT arr smp (Desc.K3.seatDigits claim).fork
      (Desc.K3.seatDigits claim).heard) _ ?_ ?_ ?_
  · -- the kind's law at the address's own arguments
    intro i' digits P sent laid hi' hpc' hP _ _ hplan
    obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
    cases digits with
    | false => exact absurd (hpc'.symm.trans hpc) (pieceAt_neD X i)
    | true =>
      have eP : P = Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x := by
        unfold placeAt at hP
        rw [hlook] at hP
        exact (Option.some.inj hP).symm
      subst eP
      exact k3_digits_goodIn_anyCap G seatT arr smp claim a.piece laid sent []
        (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim) a.piece laid sent _ [])
        (fun s rs cols s' hd => Desc.K3.Law.blockVia_decide hplan hd)
        _ rfl hback hext (digOK_at hx hB) hR hcap (hsmp sent laid hplan) hseat σ₀
  · -- a step behind the rounds
    intro f hf s t y hft ho
    exact ⟨digOn'_keeps G seatT claim y (hKeep f hf s t hft) ho,
      fun w hw => digBehind_back G seatT arr claim y (hKeep f hf s t hft) ho w hw⟩
  · -- no step
    intro _
    exact ⟨fun _ hb => hb, fun _ _ hw => hw⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digOn'_keeps
#print axioms VerifiableInference.OnPublicFiles.digBehind_back
#print axioms VerifiableInference.OnPublicFiles.k3_digits_seated
#print axioms VerifiableInference.OnPublicFiles.pieceAt_neD
