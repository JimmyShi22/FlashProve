-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsFitAtWide.lean: THE NINE CONDITIONS ON PUBLIC LETTERS (`K4PlanFit`,
Johnson/Road/K4/K4PinsEnd.lean) AT THE DATA OFF THE WIDER MEANING's OWN PARAMETERS (`k4DataWide 𝔇 E
Mg₀`, Johnson/Road/K4/K4MeansAtWide.lean), FROM THREE CLOSED TESTS THAT CAN RUN AND SIX NAMED
EQUATIONS ON 𝔇's PARAMETERS. Over the closed law
(`k4PlanFit_fast`, Johnson/Road/K4/K4PlanFast.lean), whose letters are spelled as
the composed meaning's files spell their closed term's fields. One lemma of transport, one
theorem. No draw, no count.

  `planFit_congr`: `K4PlanFit` rides along equations of its letters D, seatT, arr, ms, N.
  **`fit_wide`**: `K4PlanFit` at `k4DataWide 𝔇 E Mg₀`'s letters, at every place x with the segment's
    number as its link and `PlaceIs x p 0`, from: THE THREE TESTS `commonFastB Z` · `firstFastB Z
    p.g` · `seamFastB Z p.g` · THE SIX EQUATIONS: 𝔇.sent = `sentAt Z` · 𝔇.arr = `arrAt Z` · 𝔇.ms =
    `P5T.msAtR Z radM` (radM: any radii) · 𝔇.N has `numbersAt Z`'s sent and index · 𝔇.seat3 l false
      j = the lookup's seat by role · and what the closed law takes beside its tests.

OBJECT: `k4DataWide 𝔇 E Mg₀`. USER: `laterAt_closed` (Johnson/Road/K4/K4PinsLaterClosed.lean).
LETTERS: Z, radM, 𝔇, E, Mg₀, p, x, posI: free.

Limits. K04_law IS NOT PROVED BY THIS. THE SIX EQUATIONS ARE PREMISES: by reading they hold by
unfolding at the composed meaning's closed term: NO LEAN HAS MET THAT. (Where this and
lean/THEOREM.md differ, the page holds.) The three tests
have run at the small set (in files of evaluations, not named here); the full size: not
shown here.
-/
import Johnson.Road.K4.K4MeansAtWide
import Johnson.Road.K4.K4PinsOfMeans
import Johnson.Road.K4.K4PinsConduit
import Johnson.Road.K4.K4PlanFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (Public)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.First (Numbers ModelPart Meaning)
open VerifiableInference.Desc.First.Look (Place Sent sigListCalls LayPub szOf pubAt stepOf
  Stored.entries)
open VerifiableInference.Desc.Sound (Mem MsgT MgData WideData)
open VerifiableInference.OnPublicFiles (headLink)
open Meaning (seatBy fLay)
open Cb.Pv.Tail (Size)

/-- `K4PlanFit` rides along equations of its letters. -/
theorem planFit_congr {X : Public} {p : Par} {rows cols : ℕ} (x : Place) (q : LayPub)
    {D D' : Sent} (hD : D' = D) (rad : OracleShape → ℕ)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (seatT' : Fin (sigListCalls D' rad x.link).length → ℕ × ℕ)
    (hs : ∀ (j : Fin (sigListCalls D' rad x.link).length)
      (j' : Fin (sigListCalls D rad x.link).length), j.1 = j'.1 → seatT' j = seatT j')
    (posI : ℕ → Bool × ℕ × ℕ) (oW : Cb.OMsg Cb.Gl.E)
    (enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E)
    {arr arr' : ℕ → ℕ → ℕ} (ha : arr' = arr) {ms ms' : List Mem} (hm : ms' = ms)
    {N N' : Numbers} (hN : N' = N) (m nM nR nC first : ℕ) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (hd : ℕ)
    (F : K4PlanFit (X := X) (p := p) x q D rad seatT posI oW enc wOf arr ms N m nM nR nC first s
      seat hd) :
    K4PlanFit (X := X) (p := p) x q D' rad seatT' posI oW enc wOf arr' ms' N' m nM nR nC first s
      seat hd := by
  subst hD ha hm hN
  obtain rfl : seatT' = seatT := funext fun j => hs j j rfl
  exact F

variable {Xi P Tok : Type} {rows cols nR : ℕ}

/-- **`K4PlanFit` at the wider meaning's own parameters.** -/
theorem fit_wide {pol KL : ByteArray} {tk : Array Nat} (Z : ProofFile.Pub) (radM : ℕ → ℕ → ℕ)
    (𝔇 : MgData Xi P Tok rows cols nR Z.p.X) (E : WideData P)
    (Mg₀ : Meaning P (Wit (CellsK rows cols) Tok MsgT)) (p : Par)
    (Q1 : 𝔇.sent = sentAt Z) (Q2 : 𝔇.arr = arrAt Z) (Q3 : 𝔇.ms = P5T.msAtR Z radM)
    (Q4s : 𝔇.N.sent = (numbersAt Z).sent) (Q4i : 𝔇.N.index = (numbersAt Z).index)
    (Q6 : ∀ l j, 𝔇.seat3 l false j = P6T.seatCallsT (seatsAt Z) (sentAt Z) l j)
    (hc : commonFastB Z = true) (hf : firstFastB Z p.g = true) (hm : seamFastB Z p.g = true)
    (hg0 : 0 < p.g) (hg : p.g < 12) (x : Place)
    (hx : x.link = 2 * p.g) (hG : Z.p.X.G[p.g]? = some p.hp) (posI : ℕ → Bool × ℕ × ℕ)
    (St' : PublicSteps pol KL Z.p.X) (B : RefPub Z.p.X p.g)
    (hP : p.P = { Z.p.X.layers with tokv := tk }) (P0 : PlaceIs x p 0)
    (hgr : 2 * p.g / stepOf Z.p.X = p.g) (hhd : 2 * p.g ≠ headLink Z.p.X) :
    K4PlanFit (X := Z.p.X) (p := p) x (pubAt Z.p.X (2 * p.g / stepOf Z.p.X))
      (sentOf (k4DataWide 𝔇 E Mg₀)) (k4DataWide 𝔇 E Mg₀).L3.rad
      (fun j => (k4DataWide 𝔇 E Mg₀).L3.seat x.link false j.1) posI (k4DataWide 𝔇 E Mg₀).L3.oW
      Stored.entries (k4DataWide 𝔇 E Mg₀).L3.wOf (k4DataWide 𝔇 E Mg₀).arr
      (k4DataWide 𝔇 E Mg₀).ms (k4DataWide 𝔇 E Mg₀).N (2 * p.g) (szOf p.hp.tl).NM
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (_root_.Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (_root_.Meaning.sizesOf Z.p.X))
      (k4DataWide 𝔇 E Mg₀).hd :=
  planFit_congr x _ (D := sentAt Z) Q1 𝔇.rad3 (seatTAt Z 𝔇.rad3 x.link) _
    (fun j j' e => by
      show 𝔇.seat3 x.link false j.1 = P6T.seatCallsT (seatsAt Z) (sentAt Z) x.link j'.1
      rw [Q6, e])
    posI _ Stored.entries _ Q2 Q3 rfl _ _ _ _ _ _ _ _
    (k4PlanFit_fast Z radM Q4s Q4i p hc hf hm hg0 hg x hx hG 𝔇.rad3 posI _ Stored.entries _
      (headLink Z.p.X) St' B hP P0 hgr hhd)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.planFit_congr
#print axioms OnBytes.Road.K4.fit_wide
