-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3DigitsSeatedCut.lean (in the second form of the chain of
promises): the lookup on the digits of a segment's approximate range proof: THE ROW AT THE TABLE OF
JOINTS AT WHAT IS SEATED, WITH «A MARK STAYS» PAID AND THE SECOND TIE HANDED FOUR FACTS:
k3_digits_row_seated (K3DigitsRowSeated.lean) with hMark struck and t2 replaced by «behind», which
stands where the piece accepts and asks less. One theorem. NO RESULT ON THE PROTOCOL: EVERY PREMISE
THAT IS LEFT IS NAMED; NONE IS SHOWN AT ANY TERM.

Main name.
  k3_digits_row_seated_cut: «behind»: where the piece accepts (out a τ = some b), from the table's
    promise in front at an unmarked a with Rz k a, WITH IN HAND: SameBut a.1 b.1 · k3OnOut at the
    digits' place at b.1 · «the committed table decodes» at b · DigLeft a.1 b.1
    (K3DigitsSeatedLeaves.lean: both ledgers, the later one sized, what the other lookup heard
    unturned, «free above» and the other lookup's k3OnOut riding): the table's promise behind at b.
    fObj: asked at b alone, with the same in hand and the promise behind.
PAID HERE, ACROSS THE STEP WITHOUT A ROUND: THREE OF THE FOUR: SameBut and k3OnOut
(k3_digits_seated_turns, K3DigitsSeatedYes.lean) · DigLeft (k3_digits_seated_leaves); and «a mark
stays» (SameBut.failed). THE THIRD FACT, «the committed table decodes» behind, COMES FROM THE
PREMISE hDec.
OBJECT. Desc.K3.theStated claim readers X codes shape a, at a.link = some i and a.piece = K3.pieceAt
X i true; the table's onQ, onR, meansQ, insQ, outsQ at sub-protocol number k.
USER. k3_digits_seatLawsR (K3DigitsSeatLaws.lean).
LETTERS. Those of k3_digits_row_seated.

Compiled with the whole library.
Limits. Those of K3DigitsRowSeated.lean. «behind» IS t2 WITH FOUR FACTS IN HAND: the ties from these
facts to the meaning's fillings at the items that are open behind are still to be shown; hDec stays
a premise. That number k of the table's index is the address a is asked nowhere.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsRowSeated
import Johnson.Desc.First.Look.K3DigitsSeatedLeaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers openSets pubSets start sampledIn)

section
variable {Cl Cells Tok Xi P : Type} {Fr : Frame} (G : Desc.FileDescription Xi)

/-- **THE DIGITS' LOOKUP's ROW AT WHAT IS SEATED, THE SECOND TIE CUT.** -/
theorem k3_digits_row_seated_cut (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
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
    (q : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hq : q.b = below B')
    (hback : q.back = []) (hext : ∀ a τ w, q.ext a τ w = w)
    (hR : List.Forall₂ SameAs q.ds
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).rounds)
    (hcap : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim) a.piece laid sent
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) []).planOk = true →
      ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim) a.piece laid sent
        (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) []).decide s rs cols =
          .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < q.base) (σ₀ : (digSg x D rad).Smp)
    (hS : ∀ s Gk, smp (Desc.First.S.putFork s Gk) = smp s)
    (hH : ∀ (s : Desc.First.S) a c, s.here = .head a →
      smp { s with here := .head { a with claim := some c } } = smp s)
    (N : Numbers) (Mg : Meaning P (Desc.Wit Cells Tok MsgT)) (links : List ModelPart)
    (ps : List Desc.Place) (k m pc : ℕ) (z : P)
    (Rz : ℕ → Desc.First.S × Fr.E.Str → Prop)
    (hins : (rowQ links ps k).ins = [.constr m .lookDigits])
    (houts : (rowQ links ps k).outs =
      [.forms m pc "objects", .worth m pc "planes", .worth m pc "keys"])
    (hctx : (rowQ links ps k).ctx = [.pin m 2, .pin m 0, .pin m 1])
    (hQ : ∀ u ∈ [Pub.ledger m, .lookIn m pc, .linkFresh m, .freeAbove m],
      u ∈ (pubSets Mg.more links ps)[k]?.getD [])
    (hSeat : ∀ i, seatT i ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []))
    (fLook : ∀ s, Mg.pub (.ledger m) (z, s) = true → Mg.pub (.lookIn m pc) (z, s) = true →
      Mg.pub (.linkFresh m) (z, s) = true → Mg.pub (.freeAbove m) (z, s) = true →
      k3LookIn (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x)
        (D.arrayOf.getD x.link #[]) s = true)
    (fCf : ∀ i s y, Mg.held (seatT i).1 (seatT i).2 (z, s) = true →
      Mg.shown (seatT i).1 (seatT i).2 y → Mg.noColl (seatT i).1 (seatT i).2 (z, s) y →
      CfAt G D.codes (digList x D rad) seatT smp i s y)
    (fObj : ∀ a τ b, q.ior.red.out a τ = some b →
      onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k a → Rz k a → a.1.failed = none →
      SameBut a.1 b.1 →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) b.1 = true →
      DigLeft a.1 b.1 → onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) (k + 1) b →
      ∀ w, Mg.forms m pc "objects" (z, b.1) (strsOf Fr b.2) w →
      ∀ g F', (Desc.K3.seatDigits claim).fork b.1 = some F' →
      (Desc.K3.seatDigits claim).heard b.1 = some g →
      K3OutRows tl.f9 5 x.F.next (digNu x tl D rad seatT arr w) Reading.gl g F')
    (fPl : ∀ s y w, Mg.worth m pc "planes" (z, s) y w → ∀ g F',
      (Desc.K3.seatDigits claim).fork s = some F' → (Desc.K3.seatDigits claim).heard s = some g →
      K3OutPlanes tl.f9 5 x.F.next (digNu x tl D rad seatT arr w) Reading.gl g F')
    (fKe : ∀ s y w, Mg.worth m pc "keys" (z, s) y w → ∀ g F',
      (Desc.K3.seatDigits claim).fork s = some F' → (Desc.K3.seatDigits claim).heard s = some g →
      K3OutKeys tl.f9 5 x.F.next (digNu x tl D rad seatT arr w)
        (forK Cb.Gl.E
          (DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
          (zext (digMu x D rad seatT arr w))) Reading.gl g F')
    (fPin : ∀ s y w, (∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent m t, Mg.pin e.1 e.2 (z, s) y w) →
      PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) s y w)
    (pinBack : ∀ a τ b w, q.ior.red.out a τ = some b → ∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent m t,
      Mg.pin e.1 e.2 (z, b.1) (strsOf Fr b.2) w → Mg.pin e.1 e.2 (z, a.1) (strsOf Fr a.2) w)
    (fDig : ∀ s y w, DgP.DigIn tl (enOf x.arrays) (digMu x D rad seatT arr w) →
      Mg.constr m .lookDigits (z, s) y w)
    (ownIn : ∀ a, onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k a → Rz k a →
      a.1.failed = none → OwnIs D x.link a.1)
    (behind : ∀ a τ b, q.ior.red.out a τ = some b →
      onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k a → Rz k a → a.1.failed = none →
      SameBut a.1 b.1 →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) b.1 = true →
      Mg.decodes (z, b.1) (strsOf Fr b.2) →
      DigLeft a.1 b.1 → onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) (k + 1) b)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2)) :
    q.Own (onR (Fr := Fr) N Mg links ps (fun s => (z, s)) Rz k)
      (onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) (k + 1))
      (meansQ N Mg fun s => (z, s)) (insQ links ps k) (outsQ links ps k) := by
  have hlook : lookAt X i true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  have hT := fun u v τ hout => k3_digits_seated_turns (Fr := Fr) claim readers X codes shape a B B'
    h hOk hN i hi hpc hlook (digOK_at hx hB).shape q hq hback u v τ hout
  have hIn : ∀ u : Desc.First.S × Fr.E.Str,
      onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k u → ¬ u.1.failed ≠ none →
      Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) u.1 =
        true := by
    intro u hu hm
    obtain ⟨-, hor⟩ := hu
    rcases hor with hbad | ⟨hB', -, -, -⟩
    · exact absurd hbad hm
    · simp only [Bool.and_eq_true] at hB'
      have hp : ∀ r ∈ [Pub.ledger m, .lookIn m pc, .linkFresh m, .freeAbove m],
          Mg.pub r (z, u.1) = true :=
        fun r hr => List.all_eq_true.1 hB'.1.2 _ (List.mem_append_left _ (hQ r hr))
      exact k3LookIn_onIn
        (fLook _ (hp _ (by simp)) (hp _ (by simp)) (hp _ (by simp)) (hp _ (by simp)))
  refine k3_digits_row_seated G claim readers X codes shape a B B' h hOk hN i hi hpc hx D rad pp hB
    seatT arr smp q hq hback hext hR hcap hsmp hseat σ₀ hS hH N Mg links ps k m pc z Rz hins houts
    hctx hQ hSeat fLook fCf
    (fun u τ v hu hr hm hout hv => fObj u τ v hout hu hr (not_not.1 hm) (hT u v τ hout).1
      ((hT u v τ hout).2 (hIn u hu hm))
      (k3_digits_seated_leaves claim readers X codes shape a B B' h hOk hN i hi hpc q hq hback u v
        τ hout) hv)
    fPl fKe fPin pinBack fDig ownIn ?_ ?_ hDec
  · -- t2
    intro u τ v hu hr hm hout _
    exact behind u τ v hout hu hr (not_not.1 hm) (hT u v τ hout).1
      ((hT u v τ hout).2 (hIn u hu hm)) (hDec u τ v hout hu.1)
      (k3_digits_seated_leaves claim readers X codes shape a B B' h hOk hN i hi hpc q hq hback u v
        τ hout)
  · -- a mark stays
    intro u τ v hout hm
    rw [(hT u v τ hout).1.failed]
    exact hm

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_row_seated_cut
