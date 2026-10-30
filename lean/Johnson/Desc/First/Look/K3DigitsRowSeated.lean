-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3DigitsRowSeated.lean (in the second form of the chain of promises: carried
from K3DigitsRow.lean): the lookup on the digits of a segment's
approximate range proof: THE SEATED LAW WITH ITS STEPS PAID, AND THE ROW AT THE TABLE OF JOINTS AT
WHAT IS SEATED. Two joins of theorems that lie: no new argument. NO RESULT ON THE PROTOCOL: EVERY
PREMISE THAT IS LEFT IS NAMED; NONE IS SHOWN AT ANY DESCRIPTION.

Main names.
  k3_digits_seated_kept: k3_digits_seated (K3DigitsSeated.lean) with its premise hKeep paid by
    quietAt_keeps (K3DigitsKeeps.lean): in its place two premises on the samples' reader.
  k3_digits_row_seated: k3_digits_row_of_law (K3DigitsRow.lean) with its premise hG, the law, paid
    by k3_digits_seated_kept: Piece.Own at the table's own promise with Rz k beside it, meanings and
    row, at the piece that holds «below B'», B' any block that narrows K3.theStated's value at the
    digits' address.
OBJECT. Desc.K3.theStated claim readers X codes shape a, at a.link = some i and a.piece = K3.pieceAt
X i true; the table's onQ, meansQ, insQ, outsQ at block number k.
USER. K3DigitsSeatedCut.lean calls k3_digits_row_seated.
LETTERS. Those of the two theorems joined; the setting is X's own
(Params.settingOf X.P.frame).
Compiled with the whole library.
Limits. Those of K3DigitsSeated.lean, K3DigitsKeeps.lean and K3DigitsRow.lean. THAT BLOCK NUMBER k
OF THE TABLE's INDEX IS THE ADDRESS a IS ASKED NOWHERE: k, m, pc stand beside a, i as free letters,
tied only through hins, houts, hctx, hQ. A rule over letters.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsKeeps
import Johnson.Desc.First.Look.K3DigitsRow

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

/-- **The seated law, its steps paid.** -/
theorem k3_digits_seated_kept (claim : Aff → Cl)
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
    (hS : ∀ s Gk, smp (Desc.First.S.putFork s Gk) = smp s)
    (hH : ∀ (s : Desc.First.S) a c, s.here = .head a →
      smp { s with here := .head { a with claim := some c } } = smp s) :
    p.GoodIn
      (DigOn G x D rad seatT smp (Desc.K3.seatDigits claim).fork (OwnIs D x.link))
      (DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard (OwnIs D x.link))
      (DigFront G x tl D rad seatT arr smp)
      (DigBehind G x tl D rad seatT arr smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard) :=
  k3_digits_seated G claim readers X codes shape a B B' h hOk hN i hi hpc hx D rad pp hB seatT arr
    smp p hp hback hext hR hcap hsmp hseat σ₀
    (fun f hf s t hft =>
      quietAt_keeps smp hS hH X i f (by simpa [hi, hpc] using hf) s t hft)

/-- **THE DIGITS' LOOKUP's ROW AT WHAT IS SEATED.** -/
theorem k3_digits_row_seated (claim : Aff → Cl)
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
    (fObj : ∀ a τ b, onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k a → Rz k a →
      ¬ a.1.failed ≠ none → q.ior.red.out a τ = some b →
      onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) (k + 1) b →
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
    (t2 : ∀ a τ b, onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k a → Rz k a →
      ¬ a.1.failed ≠ none → q.ior.red.out a τ = some b →
      DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard (OwnIs D x.link) b →
      onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) (k + 1) b)
    (hMark : ∀ a τ b, q.ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2)) :
    q.Own (onR (Fr := Fr) N Mg links ps (fun s => (z, s)) Rz k)
      (onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) (k + 1))
      (meansQ N Mg fun s => (z, s)) (insQ links ps k) (outsQ links ps k) :=
  k3_digits_row_of_law G seatT arr smp claim q hext
    (k3_digits_seated_kept G claim readers X codes shape a B B' h hOk hN i hi hpc hx D rad pp hB
      seatT arr smp q hq hback hext hR hcap hsmp hseat σ₀ hS hH)
    N Mg links ps k m pc z Rz hins houts hctx hQ hSeat fLook fCf fObj fPl fKe fPin pinBack
    fDig ownIn t2 hMark hDec

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_seated_kept
#print axioms VerifiableInference.OnPublicFiles.k3_digits_row_seated
