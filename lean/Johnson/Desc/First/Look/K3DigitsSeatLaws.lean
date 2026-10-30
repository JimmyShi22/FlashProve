-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3DigitsSeatLaws.lean (IN THE SECOND FORM OF THE CHAIN OF
PROMISES): the lookup on the digits of a segment's approximate range proof: THE FOUR THINGS THAT THE
KIND's FILES OWE AT A SEAT, AS ONE LEMMA: the row's own law at the table, with the condition Rch k
beside the promise in front; what rides, in the tie's fenced form; a mark stays; «decodes» rides:
each over every sub-protocol B' that narrows K3.theStated's value Bst and whose .ok bears no mark
(SeatOf, Johnson/Desc/Sound/TiedSeat.lean), and every value z of the public part. NO RESULT ON THE
PROTOCOL: EVERY PREMISE THAT IS LEFT IS NAMED; NONE IS SHOWN AT ANY TERM.

Main name.
  k3_digits_seatLawsR: IT ENDS IN THE NAME SeatLawsR links ps k q N Mg Rch Bst
    (Johnson/Desc/Sound/TiedSeatR.lean).

The row spends neither the door's name «frame.liveIs» nor
«in order» · fObj: asked at the state behind an
accept alone · Rch k ((z, a.1), a.2) stands in hand in ownIn, fObj, behind, rides.
WHAT IS PAID IN IT: the first conjunct by k3_digits_row_seated_cut (K3DigitsSeatedCut.lean), with
hins, houts, hctx by rowQ_at and digits_row, hQ by digits_lookIn_open
(Johnson/Desc/Sound/DigitsRow.lean) · the third by k3_digits_seated_turns. THE SECOND AND THE FOURTH
ARE PREMISES HANDED THROUGH (rides, hDec).
WHAT IS LEFT, BY NAME: h, hOk · hk (a stands at k in the list of places) · hi, hsub, hpcT, hpc ·
hfit · hx, hB · hback, hR, hcap, hseat · hsmp, hS, hH · hSeat · ownIn (a fact along the fold) · six
fillings, for every z (fLook, fCf, fPl, fKe, fPin, fDig) · fObj, pinBack, behind, hDec, rides: at
every B' with SeatOf Bst B', where its piece accepts, for every z.
OBJECT. Desc.K3.theStated claim readers X codes shape a = some Bst, at a.link = some i, a.piece =
K3.pieceAt X i true; the table's words at number k of ANY list of places ps with ps[k]? = some a.
USER. k3_digits_tied_at_driver (K3DigitsAtDriver.lean [not in this library]), k3_digits_seatLaws_at (K3DigitsAtFill.lean).
Meant also: the kind's assembly in the second form.
LETTERS. claim, readers, X, codes, shape, a, Bst, i, sub;
links, ps, k; q; N, Mg, Rch;
G, seatT, arr, smp; D, rad, pp.
Compiled with the whole library.
Limits. A rule over letters, Rch among them. Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsSeatedCut
import Johnson.Desc.Sound.DigitsRow
import Johnson.Desc.Sound.TiedSeatR

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers openSets pubSets start
  sampledIn shift pubFit)

section
variable {Cl Cells Tok Xi P : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (links : List ModelPart)

/-- **WHAT THE LOOKUP's FILES OWE AT THE DIGITS' SEAT.** -/
theorem k3_digits_seatLawsR (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (ps : List Desc.Place) (k : ℕ) (a : Desc.Place)
    (Bst : Desc.Block Desc.First.S Cl)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit Cells Tok MsgT))
    (h : Desc.K3.theStated claim readers X codes shape a = some Bst) (hOk : Bst.planOk = true)
    (hk : ps[k]? = some a)
    (i : ℕ) (hi : a.link = some i) (sub : ModelPart) (hsub : links[i]? = some sub)
    (hpcT : a.piece = 7 + shift sub) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (N : Numbers) (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
    (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (hfit : pubFit Mg.more links ps = true)
    {x : Desc.First.Look.Place} {tl : HTailF2} (hx : digAt X i = some (x, tl))
    (D : Desc.First.Look.Sent) (rad : OracleShape → ℕ) (pp : ℕ)
    (hB : digB (Params.settingOf X.P.frame) x tl D rad pp = true)
    (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (smp : Desc.First.S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)
    (hback : q.back = [])
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
    (hSeat : ∀ i, seatT i ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []))
    (fLook : ∀ (z : P), ∀ s, Mg.pub (.ledger i) (z, s) = true →
      Mg.pub (.lookIn i (7 + shift sub)) (z, s) = true →
      Mg.pub (.linkFresh i) (z, s) = true → Mg.pub (.freeAbove i) (z, s) = true →
      k3LookIn (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x)
        (D.arrayOf.getD x.link #[]) s = true)
    (fCf : ∀ (z : P), ∀ i s y, Mg.held (seatT i).1 (seatT i).2 (z, s) = true →
      Mg.shown (seatT i).1 (seatT i).2 y → Mg.noColl (seatT i).1 (seatT i).2 (z, s) y →
      CfAt G D.codes (digList x D rad) seatT smp i s y)
    (fObj : ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      a.1.failed = none → SameBut a.1 b.1 →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) b.1 = true →
      DigLeft a.1 b.1 → onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) (k + 1) b →
      ∀ w, Mg.forms i (7 + shift sub) "objects" (z, b.1) (strsOf Fr b.2) w →
      ∀ g F', (Desc.K3.seatDigits claim).fork b.1 = some F' →
      (Desc.K3.seatDigits claim).heard b.1 = some g →
      K3OutRows tl.f9 5 x.F.next (digNu x tl D rad seatT arr w) Reading.gl g F')
    (fPl : ∀ (z : P), ∀ s y w, Mg.worth i (7 + shift sub) "planes" (z, s) y w → ∀ g F',
      (Desc.K3.seatDigits claim).fork s = some F' → (Desc.K3.seatDigits claim).heard s = some g →
      K3OutPlanes tl.f9 5 x.F.next (digNu x tl D rad seatT arr w) Reading.gl g F')
    (fKe : ∀ (z : P), ∀ s y w, Mg.worth i (7 + shift sub) "keys" (z, s) y w → ∀ g F',
      (Desc.K3.seatDigits claim).fork s = some F' → (Desc.K3.seatDigits claim).heard s = some g →
      K3OutKeys tl.f9 5 x.F.next (digNu x tl D rad seatT arr w)
        (forK Cb.Gl.E
          (DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
          (zext (digMu x D rad seatT arr w))) Reading.gl g F')
    (fPin : ∀ (z : P), ∀ s y w, (∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent i t, Mg.pin e.1 e.2 (z, s) y w) →
      PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) s y w)
    (pinBack : ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      ∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent i t,
      Mg.pin e.1 e.2 (z, b.1) (strsOf Fr b.2) w → Mg.pin e.1 e.2 (z, a.1) (strsOf Fr a.2) w)
    (fDig : ∀ (z : P), ∀ s y w, DgP.DigIn tl (enOf x.arrays) (digMu x D rad seatT arr w) →
      Mg.constr i .lookDigits (z, s) y w)
    (ownIn : ∀ (z : P) a, onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → a.1.failed = none → OwnIs D x.link a.1)
    (behind : ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      a.1.failed = none → SameBut a.1 b.1 →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) b.1 = true →
      Mg.decodes (z, b.1) (strsOf Fr b.2) →
      DigLeft a.1 b.1 → onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) (k + 1) b)
    (hDec : ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      Mg.decodes (z, a.1) (strsOf Fr a.2) → Mg.decodes (z, b.1) (strsOf Fr b.2))
    (rides : ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w) :
    SeatLawsR links ps k q N Mg Rch Bst := by
  unfold SeatLawsR
  have hrow := digits_row links a i sub hi hsub hpcT
  have erow := rowQ_at links ps k a hk
  have hQ : ∀ u ∈ [Pub.ledger i, .lookIn i (7 + shift sub), .linkFresh i, .freeAbove i],
      u ∈ (pubSets Mg.more links ps)[k]?.getD [] :=
    fun u hu => digits_lookIn_open Mg.more links ps k a i sub hfit hk hi hsub hpcT u hu
  have hlook : lookAt X i true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  have hT := fun (B' : Desc.Block Desc.First.S Cl) (hN : B'.Narrows Bst) u v τ hout =>
    k3_digits_seated_turns (Fr := Fr) claim readers X codes shape a Bst B' h hOk hN i hi hpc
      hlook (digOK_at hx hB).shape
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) rfl hback u v τ hout
  refine ⟨?_, rides, ?_, hDec⟩
  · intro B' hN z
    exact k3_digits_row_seated_cut G claim readers X codes shape a Bst B' h hOk hN.1 i hi hpc hx
      D rad pp hB seatT arr smp _ rfl hback (fun _ _ _ => rfl) hR hcap hsmp hseat σ₀ hS hH N Mg
      links ps k i (7 + shift sub) z (fun k a => Rch k ((z, a.1), a.2))
      (by rw [erow]; exact hrow.1) (by rw [erow]; exact hrow.2.1)
      (by rw [erow]; exact hrow.2.2) hQ hSeat (fLook z) (fCf z) (fObj B' hN z) (fPl z) (fKe z)
      (fPin z)
      (pinBack B' hN z) (fDig z) (ownIn z) (behind B' hN z) (hDec B' hN z)
  · intro B' hN u τ v hout hm
    rw [(hT B' hN.1 u v τ hout).1.failed]
    exact hm

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_seatLawsR
