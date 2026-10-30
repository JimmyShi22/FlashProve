-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3DigitsRow.lean (IN THE SECOND FORM OF THE CHAIN OF PROMISES:
a condition Rz k beside the promise in front, meant: «this state is reached»): the lookup on the
digits of a segment's approximate range proof: ITS ROW AT THE TABLE OF JOINTS, AS A RULE: from the
end theorem's law through the table's wide door in its second form (ownAtTableWideR,
Johnson/Desc/Sound/OwnAtTableR.lean) to Piece.Own at the table's own promise with Rz k beside it,
meanings and row, at sub-protocol number k. Two theorems. NO RESULT ON THE PROTOCOL: EVERY PREMISE
THAT IS LEFT IS NAMED; NONE IS SHOWN AT ANY TERM.

The piece stands over the verifier's state alone: get := fun s => (z, s), at any public part z. The
name, the mark's guard, the lift to the pair with the public part and the table's extractor are not
here: they are the table's makers'.

Main names.
  k3_digits_row_of_law: THE RULE: it takes the law itself as a premise (hG: Piece.GoodIn between
    DigOn, DigOn', DigFront, DigBehind) and names NO SUB-PROTOCOL's TEXT: so a turn of K3's text
    turns nothing here.
  k3_digits_row_any: hG paid by k3_digits_goodIn_anyCap (K3DigitsAny.lean): at a piece that holds
    «below b», b any sub-protocol whose decide's .ok gives K3.block's at seatDigits, with the cap as
    errors.
THE SHAPE OF THE LAW. The end: Own at onR … Rz k in front (onQ behind) · ownIn
(no fOrder, no fLive); the door's item liveItem m is not asked (hQ: four items) ·
fObj is asked at the state behind an accept alone · Rz k a stands in hand in ownIn, fObj, t2.
OBJECT. The table's onQ, meansQ, insQ, outsQ (BordersQ.lean) and onR (ChainOfPromisesR.lean) at
sub-protocol number k; the verifier's state's readers fork?, tl? (through seatDigits' fork and
heard). In the second theorem also Desc.K3.block at Desc.K3.seatDigits, through hyes.
USER. k3_digits_row_seated (K3DigitsRowSeated.lean).
LETTERS. N, Mg, links, ps, k, m, pc, z, Rz; q; G, seatT, arr, smp, claim;
x, tl, D, rad, set.
Compiled with the whole library.
WHAT IS LEFT, BY NAME, AND WHOSE.
  ON THE TABLE: hins, houts, hctx (number k's row is the digits' lookup's) · hQ (the four public
    items that the table's row asks, ledger m, lookIn m pc, linkFresh m, freeAbove m, are open in
    front) · hSeat (every member's seat is a tenant whose pin is open in front).
  ON THE PIECE: hext (its extractor is the identity) · hG (the law); in the second theorem, in hG's
    place: hyes, hb, hback, H, hR, hcap, hsmp, hseat.
  A FACT ALONG THE FOLD: ownIn (the promise in front, Rz k a, no mark ⟹ OwnIs D x.link a.1: the
    state's codes, the open segment's number and list of arrays, the live request's shape and its
    rows' layout are the plan's).
  ON THE LETTERS' FILLINGS: fLook (Meaning.pub at the four items TOGETHER gives k3LookIn:
    K3LookIn.lean: of it the row spends k3OnIn alone) · fCf (held, shown, noColl at a member's seat
    give CfAt) · fPl, fKe (worth "planes", worth "keys" give two of the three items of the row out
    at whatever the state holds) · fPin (the three moments' pins give PinSig) · fDig (DgP.DigIn
    gives constr at the part lookDigits).
  WHERE THE PIECE ACCEPTS: fObj (forms "objects" gives the third item of the row out: at the state
    behind, with both promises and Rz k a in hand) · pinBack (each pin of the three moments rides
    back from behind to the front) · t2 (the promise behind), whole · hMark (a mark stays) · hDec
    (the committed table's decoding rides).
Limits. A RULE OVER LETTERS, Rz AMONG THEM. No filling of the table's letters is known at which all
of these hold. Nothing on the items that ride past. Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsAny
import Johnson.Desc.First.Look.K3DigitsFill
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.Sound.OwnAtTableR

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers openSets pubSets start sampledIn)

section
variable {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {set : Params.Setting} {pp : ℕ}

variable {Cl Cells Tok Xi P : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)

local notation "theL" => DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit

/-- **THE RULE: FROM THE LAW TO THE ROW.** -/
theorem k3_digits_row_of_law (claim : Aff → Cl)
    (q : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hext : ∀ a τ w, q.ext a τ w = w)
    (hG : q.GoodIn
      (DigOn G x D rad seatT smp (Desc.K3.seatDigits claim).fork (OwnIs D x.link))
      (DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard (OwnIs D x.link))
      (DigFront G x tl D rad seatT arr smp)
      (DigBehind G x tl D rad seatT arr smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard))
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
      k3LookIn (Desc.First.Look.P.ofPlace set true x) (D.arrayOf.getD x.link #[]) s = true)
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
        (forK Cb.Gl.E theL () (zext (digMu x D rad seatT arr w))) Reading.gl g F')
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
      (meansQ N Mg fun s => (z, s)) (insQ links ps k) (outsQ links ps k) := by
  have hpins : ∀ (b : Desc.First.S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) (I : Item → Prop),
      (∀ i ∈ (rowQ links ps k).ctx, I i) →
      relAt (meansQ (Fr := Fr) N Mg fun s => (z, s)) I b w →
      ∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent m t, Mg.pin e.1 e.2 (z, b.1) (strsOf Fr b.2) w := by
    intro b w I hI hrel t ht
    refine hrel (.pin m t) (hI _ ?_)
    rw [hctx]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp
  refine ownAtTableWideR N Mg links ps (fun s => (z, s)) Rz k q _ _ _ _ hG ?_ t2 ?_ ?_ hMark hDec
  · -- t1
    intro a ha hr hm
    have hOwn := ownIn a ha hr (not_not.1 hm)
    obtain ⟨-, hor⟩ := ha
    rcases hor with hbad | ⟨hB, hS, hC, -⟩
    · exact absurd hbad hm
    · simp only [Bool.and_eq_true] at hB
      have hp : ∀ u ∈ [Pub.ledger m, .lookIn m pc, .linkFresh m, .freeAbove m],
          Mg.pub u (z, a.1) = true :=
        fun u hu => List.all_eq_true.1 hB.1.2 _ (List.mem_append_left _ (hQ u hu))
      exact k3_digits_t1 G seatT smp claim a hOwn
        (fun i => fCf i a.1 _ (List.all_eq_true.1 hS _ (hSeat i)) (hC _ (hSeat i)).1
          (hC _ (hSeat i)).2)
        (k3LookIn_onIn
          (fLook _ (hp _ (by simp)) (hp _ (by simp)) (hp _ (by simp)) (hp _ (by simp))))
  · -- t3
    intro a τ b w ha hr hm hyes ho' hrel
    have hout : ∀ i ∈ (rowQ links ps k).outs, meansQ (Fr := Fr) N Mg (fun s => (z, s)) i b w :=
      fun i hi => hrel i (List.mem_append_left _ (List.mem_append_left _ hi))
    rw [houts] at hout
    exact k3_digits_t3 G seatT arr smp _ _ _ b w
      (fPin _ _ _ (hpins b w _
        (fun i hi => List.mem_append_left _ (List.mem_append_right _ hi)) hrel))
      ho' (fObj a τ b ha hr hm hyes (t2 a τ b ha hr hm hyes ho') w
        (hout (.forms m pc "objects") (by simp)))
      (fPl _ _ _ (hout (.worth m pc "planes") (by simp)))
      (fKe _ _ _ (hout (.worth m pc "keys") (by simp)))
  · -- t4
    intro a τ b w _ _ hm hout _ hrel hRa i hi
    rw [hext] at hRa ⊢
    obtain ⟨hD, -⟩ := k3_digits_t4 G seatT arr smp a w hRa
    have hpB := hpins b w _ (fun i hi => List.mem_append_left _ (List.mem_append_right _ hi)) hrel
    unfold insQ at hi
    rw [hins, hctx] at hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl | rfl | rfl) | rfl
    · exact fDig _ _ _ hD
    · exact fun e he => pinBack a τ b w hout 2 (by simp) e he (hpB 2 (by simp) e he)
    · exact fun e he => pinBack a τ b w hout 0 (by simp) e he (hpB 0 (by simp) e he)
    · exact fun e he => pinBack a τ b w hout 1 (by simp) e he (hpB 1 (by simp) e he)
    · exact not_not.1 hm


/-- **THE DIGITS' LOOKUP's ROW, AT THE TABLE's OWN TERMS**, at any block whose decide says yes only
where K3.block's does, with the cap as the piece's errors. -/
theorem k3_digits_row_any (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before
        (Desc.First.Look.P.ofPlace set true x) guests).decide s rs cols = .ok s')
    (q : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hb : q.b = below b)
    (hback : q.back = []) (hext : ∀ a τ w, q.ext a τ w = w) (H : DigOK set x tl D rad pp)
    (hR : List.Forall₂ SameAs q.ds (Desc.First.Look.P.ofPlace set true x).rounds)
    (hcap : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (hsmp : ∀ s rs cols s', b.decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < q.base) (σ₀ : (digSg x D rad).Smp)
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
      k3LookIn (Desc.First.Look.P.ofPlace set true x) (D.arrayOf.getD x.link #[]) s = true)
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
        (forK Cb.Gl.E theL () (zext (digMu x D rad seatT arr w))) Reading.gl g F')
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
    (k3_digits_goodIn_anyCap G seatT arr smp claim piece laid before guests b hyes q hb hback hext H
      hR hcap hsmp hseat σ₀)
    N Mg links ps k m pc z Rz hins houts hctx hQ hSeat fLook fCf fObj fPl fKe fPin pinBack
    fDig ownIn t2 hMark hDec

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_row_of_law
#print axioms VerifiableInference.OnPublicFiles.k3_digits_row_any
