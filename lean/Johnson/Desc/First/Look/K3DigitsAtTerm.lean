-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3DigitsAtTerm.lean (over a letter Mg; in the second form of
the chain of promises): the lookup on the digits of a segment's approximate range proof: THE FOUR
THINGS THAT THE KIND's FILES OWE AT A SEAT, UNDER K3At X D L Mg (K3At.lean), WITH «behind» AND
«decodes rides» PAID AS FAR AS THEY ARE K3's: k3_digits_seatLaws_at (K3DigitsAtFill.lean) with its
premise behind replaced through k3_digits_behind_at (K3DigitsBehind.lean) and its premise hDec
through decodes_at_seat (Johnson/Desc/Sound/DecodesAtPiece.lean). One theorem: a
joining. NO RESULT ON THE PROTOCOL.

Main name.
  k3_digits_seatLaws_term: it ends in SeatLawsR links ps k q N Mg Rch Bst.
WHAT FALLS AGAINST k3_digits_seatLaws_at: behind · hDec.
WHAT COMES IN THEIR PLACE. Bools on the table and the numbers: hk1 with hfitS (sameStand) · hTab
(digTableB) · hbf (bookFit) with hn (this block tells no tree). ON Mg's FILLING: hdecF (decodes is
decodesOf decT) with hd (decT reads the pair's first part alone). AND SIX SENTENCES, EACH ANOTHER
LAYER's, on Mg, at every block B' with SeatOf Bst B', under its piece's own yes, WITH SameBut AND
DigLeft IN HAND: hIn (inOrder rides) · hHeld, hSh, hNc (held, shown, no collision ride at the open
pins' tenants) · othersPub (every item behind that is none of K3's constructors; formsIn i (7 + o)
"objects", whose maker the table names this block, among them) · othersP (pubP at every item but
left, leftOn).
WHAT IS LEFT BESIDE THESE, BY NAME: h, hOk, hk, hi, hsub, hpcT, hpc, hfit, hx, hB · hback, hR, hcap,
hseat · hsmp, hS, hH · hK and the three equations hrad, harr, hst · hSeat · fCf, fObj, fPin,
pinBack, fDig · ownIn · rides.
OBJECT. As in K3DigitsSeatLaws.lean.
USER. k3_digits_seatLaws_sig (K3DigitsAtSig.lean).
LETTERS. Those of k3_digits_seatLaws_at; a', told, decT.

Compiled with the whole library.
Limits. A rule over letters. Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsAtFill
import Johnson.Desc.First.Look.K3DigitsBehind
import Johnson.Desc.Sound.DecodesAtPiece

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers More openSets pubSets start
  sampledIn shift pubFit pubRowM pubStartM moreItem stepOpen pubStep pubOfItems sameStand bookFit)

section
variable {Cl Cells Tok Xi P : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (links : List ModelPart)

/-- **WHAT THE LOOKUP's FILES OWE AT THE DIGITS' SEAT, UNDER K3At, K3's SHARE PAID.** -/
theorem k3_digits_seatLaws_term (claim : Aff → Cl)
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
    (L : K3Letters Cells Tok) (hK : K3At X D L Mg) (hrad : L.rad = rad) (harr : L.arr = arr)
    (hst : seatT = fun j => L.seat x.link true j.1)
    (hSeat : ∀ i, seatT i ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []))
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
    (a' : Desc.Place) (hk1 : ps[k + 1]? = some a') (hfitS : sameStand links a a' = true)
    (hTab : digTableB Mg.more links ps k a i (shift sub) = true)
    (told : List (List Desc.Oracle)) (hbf : bookFit N ps told = true) (hn : told[k]? = some [])
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × Desc.First.S → Option Cells)
    (hdecF : Mg.decodes = decodesOf decT)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → decT c y' = decT c y)
    (hIn : ∀ B', SeatOf Bst B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      Mg.inOrder (z, u.1) = true → Mg.inOrder (z, v.1) = true)
    (hHeld : ∀ B', SeatOf Bst B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      ∀ e ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
      Mg.held e.1 e.2 (z, u.1) = true → Mg.held e.1 e.2 (z, v.1) = true)
    (hSh : ∀ B', SeatOf Bst B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      ∀ e ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
      Mg.shown e.1 e.2 (strsOf Fr u.2) → Mg.shown e.1 e.2 (strsOf Fr v.2))
    (hNc : ∀ B', SeatOf Bst B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      ∀ e ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
      Mg.noColl e.1 e.2 (z, u.1) (strsOf Fr u.2) → Mg.noColl e.1 e.2 (z, v.1) (strsOf Fr v.2))
    (othersPub : ∀ B', SeatOf Bst B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k u →
      ∀ r ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links a) ++
        pubOfItems (stepOpen ((openSets links ps (start links))[k]?.getD [])
          (Desc.First.rowOf links a)),
      k3Like r = false → Mg.pub r (z, v.1) = true)
    (othersP : ∀ B', SeatOf Bst B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k u →
      ∀ r ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links a),
      (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) → Mg.pubP r (z, v.1))
    (rides : ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w) :
    SeatLawsR links ps k q N Mg Rch Bst := by
  have hlook : lookAt X i true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  have e7 : 7 + shift sub = Desc.K3.pieceAt X i true := hpcT.symm.trans hpc
  have hOpen := digits_lookIn_open Mg.more links ps k a i sub hfit hk hi hsub hpcT
    (.lookIn i (7 + shift sub)) (by simp)
  refine k3_digits_seatLaws_at G links claim readers X codes shape ps k a Bst q h hOk hk i hi sub
    hsub hpcT hpc N Mg Rch hfit hx D rad pp hB seatT arr smp hback hR hcap hsmp hseat σ₀ hS hH L
    hK hrad harr hst hSeat fCf fObj fPin pinBack fDig ownIn ?_ ?_ rides
  · -- behind
    intro B' hN z u τ v hout hu _ hun T hOut hdec DL
    have hOnIn : Desc.K3.k3OnIn
        (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) u.1 = true := by
      have hu' := hu
      obtain ⟨-, hor⟩ := hu'
      rcases hor with hbad | ⟨hBb, -, -, -⟩
      · exact absurd hun hbad
      · simp only [Bool.and_eq_true] at hBb
        have hp : Mg.pub (.lookIn i (7 + shift sub)) (z, u.1) = true :=
          List.all_eq_true.1 hBb.1.2 _ (List.mem_append_left _ hOpen)
        rw [e7] at hp
        exact k3LookIn_onIn (fLook_at hK i true hlook z u.1 hp)
    exact k3_digits_behind_at links X D L Mg hK N ps k a a' hk hk1 hfitS i hi sub hsub hpcT
      hpc hTab hlook z u v hu hOnIn T hOut hdec DL (hIn B' hN z u τ v hout T DL) told hbf hn
      (hHeld B' hN z u τ v hout T DL) (hSh B' hN u τ v hout T DL) (hNc B' hN z u τ v hout T DL)
      (othersPub B' hN z u τ v hout T DL hu) (othersP B' hN z u τ v hout T DL hu)
  · -- decodes rides
    intro B' _ z u τ v hout hdu
    rw [hdecF] at hdu ⊢
    exact decodes_at_seat decT hd z
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) u v τ hout hdu

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_seatLaws_term
