-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3DigitsAtFill.lean (in the second form of the chain of
promises): the lookup on the digits of a segment's approximate range proof: THE FOUR THINGS THAT THE
KIND's FILES OWE AT A SEAT, AT EVERY MEANING THAT SAYS AT K3's OWN ITEMS WHAT THE LOOKUPS' LAYER
SAYS: k3_digits_seatLawsR (K3DigitsSeatLaws.lean) under K3At X D L Mg (K3At.lean): THREE PREMISES
FALL: fLook, fPl, fKe. One theorem: a joining. NO RESULT ON THE PROTOCOL.

Main name.
  k3_digits_seatLaws_at: the statement is k3_digits_seatLawsR's own, to the token, less these three,
    with hK (K3At) and three equations in their place: hrad, harr, hst (the law's letters rad, arr,
    seatT are L.rad, L.arr, fun j => L.seat x.link true j.1). It ends in SeatLawsR.
PAID: fLook, fPl, fKe by fLook_at, fPl_at, fKe_at; the table's 7 + shift sub is K3.pieceAt X i true
by hpcT with hpc. OF K3At's EIGHT FIELDS IT SPENDS lookIn AND worth ALONE.
WHAT IS LEFT, BY NAME: all else of k3_digits_seatLawsR.
OBJECT. As in K3DigitsSeatLaws.lean.
USER. k3_digits_seatLaws_term (K3DigitsAtTerm.lean).
LETTERS. Those of k3_digits_seatLawsR; L.

Compiled with the whole library.
Limits. A rule over letters. Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsSeatLaws
import Johnson.Desc.First.Look.K3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers More openSets pubSets start
  sampledIn shift pubFit pubRowM pubStartM moreItem)

section
variable {Cl Cells Tok Xi P : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (links : List ModelPart)

/-- **WHAT THE LOOKUP's FILES OWE AT THE DIGITS' SEAT, UNDER K3At.** -/
theorem k3_digits_seatLaws_at (claim : Aff → Cl)
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
  subst hst
  subst hrad
  subst harr
  have e : 7 + shift sub = Desc.K3.pieceAt X i true := hpcT.symm.trans hpc
  have hlook : lookAt X i true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  exact k3_digits_seatLawsR G links claim readers X codes shape ps k a Bst q h hOk hk i hi sub hsub
    hpcT hpc N Mg Rch hfit
    hx D L.rad pp hB (fun j => L.seat x.link true j.1) L.arr smp hback hR hcap hsmp hseat σ₀ hS hH
    hSeat
    (fun z s _ h2 _ _ => fLook_at hK i true hlook z s (by rw [← e]; exact h2))
    fCf fObj
    (fun z s y w hw => fPl_at hK claim i hx z s y w (by rw [← e]; exact hw))
    (fun z s y w hw => fKe_at hK claim i hx z s y w (by rw [← e]; exact hw))
    fPin pinBack fDig ownIn behind hDec rides

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_seatLaws_at
