-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03OthersPAt.lean: THE LOOKUPS' LEDGER's DEBT «othersP» (the public sentences of other kinds that are open behind a lookup argument hold behind it), AT THE CLOSED CONSTANT, AT ALL FIFTY PLACES. (The fence at the digits: the field's text has «reached» and «no mark» behind the promise in front; the proof is one call of the lookups' theorem at that text.)
  k03_othersP_calls: under NO PREMISE BUT l < 25: at 𝔇 := h.toAtMg.𝔇 h.𝔇 · mgBase · h.toAtMg.rch · a := IM.k3Place l false · k := k3K l false: the field othersP of CallsLastR (Johnson/P5J/K03Last.lean), to the letter, for every piece q and block b'.
  k03_othersP_digits: the like at k := k3K l true · IM.k3Place l true: the field othersP of DigLastR, to the letter: a call of the lookups' othersP_dig_mgAll (Johnson/Desc/Sound/MgAt/K3DigitsSaid.lean), which ends in that text.
  TWO «example»s AT THE END: Lean lays each theorem into its structure at the letters at which the second count asks it.
THE FIRST IS A CALL: the lookups' othersP_mgAll (Johnson/Desc/Sound/MgAt/K3CallsSaid.lean: general in the data), with: hPb: mgBase's own text (its pubP q _ IS «(saysNone q).isSome = true») · Mg.more = {}: k03_hM · the place: their calls_tests · the border's number: their kOfCalls_border (kOfCalls l = borderOf l false, which is k3K l false by unfolding).
WHAT IT IS WORTH: at mgBase a public sentence that «says nothing» holds BY THE MAKE OF mgBase: the theorem says that every sentence open behind the calls' lookup, but «left l» (at the digits: but «left m» and «leftOn m»), is of that sort or is paid by mgAll's own filling (their closed tests callsSaidB | digSaid, by the kernel): it reads neither the state nor the piece.

Limits. The head h enters only through the letters' types. Nothing on soundness by itself.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03Last
import Johnson.Desc.Sound.MgAt.K3CallsSaid
import Johnson.Desc.Sound.MgAt.K3CallsTests
import Johnson.Desc.Sound.MgAt.K3DigitsSaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (pubSets pubStep pubRowM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- **othersP at the calls' place of segment l, at the constant: the field's own text.** -/
theorem k03_othersP_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Cl : Type} {l : ℕ}
    (hl : l < 25) (b' : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S Cl)
    (q : Piece (ckP .two) FrD (ProofFile.InstPub × VerifiableInference.Desc.First.S)
      Cl (Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT)) :
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l false) u →
      h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull PS)[k3K l false]?.getD [])
          (pubRowM (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull (IM.k3Place l false)),
        p ≠ .left l → (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pubP p (z, v.1) := by
  have e : kOfCalls l = k3K l false := kOfCalls_border l
  have here : PS[kOfCalls l]? = some (IM.k3Place l false) := (calls_tests hl).1
  have k := othersP_mgAll (Dm := h.toAtMg.𝔇 h.𝔇) (Mg := mgBase) (Fr := FrD) (Rch := h.toAtMg.rch) b' q
    (fun _ _ hs => hs) k03_hM hl here
  rw [e] at k
  exact k

/-- **othersP at the digits' place of segment l, at the constant: the field's own text.** -/
theorem k03_othersP_digits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (q : Piece (ckP .two) FrD (ProofFile.InstPub × VerifiableInference.Desc.First.S)
      ProofFile.Cl (Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))
    (b' : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl) :
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) FrD VerifiableInference.Desc.First.S ProofFile.Cl
          (Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT)).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS
        (fun s => (z, s)) (k3K l true) u →
      h.toAtMg.rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
      ∀ r ∈ pubStep ((pubSets (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull PS)[(k3K l true)]?.getD [])
          (pubRowM (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull (IM.k3Place l true)),
      (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) →
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pubP r (z, v.1) :=
  othersP_dig_mgAll (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch k03_hM (fun _ _ hs => hs) hl q b'

/-- Lean's own word that the theorem's end IS the field: it is laid into the structure at the letters at
which the second count asks it (idx: any; the field does not read it). -/
example (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (idx : ℕ → ℕ) (y : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2)
    (q : Piece (ckP .two) FrD (ProofFile.InstPub × VerifiableInference.Desc.First.S)
      ProofFile.Cl (Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))
    (b' : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl)
    (V : CallsLastR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (At.num Zp)
      idx (IM.k3Place l false)
      (k3K l false) l y tl q b') :
    CallsLastR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (At.num Zp)
      idx (IM.k3Place l false)
      (k3K l false) l y tl q b' :=
  { V with othersP := k03_othersP_calls h hl b' q }

/-- The like for the digits' field. -/
example (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (y : VerifiableInference.Desc.First.Look.Place)
    (q : Piece (ckP .two) FrD (ProofFile.InstPub × VerifiableInference.Desc.First.S)
      ProofFile.Cl (Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))
    (b' : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl)
    (nos : Array ℕ) (n : ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid) (M : List OracleShape)
    (V : DigLastR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l y q b' nos n Ld M) :
    DigLastR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l y q b' nos n Ld M :=
  { V with othersP := k03_othersP_digits h hl q b' }

end P5J

#print axioms P5J.k03_othersP_calls
#print axioms P5J.k03_othersP_digits
