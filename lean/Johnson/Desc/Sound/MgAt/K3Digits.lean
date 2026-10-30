-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3Digits.lean: the lookup on the digits of a segment's approximate range
proof: DigMeanR (Johnson/Desc/First/Look/K3MeansDigR.lean) AND SO SeatLawsR AT THE COMPOSED MEANING
mgAll Dm Mg (Johnson/Desc/Sound/MgAll.lean), from what is left
(DigRestR, K3DigitsRestR.lean) and four sentences on the term's parameters. Two theorems: joinings.
NO RESULT ON THE PROTOCOL.

Main names.
  digMeanR_mgAll: DigMeanR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch claim a k l sub x tl smp q
    b'.
  seatLawsR_mgAll: so SeatLawsR linksFull PS k q Dm.N (mgAll Dm Mg) Rch b', with the plan's premises
    of seatLawsR_of_digMeanR.
PAID AT THE TERM, WITHOUT A PREMISE: K3At (k3At_mgAll, MgAt/K3At.lean) · the four equations on pin,
noColl, shown, decodes (mgAll_pin, mgAll_noColl, mgAll_shown, mgAll_decodes: MgAll.lean) ·
HeldReads (heldReads_mgAll).
WHAT IS LEFT, EACH BOOKED.
  ON THE TERM's PARAMETERS (whoever lays the closed values): hD (Dm.digitsPart is the lookups'
    sentence digitsPartK3 X Dm.sent Dm.l3) · hd (the decoder Dm.decT does not read the verifier's
    state) · hread (the reader of samples Dm.smp reads the statement and the book alone) · hIn (the
    base's "in order" reads the statement, the check and the request alone).
  DigRestR's FOURTEEN FIELDS, at the term: TESTS (for an evaluation at the term's own list of extra
    public tests): hfit, hOp, hk1, hfitS, hTab, hbf, hn, hbaseS · ON THE PLAN AND THE READERS: sits
    · A FACT ALONG THE FOLD: ownIn · WHERE THE PIECE ACCEPTS: fObj, othersPub, othersP, rides.
OBJECT. One term of the type Meaning; as in K3DigitsSeatLaws.lean, at the full size's written lists.
Used by K3Mean.lean (Johnson/Desc/Sound/MgAt/).
LETTERS. Dm, Mg, Rch, claim; a, a', k, l, sub, x, tl, smp, q, b', told; f, readers, codes, shape,
z₀, pp.


Compiled with the whole library.
Limits. A rule over letters: Dm's fields are parameters, Rch is a letter. No test of DigRestR has
been evaluated at the term's own list of extra public tests. Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3At
import Johnson.Desc.First.Look.K3DigitsRestR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning shift)

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Cl)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame

/-- **DigMeanR AT THE COMPOSED MEANING.** -/
theorem digMeanR_mgAll (a a' : Desc.Place) (k l : ℕ) (sub : ModelPart)
    (x : Desc.First.Look.Place) (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (digList x Dm.sent Dm.l3.rad).length) →
      Option ((digSg x Dm.sent Dm.l3.rad).om i).Smp)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) (told : List (List Desc.Oracle))
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hback : q.back = [])
    (hx : digAt X l = some (x, tl)) (hi : a.link = some l)
    (hsub : linksFull[l]? = some sub) (hpcT : a.piece = 7 + shift sub)
    (hpc : a.piece = Desc.K3.pieceAt X l true) (hk : PS[k]? = some a) (z₀ : P)
    (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    (hIn : InOrderReads Mg)
    (f : P → Statement × TreeBook → (s : Sending) → (i : Fin s.l.length) →
      Option ((Johnson.Pack.sigOf Dm.sent.codes s.l).om i).Smp)
    (hread : ∀ z s, Dm.smp (z, s) = f z (s.st, s.book))
    (R : DigRestR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch claim Dm.smp Dm.ms a a' k l sub x tl
      smp q b' told) :
    DigMeanR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch claim a k l sub x tl smp q b' :=
  digMeanR_of_rest Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch claim Dm.smp Dm.ms
    (k3At_mgAll Dm Mg) a a' k l sub x tl smp q b' told readers codes shape h hback hx hi hsub hpcT
    hpc hk z₀ (mgAll_pin Dm Mg) (mgAll_noColl Dm Mg) (mgAll_shown Dm Mg) Dm.decT
    (mgAll_decodes Dm Mg) hd (digPart_mgAll Dm Mg hD l) (inOrderReads_mgAll Dm Mg hIn)
    (heldReads_mgAll Dm Mg) f hread R

/-- **SO WHAT THE KIND's FILES OWE AT THE DIGITS' SEAT, AT THE COMPOSED MEANING.** -/
theorem seatLawsR_mgAll (a a' : Desc.Place) (k l : ℕ) (sub : ModelPart)
    (x : Desc.First.Look.Place) (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (digList x Dm.sent Dm.l3.rad).length) →
      Option ((digSg x Dm.sent Dm.l3.rad).om i).Smp)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) (told : List (List Desc.Oracle))
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = [])
    (hx : digAt X l = some (x, tl)) (hi : a.link = some l)
    (hsub : linksFull[l]? = some sub) (hpcT : a.piece = 7 + shift sub)
    (hpc : a.piece = Desc.K3.pieceAt X l true) (hk : PS[k]? = some a) (z₀ : P)
    (pp : ℕ) (hB : digB SET x tl Dm.sent Dm.l3.rad pp = true)
    (hR : List.Forall₂ SameAs q.ds (Desc.First.Look.P.ofPlace SET true x).rounds)
    (hcap : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    (hIn : InOrderReads Mg)
    (f : P → Statement × TreeBook → (s : Sending) → (i : Fin s.l.length) →
      Option ((Johnson.Pack.sigOf Dm.sent.codes s.l).om i).Smp)
    (hread : ∀ z s, Dm.smp (z, s) = f z (s.st, s.book))
    (R : DigRestR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch claim Dm.smp Dm.ms a a' k l sub x tl
      smp q b' told) :
    SeatLawsR linksFull PS k q Dm.N (mgAll Dm Mg) Rch b' :=
  seatLawsR_of_digMeanR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch claim readers codes shape a k l
    sub x tl smp q b' h hOk hk hi hsub hpcT hpc hx pp hB hback hR hcap
    (digMeanR_mgAll Dm Mg Rch claim a a' k l sub x tl smp q b' told readers codes shape h hback hx
      hi hsub hpcT hpc hk z₀ hD hd hIn f hread R)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digMeanR_mgAll
#print axioms VerifiableInference.OnPublicFiles.seatLawsR_mgAll
