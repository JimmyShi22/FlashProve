-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsObj.lean: the lookup on the digits of a segment's approximate range
proof: THE FIELD fObj OF DigMeanR AND DigRestR (DigObjR, Johnson/Desc/First/Look/K3DigitsBare.lean)
AT THE COMPOSED MEANING mgAll Dm Mg (Johnson/Desc/Sound/MgAll.lean)
: forms "objects" behind an accept gives the third item of the row out. One theorem: a
joining. NO RESULT ON THE PROTOCOL.

Main name.
  digObjR_mgAll: DigObjR X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch claim k l sub x tl q b'.
HOW. digits_fObj (Johnson/Top/H/Keep/FormsObjectsDigits.lean) at the state behind: the term IS
meaningForms … over the parts beneath, by its make · its premise «the heard rows are bare» by
k3_digits_seated_bare, whose Sized F comes from the promise in front: lookIn is open
(digits_lookIn_open), says k3LookIn (fLook_at under k3At_mgAll), and so k3OnIn (k3LookIn_onIn,
k3OnIn_ledger) · its premise MaskOk: handed in (DigMaskR).
WHAT IS LEFT, EACH BOOKED.
  ON THE LETTER claim: hA (AtS2: its claims are plain forms).
  A TEST ON THE PLAN: hB (maskB) · hfit (pubFit at the term's own list of extra public tests).
  ON THE TERM's PARAMETERS (the readers of the claims on linear forms): hrun, hah, hlink, pass with
    hpass, hfind.
  FACTS ALONG THE FOLD, UNDER fObj's PREMISES: hM (DigMaskR: MaskOk's five clauses at the part of
    the state behind).
  THE PLACE AND THE PIECE: h, hOk, hback, hx, hi, hsub, hpcT, hpc, hk.
OBJECT. One term of the type Meaning; as in K3DigitsSeatLaws.lean.
USER. digOwed_mgAll (MgAt/K3DigitsOwed.lean), at DigOwedR's field fObj. Meant: whoever fills
DigRestR.fObj at the term.
LETTERS. Dm, Mg, Rch, claim; a, k, l, sub, x, tl, q, b'; readers, codes, shape; pr, H, lk, pass.


Compiled with the whole library.
Limits. A rule over letters. The type of claims is Desc.Claim here (digits_fObj's). Nothing on
hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3At
import Johnson.Desc.First.Look.K3DigitsBare
import Johnson.Top.H.Keep.FormsObjectsDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Meaning shift pubFit)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Desc.Claim)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **fObj AT THE COMPOSED MEANING.** -/
theorem digObjR_mgAll (a : Desc.Place) (k l : ℕ) (sub : ModelPart)
    (x : Desc.First.Look.Place) (tl : HTailF2)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim
      (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Desc.Claim)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = [])
    (hx : digAt X l = some (x, tl)) (hi : a.link = some l)
    (hsub : linksFull[l]? = some sub) (hpcT : a.piece = 7 + shift sub)
    (hpc : a.piece = Desc.K3.pieceAt X l true) (hk : PS[k]? = some a)
    (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (hA : AtS2 (Desc.K3.seatDigits claim))
    (hB : maskB Dm.sent (digList x Dm.sent Dm.l3.rad) x.link x.arrays.ns = true)
    (pr : ℕ) (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim)
    (hrun : (pr, "objects") ∈ Dm.runs l (7 + shift sub) "objects")
    (hah : Dm.ah pr "objects" = false) (hlink : Dm.Rd l = readersOfLink H lk)
    (pass : Desc.First.S → Desc.First.S → Prop) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatDigits claim)))
    (hM : DigMaskR X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch Dm.ms k l x q b') :
    DigObjR X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch claim k l sub x tl q b' := by
  have hlook : lookAt X l true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  have e7 : 7 + shift sub = Desc.K3.pieceAt X l true := hpcT.symm.trans hpc
  have hOpen := digits_lookIn_open (mgAll Dm Mg).more linksFull PS k a l sub hfit hk hi hsub hpcT
    (.lookIn l (7 + shift sub)) (by simp)
  intro B' hN z u τ v hout hu hr hun T hOut DL hv w hw g F' hF' hg
  have hOnIn : Desc.K3.k3OnIn
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) u.1 = true := by
    have hu' := hu
    obtain ⟨-, hor⟩ := hu'
    rcases hor with hbad | ⟨hBb, -, -, -⟩
    · exact absurd hun hbad
    · simp only [Bool.and_eq_true] at hBb
      have hp : (mgAll Dm Mg).pub (.lookIn l (7 + shift sub)) (z, u.1) = true :=
        List.all_eq_true.1 hBb.1.2 _ (List.mem_append_left _ hOpen)
      rw [e7] at hp
      exact k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l true hlook z u.1 hp)
  obtain ⟨Fk, hf, hz, -⟩ := k3OnIn_ledger hOnIn
  unfold mgAll at hw
  exact digits_fObj x tl Dm.sent Dm.l3.rad (fun j => Dm.l3.seat x.link true j.1) Dm.l3.arr Dm.ms
    Dm.Rd Dm.runs Dm.St Dm.after Dm.N Dm.wt Dm.rw Dm.ah _ l (7 + shift sub) pr H lk claim hA hB
    hrun hah hlink pass hpass hfind z v.1 _ w hw (hM B' hN z u τ v hout hu hr hun T hOut DL hv) g
    F' hF' hg
    (k3_digits_seated_bare claim readers X codes shape a b' B' h hOk hN.1 l hi hpc
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Desc.Claim (Desc.Wit (CellsQ rows cols) Tok MsgT))
      rfl hback u v τ hout hf hz g hg)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digObjR_mgAll
