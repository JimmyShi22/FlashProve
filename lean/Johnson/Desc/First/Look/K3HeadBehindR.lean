-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeadBehindR.lean: the kind "lookup" (K3), the lookup argument on the calls
at the output head's link: THE FIELD "behind" OF `HeadAtTableR`
(Johnson/Desc/First/Look/K3HeadAtTableR.lean) FROM `BehindPartsR`
(Johnson/Desc/First/Look/K3CallsBehindR.lean) AT THE PIECE 3: one call of `calls_behindR`.

Main name: `head_behindR`. Two of the field's premises go unspent (what is known of the ledger
behind; that it is free above its next slot).

`BehindPartsR` names no item that has been struck from the composed meaning: AS MEMBERS OF THE
OPEN PUBLIC SET at the border it asks lookIn, freeAbove and linkFresh (they are:
Johnson/Desc/Sound/MgAt/K3Open.lean, by the kernel); its other fields speak of what items say
(lookOut, ledger, left among them) and of what rides: whether these hold at that meaning is not
shown here.

THE WEIGHT LIES IN ITS FIELD bPub: beside the five items that the rule pays
itself, these are open behind the place at mgAll, and whoever pays bPub must
SHOW each there: look 24 (this row makes it) · ledger.treesAre 24 (it reads the ledger the lookup
argument writes) · frame.sentIs 24 · tokenSmall · formsInT 24 3 "objects" · indexIs · indexThere.

Limits: `BehindPartsR`, hs and hY are premises. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3CallsBehindR
import Johnson.Desc.First.Look.K3HeadAtTableR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Maker Run
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning Numbers)

/-- **"behind", at the head's calls, second form.** -/
theorem head_behindR {P Cl Cells Tok : Type} {Fr : Frame} {x : Desc.First.Look.Place}
    {set : Params.Setting} {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)}
    {links : List ModelPart}
    {ps : List Desc.Place} {pi : P} {k m : ℕ} {arrs : Array (Nat × String)}
    {p p' : Desc.Place} {told : List (List Desc.Oracle)}
    {Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop}
    {Rc : Desc.First.S × Fr.E.Str → Prop} (Q : Fork → Prop) (claim : Aff → Cl)
    (hs : (Desc.First.Look.P.ofPlace set false x).shape = some x.fs)
    (hY : ∀ a c, Yes a c →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
          (Desc.First.Look.P.ofPlace set false x) guests).decide a.1 rs cols = .ok c.1)
    (B : BehindPartsR (Fr := Fr) x set N Mg links ps pi k m 3 arrs p p' told Yes Rc) :
    ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
      a.1.failed = none → Yes a b → SameBut a.1 b.1 →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace set false x) b.1 = true →
      Mg.decodes (pi, b.1) (strsOf Fr b.2) →
      K3LeftAt (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next Q
        b.1 →
      FreeAt (Desc.K3.seatCalls claim).fork b.1 → onQ N Mg links ps (fun s => (pi, s)) (k + 1) b :=
  fun a b ha hr hu hy hsb hout hdec _ _ => calls_behindR claim hs hY B a b ha hr hu hy hsb hout hdec

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.head_behindR
