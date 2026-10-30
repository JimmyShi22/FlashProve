-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsFill.lean: the lookup on the digits of a link's smallness test: ONE
OF THE TABLE OF JOINTS' LETTERS, FILLED AT THE DIGITS, as a definition in this file's own letters:
the part «every digit is a row of its table»; and t1's lower storey from the public item «the
lookup's condition in front of its block» as Johnson/Desc/First/Look/K3LookIn.lean fills it for both
seats. A definition, statements and proofs. NO SOUNDNESS IS CLAIMED.

Main names.
  digPart x tl D rad seatT arr w: every digit, read off the witness's messages at its seat by the
    closed caller, is a row of its table: DgP.DigIn at digMu.
  digPart_of_front: the end theorem's relation in front gives it.
  k3_digits_t1': t1's lower storey from k3LookIn at the digits' place, the three equations on the
    record's codes, shape and layout, and «no collision» at every member.
OBJECT. No block's text: the closed caller's reading digMu (K3DigitsGoodIn.lean); k3LookIn.
USER. K3DigitsRow.lean imports this file; outside this file nothing calls its declarations by name.
Of the table's filling (Meaning.constr at the part
lookDigits): nobody yet.
LETTERS. x, tl, D, rad, seatT, arr; set, claim, smp.

Compiled with the whole library.
Limits. A definition and unfoldings. digPart is this file's own clause: whether it is what the
smallness test's law leans on is that test's files' to say.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsTies
import Johnson.Desc.First.Look.K3LookIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {S Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (x : Desc.First.Look.Place) (tl : HTailF2) (D : Desc.First.Look.Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)

/-- **Every digit is a row of its table**, at the witness's messages. -/
def digPart (w : Desc.Wit Cells Tok MsgT) : Prop :=
  DgP.DigIn tl (enOf x.arrays) (digMu x D rad seatT arr w)

variable {x tl D rad}

theorem digPart_of_front
    (smp : S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)
    (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (h : DigFront G x tl D rad seatT arr smp a w) : digPart x tl D rad seatT arr w :=
  h.2

/-- **t1, the lower storey, from the filled public item.** -/
theorem k3_digits_t1'
    (smp : Desc.First.S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)
    (claim : Aff → Cl) {set : Params.Setting} (a : Desc.First.S × Fr.E.Str)
    (hIn : k3LookIn (Desc.First.Look.P.ofPlace set true x) (D.arrayOf.getD x.link #[]) a.1 = true)
    (hc : a.1.st.codes = D.codes) (hs : a.1.live.frame.shape = D.shape)
    (hl : a.1.live.rows.layout = D.layout)
    (hCf : ∀ i, CfAt G D.codes (digList x D rad) seatT smp i a.1 (strsOf Fr a.2)) :
    DigOn G x D rad seatT smp (Desc.K3.seatDigits claim).fork (OwnIs D x.link) a :=
  k3_digits_t1 G seatT smp claim a (ownIs_of hIn hc hs hl) hCf (k3LookIn_onIn hIn)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digPart_of_front
#print axioms VerifiableInference.OnPublicFiles.k3_digits_t1'
