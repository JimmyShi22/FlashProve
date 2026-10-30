-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3Sig.lean: the kind "lookup" (K3): WHAT THE COMPOSED MEANING `mgAll 𝔇 Mg`
(Johnson/Desc/Sound/MgAll.lean) SAYS OF AN ORACLE MESSAGE THAT WAS SENT EARLIER DOES NOT TURN WHERE
A SUB-PROTOCOL THAT LEAVES THE STATEMENT AND THE BOOK ACCEPTS: at all fifty places at once.

Main names (p: any piece over the verifier's state; a, b: the statements in front and behind an
accepting; (j, t): a tenant of a tree sent before the piece, j < p.base):
  `k3Mg_pin`: the pin at (j, t) behind ⟺ in front, at every witness.
  `k3Mg_pinBack`: the field pinBack of `AttAtTable`, `LayAtTable` and `HeadAtTable`, to the letter.
  `k3Mg_shown`, `k3Mg_noColl`, `k3Mg_held`: "shown", "no collision" and "the OOD sample is held"
    ride forward: what the lookups' authors' `BehindParts` asks as bShown, bNoColl, bHeld.

A joining: Johnson/Desc/Sound/SigRides.lean at `mgAll_pin`, `mgAll_shown`, `mgAll_noColl`,
`mgAll_held`. Kind-free in truth: of K3 only "an accepting leaves the statement and the book" is
spent (`SameBut`).

Limits: hsmp (the reader of OOD samples reads the state's statement alone) is a premise on 𝔇: it
holds of `smpNamed` (Johnson/Desc/Sound/SmpNamed.lean: `smpNamed_same`). "j < p.base" is a premise
at each tenant. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.SigRides
import Johnson.Desc.First.Look.K3CallsTurns

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Maker Run
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Wit)

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  {C : Run.PQ.CK}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  (hsmp : ∀ (z : P) (s s' : Desc.First.S), s'.st = s.st → 𝔇.smp (z, s') = 𝔇.smp (z, s))
  (z : P) (p : Piece C Fr Desc.First.S Cl (Wit (CellsQ rows cols) Tok MsgT))
  (a b : Desc.First.S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (hb : p.ior.red.out a τ = some b)

include hsmp hb in
/-- **The pin, behind and in front.** -/
theorem k3Mg_pin (hst : b.1.st = a.1.st) (j t : ℕ) (hj : j < p.base)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).pin j t (z, b.1) (strsOf Fr b.2) w ↔
      (mgAll 𝔇 Mg).pin j t (z, a.1) (strsOf Fr a.2) w :=
  pinJT_rides 𝔇.cs 𝔇.G 𝔇.arr (fun s => 𝔇.smp (z, s)) p 𝔇.ms j t hj a b τ hb
    (fun x _ _ => congrFun (congrFun (hsmp z a.1 b.1 hst) x.1) x.2) w

include hb in
/-- **"Shown" rides.** -/
theorem k3Mg_shown (j t : ℕ) (hj : j < p.base)
    (h : (mgAll 𝔇 Mg).shown j t (strsOf Fr a.2)) : (mgAll 𝔇 Mg).shown j t (strsOf Fr b.2) :=
  shownJT_rides 𝔇.cs 𝔇.G p 𝔇.ms j t hj a b τ hb h

include hsmp hb in
/-- **"No collision" rides.** -/
theorem k3Mg_noColl (hst : b.1.st = a.1.st) (j t : ℕ) (hj : j < p.base)
    (h : (mgAll 𝔇 Mg).noColl j t (z, a.1) (strsOf Fr a.2)) :
    (mgAll 𝔇 Mg).noColl j t (z, b.1) (strsOf Fr b.2) :=
  noCollJT_rides 𝔇.cs 𝔇.G (fun s => 𝔇.smp (z, s)) p 𝔇.ms j t hj a b τ hb
    (fun x _ _ => congrFun (congrFun (hsmp z a.1 b.1 hst) x.1) x.2) h

omit p τ in
/-- **"The OOD sample is held" rides.** -/
theorem k3Mg_held (hst : b.1.st = a.1.st) (hbk : b.1.book = a.1.book) (j t : ℕ) :
    (mgAll 𝔇 Mg).held j t (z, b.1) = (mgAll 𝔇 Mg).held j t (z, a.1) :=
  smpHeld_rides a.1.st b.1.st a.1.book b.1.book j t hst hbk

end

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  {C : Run.PQ.CK}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **pinBack.** -/
theorem k3Mg_pinBack
    (hsmp : ∀ (z : P) (s s' : Desc.First.S), s'.st = s.st → 𝔇.smp (z, s') = 𝔇.smp (z, s))
    (z : P) (p : Piece C Fr Desc.First.S Cl (Wit (CellsQ rows cols) Tok MsgT)) (m : ℕ)
    (hbase : ∀ t ∈ 𝔇.N.sent m 0, t.1 < p.base) :
    ∀ (a b : Desc.First.S × Fr.E.Str) w, (∃ τ, p.ior.red.out a τ = some b) → SameBut a.1 b.1 →
      (∀ t ∈ 𝔇.N.sent m 0, (mgAll 𝔇 Mg).pin t.1 t.2 (z, b.1) (strsOf Fr b.2) w) →
      ∀ t ∈ 𝔇.N.sent m 0, (mgAll 𝔇 Mg).pin t.1 t.2 (z, a.1) (strsOf Fr a.2) w :=
  fun a b w ⟨τ, hb⟩ hs h t ht =>
    (k3Mg_pin 𝔇 Mg hsmp z p a b τ hb hs.st t.1 t.2 (hbase t ht) w).1 (h t ht)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3Mg_pin
#print axioms VerifiableInference.OnPublicFiles.k3Mg_shown
#print axioms VerifiableInference.OnPublicFiles.k3Mg_noColl
#print axioms VerifiableInference.OnPublicFiles.k3Mg_held
#print axioms VerifiableInference.OnPublicFiles.k3Mg_pinBack
