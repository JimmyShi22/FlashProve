-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3DigitsMaskAt.lean: the lookup on the digits of a segment's approximate
range proof, AT THE TABLE OF JOINTS: THE PREMISE DigMaskR OF digObjR_mgAll (K3DigitsBare.lean:
MaskOk at the part of the verifier's state behind the digits' sub-protocol, under the hands of the
field fObj), from: SEVEN FACTS ALONG THE FOLD AT THE BORDER IN FRONT, each a plain premise · one
public test that is open at the border behind (freeAbove) · the promise's own conjunct bookAt there
· tests on the list of rounds and on the table's list of members. One theorem: a call of maskOk_at
(K3DigitsMaskOk.lean). NO SOUNDNESS IS CLAIMED.

Main name.
  digMaskR_of_facts: … → DigMaskR X Dn L N Mg Rch ms k l x q b'.
HOW THE FACTS IN FRONT REACH THE STATE BEHIND. They read the open segment's link context, the
statement and the book alone, which the lookup's accept leaves (SameBut, in the field's hands).
EACH PREMISE, BOOKED.
  FACTS ALONG THE FOLD, AT THE BORDER k, AT A REACHED STATE WITHOUT A MARK: hLive, hGroups (the
    sentences of FoldFacts' fields liveShape, liveGroups) · hLink, hNext, hOwn (three of its field
    frameIs' clauses: the live frame's link, next, own) · hSeats, hShapes (seatsCarried, msgShapes).
  TESTS ON THE TABLE: askFree (freeAbove l is open at the border k + 1).
  ON THE MEANING: pubFree (its test at freeAbove l says the ledger has n slots and is free above).
  TESTS ON THE LIST OF ROUNDS: hn (n ≤ x.arrays.ns) · hTests (maskTestsB, K3MaskOkTools.lean).
  TESTS ON THE TABLE's LIST OF MEMBERS: hsome (DigSits' field some) · h6 (oneShapeB).
OBJECT. The table of joints' promise at two borders.
USER. digObjR_mgAll's premise hM (Johnson/Desc/Sound/MgAt/K3DigitsObj.lean).
LETTERS. X, Dn, L, N, Mg, Rch, ms; k, l, x, q, b'; nos, n, Ld, M.


Compiled with the whole library.
Limits. One way. A rule over letters.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsMaskOk
import Johnson.Desc.First.Look.K3DigitsBare
import Johnson.Desc.First.Look.K3AttAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Pub Meaning Numbers bookAt pubSets)

section
variable {P Cl Cells Tok : Type} {Fr : Frame} (X : Verify.Public)
  (Dn : Desc.First.Look.Sent) (L : K3Letters Cells Tok) (N : Numbers)
  (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **DigMaskR FROM THE FACTS ALONG THE FOLD, THE PROMISE AND THE TESTS.** -/
theorem digMaskR_of_facts (ms : List Mem) (k l : ℕ) (x : Desc.First.Look.Place)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit Cells Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) {nos : Array ℕ} {n : ℕ} {Ld : Desc.K12.Door.Laid}
    {M : List OracleShape}
    (hLive : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
      a.1.live.frame.shape = Dn.shape)
    (hGroups : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
      a.1.live.frame.groups = reqGroups a.1.live.frame.shape)
    (hLink : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
      a.1.live.frame.link = x.link)
    (hNext : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
      a.1.live.frame.next = .laterOrClose)
    (hOwn : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
      a.1.live.frame.own = nos)
    (hSeats : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
      Desc.K12.Door.atFirstSeats Ld a.1 = true)
    (hShapes : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
      Desc.K12.Door.atFirstShapes M a.1 = true)
    (askFree : Pub.freeAbove l ∈ (pubSets Mg.more linksFull PS)[k + 1]?.getD [])
    (pubFree : ∀ (z : P) s, Mg.pub (.freeAbove l) (z, s) = true →
      H2K5.Door.freeAboveB n s = true)
    (hn : n ≤ x.arrays.ns)
    (hTests : maskTestsB (maskOwnIx Dn x.link) 0 nos N PS[k + 1]? Ld M (N.group l)
      (L.seat x.link true) = true)
    (hsome : ∀ i, ∃ y ∈ ms,
      Alike y ⟨⟨digList x Dn L.rad, fun j => L.seat x.link true j.1⟩, i⟩)
    (h6 : oneShapeB ms = true) :
    DigMaskR X Dn L N Mg Rch ms k l x q b' := by
  intro B' _ z a τ b _ _ hr hu T _ _ hb p hseg
  have hub : b.1.failed = none := T.failed.trans hu
  obtain ⟨hq, -⟩ := onQ_arm hb hub
  have hbook : bookAt N PS[k + 1]? b.1 = true := by
    obtain ⟨-, hm | ⟨h1, -⟩⟩ := hb
    · exact absurd hub hm
    · simp only [Bool.and_eq_true] at h1
      exact h1.2
  have eLive : b.1.live = a.1.live := by
    unfold Desc.First.S.live
    rw [T.link]
    cases a.1.link? with
    | none => exact T.check
    | some C => rfl
  refine maskOk_at x Dn L.rad (fun j => L.seat x.link true j.1) ms (N.group l)
    (L.seat x.link true) (fun _ => rfl) ?_ ?_ ?_ ?_ ?_ (pubFree z _ (hq _ askFree)) hn hbook ?_ ?_
    hTests hsome h6 p hseg
  · rw [eLive]
    exact hLive z a hr hu
  · rw [eLive]
    exact hGroups z a hr hu
  · rw [eLive]
    exact hLink z a hr hu
  · rw [eLive]
    exact hNext z a hr hu
  · rw [eLive]
    exact hOwn z a hr hu
  · have h0 := hSeats z a hr hu
    unfold Desc.K12.Door.atFirstSeats at h0 ⊢
    rw [T.book]
    exact h0
  · have h0 := hShapes z a hr hu
    unfold Desc.K12.Door.atFirstShapes at h0 ⊢
    rw [T.st]
    exact h0

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digMaskR_of_facts
