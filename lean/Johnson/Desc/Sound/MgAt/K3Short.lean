-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3Short.lean: the kind "lookup" (K3): THE LEDGER's TWO FAMILIES AT THE 24
CALLS' PLACES IN FRONT OF THE HEAD's, SHORTER: `CallsShortR`: the six fields of `AttOwedR` and of
`LayOwedR` (Johnson/Desc/Sound/MgAt/K3Owed.lean; in both the six are one text) that are neither
theorems in the goals' scope nor paid at the closed constant (Johnson/P5J/K03LeftAt.lean): THREE
TESTS: tie · one · own; THREE FIELDS "WHERE THE PIECE ACCEPTS": othersPub · othersP · rides. And
`K3ShortR`: the fields fold, att, lay of `K3LeftR` (Johnson/Desc/Sound/MgAt/K3OwedLeft.lean) with it
in the two families' places, without the conjunct on `lookAt`. (objects: `ObjShortR`,
Johnson/P5J/K03ObjAt.lean · the digits' family: `DigShortR`, Johnson/P5J/K03DigAt.lean · the head's
family stays `HeadRestR`.)

THE FIELDS' TEXTS ARE THE LEDGER's OWN, LAID HERE BY A PROGRAM; Lean holds each against its original
where the structure is used.

Limits: definitions alone. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.Sound.MgAt.K3OwedLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc smpWc strWc)
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubFit shift sameStand bookFit pubStep pubRowM stepOpen pubOfItems)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Cl)
  (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (tls : ℕ → HTailF2)
  (a : Desc.Place) (k l : ℕ) (x : Desc.First.Look.Place)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

/-- **What is left at a segment's calls.** -/
structure CallsShortR (tl : HTailF2)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) : Prop where
  /-- test on the public parameters and the layout -/
  tie : linkTieB X Dm.sent Dm.rad3 num idx x.link tl = true
  /-- test on the list of rounds: a member's number is its label's; no pad's place -/
  one : OneNumber X Dm.sent Dm.rad3 num idx tls x.link seatL Dm.arr id
  /-- test on the table's numbers: one tenant with that number; no pad's place -/
  own : OwnNamed X Dm.sent num tls x.link Dm.arr Dm.ms Dm.N
  /-- accept: the other kinds' public tests that are open behind hold behind -/
  othersPub : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
    ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull a) ++
        pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
          (Desc.First.rowOf linksFull a)),
      p ∉ paidCallsR l 2 → (mgAll Dm Mg).pub p (z, v.1) = true
  /-- accept: the like for the public sentences -/
  othersP : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
    ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull a),
      p ≠ .left l → (mgAll Dm Mg).pubP p (z, v.1)
  /-- accept: every open item that the row does not close rides -/
  rides : RidesAtR Dm.N (mgAll Dm Mg) Rch k q b'

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  {Fr : Frame} (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (codes : Codes) (shape : Params.ReqShape)
  (pieces : List (Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl
    (Desc.Wit (CellsQ rows cols) Tok MsgT)))
  (seats : List (ℕ × ℕ)) (s₀ : Desc.First.S)
  (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ → ℕ) (tls : ℕ → HTailF2)
  (tok : Desc.Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V)
  (told : List (List Desc.Oracle)) (arrs : Array (Nat × String))

/-- **What is left of the ledger at the fold and the 24 calls' places, shorter.** -/
structure K3ShortR : Prop where
  /-- what the kind's paid fields spend of the facts along the fold -/
  fold : K3Fold Rch 𝔇.sent
  att : ∀ l < 25, ∀ x A tl, attAt X l = some (x, A, tl) →
    ∀ q, pieces[k3K l false]? = some q → ∀ b', k3Const X codes shape l false = some b' →
      CallsShortR 𝔇 Mg Rch num (idx l) tls (IM.k3Place l false) (k3K l false) l x tl q b'
  lay : ∀ l < 25, ∀ x tl, layAt X l = some x → tlAt X l = some tl →
    ∀ q, pieces[k3K l false]? = some q → ∀ b', k3Const X codes shape l false = some b' →
      CallsShortR 𝔇 Mg Rch num (idx l) tls (IM.k3Place l false) (k3K l false) l x tl q b'

end

end VerifiableInference.OnPublicFiles
