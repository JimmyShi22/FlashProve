-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03LeftAt.lean: the kind "lookup" (K3): THE ASSEMBLY AT THE CLOSED CONSTANT: `K3LeftR`
(Johnson/Desc/Sound/MgAt/K3OwedLeft.lean: what is left of the kind's ledger) FROM THE SHORTER
`K3ShortR` (Johnson/Desc/Sound/MgAt/K3Short.lean), at num := `At.num Zp`, tls :=
`Meaning.tlAt (At.X Zp)`, tok := fun w => `tokVOf` w.tok, seats := `At.seats Zp`, told :=
`At.told cF`.

PAID HERE, AT EACH OF THE 24 CALLS' PLACES IN FRONT OF THE HEAD's: the conjunct on `lookAt` and the
fields that are theorems in the goals' scope (`attOwed_scope`, `layOwed_scope`: the lookups'
authors') · slots (`k03_slots_att`, `k03_slots_lay`: Johnson/P5J/K03SlotsAt.lean) · some, sent, fits
(`k03_calls_seats`: Johnson/P5J/K03SeatsAt.lean) · seated (the head's plan) · book, tells
(`k03_book_at`: true by the numbers' own make · `k03_tells_at`: Johnson/P5J/K03BookAt.lean) · base
(`k03_base_at`; of its three tests fenceFit alone is left) ·
stand, pubs (the lookups' authors' closed tests by the kernel) · hid, small (by unfolding) · reads
(`k03_reads_at`: Johnson/P5J/PadsFreeAt.lean, under the test padsAtZ) · objects
(`k03_objects_att`, `k03_objects_lay`: Johnson/P5J/K03ObjAt.lean, from `ObjShortR`).

Main names: `k03_left_at` · `k03_cond_short`: so `h.K3Cond 𝔏` from the head, q₁ q₂ q₃, the door's
two rows, fenceFit, padsAtZ, `K3ShortR`, `ObjShortR` at the 24 calls, `DigShortR` at the 25
digits and `HeadRestR`.

AT THE 25 DIGITS' PLACES: `k03_dig_at` (Johnson/P5J/K03DigAt.lean), from `DigShortR`.

Limits: `K3ShortR`, `ObjShortR`, `DigShortR`, `HeadRestR` and the four tests are premises. The
head's family stands as it stands in the ledger. No member is known. At secondHashFunction alone. Nothing on
soundness by itself; nothing on hiding.


-/
import Johnson.P5J.K03CondAt
import Johnson.P5J.K03TermsCalls
import Johnson.P5J.K03SeatsAt
import Johnson.P5J.K03DigAt
import Johnson.P5J.K03BookAt
import Johnson.P5J.K03ObjAt
import Johnson.P5J.K03SlotsAt
import Johnson.Desc.Sound.MgAt.K3Short
import Johnson.Desc.Sound.MgAt.K3CallsOwedScope
import Johnson.Desc.Sound.MgAt.K3CallsStand
import Johnson.Desc.Sound.MgAt.K3Tests
import Johnson.P5J.PadsFreeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model OnBytes.Road
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain KindName Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (attAt layAt digAt lookAt)
open VerifiableInference.Desc.Kinds.Head.Law (OffPad.padsAtZ)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- In scope attention's reader's place is the table's own. -/
theorem k03_look_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {y : VerifiableInference.Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
    (hx : attAt (At.X Zp) l = some (y, A, tl)) : lookAt (At.X Zp) l false = some y := by
  have ho := attAt_odd hx
  obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
  exact (VerifiableInference.Desc.First.Look.attAt_letters h.toAtMg.scope h.toAtMg.reads
    h.toAtMg.pubOne (by omega) hx).2.2.2

/-- The like at the layers'. -/
theorem k03_look_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {y : VerifiableInference.Desc.First.Look.Place}
    (hx : layAt (At.X Zp) l = some y) : lookAt (At.X Zp) l false = some y := by
  obtain ⟨hp4, hN, -, -⟩ :=
    _root_.Meaning.scope_plans h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne
  have he := layAt_even hp4 hN hx
  obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
  exact (VerifiableInference.Desc.First.Look.layAt_letters h.toAtMg.scope h.toAtMg.reads
    h.toAtMg.pubOne (by omega) hx).1

/-- In scope the layers' reader answers in front of the head's segment alone. -/
theorem k03_lay_lt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {y : VerifiableInference.Desc.First.Look.Place}
    (hx : layAt (At.X Zp) l = some y) : l < 24 := by
  obtain ⟨hp4, hN, -, -⟩ :=
    _root_.Meaning.scope_plans h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne
  have he := layAt_even hp4 hN hx
  omega

set_option maxHeartbeats 4000000 in
/-- **What is left of the ledger, from the shorter structures.** -/
theorem k03_left_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (idx : ℕ → ℕ → ℕ)
    (arrs : Array (Nat × String))
    (hg : VerifiableInference.Desc.First.fenceFit (At.N Zp cF) linksFull
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true) = true)
    (hp : OffPad.padsAtZ Zp = true)
    (nos : ℕ → Array ℕ) (n : ℕ → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (M : List OracleShape)
    (S : ∀ l < 25, ∀ y tl, digAt (At.X Zp) l = some (y, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigShortR
          (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
            (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
          (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l y q b' (nos l) (n l) Ld M)
    (Oa : ∀ l < 25, ∀ y A tl, attAt (At.X Zp) l = some (y, A, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        ObjShortR
          (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
            (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
          (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q b' Ld M)
    (Ol : ∀ l < 25, ∀ y, layAt (At.X Zp) l = some y →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        ObjShortR
          (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
            (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
          (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q b' Ld M)
    (Hd : ∀ y, VerifiableInference.Desc.Kinds.Head.Law.headAt (At.X Zp) = some y →
      ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
        HeadRestR
          (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
            (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
          (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (At.seats Zp) s₀ y q b' arrs
          (IM.k3Place 24 false) (MgAt.nextOf 24 false) (At.told cF))
    (V : K3ShortR
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes Zp.first.shape (h.toAtMg.row 𝔏)
      (At.num Zp) idx (_root_.Meaning.tlAt (At.X Zp))) :
    K3LeftR
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes Zp.first.shape (h.toAtMg.row 𝔏)
      (At.seats Zp) s₀ (At.num Zp) idx (_root_.Meaning.tlAt (At.X Zp))
      (fun w => tokVOf w.tok) (At.told cF) arrs where
  fold := V.fold
  dig := k03_dig_at h 𝔏 q₁ q₂ q₃ hg nos n Ld M S
  att := fun l hl y A tl hx q hq b' hb' =>
    have S := V.att l hl y A tl hx q hq b' hb'
    have T := k03_calls_seats h hl (k03_look_att h hl hx)
    attOwed_scope h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne rfl hl hx S.tie S.one S.own
      h.toAtMg.plan.hG
      (k03_base_at h.toAtMg 𝔏 q₁ q₂ q₃ (k03_blocks_at h.toAtMg) (k03_bookHeld_at Zp Np cF) hg l hl
        false q hq)
      (k03_slots_att h (by have := attAt_odd hx; omega) hx) (stand_at hl) (k03_book_at Zp cF)
      (k03_tells_at h.toAtMg l hl false)
      (hfit_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl) (k03_hid h)
      (k03_small h)
      (k03_reads_at h hp)
      (k03_objects_att h Ld M hl hx q b' (Oa l hl y A tl hx q hq b' hb')) S.othersPub S.othersP
      S.rides T.1 T.2.1 T.2.2
  lay := fun l hl y tl hx ht q hq b' hb' =>
    have S := V.lay l hl y tl hx ht q hq b' hb'
    have T := k03_calls_seats h hl (k03_look_lay h hl hx)
    layOwed_scope h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne rfl hl hx ht S.tie S.one S.own
      h.toAtMg.plan.hG
      (k03_base_at h.toAtMg 𝔏 q₁ q₂ q₃ (k03_blocks_at h.toAtMg) (k03_bookHeld_at Zp Np cF) hg l hl
        false q hq)
      (k03_slots_lay h (k03_lay_lt h hl hx) hx) (stand_at hl) (k03_book_at Zp cF)
      (k03_tells_at h.toAtMg l hl false)
      (hfit_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl) (k03_hid h)
      (k03_small h)
      (k03_reads_at h hp)
      (k03_objects_lay h Ld M hl hx _ tl q b' (Ol l hl y hx q hq b' hb')) S.othersPub S.othersP
      S.rides T.1 T.2.1 T.2.2
  head := Hd

/-- **THE KIND's CONDITION, FROM THE SHORTER STRUCTURE.** -/
theorem k03_cond_short (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (idx : ℕ → ℕ → ℕ)
    (arrs : Array (Nat × String))
    (z₀ : ProofFile.InstPub)
    (hDig : VerifiableInference.Desc.K3Asks.digRow (At.X Zp)
      (VerifiableInference.Desc.K3Asks.sentOf Zp) = true)
    (hHead : VerifiableInference.Desc.K3Asks.headRow (At.X Zp) = true)
    (hg : VerifiableInference.Desc.First.fenceFit (At.N Zp cF) linksFull
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true) = true)
    (hp : OffPad.padsAtZ Zp = true)
    (nos : ℕ → Array ℕ) (n : ℕ → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (M : List OracleShape)
    (S : ∀ l < 25, ∀ y tl, digAt (At.X Zp) l = some (y, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigShortR
          (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
            (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
          (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l y q b' (nos l) (n l) Ld M)
    (Oa : ∀ l < 25, ∀ y A tl, attAt (At.X Zp) l = some (y, A, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        ObjShortR
          (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
            (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
          (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q b' Ld M)
    (Ol : ∀ l < 25, ∀ y, layAt (At.X Zp) l = some y →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        ObjShortR
          (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
            (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
          (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q b' Ld M)
    (Hd : ∀ y, VerifiableInference.Desc.Kinds.Head.Law.headAt (At.X Zp) = some y →
      ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
        HeadRestR
          (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
            (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
          (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (At.seats Zp) s₀ y q b' arrs
          (IM.k3Place 24 false) (MgAt.nextOf 24 false) (At.told cF))
    (V : K3ShortR
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes Zp.first.shape (h.toAtMg.row 𝔏)
      (At.num Zp) idx (_root_.Meaning.tlAt (At.X Zp))) :
    h.K3Cond 𝔏 :=
  k03_cond_at h 𝔏 q₁ q₂ q₃ s₀ (At.num Zp) idx (_root_.Meaning.tlAt (At.X Zp))
    (fun w => tokVOf w.tok) (At.told cF) arrs z₀ hDig hHead
    (k03_left_at h 𝔏 q₁ q₂ q₃ s₀ idx arrs hg hp nos n Ld M S Oa Ol Hd V)

end P5J

#print axioms P5J.k03_look_att
#print axioms P5J.k03_look_lay
#print axioms P5J.k03_left_at
#print axioms P5J.k03_cond_short
