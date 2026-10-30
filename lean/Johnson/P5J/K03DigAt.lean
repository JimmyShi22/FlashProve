-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03DigAt.lean: THE KIND "LOOKUP" (K3): THE LEDGER's FIELD dig (the lookup on the digits, at all 25 segments) AT THE CONSTANT, BY ONE CALL OF digOwed_mgAll (Johnson/Desc/Sound/MgAt/K3DigitsOwed.lean), WITH WHAT IS STILL LEFT AS ONE STRUCTURE's FIELDS. One structure, one theorem. told := At.told cF is laid. k03_book_at · k03_tells_at · k03_blocks_at · k03_bookHeld_at (Johnson/P5J/K03BookAt.lean) pay hbf · hn of digOwed_mgAll and two premises of k03_base_at, and k03_digits_seats (Johnson/P5J/K03SeatsAt.lean) pays hSome · hSent · hFits from the head. A joining.

  DigShortR Dm Mg Rch l x q b' nos n Ld M : Prop: FIFTEEN FIELDS, EACH digOwed_mgAll's OWN BINDER's TEXT UNDER ITS OWN NAME (lifted by program):
    tests on the list of rounds: hB · hTests · h6 · hnS · accept: othersPub · othersP · rides · pubFree · facts on every reached state (seven): hLive · hGroups · hLink · hNext · hOwn · hSeats · hShapes.
  k03_dig_at: UNDER h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀, 𝔏 : Free … WITH ITS THREE EQUATIONS q₁ q₂ q₃, AND DigShortR AT EVERY SEGMENT: THE FIELD dig OF K3LeftR | K3ShortR TO THE LETTER, at 𝔇 := h.toAtMg.𝔇 h.𝔇 · Mg := mgBase · Rch := h.toAtMg.rch · the pieces := h.toAtMg.row 𝔏 · seats := At.seats Zp · told := At.told cF. ONE NAMED TEST STAYS A BINDER: hg (fenceFit).
(Where this and lean/THEOREM.md differ, the page
holds.)
  PAID INSIDE: hM (k03_hM) · hOk | hback (k03_pieces_at) · hbaseS (k03_base_at) · hrun · hah · hlink · pass | hpass · hfind (Johnson/P5J/K03ObjTerms.lean) · hSome | hSent | hFits (Johnson/P5J/K03SeatsAt.lean, at lookAt X l true = some x, which digAt binds).
  THE CLOSED TERMS PER SEGMENT l: pr := IM.k3Ix l true · lk := the head's own chain's link l · H := K9.holesAt X (headLink X) l lk · pass := passR.
  nos · n (per l) · Ld · M STAY LETTERS. THEY ARE ONE CHOICE FOR BOTH SIDES: the seven facts on reached states AND hTests | hnS | pubFree must hold at the SAME four. MEANT (BY READING; NOT CHECKED BY LEAN HERE, NOT EVALUATED): Ld := L with At.laid? Zp = some L · M := the planner's first chain's oracle messages' shapes · nos l := (At.foldD Zp cF L).ownAt l 3 · n l := the built link l's number of slots. pubFree ends in H2K5.Door.freeAboveB (Johnson/Desc/First/Att/Door/DoorBools.lean); the table's own item "freeAbove" is typed at the table's: that the two texts are one is not looked at here.
Limits. DigShortR is a premise: no member is shown. The head is a premise. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03ObjTerms
import Johnson.P5J.K03Terms
import Johnson.P5J.K03PiecesAt
import Johnson.P5J.K03SeatsAt
import Johnson.P5J.K03BookAt
import Johnson.Desc.Sound.MgAt.K3DigitsOwed
import Johnson.Desc.Sound.MgAt.K3OwedLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Pub Meaning shift pubFit pubSets pubStep pubRowM pubOfItems
  stepOpen openSets start sampledIn bookFit)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **What is left of the digits' ledger at segment l.** -/
structure DigShortR (l : ℕ) (x : Desc.First.Look.Place)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl)
    (nos : Array ℕ) (n : ℕ) (Ld : Desc.K12.Door.Laid) (M : List OracleShape) : Prop where
  othersPub : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
    SameBut u.1 v.1 → DigLeft u.1 v.1 →
    onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
    Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
    ∀ r ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[(k3K l true)]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place l true)) ++
      pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[(k3K l true)]?.getD [])
        (Desc.First.rowOf linksFull (IM.k3Place l true))),
    k3Like r = false → (mgAll Dm Mg).pub r (z, v.1) = true
  othersP : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
    SameBut u.1 v.1 → DigLeft u.1 v.1 →
    onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
    Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
    ∀ r ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[(k3K l true)]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place l true)),
    (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) → (mgAll Dm Mg).pubP r (z, v.1)
  rides : RidesAtR Dm.N (mgAll Dm Mg) Rch (k3K l true) q b'
  hB : maskB Dm.sent (digList x Dm.sent Dm.l3.rad) x.link x.arrays.ns = true
  hLive : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → a.1.live.frame.shape = Dm.sent.shape
  hGroups : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → a.1.live.frame.groups = reqGroups a.1.live.frame.shape
  hLink : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → a.1.live.frame.link = x.link
  hNext : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → a.1.live.frame.next = .laterOrClose
  hOwn : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → a.1.live.frame.own = nos
  hSeats : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → Desc.K12.Door.atFirstSeats Ld a.1 = true
  hShapes : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → Desc.K12.Door.atFirstShapes M a.1 = true
  pubFree : ∀ (z : P) s, (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true →
    H2K5.Door.freeAboveB n s = true
  hnS : n ≤ x.arrays.ns
  hTests : maskTestsB (maskOwnIx Dm.sent x.link) 0 nos Dm.N PS[k3K l true + 1]? Ld M
    (Dm.N.group l) (Dm.l3.seat x.link true) = true
  h6 : oneShapeB Dm.ms = true

end

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (digAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE LEDGER's FIELD dig AT THE CONSTANT.** -/
theorem k03_dig_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hg : VerifiableInference.Desc.First.fenceFit (At.N Zp cF) linksFull
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true) = true)
    (nos : ℕ → Array ℕ) (n : ℕ → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (M : List OracleShape)
    (S : ∀ l < 25, ∀ x tl, digAt (At.X Zp) l = some (x, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigShortR
          (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
          (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l x q b' (nos l) (n l) Ld M) :
    ∀ l < 25, ∀ sub, linksFull[l]? = some sub → ∀ x tl, digAt (At.X Zp) l = some (x, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigOwedR
          (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
          (h.toAtMg.𝔇 h.𝔇).G (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3
          (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch K3Lot.ofForm
          (h.toAtMg.𝔇 h.𝔇).ms (IM.k3Place l true) (MgAt.nextOf l true) (k3K l true) l sub x tl
          (smpDigits (At.seats Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad
            (h.toAtMg.𝔇 h.𝔇).l3.seat x) q b' (At.told cF) := by
  intro l hl sub hsub x tl hx q hq b' hb'
  have T := S l hl x tl hx q hq b' hb'
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have hlook : VerifiableInference.Desc.First.Look.lookAt (At.X Zp) l true = some x := by
    unfold VerifiableInference.Desc.First.Look.digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  have Sd := k03_digits_seats h hl hlook
  obtain ⟨lk, -, hlink, nm, run, hfd, hov⟩ := k03_hfind h l hl true
  have hrun := (k03_hrun h l sub hsub).2
  rw [← (k03_ix l hl sub hsub).2] at hrun
  exact digOwed_mgAll
    (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
    (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes Zp.first.shape k03_hM hl
    hsub hx _ q b' hb' (Pc.planOk l hl true b' hb') (Pc.back l hl true q hq) (At.told cF)
    (k03_book_at Zp cF) (k03_tells_at h.toAtMg l hl true)
    (k03_base_at h.toAtMg 𝔏 q₁ q₂ q₃ (k03_blocks_at h.toAtMg) (k03_bookHeld_at Zp Np cF) hg l hl true q hq) T.othersPub T.othersP T.rides
    Sd.1 Sd.2.1 Sd.2.2 T.hB (IM.k3Ix l true) _ lk hrun (k03_hah h _) hlink passR k03_hpass
    ⟨nm, run, hfd, hov⟩ T.hLive T.hGroups T.hLink T.hNext T.hOwn T.hSeats T.hShapes T.pubFree
    T.hnS T.hTests T.h6

end P5J

#print axioms P5J.k03_dig_at
