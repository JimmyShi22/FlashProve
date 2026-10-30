-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendAtDesc.lean: THEOREMS. **The law of a sending at the three sendings of the key file's first chain, AT THE SEATED TEXT: one ground, one theorem a seat, one over the three.**
OBJECT. The constants of the seated text: (Key.descriptionFromSource X N P).first.blocksInOrder, at the places 0, 1 and «behind first, front, all the links' flat lists and three blocks of back»: by idx_at | msg_at | w_at these ARE bareOf (Key.sendIndexMasks …),
  bareOf (Key.sendOwnMessage …), bareOf bw with Key.sendW … = some bw: the blocks as Chain.blocksInOrder lays them.
USER. Whoever fills a frame's row at these three places with K1's piece (sendPiece b …) and wants GoodIn and Err.Below of it: it calls seat_idx | seat_msg | seat_w, or three_seats. Nobody calls them yet.
LETTERS. FREE IN EVERY STATEMENT: rad (the radii: fixed by whoever lays the reading of the oracles; the proximity tests' laws say which) · K (129 at the two stored sets) · base, d₁, d₂ (the frame's cut of the written rounds) · F, W ·
  fOf, fIn (a constant family meets hf: the debt of whoever spends Sealed: fOf y k IS the frame's reading of that oracle message) · On, On', R, R' (the borders' condition and relation).
WHAT IS ASKED AND WHAT IS PAID. PAID FROM THE RUN's YES (Key.descriptionFromSource's own): the block's test on the plan, so the kind's own (Pays) · the codes' lengths are powers of two (the source's clause «lengths»).
  ASKED, AS ONE STRUCTURE (SendAsks K P rad): tests with code that no theorem gives at every source: one seed · meetsB at every sampled message · shareB K · belowB K. [RAN true at both stored sets at each message's last radius; smaller radii by KeySendMono.]
  LEFT: SeedRound P d₁ (the first written round is the round of seeds): had from the block's own first round by seedRound_at, given the frame's cut.
  idx_at | msg_at | w_at      the seats
  SendAsks                    the four tests
  seat_idx | seat_msg | seat_w   send_seat at the seat
  three_seats                 the three in one statement (W's part reads «for every bw with Key.sendW … = some bw»: where sendW gives nothing the chain has no such seat, and that part says nothing)
What is not claimed. That the asks hold. That a frame's piece at the seat is sendPiece. Nothing on the honest prover. Nothing on soundness.

-/
import Johnson.RunOne.KeySendSeat
import Johnson.RunOne.KeySendFlat
import Johnson.RunOne.KeySendRound
import Johnson.RunOne.KeySendPlan

set_option autoImplicit false

namespace Johnson.RunOne.KeySendGood

open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice Johnson.Pack Cb Cb.Ood Iop Prob Run
open Johnson.RunOne.KeySendErr Johnson.RunOne.KeyKeeps Johnson.RunOne.KeyPay
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.K1 (Par errPort sendPiece Sealed shapeAt shapesOf sampledAt)
open VerifiableInference.Desc.Key
open scoped ENNReal

/-! ## The numbers of the three places, as Key.firstChain lays them -/

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- The groups told at the first sending, the second, and W's. -/
def gIdx : List (List Nat) := groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0)
def gMsg : List (List Nat) := groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 2) (rootsAt X.Y.D.1 2)
def gW : List (List Nat) := groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))

def parIdx : Par := sendingPar X.Y.k.oneTime pieces.idx "the index masks" #[X.Y.k.oneTime.indexMasks] (gIdx X)
def parMsg : Par := sendingPar X.Y.k.oneTime pieces.msg "the lookups' own message and what rides with it" (Wf.messageOf X.Y.k.oneTime.ranges) (gMsg X)
def parW (msg : Array OracleNotice) : Par := sendingPar X.Y.k.oneTime pieces.w "W and what rides with it" msg (gW X)

/-! ## The seats -/

theorem first_is : (descriptionFromSource X N P).first = firstChain X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N := rfl

theorem idx_at : (descriptionFromSource X N P).first.blocksInOrder[0]? = some (bareOf (sendIndexMasks X.Y.k.oneTime pieces (gIdx X))) :=
  flat_first _

theorem msg_at : (descriptionFromSource X N P).first.blocksInOrder[1]? = some (bareOf (sendOwnMessage X.Y.k.oneTime pieces (gMsg X))) :=
  flat_front _ 0 _ rfl

theorem w_at {bw : Block FirstState Claim}
    (hb : sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X) = some bw) :
    (descriptionFromSource X N P).first.blocksInOrder[(descriptionFromSource X N P).first.front.length + ((descriptionFromSource X N P).first.links.flatMap Link.blocksInOrder).length + 3 + 1]? = some (bareOf bw) := by
  refine flat_back _ 3 _ ?_
  show ([_, _, _] ++ (sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X)).toList)[3]? = some bw
  rw [hb]
  rfl

/-! ## What is asked -/

/-- The tests with code that no theorem gives at every source. -/
structure SendAsks (K : Nat) (Q : Par) (rad : Nat → Nat) : Prop where
  seeds : Q.seeds = 1
  meets : ∀ k, sampledAt Q k → meetsB Q.codes (shapeAt Q k) (rad k.val) = true
  share : shareB K Q rad = true
  below : belowB K Q = true

/-- The first written round is the round of seeds, from the block's own first round and the frame's cut of it. -/
theorem seedRound_at (Q : Par) {T Cl : Type} (b : Block T Cl) (hr : b.rounds = VerifiableInference.Desc.K1.rounds Q) (r : Fmt.DeclaredRound) (d : RDT)
    (h0 : b.rounds[0]? = some r) (he : d.entry = r.entry) (hk : Fmt.kindOf r.entry.name = some d.kind) : SeedRound Q d :=
  seedRound_of Q r d (hr ▸ h0) he hk

/-! ## The law at a seat -/

variable {X N P}
variable {W : Type} {F : Frame}

/-- What send_seat concludes, of a block b at the numbers Q. -/
def SeatLaw (W : Type) (F : Frame) (Q : Par) (rad : Nat → Nat) (b : Block FirstState Claim) : Prop :=
  ∀ (base : Nat) (d₁ d₂ : RDT), SeedRound Q d₁ →
    ∀ (fOf : F.E.Str → ∀ k, (portOmZ Q.codes (shapeAt Q k) (rad k.val)).Str)
      (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ Q.codes (shapeAt Q k) (rad k.val)).Str),
      (∀ y τ, fOf ((sendPiece (W := W) (F := F) b base d₁ d₂ Q.coordinates (errPort Q rad)).ior.imp y τ) = fIn y τ.1) →
    ∀ (On On' : FirstState × F.E.Str → Prop) (R R' : FirstState × F.E.Str → W → Prop),
      (∀ a τ x, On a → (sendPiece (W := W) (F := F) b base d₁ d₂ Q.coordinates (errPort Q rad)).ior.red.out a τ = some x → On' x) →
      (∀ a τ x w, On a → (sendPiece (W := W) (F := F) b base d₁ d₂ Q.coordinates (errPort Q rad)).ior.red.out a τ = some x → R' x w → R a w) →
      (sendPiece (W := W) (F := F) b base d₁ d₂ Q.coordinates (errPort Q rad)).GoodIn On
        (fun x => On' x ∧ ∀ k, sampledAt Q k →
          Sealed Q.codes (shapeAt Q k) (rad k.val) (fOf x.2 k) (st₁ x.1) ((st₁ x.1).oracles.size - (shapesOf Q).length + k.val)) R R' ∧
        Err.Below (sendPiece (W := W) (F := F) b base d₁ d₂ Q.coordinates (errPort Q rad)).err ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem seatLaw_of (K : Nat) (Q : Par) (rad : Nat → Nat) (b : Block FirstState Claim) (hb : Pays Q st₁ b) (hl : Q.codes.lengthsOk = true) (a : SendAsks K Q rad) :
    SeatLaw W F Q rad b :=
  fun base d₁ d₂ hd fOf fIn hf On On' R R' hkeep hback =>
    send_seat K Q rad a.seeds b st₁ hb hl a.meets a.share a.below base d₁ d₂ hd fOf fIn hf On On' R R' hkeep hback

variable {x : Xi} {v₁ v₂ v₃ : Fmt.View}

theorem seat_idx (hy : (descriptionFromSource X N P).run x v₁ v₂ v₃ = true) (K : Nat) (rad : Nat → Nat) (a : SendAsks K (parIdx X) rad) :
    SeatLaw W F (parIdx X) rad (bareOf (sendIndexMasks X.Y.k.oneTime pieces (gIdx X))) := by
  obtain ⟨hl, hp⟩ := send_plan_of_yes hy
  exact seatLaw_of K _ rad _ (pays_bare _ _ _ (idx_pays _ _ _) (hp _ (List.mem_of_getElem? (idx_at X N P)))) (hl _ _ _ _) a

theorem seat_msg (hy : (descriptionFromSource X N P).run x v₁ v₂ v₃ = true) (K : Nat) (rad : Nat → Nat) (a : SendAsks K (parMsg X) rad) :
    SeatLaw W F (parMsg X) rad (bareOf (sendOwnMessage X.Y.k.oneTime pieces (gMsg X))) := by
  obtain ⟨hl, hp⟩ := send_plan_of_yes hy
  exact seatLaw_of K _ rad _ (pays_bare _ _ _ (msg_pays _ _ _) (hp _ (List.mem_of_getElem? (msg_at X N P)))) (hl _ _ _ _) a

theorem seat_w (hy : (descriptionFromSource X N P).run x v₁ v₂ v₃ = true) {bw : Block FirstState Claim}
    (hb : sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X) = some bw) (K : Nat) (rad : Nat → Nat)
    (a : ∀ msg, linMessageW X.Y.k.oneTime.lin = some msg → SendAsks K (parW X msg) rad) :
    ∃ msg, linMessageW X.Y.k.oneTime.lin = some msg ∧ SeatLaw W F (parW X msg) rad (bareOf bw) := by
  obtain ⟨hl, hp⟩ := send_plan_of_yes hy
  have hpl : (bareOf bw).planOk = true := hp _ (List.mem_of_getElem? (w_at X N P hb))
  have hpl' : bw.planOk = true := (Bool.and_eq_true_iff.1 (show (bw.planOk && bw.hasNoClaimsAndNothingAfter) = true from hpl)).1
  obtain ⟨msg, hm, hP⟩ := w_pays hb hpl'
  exact ⟨msg, hm, seatLaw_of K _ rad _ (pays_bare _ _ _ (fun _ => hP) hpl) (hl _ _ _ _) (a msg hm)⟩

/-- **The three seats in one statement.** -/
theorem three_seats (hy : (descriptionFromSource X N P).run x v₁ v₂ v₃ = true) (K : Nat) (radI radM radW : Nat → Nat)
    (aI : SendAsks K (parIdx X) radI) (aM : SendAsks K (parMsg X) radM)
    (aW : ∀ msg, linMessageW X.Y.k.oneTime.lin = some msg → SendAsks K (parW X msg) radW) :
    (∃ b, (descriptionFromSource X N P).first.blocksInOrder[0]? = some b ∧ SeatLaw W F (parIdx X) radI b) ∧
    (∃ b, (descriptionFromSource X N P).first.blocksInOrder[1]? = some b ∧ SeatLaw W F (parMsg X) radM b) ∧
    ∀ bw : Block FirstState Claim, sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X) = some bw →
      ∃ b msg, (descriptionFromSource X N P).first.blocksInOrder[(descriptionFromSource X N P).first.front.length + ((descriptionFromSource X N P).first.links.flatMap Link.blocksInOrder).length + 3 + 1]? = some b ∧
        linMessageW X.Y.k.oneTime.lin = some msg ∧ SeatLaw W F (parW X msg) radW b :=
  ⟨⟨_, idx_at X N P, seat_idx hy K radI aI⟩, ⟨_, msg_at X N P, seat_msg hy K radM aM⟩,
    fun bw hb => by
      obtain ⟨msg, hm, h⟩ := seat_w (W := W) (F := F) hy hb K radW aW
      exact ⟨_, msg, w_at X N P hb, hm, h⟩⟩

end Johnson.RunOne.KeySendGood

#print axioms Johnson.RunOne.KeySendGood.idx_at
#print axioms Johnson.RunOne.KeySendGood.msg_at
#print axioms Johnson.RunOne.KeySendGood.w_at
#print axioms Johnson.RunOne.KeySendGood.seat_idx
#print axioms Johnson.RunOne.KeySendGood.seat_msg
#print axioms Johnson.RunOne.KeySendGood.seat_w
#print axioms Johnson.RunOne.KeySendGood.three_seats
