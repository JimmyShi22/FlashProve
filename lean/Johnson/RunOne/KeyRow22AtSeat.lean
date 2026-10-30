-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow22AtSeat.lean: THE KEY FILE, THE SHARED CHAIN, ROWS 2.2 («send o_u») AND 2.5 («send o_omega»): THE PROMISE's FORWARD HALVES AT THE SEAT: sure22 | sure25 (Johnson/RunOne/KeyRow22.lean) CALLED AT THE SUB-PROTOCOLS NUMBER 2 AND 5 OF THE IOP AS WRITTEN IN LEAN, (descriptionFromSource X N P).shared.blocksInOrder. Two tests with code, statements and proofs.

  roundsFit_noDigest   the rounds' test does not read the sealed digest.
  sends_at_blocks      which sendAt K14's second and fifth sub-protocol are. (Kin: blocks_two, Johnson/Desc/Sound/FenceK14Named.lean: the same fact by the same five lines; typed here so that its cone is not drawn in.)
  planOwn_of_sendAt    sendAt's test on the plan holds K1's own.
  sent_parK1           what parK1 … sent sends is sent.
  plan22B | plan25B    TESTS WITH CODE ON THE PLAN ALONE: two messages · the answers are a, not 0 · the mask has no answer · one tree | the shape splits · omega's and the split's answers are a, not 0 · the split has mask rows · a tree each.
  plan22_of_B | plan25_of_B   they give Plan22 | Plan25 AT K14's OWN PLACES parK1 P 2 … sentU | parK1 P 5 … (withOmega P.S): «what is sent» and «firstTree = 0» by proof.
  shared_2 | shared_5 · laid22_at_desc | laid25_at_desc   the seated sub-protocol accepting, at rounds that fit, gives Laid22 | Laid25.
  step₂_2 | step₂_5    ON THE VERIFIER's STATE ALONE, IN THE FORM THAT THE FOLD ASKS (its StepInvP, unfolded): Tests₂ … k (p, s) → Tests₂ … (k + 1) (p, s').
  yes22_seat | yes25_seat   THE PREMISE «yes» OF keeps₂_send2 | keeps₂_send5, at pc.b = held b, at the tables' own reading T.h₂, with New := «every leaf is shown at the new pins».

OBJECT. (descriptionFromSource X N P).shared.blocksInOrder[2] | [5], their field decide. USER. keeps₂_send2 | _send5's «yes»; Gaps₂'s fields at 2 | 5.
IN FRONT OF EACH: K14.blocks (p14At X P) says its eight · b2 | b5's test on the plan · masksAhead | the shape splits · plan22B | plan25B = true · at_ 3 | 4 | 5 (the tables' AtOk) · (the «yes» alone) CellOnly coll. ALL PUBLIC OR THE LETTERS'. NO BARE ∀ OVER STATES.
THE CAUTION: UNTIL A MEMBER IS SHOWN, EVERY LAW THAT HAS PIN AS AN ITEM OR NoColl IN ITS PROMISE MAY BE TRUE AND EMPTY AT THE REAL PROTOCOL, AND COUNTS AS CLOSING NOTHING: so yes22_seat | yes25_seat. step₂_2 | step₂_5 read no pin and no string.
IS IT EMPTY? Both tests say yes at keyFull's shape and codes, at one answer to a sample (Johnson/Top/Fire/Code/KeyASide2All.lean). What else stands in front of each stays a premise here; no member is shown. Elsewhere all six may be idle.
Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.RunOne.KeyRow22
import Johnson.Desc.Key.Laid.Laid2
import Johnson.RunOne.KeyBridges23
import Johnson.RunOne.KeyPinsAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState)
open VerifiableInference.Desc.Key.LaidW (Laid22 Laid25 laid22_of_yes laid25_of_yes)
open _root_.Desc.K14 (P14 sendAt behindU behindOmega parK1 withU withOmega)
open LKFU.Shape23 (ok shape₂)

/-- The rounds' test does not read the sealed digest. -/
theorem roundsFit_noDigest : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds (rs.map noDigest) = roundsFit ds rs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, r :: rs => by
    simp only [List.map_cons, VerifiableInference.Desc.roundsFit]
    rw [roundsFit_noDigest ds rs]
    rfl

/-- Which sendings K14's second and fifth sub-protocol are. -/
theorem sends_at_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block _root_.Desc.K14.St Unit)
    (hbl : _root_.Desc.K14.blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∃ sentU, withU P.S = some sentU ∧
      b2 = sendAt P "send o_u" (parK1 P 2 "o_u and the first mask" sentU)
        (_root_.Desc.K14.entries P)[0]? [[0], []] (behindU P.par) ∧
      b5 = sendAt P "send o_omega" (parK1 P 5 "o_omega and o_sp" (withOmega P.S))
        (_root_.Desc.K14.entries P)[1]? [[1], [1, 0]] (behindOmega P.par) := by
  unfold _root_.Desc.K14.blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  exact ⟨sentU, hU, rfl, rfl⟩

/-- sendAt's test on the plan holds K1's own. -/
theorem planOwn_of_sendAt (P : P14) (n : String) (Q : K1.Par) (inFront : Option Fmt.Entry)
    (groups : List (List Nat)) (behind : _root_.Desc.K14.St → Array Nat → Option _root_.Desc.K14.St)
    (h : (sendAt P n Q inFront groups behind).planOk = true) : K1.planOkOwn Q = true := by
  have h1 := (Bool.and_eq_true_iff.1 h).1
  have h2 := (Bool.and_eq_true_iff.1 h1).1
  have h3 := (Bool.and_eq_true_iff.1 h2).1
  exact (Bool.and_eq_true_iff.1 h3).1

theorem sent_parK1 (P : P14) (i : Nat) (s : String) (sent : Array OracleNotice) :
    (parK1 P i s sent).sent = sent := by
  simp [K1.Par.sent, parK1]

/-! ## The plan's tests -/

/-- **Plan22 as a test with code.** -/
def plan22B (S : LinShape) (a : Nat) (codes : Codes) (sent : Array OracleNotice) : Bool :=
  sent.size == 2 && S.fold.u.answers == a && a != 0 &&
    (sent[1]?).any (fun n => n.shape.answers == 0) &&
    (layTrees codes sent).all fun lay => lay.shapes.size == 1

/-- **Plan25 as a test with code.** -/
def plan25B (S : LinShape) (a : Nat) (codes : Codes) : Bool :=
  S.sharedSplitNeeded && S.omega.answers == a && S.sharedSplit.answers == a && a != 0 &&
    decide (0 < S.sharedSplit.maskRows) &&
    (layTrees codes (withOmega S)).all fun lay =>
      lay.shapes.size == 2 && lay.tree.getD 0 0 == 0 && lay.tree.getD 1 0 == 1

theorem plan22_of_B (P : P14) (a : Nat) (s : String) (sentU : Array OracleNotice)
    (hU : withU P.S = some sentU) (h : plan22B P.S a P.codes sentU = true) :
    Plan22 P.S a (parK1 P 2 s sentU) := by
  have es := sent_parK1 P 2 s sentU
  unfold plan22B at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨by rw [es]; exact hU, by rw [es]; exact h1, h2, h3, ?_, fun lay hl => ?_, rfl⟩
  · rw [es]
    cases hn : sentU[1]? with
    | none => rw [hn] at h4; cases h4
    | some n =>
      rw [hn] at h4
      exact ⟨n, rfl, by simpa using h4⟩
  · rw [es] at hl
    have hl' : layTrees P.codes sentU = some lay := hl
    rw [hl'] at h5
    simpa using h5

theorem plan25_of_B (P : P14) (a : Nat) (s : String) (h : plan25B P.S a P.codes = true) :
    Plan25 P.S a (parK1 P 5 s (withOmega P.S)) := by
  have es := sent_parK1 P 5 s (withOmega P.S)
  unfold plan25B at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨es.symm, h1, h2, h3, h4, h5, fun lay hl => ?_, rfl⟩
  rw [es] at hl
  have hl' : layTrees P.codes (withOmega P.S) = some lay := hl
  rw [hl'] at h6
  simpa [and_assoc] using h6

/-! ## At the seat -/

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block _root_.Desc.K14.St Unit)
  (h : _root_.Desc.K14.blocks (p14At X P) = some [b1, b2, b3, b4, b5, b6, b7, b8])
include h

theorem shared_2 : (descriptionFromSource X N P).shared.blocksInOrder[2]? = some (seat b2) := by
  rw [shared_at_blocks X N P _ h]
  rfl

theorem shared_5 : (descriptionFromSource X N P).shared.blocksInOrder[5]? = some (seat b5) := by
  rw [shared_at_blocks X N P _ h]
  rfl

/-- **Row 2.2's sub-protocol, as it is seated: accepting at rounds that fit, it gives Laid22.** -/
theorem laid22_at_desc (hM : (p14At X P).S.masksAhead = true) (hp : b2.planOk = true)
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[2]? = some b) :
    ∀ d rs gs d', roundsFit b.rounds rs = true → b.decide d (rs.map noDigest) gs = .ok d' →
      ∃ sentU, withU (p14At X P).S = some sentU ∧
        Laid22 (p14At X P).S (parK1 (p14At X P) 2 "o_u and the first mask" sentU) d d' := by
  have e : b = seat b2 := Option.some.inj (hb.symm.trans (shared_2 X N P b1 b2 b3 b4 b5 b6 b7 b8 h))
  subst e
  obtain ⟨sentU, hU, e2, _⟩ := sends_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h
  intro d rs gs d' hf hd
  have hf' : roundsFit b2.rounds rs = true := hf
  have hd' : b2.decide d (rs.map noDigest) gs = .ok d' := hd
  rw [e2] at hf' hd' hp
  have hl : rs.length = 2 := roundsFit_length _ _ hf'
  obtain ⟨q₁, q₂, rfl⟩ := List.length_eq_two.1 hl
  refine ⟨sentU, hU, laid22_of_yes (p14At X P) _ _ _ _ d d' (noDigest q₁) (noDigest q₂) gs
    (planOwn_of_sendAt _ _ _ _ _ _ hp) ?_ hM hd'⟩
  have := roundsFit_noDigest (K1.rounds (parK1 (p14At X P) 2 "o_u and the first mask" sentU))
    [q₁, q₂]
  exact this.trans hf'

/-- **Row 2.5's sub-protocol, as it is seated: accepting at rounds that fit, it gives Laid25.** -/
theorem laid25_at_desc (hS : (p14At X P).S.sharedSplitNeeded = true) (hp : b5.planOk = true)
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[5]? = some b) :
    ∀ d rs gs d', roundsFit b.rounds rs = true → b.decide d (rs.map noDigest) gs = .ok d' →
      Laid25 (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)) d d' := by
  have e : b = seat b5 := Option.some.inj (hb.symm.trans (shared_5 X N P b1 b2 b3 b4 b5 b6 b7 b8 h))
  subst e
  obtain ⟨_, _, _, e5⟩ := sends_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h
  intro d rs gs d' hf hd
  have hf' : roundsFit b5.rounds rs = true := hf
  have hd' : b5.decide d (rs.map noDigest) gs = .ok d' := hd
  rw [e5] at hf' hd' hp
  have hl : rs.length = 2 := roundsFit_length _ _ hf'
  obtain ⟨q₁, q₂, rfl⟩ := List.length_eq_two.1 hl
  refine laid25_of_yes (p14At X P) _ _ _ _ d d' (noDigest q₁) (noDigest q₂) gs
    (planOwn_of_sendAt _ _ _ _ _ _ hp) ?_ hS hd'
  have := roundsFit_noDigest
    (K1.rounds (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S))) [q₁, q₂]
  exact this.trans hf'

section
variable (at_ : Where) (K₁ : KPlan) (a : Nat) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **2 → 3 on the verifier's state alone, at the seat.** -/
theorem step₂_2 (hM : (p14At X P).S.masksAhead = true) (hp : b2.planOk = true)
    (hpl : ∀ sentU, withU (p14At X P).S = some sentU →
      plan22B (p14At X P).S a (p14At X P).codes sentU = true) (at3 : at_ 3 = (off₂ 0, 0))
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[2]? = some b) :
    ∀ (p : P₂) (s s' : St₂) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' →
      Tests₂ at_ (p14At X P).S K₁ a last₁ off₂ 2 (p, s) → Tests₂ at_ (p14At X P).S K₁ a last₁ off₂ 3 (p, s') := by
  intro p s s' rs gs hf hd T
  obtain ⟨sentU, hU, L⟩ := laid22_at_desc X N P b1 b2 b3 b4 b5 b6 b7 b8 h hM hp b hb s rs gs s' hf hd
  exact tests₂_23 at_ _ K₁ a last₁ off₂ _ p s s' (plan22_of_B _ a _ sentU hU (hpl sentU hU)) L at3 T

/-- **5 → 6 on the verifier's state alone, at the seat.** -/
theorem step₂_5 (hp : b5.planOk = true) (hpl : plan25B (p14At X P).S a (p14At X P).codes = true)
    (at4 : at_ 4 = (off₂ 1, 0)) (at5 : at_ 5 = (off₂ 2, 0))
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[5]? = some b) :
    ∀ (p : P₂) (s s' : St₂) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' →
      Tests₂ at_ (p14At X P).S K₁ a last₁ off₂ 5 (p, s) → Tests₂ at_ (p14At X P).S K₁ a last₁ off₂ 6 (p, s') := by
  intro p s s' rs gs hf hd T
  have PW := plan25_of_B (p14At X P) a "o_omega and o_sp" hpl
  have L := laid25_at_desc X N P b1 b2 b3 b4 b5 b6 b7 b8 h PW.split hp b hb s rs gs s' hf hd
  exact tests₂_56 at_ _ K₁ a last₁ off₂ _ p s s' PW L at4 at5 T

end

section
variable {XI Cells M Smp Rec W : Type} {C : CK} (F : FileDescription XI) (Fr₂ : Frame)
  (T : BaseSt Cells M Smp Rec) (at_ : Where)
  (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **ROW 2.2: THE PREMISE «yes» AT THE SEAT.** -/
theorem yes22_seat (hM : (p14At X P).S.masksAhead = true) (hp : b2.planOk = true)
    (hpl : ∀ sentU, withU (p14At X P).S = some sentU →
      plan22B (p14At X P).S a (p14At X P).codes sentU = true) (at3 : at_ 3 = (off₂ 0, 0))
    (hc : CellOnly coll) (pc : Piece C Fr₂ (P₂ × St₂) Claim W)
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[2]? = some b)
    (hpb : pc.b = held b) :
    ∀ z rs gs z' y y', roundsFit pc.b.rounds rs = true →
      pc.b.decide z (rs.map noDigest) gs = .ok z' → StrsStay F at_ (open₂ 2) y y' →
      ShownAt F at_ 3 y' →
      onAt F T.h₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => ok (shape₂ (p14At X P).S a 2 d))
        (Free₂ F T.h₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 2) (open₂ 2) z y →
      ok (shape₂ (p14At X P).S a 3 z'.2) = true ∧ Free₂ F T.h₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 3 z' y' := by
  intro z rs gs z' y y' hf hd Hy hnew hon
  rw [hpb] at hf hd
  obtain ⟨e1, e2⟩ := held_decide b z _ gs z' hd
  obtain ⟨sentU, hU, L⟩ := laid22_at_desc X N P b1 b2 b3 b4 b5 b6 b7 b8 h hM hp b hb z.2 rs gs z'.2 hf e2
  have ez : z' = (z.1, z'.2) := Prod.ext e1 rfl
  rw [ez]
  exact sure22 F T.h₂ at_ _ K₁ R enc rad a coll last₁ off₂ _ z.1 z.2 z'.2 y y'
    (plan22_of_B _ a _ sentU hU (hpl sentU hU)) L at3 hc rfl Hy hnew hon

/-- **ROW 2.5: THE PREMISE «yes» AT THE SEAT.** -/
theorem yes25_seat (hp : b5.planOk = true) (hpl : plan25B (p14At X P).S a (p14At X P).codes = true)
    (at4 : at_ 4 = (off₂ 1, 0)) (at5 : at_ 5 = (off₂ 2, 0))
    (hc : CellOnly coll) (pc : Piece C Fr₂ (P₂ × St₂) Claim W)
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[5]? = some b)
    (hpb : pc.b = held b) :
    ∀ z rs gs z' y y', roundsFit pc.b.rounds rs = true →
      pc.b.decide z (rs.map noDigest) gs = .ok z' → StrsStay F at_ (open₂ 5) y y' →
      (∀ j ∈ [4, 5], ShownAt F at_ j y') →
      onAt F T.h₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => ok (shape₂ (p14At X P).S a 5 d))
        (Free₂ F T.h₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 5) (open₂ 5) z y →
      ok (shape₂ (p14At X P).S a 6 z'.2) = true ∧ Free₂ F T.h₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 6 z' y' := by
  intro z rs gs z' y y' hf hd Hy hnew hon
  rw [hpb] at hf hd
  obtain ⟨e1, e2⟩ := held_decide b z _ gs z' hd
  have PW := plan25_of_B (p14At X P) a "o_omega and o_sp" hpl
  have L := laid25_at_desc X N P b1 b2 b3 b4 b5 b6 b7 b8 h PW.split hp b hb z.2 rs gs z'.2 hf e2
  have ez : z' = (z.1, z'.2) := Prod.ext e1 rfl
  rw [ez]
  exact sure25 F T.h₂ at_ _ K₁ R enc rad a coll last₁ off₂ _ z.1 z.2 z'.2 y y' PW L at4 at5 hc rfl
    Hy hnew hon

end

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.plan22_of_B
#print axioms Johnson.RunOne.KeyRows23.plan25_of_B
#print axioms Johnson.RunOne.KeyRows23.step₂_2
#print axioms Johnson.RunOne.KeyRows23.step₂_5
#print axioms Johnson.RunOne.KeyRows23.yes22_seat
#print axioms Johnson.RunOne.KeyRows23.yes25_seat
