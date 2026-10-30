-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/RecordAtBase.lean: the shared sending (kind K1) at the base prover of the online proof.

The base prover is A.H, where onlineProverFromPublicFiles returns A at the filling onlineProverPartsInUse I secondHashFunction S Op, with the
index's reader I a parameter. The honest online prover of E2E/TheHonestProver.lean is this prover read
through OnlineProverParts.through.

  1  witB, jobTwoAt, jobLaterAt, jobWAt   K1's reader and its 52 jobs, as that filling lays them
  2  hex_base, ho_base   the filling holds K1's list of sides, and no other list has a side of the kind
     K1 at a link
  3  scriptAt   the first chain's Script: joinQ (Honest/Thread/Join.lean) at these 52 jobs and at a
     record Oth of the other senders' lots
  4  OthersApart   what K1 asks of that record: the four hypotheses of RecordAtJoin.lean
  5  k1Seated_at_base   the record K1Seated (Honest/K1/Seated.lean), all twenty fields, at each of the
     52 members, at lettersHead with scriptAt for its Script, at A.H and A.B
  6  othersApart_at_shares   OthersApart holds of the sum of the code switch's share and the proximity
     test's share

Limits.
  * k1Seated_at_base says that hypotheses are met. It does not say that the thread's invariant holds in
    front of a member at any run.
  * cells, tok and Oth are parameters of scriptAt. The other ten parameters of lettersHead are bound by
    "for all", and no hypothesis is put on them. At Vd := fun _ => False the fields msgs and pads hold for
    nothing.
  * The head h and the return hA are hypotheses.
  * othersApart_at_shares takes hJ: the proximity test's job has six stages. The numbers 77 and 354 are
    written by hand. Nothing here says that the shares' lots are what the prover's sides of the kinds K2
    and K12 play.
  * The first chain alone. The full size alone.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.RecordAtFull
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.K1.Law.LotAtWider

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.K1 (momL)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open P5T (PSeat)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (switchShareAt)

/-! ## 1 The reader and the jobs -/

/-- The input of a side of the base prover. -/
abbrev LocB (W₀ : Type) := Local W₀ IndexCommitterCoins ProofFile.Inst Cells

/-- K1's reader at the base prover, at the public part Zq. -/
def witB {W₀ : Type} (I : WiderIn W₀) (Zq : ProofFile.Pub) : LocB W₀ → PlaceIn ProofFile.Inst :=
  fun v => ⟨v.x, ⟨v.trace, I.weights Zq v.w₀, v.rc⟩⟩

/-- The job at number 2, the opening. -/
def jobTwoAt (S : OnBytes.HonestTrace.Sz) (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    SendJob (PlaceIn ProofFile.Inst) Unit :=
  placeJob (K1.firstPar G.first (K1.gpOf Zq)) (lotNo OnBytes.secondHashFunction Zq ⟨1, some 0, 1, .K1⟩)
    (firstFold G.first) (lotData S Zq G)

/-- The job at number K1.noL l d. -/
def jobLaterAt (S : OnBytes.HonestTrace.Sz) (Zq : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) :
    SendJob (PlaceIn ProofFile.Inst) Unit :=
  laterJobAt G.first (K1.gpOf Zq) l (IM.k1Ix l d + 1) (if d then 2 else 1)
    (lotNo OnBytes.secondHashFunction Zq ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (lotData S Zq G)

/-- The job at number 356, the message W. -/
def jobWAt (Op : OnlineProverArguments) (Zq : ProofFile.Pub) (G : ProofFile.Ground) : SendJob (PlaceIn ProofFile.Inst) Unit :=
  wJobAt Zq.first (wGp Zq) 4 wMsgFull (lotNo OnBytes.secondHashFunction Zq ⟨1, none, 4, .K1⟩)
    (K13.wDataAt Op.pile Zq G)

/-! ## 2 The filling's lists -/

section Fill
variable {W₀ : Type} (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Op : OnlineProverArguments)

/-- **The filling holds K1's list.** No hypothesis. -/
theorem hex_base (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    ∃ M ∈ (onlineProverPartsInUse I OnBytes.secondHashFunction S Op).lots,
      M.halves Zq G = lotHalves (witB I Zq) (lotNo OnBytes.secondHashFunction Zq) (lotData S) Zq G := by
  obtain ⟨M, hM, e⟩ := hex_wider I OnBytes.secondHashFunction S Op Zq G
  refine ⟨M, ?_, e⟩
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hM))

/-- **Every other list has no side of the kind K1 at a link.** No hypothesis. -/
theorem ho_base (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ M ∈ (onlineProverPartsInUse I OnBytes.secondHashFunction S Op).lots,
      (∀ x ∈ M.halves Zq G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves Zq G = lotHalves (witB I Zq) (lotNo OnBytes.secondHashFunction Zq) (lotData S) Zq G := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · exact ho_wider (FirstFill.widerKinds I OnBytes.secondHashFunction S Op Zq G) M h
  · refine .inl fun x hx e => ?_
    have hk := closeLotAt_kinds I S Zq G x hx
    rw [e] at hk
    cases hk
  · refine .inl fun x hx e => ?_
    have hk := proxLotAt_kinds I S Zq G x hx
    rw [e] at hk
    cases hk
  · refine .inl fun x hx _ => ?_
    rw [wLotAt_halves] at hx
    cases hm : OnBytes.linMessageW Zq.first.lin with
    | none =>
      rw [hm] at hx
      cases hx
    | some msg =>
      rw [hm] at hx
      have e : x = _ := List.mem_singleton.1 hx
      rw [e]
      rfl

end Fill

/-! ## 3 The Script -/

section Base
variable {Z : VerifierAndGoals.PublicFiles} {W₀ : Type} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The first chain's Script at the base prover, in the other senders' record**: joinQ at K1's 52
jobs as the filling lays them. -/
def scriptAt (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Op : OnlineProverArguments)
    (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) (cF : Chain TS ProofFile.Cl)
    (cells : LocB W₀ → CellsM OnBytes.Flat.numsFull) (tok : LocB W₀ → P5J.At.Tok)
    (Oth : Others A.B (LocB W₀)) :
    Script A.B (LocB W₀) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT :=
  joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr A.Z) (witB I A.Z) ()
    (k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G)) Oth

/-- **What K1 asks of the other senders' record.** Their lots agree among themselves, and each stands
at a seat of the plan's list that is in none of K1's 52 sendings; a lot of messages at no kept copy's
seat. -/
structure OthersApart (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) (Oth : Others A.B (LocB W₀)) : Prop where
  msgs : MsgsAgree Oth.ml
  msgsFar : ∀ L' ∈ Oth.ml, ∃ (j t : ℕ) (q : PSeat),
    ((P5J.At.pseatsAll A.Z).find? fun p => p.j == j && p.t == t) = some q ∧
      L'.n = P5J.At.arr A.Z j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81
  pads : PadsAgree Oth.pl
  padsFar : ∀ L' ∈ Oth.pl, ∃ q ∈ P5J.At.pseatsAll A.Z, L'.j = q.j ∧ L'.t = q.t ∧ q.send ≠ 0 ∧
    (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81

/-! ## 4 The record at the 52 members -/

variable {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **K1Seated, all twenty fields, at each of the 52 members, at the base prover and its book.** Under
the head, the maker's return and OthersApart. The fields msgs and pads are paid inside, at scriptAt. -/
theorem k1Seated_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (cells : LocB W₀ → CellsM OnBytes.Flat.numsFull) (tok : LocB W₀ → P5J.At.Tok)
    (Oth : Others A.B (LocB W₀)) (hO : OthersApart A Oth)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) :
    (∃ blk, K1Seated (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth)
        test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      2 blk (witB I A.Z) (jobTwoAt S A.Z A.G) () .opening (P5J.At.arr A.Z) (P5J.At.seats A.Z)
      (P5J.At.ms A.Z Z.lay) (K1.radRec 0 (jobTwoAt S A.Z A.G).P)) ∧
    (∀ l, l < 25 → ∀ d : Bool, ∃ blk, K1Seated (lettersHead h A.H
        (scriptAt I S Op A cF cells tok Oth) test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      (K1.noL l d) blk (witB I A.Z) (jobLaterAt S A.Z A.G l d) () (cond d (.digits l) (.reads l))
      (P5J.At.arr A.Z) (P5J.At.seats A.Z) (P5J.At.ms A.Z Z.lay)
      (K1.radRec (3 * l + (if d then 2 else 1)) (jobLaterAt S A.Z A.G l d).P)) ∧
    (∃ blk, K1Seated (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth)
        test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      356 blk (witB I A.Z) (jobWAt Op A.Z A.G) () .w (P5J.At.arr A.Z) (P5J.At.seats A.Z)
      (P5J.At.ms A.Z Z.lay) (K1.radRec 81 (jobWAt Op A.Z A.G).P)) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hJ₂ : jobTwoAt S A.Z A.G = placeJob (K1.firstPar Bs.G₀.first (K1.gpOf A.Z))
      (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩) (firstFold Bs.G₀.first)
      (lotData S A.Z Bs.G₀) := congrArg (jobTwoAt S A.Z) eG
  have hJl : ∀ l d, jobLaterAt S A.Z A.G l d = laterJobAt Bs.G₀.first (K1.gpOf A.Z) l
      (IM.k1Ix l d + 1) (if d then 2 else 1)
      (lotNo OnBytes.secondHashFunction A.Z ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (lotData S A.Z Bs.G₀) :=
    fun l d => congrArg (fun G => jobLaterAt S A.Z G l d) eG
  have hJw : jobWAt Op A.Z A.G = wJobAt A.Z.first (wGp A.Z) 4 wMsgFull
      (lotNo OnBytes.secondHashFunction A.Z ⟨1, none, 4, .K1⟩) (K13.wDataAt Op.pile A.Z Bs.G₀) :=
    congrArg (jobWAt Op A.Z) eG
  refine ⟨?_, ?_, ?_⟩
  · exact k1Seated_two_at_join h O hA (witB I A.Z) (lotData S) (K13.wDataAt Op.pile) cells tok ()
      hJ₂ hJl hJw Oth hO.msgs hO.msgsFar hO.pads hO.padsFar test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (hex_base I S Op A.Z A.G) (ho_base I S Op A.Z A.G)
  · intro l hl d
    exact k1Seated_fifty_at_join h O hA (witB I A.Z) (lotData S) (K13.wDataAt Op.pile) cells tok ()
      hJ₂ hJl hJw Oth hO.msgs hO.msgsFar hO.pads hO.padsFar test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (hex_base I S Op A.Z A.G) (ho_base I S Op A.Z A.G) hl d
  · exact k1Seated_w_at_join h O hA (witB I A.Z) (lotData S) (K13.wDataAt Op.pile) cells tok ()
      hJ₂ hJl hJw Oth hO.msgs hO.msgsFar hO.pads hO.padsFar test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (lotNo OnBytes.secondHashFunction A.Z) (hex_wM I OnBytes.secondHashFunction S Op A.Z A.G)
      (ho_wM I OnBytes.secondHashFunction S Op A.Z A.G)

/-! ## 5 The two other senders' shares -/

/-- **OthersApart holds of the sum of the code switch's share and the proximity test's**, at every
value of their parameters, where the test's job has six stages. -/
theorem othersApart_at_shares (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Ds : RowDataOf ProofFile.Inst) (readers : LocB W₀ → Readers)
    (rest : Nat → TreeLot A.B (LocB W₀)) {X₂ : Type} (ch : Nat) (J : K12.TestJob (LocB W₀) X₂)
    (hJ : J.p.nums.stages.length = 6) (own₂ : X₂) (n₀ : Nat)
    (ok : LocB W₀ → List Fmt.Drawn → (Nat → K12.Stretch) → Bool) (codes : OnBytes.Codes)
    (sh sh₁ : Nat → OnBytes.OracleShape) (rest₂ : Nat → TreeLot A.B (LocB W₀)) :
    OthersApart A ((switchShareAt A.B cF.blocksInOrder 0 A.Z A.G Ds readers rest).add
      (K12.k12Share ch J own₂ n₀ 77 (P5J.At.arr A.Z) ok codes sh sh₁ 354 rest₂)) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  obtain ⟨a1, a2, a3, a4⟩ := four_at_full (Bk := A.B) h O 0 Ds readers rest ch J hJ own₂ n₀ ok
    codes sh sh₁ rest₂ (congrArg (fun G => (switchShareAt A.B cF.blocksInOrder 0 A.Z G Ds readers rest).add
      (K12.k12Share ch J own₂ n₀ 77 (P5J.At.arr A.Z) ok codes sh sh₁ 354 rest₂)) eG)
  exact ⟨a1, a2, a3, a4⟩

end Base

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.hex_base
#print axioms ProofFile.Honest.K1.ho_base
#print axioms ProofFile.Honest.K1.k1Seated_at_base
#print axioms ProofFile.Honest.K1.othersApart_at_shares
