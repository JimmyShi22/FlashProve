-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PlaysFive.lean

What is here. The threads' debts Plays and PlaysS at the member of the layers' own rounds (kind K4)
FROM FIVE FIELDS OF THE SEAT ALONE, and so, at the first chain's thread at the library's own
parameters (`lettersHead`), FROM h, THE MEMBER's LAYING AND ONE HYPOTHESIS: half (the prover's first
halves hold K4's own half at K4's place, at the public data `k4PubAt cF k x`). Law/Plays.lean's
statements take the whole seat `K4Seated` and read five of its nine fields: member, rounds, oracles,
own, half; the field fits (the makers' test accepts) is never read: the row plays also where its
public data do not fit. Here the five stand as a structure of their own, Law/Plays.lean's five short
statements on the seat are typed again over it, word for word, and the five are shown at the thread.

  `K4SeatedP`: the five fields. This defines a hypothesis.
  `K4Seated.toP`: whoever has the seat whole has the five: so Lean holds that they are its own.
  `k4_plays_five`: PlaysAt T At b from the five, at any At.
  `seatedP_head`: the five at the thread, at Qp := k4PubAt cF k x.
  `k4_plays_half, k4_playsS_half`: Plays T k · PlaysS T Said k.

Limits. CONDITIONAL: on h · LaidK4 · half. half is a fact on the prover's term: it is false of a
term that lays no half of this kind. The play returns; NOTHING IS SAID ON WHAT IS SENT. THE FULL
SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h holds of any files is not shown here: the
side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with LaidK4 · half no example is known to us; LaidK4 alone asks nothing
beyond h and g < 12 (`laid_at`, Law/LaidAtGroup.lean). IT IS A LAW, NOT A PART: it rests on modules
under Johnson/Goal/: no file that defines a part may build on it. Nothing on soundness, on
completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Plays
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedHead
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontCount
import Johnson.Desc.ProofFile.Honest.K4.Law.DearTop
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4 (Par k0 rounds)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Place Oracle)
open ProofFile.Honest.SumLaw (StatedBy plays_unit_sumPart scalarsOf_length moves_length)
open ProofFile.Honest.Small (statedBy_length statedBy_split plays_lift_quiet plays_lift_scalars)
open VerifiableInference.Desc.Part.MaskedSum (Var)

section
variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}

/-- **What the statements on the play spend of the seat.** This defines a hypothesis; the definition
claims nothing. -/
structure K4SeatedP (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub)
    (p : Par) (blk : Block S Cl) : Prop where
  /-- blk is the member -/
  member : T.bs[b]? = some blk
  /-- its rounds are the verifier's, at the parameters p -/
  rounds : blk.rounds = (OnBytes.Desc.First.K4.blockAtC p).rounds
  /-- no round has an oracle message -/
  oracles : blk.oracles = blk.rounds.map fun _ => []
  /-- the parameters are the public data's -/
  own : p.P = Q.P ∧ p.hp = Q.hp ∧ p.g = Q.g ∧ p.link = Q.link ∧ p.piece = Q.piece
  /-- the half that the fold finds for the member's place -/
  half : T.hs.find? (fun h => h.place == blk.place) = some (k4Half cells weights tokens look Q)

variable {T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block S Cl}

/-- Whoever has the seat whole has these five. -/
theorem K4Seated.toP (Se : K4Seated T b cells weights tokens look Q p blk) :
    K4SeatedP T b cells weights tokens look Q p blk :=
  ⟨Se.member, Se.rounds, Se.oracles, Se.own, Se.half⟩

/-- The member's rounds, in the public data's letters. -/
theorem k4_roundsP (Se : K4SeatedP T b cells weights tokens look Q p blk) :
    blk.rounds = ((rounds Q.P Q.hp Q.g).map OnBytes.Desc.First.K4.entryOf).map fun e =>
      ({ entry := e } : Fmt.DeclaredRound) := by
  obtain ⟨eP, eh, eg, _, _⟩ := Se.own
  rw [Se.rounds, ← eP, ← eh, ← eg]
  rfl

/-- **The member's rounds state that column**, and no oracle message. -/
theorem k4_statedP (Se : K4SeatedP T b cells weights tokens look Q p blk) :
    StatedBy ((rounds Q.P Q.hp Q.g).map (·.sent)) (blk.rounds.zip blk.oracles) := by
  rw [Se.oracles, k4_roundsP Se]
  exact stated_table _

/-- The member's rounds read no column. -/
theorem k4_no_columnP (Se : K4SeatedP T b cells weights tokens look Q p blk) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64)) (tree : Fmt.TreeSource → Option (Place × Table))
    (ds : List Fmt.Drawn) : readsOf chain ft stored tree blk.rounds ds = [] := by
  rw [k4_roundsP Se]
  exact readsOf_none chain ft stored tree _ ds

/-- Behind the member no source is new. -/
theorem k4_no_treeP (Se : K4SeatedP T b cells weights tokens look Q p blk) : T.fresh b = [] := by
  have e : T.hand (b + 1) = T.hand b := by
    unfold Thread.hand
    rw [treesTo_succ Se.member, Se.oracles]
    have z : ((blk.rounds.map fun _ => ([] : List Oracle)).flatMap id).length = 0 := by
      induction blk.rounds with
      | nil => rfl
      | cons _ _ ih => exact ih
    rw [z]
    rfl
  refine List.eq_nil_iff_forall_not_mem.2 fun σ hσ => ?_
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hσ
  rw [e] at h1
  simp [h1] at h2

/-- **IT PLAYS, AT K4's MEMBER**, at the stands in front that At names, whichever: At is not read:
the play returns at every state of the prover's run. CONDITIONAL on the five fields. -/
theorem k4_plays_five (Se : K4SeatedP T b cells weights tokens look Q p blk)
    (At : Coins Bk → S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop) : PlaysAt T At b := by
  intro blk' hblk' k s m E ds l _ hd _ hl
  obtain rfl : blk = blk' := Option.some.inj (Se.member.symm.trans hblk')
  obtain ⟨c, _, rfl, _, _⟩ := chainSteps_one hl Se.half
  have hlen : ds.length = (k4Sends Q).flatten.length := by
    rw [drawsFit_length _ _ hd, k4_roundsP Se, k4_sends_table, List.length_map, List.length_map,
      List.length_map]
  obtain ⟨y, hy⟩ := row_plays blk.name blk.place (T.φ.sees m.st.input) _ (k4Sends Q) 0
    (blk.rounds.zip blk.oracles) c ds [] m (k4_row_parts Q cells weights tokens (look Q))
    (by rw [k4_sends_table]; exact k4_statedP Se) hlen
  refine ⟨y, [], ⟨⟨_, hl, hy⟩, ?_⟩, ?_⟩
  · rw [k4_no_columnP Se]
    rfl
  · rw [k4_no_treeP Se]
    intro σ hσ
    cases hσ

end

open OnBytes.Model (Forest.Heard)
open OnBytes.Road.K4 (parOf)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 member_head pub_of)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **The five at the thread.** CONDITIONAL: on h, Lh and half. -/
theorem seatedP_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look (k4PubAt cF k x))) :
    K4SeatedP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look (k4PubAt cF k x) (parOf x) blk₀ :=
  { member := member_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh
    rounds := laid_rounds Lh.laid
    oracles := laid_oracles Lh.laid
    own := (pub_of Lh (k4Pub_head h Lh)).1
    half := by
      rw [IM.alone_place Lh.laid]
      exact half }

/-- **`Plays` AT K4's MEMBER, AT THE THREAD.** CONDITIONAL: on h, Lh and half. -/
theorem k4_plays_half {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look (k4PubAt cF k x))) :
    Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k :=
  k4_plays_five (seatedP_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh half)
    (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k)

/-- **`PlaysS` AT K4's MEMBER, AT THE THREAD.** CONDITIONAL: on h, Lh and half. -/
theorem k4_playsS_half
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look (k4PubAt cF k x))) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k :=
  k4_plays_five (seatedP_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh half)
    (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.K4Seated.toP
#print axioms ProofFile.Honest.K4.k4_roundsP
#print axioms ProofFile.Honest.K4.k4_statedP
#print axioms ProofFile.Honest.K4.k4_no_columnP
#print axioms ProofFile.Honest.K4.k4_no_treeP
#print axioms ProofFile.Honest.K4.k4_plays_five
#print axioms ProofFile.Honest.K4.seatedP_head
#print axioms ProofFile.Honest.K4.k4_plays_half
#print axioms ProofFile.Honest.K4.k4_playsS_half
