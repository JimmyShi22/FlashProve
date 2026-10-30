-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/ReplyAtPlaceN.lean.

WHAT IT DOES NOT SHOW. No soundness by itself. NO MEMBER: no print of this block's yes at a real
record is tied to it. That onlineDescription returns in scope: a premise (through the opening O). That the
blocks between the next token's place and the end leave the reply: not here (the driver's guard asks
it of each; another file's law on the whole flat list has it). SO k7_place AND k7_last ARE NOT
JOINED: that the record at the end still holds a token (ht) and still passes the record's own test
on the request (hq) are premises of k7_last, paid by nobody here.
Of b's rounds, tests on the plan, "before" and "after", "laid" says what the
joined form says and no more. That no other block of the flat list stands at a place of this kind:
not here.
LETTERS. Under "there is": Lk: pinned by c.links[24]? = some Lk · b: by Lk.hear[0]? = some b · x: by
t.out.reply = some x · in "meets": s0: by headFrontQ's yes from s · t0: by the kind's own decision's
yes from s0 · k: the length of the front stretch of rs: NOT PINNED IN Met's TEXT (k7_place hands in
the seated constant's number of rounds): the decision's own test "one round" pins the stretch to
rs's first round. The records s, t, the rounds and the groups are the caller's, under "for all".
Idle in k7_last's statement, in effect: o, Z, c (the last test's text reads none of them), hS and
iU3 ("at the output head's seat" is "at out.reply").
OBJECT. ProofFile.onlineDescription's value at the second hash function, opened (IMR/SeatOpen.lean: Open
OnBytes.secondHashFunction): the first block before the batching of its first chain's link 24: number 338 of the
flat list: THE SEATED CONSTANT IS (IM.k7Block W 24).retype (IMR/K7Seat.lean): a quiet step under the
guard on the reply's seat, then Stored/ReplySeatAt.lean's blockOf W 24. And the value's last test.
USER. In this file: k7_first spends "meets". "same" is what the field "yes" of the bill of the next
token's tie asks (Law/K7Seated.lean: K7Left): ReplyTiedN.lean's k7_left_seat has it in the bill's
letters. Beyond these nobody yet: the table's row at that place; the premises of the law on the next
token (Law/K07Statement.lean): its first sentence's ("meets") and its last test's (k7_last).
WHAT IT IS. THE LAWS ON THE NEXT TOKEN's BLOCK, AT THE BLOCK THAT THE DESCRIPTION HOLDS AT ITS
PLACE.
  met_iff           "meets", WRITTEN OUT WITHOUT A LETTER THAT IS NOT PINNED: the seat was empty at
                    s; the entry of the head's link says yes at s; rs has a first round r; r holds
                    just one plain element h and draws nothing; h is an entry of the vocabulary; and
                    h is what stands in the seat behind.
  met_first         so: what stands in the seat behind is the FIRST round's element.
  PlaceK7           the clauses, at given letters.
  k7_place          they hold at the letters that IM.k7_sits hands out.
    laid    b is the seated constant as the first chain lays it, with the "opened" of the head's own
            row of the links' frames joined behind (IMR/SameSpot.lean: Joined).
    same    a yes of b is the seated constant's yes, on the front of the rounds and groups, to the
            SAME record; and that record bears no mark.
    cut     the flat list is its first 338 blocks, b, the blocks from number 339 on.
    meets   AT b's OWN RECORD AND ROUNDS: where b's decision goes on from s at the rounds rs: the
            reply's seat was empty at s; the step that enters the head's link led from s to s0
            (Top/H0/Tw/K2C/Head.lean: headFrontQ); the kind's own decision (ReplyKind.lean: decide)
            said yes from s0, at a front stretch of rs, to t0; and the reply that it laid is the
            reply behind b. (That decision takes just one round: so the element laid is the first
            round's of those that b was shown.)
    made    behind every yes of b: an element stands in the reply's one seat, and it is an entry of
            the vocabulary (TokSmall: the promise that pays K6Left's second clause).
    step    the last two behind every step of b that goes on.
  k7_first          THE LAW ON THE NEXT TOKEN (Law/K07Proof.lean: k07Law), ITS FIRST SENTENCE,
                    CALLED at "meets": behind every yes of b the token at out.reply is a number
                    below V. (No new fact beside "made": Lean's word that the premise fits to the
                    letter.)
  k7_last           where the description's last test says yes at an instance and a record that
                    passes the record's own test on the request, and TokSmall holds: the kind's part
                    of the last test says yes (ReplyKind.lean: fin), at the output head's seat: the
                    premise that K07's law takes; and the request's words are still the instance's.
The seated constant's first half is guarded: that its yes is the entry's own is guarded_under.
What the form of these statements guards against. "meets" stands at b's own record and rounds: with
the record and the rounds of the kind's decision tied to nothing, whoever holds "made" could make
them up, and the clause would say no more than "made" · met_iff weighs "what is laid is the
round's", which negations by the two cheapest tests on a block that is wrong on purpose do not ·
k7_first calls the law and spends "meets" · the seated constant of "laid" is named and handed
out.









-/
import Johnson.IMR.FirstSeats
import Johnson.IMR.FlatScope
import Johnson.Top.H0.Tw.K2C.Reply
import Johnson.Desc.Kinds.Law.ReplyMeets
import Johnson.Desc.Kinds.Law.RowPins
import Johnson.Desc.Kinds.Law.ReplyHears
import Johnson.Desc.Kinds.Law.TokenSmall
import Johnson.Desc.Kinds.Law.FinAsked
import Johnson.Desc.Kinds.Law.K07Proof

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4

open VerifiableInference.Desc (Block Chain Link FileDescription OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds (Reply.fin)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law
open OnBytes.Desc.Reply (tokOf)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

/-- Behind a yes of the next token's block: an element is heard, and it is a token. -/
def Heard (V : Nat) (t : S) : Prop := TokSmall V t ∧ ∃ x, t.out.reply = some x

theorem heard_own (W : OnBytes.Model.Verify.Public) (l : Nat) :
    ∀ s rs gs t, (VerifiableInference.Desc.Kinds.Reply.blockOf W l).decide s rs gs = .ok t →
      Heard W.hS.V t := by
  intro s rs gs t hd
  refine ⟨tokSmall_made l W.hS.V hd, ?_⟩
  obtain ⟨o, h, _, _, _, _, rfl⟩ := Came.reply_record l W.hS.V hd
  exact ⟨h, rfl⟩

/-- At the block's own record s and rounds rs: the seat was empty at s; the entry of the head's link
led from s to s0; the kind's own decision said yes from s0, at a front stretch of rs, to t0; what it
laid is t's. -/
def Met (W : OnBytes.Model.Verify.Public) (s : S) (rs : List Fmt.RoundView) (t : S) : Prop :=
  s.out.reply = none ∧ ∃ s0 t0 k,
    VerifiableInference.Desc.First.K2.headFrontQ W.H.tl s = .ok s0 ∧
    VerifiableInference.Desc.Kinds.Reply.decide W.hS.V
      VerifiableInference.Desc.Kinds.Reply.seatAt s0 (rs.take k) = some t0 ∧
    t.out.reply = t0.out.reply

/-- **"meets", written out**: no letter under "there is" is left unpinned: s0 by the entry's yes; r,
rest by rs; h by the round. -/
theorem met_iff (W : OnBytes.Model.Verify.Public) (s : S) (rs : List Fmt.RoundView) (t : S) :
    Met W s rs t ↔ s.out.reply = none ∧
      (∃ s0, VerifiableInference.Desc.First.K2.headFrontQ W.H.tl s = .ok s0) ∧
      ∃ r rest h, rs = r :: rest ∧ OnBytes.Desc.Reply.readReply r = some h ∧
        OnBytes.Desc.Reply.isToken W.hS.V h = true ∧ t.out.reply = some h := by
  constructor
  · rintro ⟨h0, s0, t0, k, g1, g2, g3⟩
    refine ⟨h0, ⟨s0, g1⟩, ?_⟩
    unfold VerifiableInference.Desc.Kinds.Reply.decide
      VerifiableInference.Desc.Kinds.Reply.decideE at g2
    split at g2
    · rename_i r hr
      split at g2
      · cases g2
      · split at g2
        · cases g2
        · rename_i h hh
          split at g2
          · rename_i htok
            obtain rfl : VerifiableInference.Desc.Kinds.Reply.seatAt.setReply s0 h = t0 :=
              Option.some.inj g2
            cases rs with
            | nil => rw [List.take_nil] at hr; cases hr
            | cons a rest =>
              cases k with
              | zero => cases hr
              | succ k =>
                rw [List.take_succ_cons] at hr
                injection hr with e1 _
                exact ⟨a, rest, h, rfl, e1 ▸ hh, htok, g3⟩
          · cases g2
    · cases g2
  · rintro ⟨h0, ⟨s0, g1⟩, r, rest, h, rfl, hh, htok, g3⟩
    have he : s0.out.reply = none := by
      rw [VerifiableInference.Desc.First.K2.headFrontOut _ _ _ g1]
      exact h0
    refine ⟨h0, s0, VerifiableInference.Desc.Kinds.Reply.seatAt.setReply s0 h, 1, g1, ?_, g3⟩
    show (VerifiableInference.Desc.Kinds.Reply.decideE W.hS.V
      VerifiableInference.Desc.Kinds.Reply.seatAt s0 [r]).toOption = _
    unfold VerifiableInference.Desc.Kinds.Reply.decideE
    have he' : (VerifiableInference.Desc.Kinds.Reply.seatAt.reply s0).isSome = false := by
      show s0.out.reply.isSome = false
      rw [he]
      rfl
    simp only [he', hh, htok, if_true, Bool.false_eq_true, if_false]
    rfl

/-- **WHAT STANDS IN THE SEAT BEHIND IS THE FIRST ROUND's ELEMENT.** -/
theorem met_first (W : OnBytes.Model.Verify.Public) (s : S) (r : Fmt.RoundView) (rest : List Fmt.RoundView)
    (t : S) (h : Met W s (r :: rest) t) : t.out.reply = OnBytes.Desc.Reply.readReply r := by
  obtain ⟨_, _, r', rest', x, e, h1, _, h3⟩ := (met_iff W s (r :: rest) t).1 h
  injection e with e1 _
  rw [h3, e1, h1]

/-- **What the laws give at the place**, at given letters. k: the block's number in the flat list.
-/
structure PlaceK7 (flat : List (Block S Cl)) (k : Nat) (Z : ProofFile.Pub)
    (W : OnBytes.Model.Verify.Public) (b : Block S Cl) : Prop where
  laid : IM.Joined Z 24 b (IM.k7Block W 24).retype IM.k7Place
  same : ∀ s rs gs t, b.decide s rs gs = .ok t →
    (IM.k7Block W 24).decide s (rs.take (IM.k7Block W 24).rounds.length)
      (gs.take (IM.k7Block W 24).openings) = .ok t ∧ t.failed = none
  cut : flat = flat.take k ++ b :: flat.drop (k + 1)
  meets : ∀ s rs gs t, b.decide s rs gs = .ok t → Met W s rs t
  made : ∀ s rs gs t, b.decide s rs gs = .ok t → Heard W.hS.V t
  step : ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (t : S) (n : Nat),
    b.step ft s rs cols = .ok (t, n) →
    Met W s (rs.map VerifiableInference.Desc.noDigest) t ∧ Heard W.hS.V t

/-- **AT THE PLACE.** -/
theorem k7_place {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (b : Block S Cl), c.links[24]? = some Lk ∧ Lk.hear[0]? = some b ∧
      PlaceK7 c.blocksInOrder 338 Z Bs.G₀.W b := by
  obtain ⟨Lk, b, e1, e2, hl, -⟩ := IM.k7_sits hS hR O
  have hsame := fun s rs gs t (hy : b.decide s rs gs = .ok t) => IM.k7_sits_yes hS hR O hl hy
  have e : IM.flatIx c 24 0 = 338 := IM.flatIx_scope hS hR O (by decide) 0
  have hcut := IM.hear_cut e1 e2
  rw [e] at hcut
  have key : ∀ s rs gs t, (IM.k7Block Bs.G₀.W 24).decide s rs gs = .ok t →
      Heard Bs.G₀.W.hS.V t := by
    unfold IM.k7Block
    exact behind_andThen _ _ _ _ (heard_own Bs.G₀.W 24)
  have keyM : ∀ s rs gs t, (IM.k7Block Bs.G₀.W 24).decide s rs gs = .ok t →
      s.out.reply = none ∧ ∃ s0,
        VerifiableInference.Desc.First.K2.headFrontQ Bs.G₀.W.H.tl s = .ok s0 ∧
        VerifiableInference.Desc.Kinds.Reply.decide Bs.G₀.W.hS.V
          VerifiableInference.Desc.Kinds.Reply.seatAt s0 rs = some t := by
    intro s rs gs t hd
    unfold IM.k7Block at hd
    obtain ⟨s0, g1, g2, g3⟩ := joined_meets Bs.G₀.W 24 _ _ s rs gs t hd
    have g1' : VerifiableInference.Desc.First.K2.headFrontQ Bs.G₀.W.H.tl s = .ok s0 :=
      VerifiableInference.Desc.guarded_under ProofFile.sameReply (fun _ => false) _ _ _ _ _ g1
    have g2' : VerifiableInference.Desc.Kinds.Reply.decide Bs.G₀.W.hS.V
        VerifiableInference.Desc.Kinds.Reply.seatAt s0 rs = some t := g2
    refine ⟨?_, s0, g1', g2'⟩
    rw [← VerifiableInference.Desc.First.K2.headFrontOut _ _ _ g1']
    exact g3
  have hmeets : ∀ s rs gs t, b.decide s rs gs = .ok t → Met Bs.G₀.W s rs t := by
    intro s rs gs t hy
    obtain ⟨g0, s0, g1, g2⟩ := keyM s _ _ t (hsame s rs gs t hy).1
    exact ⟨g0, s0, t, _, g1, g2, rfl⟩
  have hmade : ∀ s rs gs t, b.decide s rs gs = .ok t → Heard Bs.G₀.W.hS.V t := by
    intro s rs gs t hy
    exact key s _ _ t (hsame s rs gs t hy).1
  refine ⟨Lk, b, e1, e2, hl, hsame, hcut, hmeets, hmade, ?_⟩
  intro ft s rs cols t n hs
  obtain ⟨gs, hd⟩ := Came.step_decide ft b s rs cols t n hs
  exact ⟨hmeets _ _ _ _ hd, hmade _ _ _ _ hd⟩

/-- **THE LAW's FIRST SENTENCE, CALLED AT "meets".** iU3, work: letters of the output head's seat
and parameters, of which the sentence reads the vocabulary's size alone. -/
theorem k7_first (W : OnBytes.Model.Verify.Public) (iU3 work : Nat) {s t : S} {rs : List Fmt.RoundView}
    (h : Met W s rs t) :
    ∃ n, n < W.hS.V ∧ VerifiableInference.Desc.Kinds.Reply.token
      VerifiableInference.Desc.Kinds.Reply.seatAt t = some n := by
  obtain ⟨_, s0, t0, k, _, g2, g3⟩ := h
  obtain ⟨_, n, hn, ht⟩ := (k07Law S (seatAt W.hS iU3) (fun _ _ => rfl)
    (VerifiableInference.Desc.Kinds.Head.parOf W.hS work) 0 0 0 0).1 s0 t0 (rs.take k) g2
  refine ⟨n, hn, ?_⟩
  have ht' : (t0.out.reply).map tokOf = some n := ht
  show (t.out.reply).map tokOf = some n
  rw [g3]
  exact ht'

/-- **THE LAST TEST**: where the description's own last test says yes. s₁: the first chain's last
record. (O.desc says that F is this term.) -/
theorem k7_last (o : ProofFile.SecondHashFunctionArgument) {Z : ProofFile.Pub} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (x : ProofFile.Inst) (s₁ : S) (s₂ : A.σ) (s₃ : B.σ)
    (hfin : (ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c).fin x s₁ s₂
      s₃ = true) (V T iU3 : Nat) (hS : OnBytes.Model.Head.Shape) (ht : TokSmall V s₁)
    (hq : s₁.reqOk T V = true) :
    Reply.fin V T s₁.rowR s₁.rowE (tokOf x.asked) (seatAt hS iU3).toSeat s₁ = true ∧
      s₁.req = OnBytes.Model.Verify.words32 x.pub.request := by
  have h : (s₁.finAsked x.asked && s₁.req == OnBytes.Model.Verify.words32 x.pub.request &&
      (A.ended s₂).isSome && B.done s₃) = true := hfin
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨fin_of_heard V T x.asked s₁ h.1.1.1 ht hq, h.1.1.2⟩

end P4

#print axioms P4.met_iff
#print axioms P4.met_first
#print axioms P4.k7_first
#print axioms P4.k7_place
#print axioms P4.k7_last
