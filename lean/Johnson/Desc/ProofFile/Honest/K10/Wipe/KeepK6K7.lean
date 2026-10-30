-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepK6K7.lean: the closing of a segment (K10): the block of the next token (kind
K7, Johnson/Stored/ReplySeatAt.lean: blockOf) and the output head's own block as a lot seats it (kind K6,
Johnson/Stored/HeadAddsAtS.lean: seatedClaims) do alike at two states of the first chain that are one once wiped. Two
structures of type Prop; the rest are theorems.

Words. wipeS sets to zero the targets of the rows that a state of the first chain holds (Honest/K10/WipeS.lean says
which). Two states are one under w where w s = w s'. A reader does not see w where it returns at w s what it returns
at s. A writer goes through w where it returns at w s the image under w of what it returns at s. Two outcomes are
alike where both refuse with the same word, or both return and the values are one under w (AlikeE, Wipe/Alike.lean). A
block does alike (Whole2 w) where its decide, each of its runs of claims and each of its runs behind the batching have
like outcomes at two states that are one under w; the claims of a run are then equal.

What is proved.
  ReplyBlind w L  what is asked of the seat L of the heard reply: its reader does not see w; its laying goes through w
  decideE2, kind7_whole2   ReplyBlind w L ⊢ K7's decide, and so its block, do alike, at any type of state
  replyAt_blind, openedAt_blind   ReplyBlind wipeS of the seat at the first chain's state; what the test in front of
                  K7's block reads does not see the wiping
  **k7_keeps**      Whole2 wipeS (Reply.blockOf W l): the field k7 of SeatKeeps2 (Wipe/Lots2.lean)
  HeadBlind w L what is asked of K6's seat L: its six readers do not see w; four of its five layings go through w (of
                  the inherited setReply, which K6's text does not call, nothing is asked)
  given_blind, lettersAt_blind, callerKeys_blind   what the kind makes of the state before it computes (its letters;
                  the keys for "join") does not see w
  decideBy2, runsBy2, kind6_whole2, kindWithJoin_whole2   HeadBlind w L (for the last also K3Blind w of the lookup's
                  seat, Wipe/KeepK3.lean) ⊢ the kind's decide, its runs, its block, and its block with the run "join" do
                  alike, at any type of state
  headAt_blind    HeadBlind wipeS (Head.seatAt h iU3)
  **k6_keeps**      seatedClaims W l before = some b ⊢ Whole2 wipeS b: the field k6

By what. At any type of state: what the seat's readers return at s is rewritten to what they return at s'; then the
two texts make the same calls, one after the other (AlikeE.head'). K6's decide ends in three layings in a row: each
takes like states to like states (AlikeE.bind'). The hearings and the formulas are handed letters, a ledger and
rounds, never the state: they are not opened. At the first chain's state: Wipe/WipeLaws.lean, or the state is taken
apart by the kind of place. The tests in front of the two blocks: Wipe/Wrap2.lean's entered_whole2 and tested_whole2.

Limits. Nothing is said of what the hearings or the formulas compute. No property of the protocol is claimed: nothing
is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK3
import Johnson.Stored.ReplySeatAt
import Johnson.Stored.HeadAddsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First

/-! ## 1 K7 -/

/-- What is asked of the seat of the heard reply: the reader does not see w; the laying goes through w. -/
structure ReplyBlind {T : Type} (w : T → T) (L : Kinds.Reply.Seat T) : Prop where
  reply : ∀ s, L.reply (w s) = L.reply s
  setReply : ∀ s x, L.setReply (w s) x = w (L.setReply s x)

/-- K7's decide has like outcomes at two states that are one under w. -/
theorem decideE2 {T : Type} {w : T → T} {L : Kinds.Reply.Seat T} (h : ReplyBlind w L) (V : Nat) {s s' : T}
    (hs : w s = w s') (rs : List Fmt.RoundView) :
    AlikeE w (Kinds.Reply.decideE V L s rs) (Kinds.Reply.decideE V L s' rs) := by
  rcases rs with _ | ⟨r, _ | ⟨r', rest⟩⟩
  · exact AlikeE.error _
  · simp only [Kinds.Reply.decideE]
    refine AlikeE.iteB (by rw [blind2 (f := L.reply) h.reply hs]) (AlikeE.error _) ?_
    cases OnBytes.Desc.Reply.readReply r with
    | none => exact AlikeE.error _
    | some x => exact AlikeE.iteB rfl (AlikeE.ok (put2 (f := L.setReply) h.setReply hs x)) (AlikeE.error _)
  · exact AlikeE.error _

/-- K7's block does alike at a seat whose reader does not see w and whose laying goes through w. -/
theorem kind7_whole2 {T Cl : Type} {w : T → T} {L : Kinds.Reply.Seat T} (h : ReplyBlind w L) (link piece V : Nat) :
    Whole2 w (Kinds.Reply.kind (Cl := Cl) L link piece V) :=
  whole2_bare (fun _ _ rs _ _ hs _ => decideE2 h V hs rs) rfl rfl

/-- The seat of the heard reply at the first chain's state: its reader does not see the wiping; its laying goes
through it. -/
theorem replyAt_blind : ReplyBlind wipeS Kinds.Reply.seatAt := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- Whether the state stands in the head's segment, and whether that is opened, is the same at the wiped state and at
the state. -/
theorem openedAt_blind (s : S) : openedAt (wipeS s) = openedAt s := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- **Kind K7's block does alike at two states that are one once wiped.** -/
theorem k7_keeps (W : Verify.Public) (l : Nat) : Whole2 wipeS (Kinds.Reply.blockOf W l) :=
  entered_whole2 openedAt_blind (kind7_whole2 replyAt_blind l 1 W.hS.V)

/-! ## 2 K6 at any type of state -/

section letter
variable {T Cl : Type} {w : T → T} {L : Kinds.Head.Seat T}

/-- What is asked of K6's seat: the readers do not see w; four of its five layings go through w (of the inherited
setReply, which K6's text does not call, nothing is asked). -/
structure HeadBlind (w : T → T) (L : Kinds.Head.Seat T) : Prop where
  reply : ∀ s, L.reply (w s) = L.reply s
  request : ∀ s, L.request (w s) = L.request s
  ledger : ∀ s, L.ledger (w s) = L.ledger s
  lookup : ∀ s, L.lookup (w s) = L.lookup s
  reads : ∀ s, L.reads (w s) = L.reads s
  heard : ∀ s, L.heard (w s) = L.heard s
  setLedger : ∀ s F, L.setLedger (w s) F = (L.setLedger s F).map w
  setHeard : ∀ s H, L.setHeard (w s) H = (L.setHeard s H).map w
  setWeightClaim : ∀ s x, L.setWeightClaim (w s) x = w (L.setWeightClaim s x)
  setKeyForms : ∀ s k, L.setKeyForms (w s) k = w (L.setKeyForms s k)

/-- The letters in front of the hearing do not see w. -/
theorem given_blind (h : HeadBlind w L) (p : Kinds.Head.Par) (s : T) :
    Kinds.Head.given p L (w s) = Kinds.Head.given p L s := by
  unfold Kinds.Head.given Kinds.Reply.token
  rw [h.lookup s, h.reply s, h.request s]

/-- The letters behind the hearing and the sending of the reads do not see w either. -/
theorem lettersAt_blind (h : HeadBlind w L) (p : Kinds.Head.Par) (s : T) :
    Kinds.Head.lettersAt p L (w s) = Kinds.Head.lettersAt p L s := by
  unfold Kinds.Head.lettersAt
  rw [given_blind h p s, h.heard s, h.reads s]

/-- K6's keys for "join" do not see w. -/
theorem callerKeys_blind (h : HeadBlind w L) (p : Kinds.Head.Par) (s : T) :
    Kinds.Head.callerKeys p L (w s) = Kinds.Head.callerKeys p L s := by
  unfold Kinds.Head.callerKeys
  rw [lettersAt_blind h p s]

/-- K6's decide, whatever rounds, hearing and claim on the weights it is handed, has like outcomes at two states that
are one under w. The three letters' types are left to Lean: rounds : Given → List Round, hear : Given → Hear HeardAll,
weights : Given → Behind → SumOnMatrix, as the library's `decideBy` has them. -/
theorem decideBy2 (h : HeadBlind w L) (rounds : _) (hear : _) (weights : _) (p : Kinds.Head.Par) {s s' : T}
    (hs : w s = w s') (rs : List Fmt.RoundView) :
    AlikeE w (Kinds.Head.decideBy rounds hear weights p L s rs)
      (Kinds.Head.decideBy rounds hear weights p L s' rs) := by
  unfold Kinds.Head.decideBy
  rw [blind2 (f := Kinds.Head.given p L) (given_blind h p) hs, blind2 (f := L.ledger) h.ledger hs]
  refine AlikeE.head' fun g => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun y => ?_
  obtain ⟨H, F, left⟩ := y
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.bind' (putE2 (f := L.setLedger) h.setLedger hs F) fun s1 s1' h1 => ?_
  refine AlikeE.bind' (putE2 (f := L.setHeard) h.setHeard h1 H) fun s2 s2' h2 => ?_
  exact AlikeE.ok (put2 (f := L.setWeightClaim) h.setWeightClaim h2 _)

/-- K6's runs of claims, whatever named runs of forms they are made of, return equal claims and like states. Two
letters' types are left to Lean: runs : Given → Behind → Places → List (String × List Form), keys : Given → Behind →
Places → List Form, as the library's `runsBy` has them. -/
theorem runsBy2 (h : HeadBlind w L) (names : List String) (runs : _) (keys : _) (toCl : Kinds.Form → Cl)
    (p : Kinds.Head.Par) : ∀ c ∈ Kinds.Head.runsBy names runs keys toCl p L, ∀ n, FnCl2 w (c.2 n) := by
  intro c hc n s s' hs
  unfold Kinds.Head.runsBy at hc
  obtain ⟨name, -, rfl⟩ := List.mem_map.1 hc
  dsimp only
  rw [blind2 (f := Kinds.Head.lettersAt p L) (lettersAt_blind h p) hs]
  refine AlikeE.head' fun y => ?_
  obtain ⟨g, b, x⟩ := y
  refine AlikeE.head' fun fs => ?_
  refine AlikeE.ok (wCl_eq ?_)
  by_cases hn : (names.head? == some name) = true
  · rw [if_pos hn, if_pos hn]
    exact put2 (f := L.setKeyForms) h.setKeyForms hs _
  · rw [if_neg hn, if_neg hn]
    exact hs

/-- **K6's block does alike at a seat whose readers do not see w and whose layings go through w.** -/
theorem kind6_whole2 (h : HeadBlind w L) (cl : Kinds.Form → Cl) (link piece : Nat) (p : Kinds.Head.Par) :
    Whole2 w (Kinds.Head.kind cl L link piece p) := by
  refine ⟨fun s s' rs gs gs' hs _ => ?_, fun c hc => ?_, (fun _ hc => nomatch hc)⟩
  · simp only [Kinds.Head.kind]
    exact decideBy2 h _ _ _ p hs rs
  · simp only [Kinds.Head.kind] at hc
    exact runsBy2 h _ _ _ _ p c hc

/-- **So does K6's block with the lookup's run "join" among its runs.** -/
theorem kindWithJoin_whole2 {look : K3.Seat T Cl} (hl : K3Blind w look) (h : HeadBlind w L) (link piece : Nat)
    (p : Kinds.Head.Par) : Whole2 w (Kinds.Head.kindWithJoin look L link piece p) := by
  have W := kind6_whole2 h look.claim link piece p
  refine ⟨W.1, fun c hc => ?_, W.2.2⟩
  have hc' : c ∈ (Kinds.Head.kind look.claim L link piece p).claims.take 1 ++
      [("join", K3.joinRun look (Kinds.Head.callerKeys p L))] ++
      (Kinds.Head.kind look.claim L link piece p).claims.drop 1 := hc
  rcases List.mem_append.1 hc' with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · exact W.2.1 c (List.mem_of_mem_take hx)
    · obtain rfl := List.mem_singleton.1 hx
      exact fun n => joinRun2 hl (callerKeys_blind h p) n
  · exact W.2.1 c (List.mem_of_mem_drop hx)

end letter

/-! ## 3 K6 at the first chain's state -/

/-- K6's seat at the first chain's state: its readers do not see the wiping; its layings go through it. -/
theorem headAt_blind (h : Model.Head.Shape) (iU3 : Nat) : HeadBlind wipeS (Kinds.Head.seatAt h iU3) where
  reply _ := rfl
  request s := by
    show Kinds.Head.requestOf (wipeS s) = Kinds.Head.requestOf s
    unfold Kinds.Head.requestOf
    rw [tokv_wipe, rowR_wipe, rowE_wipe]
  ledger s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl
  lookup s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl
  reads s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl
  heard s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl
  setLedger s F := putFork?_wipe s F
  setHeard s H := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _ | _⟩ | _ | _, _⟩ <;> rfl
  setWeightClaim _ _ := rfl
  setKeyForms _ _ := rfl

/-- **Kind K6's block, as a lot seats it, does alike at two states that are one once wiped.** -/
theorem k6_keeps {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)} {b : Block S Claim}
    (h : Kinds.Head.seatedClaims W l before = some b) : Whole2 wipeS b := by
  unfold Kinds.Head.seatedClaims at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold Kinds.Head.blockClaims at h0
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h0
  exact tested_whole2 _ _ _ (fun s => reqOk_wipe _ _ s)
    (kindWithJoin_whole2 (seatCalls_blind _) (headAt_blind _ _) _ _ _)

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.ReplyBlind
#print axioms ProofFile.Honest.K10.decideE2
#print axioms ProofFile.Honest.K10.kind7_whole2
#print axioms ProofFile.Honest.K10.replyAt_blind
#print axioms ProofFile.Honest.K10.openedAt_blind
#print axioms ProofFile.Honest.K10.k7_keeps
#print axioms ProofFile.Honest.K10.HeadBlind
#print axioms ProofFile.Honest.K10.given_blind
#print axioms ProofFile.Honest.K10.lettersAt_blind
#print axioms ProofFile.Honest.K10.callerKeys_blind
#print axioms ProofFile.Honest.K10.decideBy2
#print axioms ProofFile.Honest.K10.runsBy2
#print axioms ProofFile.Honest.K10.kind6_whole2
#print axioms ProofFile.Honest.K10.kindWithJoin_whole2
#print axioms ProofFile.Honest.K10.headAt_blind
#print axioms ProofFile.Honest.K10.k6_keeps
