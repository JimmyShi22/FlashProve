-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndTakesFrame.lean: which entries of the plan the calls of a link use up that
are not the sub-proof's own: a sending, the code switch, the draw of the matrix, the batching
element, the fold.

Theorems with their proofs, by the laws of OnBytes/Tie/Pv/Tail/EndTakes.lean (`Takes x N`: wherever
x returns it has used up entries with just the names N). A stretch of a routine's text that closes
no round is passed by the class of OnBytes/Tie/Pv/Tail/EndLullModel.lean. The lists are those that
OnBytes/Tie/Pv/Req/Names.lean and Link.lean say of the planner's routines.

Main names:
  `qb`, `qs`, `ql`: tactics that pass a stretch of a text which closes no round.
  `takes_closeOne`, `takes_closeEmpty`, `takes_closePositions`: closings.
  `takes_send`, `takes_sendVerify`: SEND seed, and SEND answer if the sending closes its own round
    of answers.
  `takes_later`, `takes_checkLater`, `takes_call`, `takes_rootInH`: a sending of a link: SEND seed,
    SEND answer.
  `takes_switch`: the code switch without a challenge: SEND seed, LOC.
  `takes_getB`, `takes_mustB`: a value that must be there, or a public condition, then f, which may
    use it.
  `beginLink_link`: the link's number is kept where a link begins.
  `firstNames`, `closeNames`: the names of the rounds of a link's first call and of its closing.
  `takes_trits`, `takes_drawMatrixF`: RNG. `takes_batchOpen`, `takes_batch`, `takes_t2Batch`:
    BAT-sigma.
  `takes_batVerify`: BAT. `takes_foldRounds`, `takes_fold`: FOLD epsilon, and as many FOLD round as
    the fold's shape says.

Limits: names alone. One direction: from a run that returns. Of a link's first call and of its
closing the lists are defined here; that the calls use up these entries is not shown.


-/
import OnBytes.Tie.Pv.Tail.EndLullModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Lull
open OnBytes OnBytes.Model OnBytes.L5 OnBytes.Tie.Pv.Tail.Used

/-- Passes a stretch of a block's text that closes no round. -/
macro "qb" : tactic => `(tactic| exact takes_lull_blk (by keepsM))

/-- The same in a routine of a sub-proof. -/
macro "qs" : tactic => `(tactic| exact takes_lull_sub (by keepsM))

/-- The same in a routine of a link. -/
macro "ql" : tactic => `(tactic| exact takes_lull_link (by keepsM))

/-! ## Closings -/

theorem takes_closeOne (name : String) (kind : Fmt.Kind) (nz : Nat) :
    Takes (Blk.closeOne name kind nz) [name] := by
  unfold Blk.closeOne
  refine Takes.before (takes_close _ _ _) fun d => ?_
  split
  · exact Takes.pure _
  · exact fun _ _ _ h => by cases h

/-- `Blk.closeEmpty` uses up entries with just the names of the statement, in this order. -/
theorem takes_closeEmpty (name : String) : Takes (Blk.closeEmpty name) [name] := by
  unfold Blk.closeEmpty
  exact Takes.before (takes_close _ _ _) fun _ => Takes.pure _

/-- `Blk.closePositions` uses up entries with just the names of the statement, in this order. -/
theorem takes_closePositions (name : String) (logN : Nat) :
    Takes (Blk.closePositions name logN) [name] := by
  unfold Blk.closePositions
  exact Takes.before (takes_close _ _ _) fun _ => by qb

/-! ## Sendings -/

theorem takes_send (ids : Array Nat) (own : Bool) :
    Takes (Send.verify ids own) ("SEND seed" :: (if own = true then ["SEND answer"] else [])) := by
  unfold Send.verify
  refine Takes.after (by qb) fun S => ?_
  dsimp only
  refine Takes.after (by qb) fun _ => Takes.after (by qb) fun _ => Takes.after (by qb) fun _ => ?_
  refine Takes.bind (N := ["SEND seed"]) (takes_close _ _ _) fun _ => ?_
  refine Takes.after (by qb) fun _ => Takes.after (by qb) fun _ => Takes.after (by qb) fun _ => ?_
  cases own with
  | true => exact takes_closeEmpty _
  | false => exact Takes.pure _

/-- `sendVerify` uses up entries with just the names of the statement, in this order. -/
theorem takes_sendVerify (notices : Array OracleNotice) (own : Bool) :
    Takes (sendVerify notices own)
      ("SEND seed" :: (if own = true then ["SEND answer"] else [])) := by
  unfold sendVerify
  exact Takes.after (by qb) fun _ => Takes.before (takes_send _ _) fun _ => Takes.pure _

/-- `f.later` uses up entries with just the names of the statement, in this order. -/
theorem takes_later (f : ReqFrame) : Takes f.later ["SEND seed", "SEND answer"] := by
  unfold ReqFrame.later
  refine Takes.after (by qb) fun _ => Takes.after (by qb) fun _ => ?_
  exact Takes.before (takes_sendVerify _ true) fun _ => by qb

/-- `k.later` uses up entries with just the names of the statement, in this order. -/
theorem takes_checkLater (k : ChainCheck) : Takes k.later ["SEND seed", "SEND answer"] := by
  unfold ChainCheck.later
  refine Takes.after (by qb) fun _ => Takes.before (takes_later _) fun x => ?_
  obtain ⟨f, sent⟩ := x
  exact Takes.pure _

/-- A call of the chain takes what the chain's routine takes. -/
theorem takes_call {f : ChainCheck → Blk ChainCheck} {N : List String} (hf : ∀ k, Takes (f k) N) :
    Takes (LinkM.call f) N := fun s u s' h => by
  obtain ⟨_, chk, h1, _, _⟩ := call_L h
  exact hf _ _ _ _ h1

/-- `rootInH` uses up entries with just the names of the statement, in this order. -/
theorem takes_rootInH (trees : List Nat) : Takes (rootInH trees) ["SEND seed", "SEND answer"] := by
  unfold rootInH
  refine Takes.after (by ql) fun L => Takes.after (by ql) fun _ => ?_
  exact Takes.before (takes_call takes_checkLater) fun _ => by ql

/-! ## A link's first call -/

theorem takes_switch (old : SingleRows) (T : SwitchTarget) (dest : Nat)
    (others : Array OracleNotice) :
    Takes (csSigmaVerify old T dest others) ["SEND seed", "LOC"] := by
  unfold csSigmaVerify switchVerify
  refine Takes.before ?_ fun _ => Takes.pure _
  refine Takes.after (by qb) fun S => Takes.after (by qb) fun _ => ?_
  dsimp only
  refine Takes.bind (N := ["SEND seed"]) (takes_sendVerify _ false) fun ids => ?_
  refine Takes.after (by qb) fun code => ?_
  exact Takes.before (takes_closePositions _ _) fun _ => by qb

/-- The names of the rounds of a link's first call. plain: the number of the link's plain scalars;
l: the link's number. -/
def firstNames (plain l : Nat) : List String :=
  (if (plain != 0) = true then ["REPLY"] else []) ++
    (if (l == 0) = true then ["SEND seed", "SEND answer"] else ["SEND seed", "LOC"])

/-- A value that must be there, then f: f may use what it is. -/
theorem takes_getB {α β : Type} {x : Option α} {n : String} {f : α → Blk β} {N : List String}
    (hf : ∀ a, x = some a → Takes (f a) N) : Takes (Blk.get x n >>= f) N := fun s b s' h => by
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind (m := Blk) h
  obtain ⟨hx, e⟩ := runs_blkGet h1
  rw [e] at h2
  exact hf a hx s b s' h2

/-- A public condition, then f: f may use it. -/
theorem takes_mustB {β : Type} {b : Bool} {n : String} {f : Unit → Blk β} {N : List String}
    (hf : b = true → Takes (f ()) N) : Takes (Blk.must b n >>= f) N := fun s a s' h => by
  obtain ⟨u, s1, h1, h2⟩ := HasRuns.runs_bind (m := Blk) h
  obtain ⟨hb, e⟩ := (PscRun.mustB_ok b n s (u, s1)).1 h1
  have e1 : s1 = s := congrArg Prod.snd e
  rw [e1] at h2
  exact hf hb s a s' h2

/-- The link's number is kept where a link begins. -/
theorem beginLink_link (f : ReqFrame) (s : Ctx) (f1 : ReqFrame) (s' : Ctx)
    (h : Runs f.beginLink s f1 s') : f1.link = f.link := by
  unfold ReqFrame.beginLink at h
  obtain ⟨g, s1, -, h2⟩ := HasRuns.runs_bind (m := Blk) h
  rw [(HasRuns.runs_pure (m := Blk) h2).1]

/-! ## The draw of the matrix; the batching element -/

theorem takes_trits (columns combinations : Nat) :
    Takes (SubM.trits columns combinations) ["RNG"] := by
  refine Takes.lift ?_
  unfold trTrits
  exact Takes.after (by qb) fun _ => Takes.before (takes_closeAs _ _ _ _ _) fun _ => Takes.pure _

/-- `tl.drawMatrixF` uses up entries with just the names of the statement, in this order. -/
theorem takes_drawMatrixF (tl : HTailF2) : Takes tl.drawMatrixF ["RNG"] := by
  unfold HTailF2.drawMatrixF
  exact Takes.after (by qs) fun _ => Takes.before (takes_trits _ _) fun _ => Takes.pure _

/-- `SubM.batchOpen` uses up entries with just the names of the statement, in this order. -/
theorem takes_batchOpen : Takes SubM.batchOpen ["BAT-sigma"] := by
  refine Takes.lift ?_
  unfold trBatchOpen
  exact Takes.before (takes_closeAs _ _ _ _ _) fun _ => takes_oneOf _

/-- `SubM.batch` uses up entries with just the names of the statement, in this order. -/
theorem takes_batch (rows : Nat) : Takes (SubM.batch rows) ["BAT-sigma"] := by
  refine Takes.lift ?_
  unfold trBatch trBatchOpen
  refine Takes.after (by qb) fun _ => ?_
  refine Takes.before (Takes.before (takes_closeAs _ _ _ _ _) fun _ => takes_oneOf _) fun _ => by qb

/-- A routine of a sub-proof, in a link. -/
theorem takes_sub {α : Type} {x : SubM α} {N : List String} (hx : Takes x N) :
    Takes (LinkM.sub x) N := fun s a s' h => hx s.2 a s'.2 (runs_sub h).1

/-- `t2Batch` uses up entries with just the names of the statement, in this order. -/
theorem takes_t2Batch (used : Nat) : Takes (t2Batch used) ["BAT-sigma"] := by
  unfold t2Batch
  refine Takes.after (by ql) fun L => Takes.after (by ql) fun x => ?_
  obtain ⟨ns, planClaims⟩ := x
  dsimp only
  refine Takes.after (by ql) fun _ => Takes.after (by ql) fun _ => Takes.after (by ql) fun _ => ?_
  exact Takes.before (takes_sub takes_batchOpen) fun _ => by ql

/-! ## The closing of a link -/

theorem takes_batVerify (g : Nat) : Takes (batVerify g) ["BAT"] := by
  unfold batVerify
  exact Takes.after (by qb) fun _ => Takes.before (takes_closeOne _ _ _) fun _ => by qb

/-- n rounds of a fold use up n entries named FOLD round. -/
theorem takes_foldRounds : ∀ (n : Nat) (claim : E),
    Takes (foldRounds n claim) (List.replicate n "FOLD round")
  | 0, claim => by
    unfold foldRounds
    exact Takes.pure _
  | n + 1, claim => by
    unfold foldRounds
    refine Takes.after (by qb) fun _ => Takes.after (by qb) fun _ => ?_
    refine Takes.bind (N := ["FOLD round"]) (takes_closeOne _ _ _) fun g => ?_
    exact Takes.before (takes_foldRounds n _) fun _ => Takes.pure _

/-- `foldVerify` uses up entries with just the names of the statement, in this order. -/
theorem takes_fold (F : FoldShape) (row : GroupRow) (mask : Option Nat) :
    Takes (foldVerify F row mask) ("FOLD epsilon" :: List.replicate F.layout.k "FOLD round") := by
  unfold foldVerify foldEpsilon foldRoundsVerify
  refine Takes.after (by qb) fun s => ?_
  refine Takes.bind (N := ["FOLD epsilon"]) ?_ fun s1 => ?_
  · exact Takes.after (by qb) fun _ => Takes.before (takes_closeOne _ _ _) fun _ => Takes.pure _
  refine Takes.after (by qb) fun _ => ?_
  dsimp only
  refine Takes.after (by qb) fun _ => Takes.after (by qb) fun _ => Takes.after (by qb) fun _ => ?_
  exact Takes.before (takes_foldRounds _ _) fun _ => Takes.pure _

/-- The names of the rounds of a link's closing. k: the number of the group's folding rounds. -/
def closeNames (k : Nat) : List String := "BAT" :: "FOLD epsilon" :: List.replicate k "FOLD round"

end OnBytes.Tie.Pv.Tail.Lull

#print axioms OnBytes.Tie.Pv.Tail.Lull.takes_rootInH
#print axioms OnBytes.Tie.Pv.Tail.Lull.takes_t2Batch
#print axioms OnBytes.Tie.Pv.Tail.Lull.takes_fold
#print axioms OnBytes.Tie.Pv.Tail.Lull.takes_switch
#print axioms OnBytes.Tie.Pv.Tail.Lull.takes_drawMatrixF
