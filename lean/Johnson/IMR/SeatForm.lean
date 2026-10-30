-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SeatForm.lean.
A CAUTION: LaidAlone DOES NOT DETERMINE b': EVERY SEATED BLOCK BEARS IT TO ITSELF: A STATEMENT IS WORTH ITS EQUATION FOR b', NEVER LaidAlone ALONE.
guardMark_yes IS decide_guards, CALLED (Johnson/Desc/First/K8/LawSeated.lean); step_iff is general in Q, step_guards is its case «no mark behind».
A LAW ABOUT ProofFile.guardMark AND Block.guarded, NO PART OF THEM: THE FORM IN WHICH A LOT's BLOCK STANDS
IN
onlineDescription's FIRST CHAIN, and what a yes, a run of claims and a run behind the batching of the seated block say of the
lot's block.
OBJECT. No constant of the protocol: the three layers that the harness and the driver lay around ANY block b' of a lot:
  ProofFile.guardMark (Johnson/Desc/ProofFile/Frames1.lean) · the spot's name and the driver's address written in · Block.guarded same hearsReply (the driver's
  layer, Johnson/Desc/SeatGuard.lean, laid by firstChain).
USER. Johnson/IMR/PureChain.lean and the seats (Johnson/IMR/K6Seat.lean …), and whoever holds a law on its own block and wants it at the seated block.
LETTERS. same: the guard's test (at onlineDescription's seat: ProofFile.sameReply) · b: the chain's block · b': the lot's block, at the fold's claims
  (a block of Lot.hearC as it is; a block x of Lot.own as x.retype) · name: the spot's name ·
  a: the driver's address.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7' | G7'bits (Ladder.lean · Ladder/Bits.lean) hand every o: for these the in-scope halves are owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

  seatedAs same b' name a   THE TERM: (({ guardMark b' with name := name }) with place := a).guarded same hearsReply.
  LaidAlone same b b' name a   b IS that term. Nothing is joined behind. NO «there is» stands in it.
  Laid same b b' name a     b is that term, OR the like with a block q joined behind the marked block (Block.andThen), q itself guarded
                            at no place free (chainBy's text). q STANDS UNDER «there is» AND ITS EQUATION DOES NOT DETERMINE IT (andThen swallows q's name and place): A SEAT AT A
                            LINK's FIRST PLACE HANDS q OUT BY NAME (seatedWith); Laid serves laid_planOk | yes_laid alone.
  alone_planOk | _rounds | _oracles | _before | _name | _place    the six fields that no layer turns, or that are the letters.
  laid_planOk | retype_planOk   the seated block's test on the plan holds the lot's block's, at either arm; a carried block's holds its own.
  yes_alone                 at an address that is not K7's: b.decide s rs gs = ok t  ↔  b'.decide s rs gs = ok t ∧ t bears no mark ∧
                            same s t = true: THE SAME RECORD t, the same rounds, the same groups.
  yes_alone_K7              at K7's address the guard leaves the decision free: ↔ b'.decide s rs gs = ok t ∧ t bears no mark.
  step_alone (by step_iff)  THE GUARDS OFF AT THE STEP, at an address that is not K7's: b.step ft s rs cols = ok (t, k) ↔ b'.step ft s rs cols = ok (t, k) ∧ t bears no mark ∧ same s t = true.
  sameReply_eq              ProofFile.sameReply s t = true → s.out.reply = t.out.reply.
  alone_underR              at every address: Block.UnderR b b' (Johnson/Desc/Sound/SeatGuardChain.lean): that file's step_under | fold_under carry a yes of the step over.
  claims_alone | after_alone   b's runs are b''s runs, name by name in the same order, each behind the guard's test.
  claim_yes | after_yes     a run that is looked up by name in b: there is the run of that name in b' (looked up, not «a member»), and
                            its yes holds if and only if that run's yes does with same t y.2 = true. (From a look-up in b' to one in b: claims_lookup | after_lookup.)
                            NO «no mark» FOR A RUN: guardMark wraps the decision alone.
  yes_laid                  at either arm, with the record behind tied.

What is not claimed. WHICH block stands where (Johnson/IMR/PureChain.lean and the seats). Nothing on
the batching's block, on Link.each | tests.
A law that CONCLUDES a yes of b' does not pass to b without «no mark» and «same». No soundness.
-/
import Johnson.Desc.ProofFile.Frames1
import Johnson.Desc.Sound.SeatGuardChain
import Johnson.Desc.First.K8.LawSeated

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Place KindName seatSame)
open VerifiableInference.Desc.First (S hearsReply)
open ProofFile (Cl)

/-- The marked block under the spot's name. -/
def marked (b' : Block S Cl) (name : String) : Block S Cl := { ProofFile.guardMark b' with name := name }

/-- **THE TERM: a lot's block as it stands in the first chain, alone.** -/
def seatedAs (same : S → S → Bool) (b' : Block S Cl) (name : String) (a : Place) : Block S Cl :=
  Block.guarded same hearsReply { marked b' name with place := a }

/-- The like with a block joined behind (chainBy: the half that is joined is guarded at no place free). -/
def seatedWith (same : S → S → Bool) (b' q : Block S Cl) (name : String) (a : Place) : Block S Cl :=
  Block.guarded same hearsReply
    { (marked b' name).andThen name (q.guarded same fun _ => false) with place := a }

/-- b is the lot's block b', alone, under that name at that address. -/
def LaidAlone (same : S → S → Bool) (b b' : Block S Cl) (name : String) (a : Place) : Prop :=
  b = seatedAs same b' name a

/-- Alone, or with a block joined behind. -/
def Laid (same : S → S → Bool) (b b' : Block S Cl) (name : String) (a : Place) : Prop :=
  LaidAlone same b b' name a ∨ ∃ q : Block S Cl, b = seatedWith same b' q name a

theorem LaidAlone.laid {same : S → S → Bool} {b b' : Block S Cl} {name : String} {a : Place}
    (h : LaidAlone same b b' name a) : Laid same b b' name a := Or.inl h

section
variable {same : S → S → Bool} {b b' : Block S Cl} {name : String} {a : Place}

theorem alone_planOk (h : LaidAlone same b b' name a) : b.planOk = b'.planOk := by subst h; rfl
theorem alone_rounds (h : LaidAlone same b b' name a) : b.rounds = b'.rounds := by subst h; rfl
theorem alone_oracles (h : LaidAlone same b b' name a) : b.oracles = b'.oracles := by subst h; rfl
theorem alone_before (h : LaidAlone same b b' name a) : b.before = b'.before := by subst h; rfl
theorem alone_name (h : LaidAlone same b b' name a) : b.name = name := by subst h; rfl
theorem alone_place (h : LaidAlone same b b' name a) : b.place = a := by subst h; rfl

theorem with_planOk (q : Block S Cl) (h : b = seatedWith same b' q name a) :
    b.planOk = (b'.planOk && q.planOk) := by subst h; rfl

/-- **The plan's test of the seated block holds the lot's block's**, at either arm. -/
theorem laid_planOk (h : Laid same b b' name a) (hp : b.planOk = true) : b'.planOk = true := by
  rcases h with h | ⟨q, h⟩
  · rw [← alone_planOk h]
    exact hp
  · rw [with_planOk q h, Bool.and_eq_true] at hp
    exact hp.1

/-- A block of Lot.own, carried over to the fold's claims: its test on the plan holds the block's own. -/
theorem retype_planOk {C : Type} (x : Block S C) (hp : (x.retype : Block S Cl).planOk = true) :
    x.planOk = true ∧ x.claims.isEmpty = true := by
  have hp' : (x.planOk && x.claims.isEmpty) = true := hp
  rwa [Bool.and_eq_true] at hp'

/-- guardMark's yes: decide_guards (Johnson/Desc/First/K8/LawSeated.lean), called at ProofFile.guardMark: «Guards (guardMark b') b'» holds by the two texts. -/
theorem guardMark_yes (b' : Block S Cl) (s u : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (ProofFile.guardMark b').decide s rs gs = .ok u ↔ b'.decide s rs gs = .ok u ∧ u.failed = none :=
  VerifiableInference.Desc.First.K8.decide_guards (c := ProofFile.guardMark b') (b := b')
    ⟨rfl, fun _ _ _ => rfl⟩ s u rs gs

/-- **Alone, at an address that is not K7's: the same record, no mark, the reply as it was.** -/
theorem yes_alone (h : LaidAlone same b b' name a) (hk : a.kind ≠ KindName.K7) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = .ok t ↔ b'.decide s rs gs = .ok t ∧ t.failed = none ∧ same s t = true := by
  subst h
  have hp : hearsReply ({ marked b' name with place := a } : Block S Cl).place = false := by
    show (a.kind == KindName.K7) = false
    simpa using hk
  unfold seatedAs
  rw [VerifiableInference.Desc.guarded_yes same hearsReply _ hp]
  show (ProofFile.guardMark b').decide s rs gs = .ok t ∧ _ ↔ _
  rw [guardMark_yes, and_assoc]

/-- At K7's address the guard leaves the decision free. -/
theorem yes_alone_K7 (h : LaidAlone same b b' name a) (hk : a.kind = KindName.K7) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = .ok t ↔ b'.decide s rs gs = .ok t ∧ t.failed = none := by
  subst h
  have hp : hearsReply a = true := by
    show (a.kind == KindName.K7) = true
    simpa using hk
  show (if hearsReply a then (ProofFile.guardMark b').decide s rs gs
    else ((ProofFile.guardMark b').decide s rs gs).bind (seatSame same s)) = .ok t ↔ _
  rw [hp]
  exact guardMark_yes b' s t rs gs

/-- **AT EVERY ADDRESS: the seated block has the lot's block's rounds, and its yes is the lot's block's yes at the same record** (Block.UnderR,
Johnson/Desc/Sound/SeatGuardChain.lean: so step_under | fold_under of that file carry a yes of the step over). -/
theorem alone_underR (h : LaidAlone same b b' name a) : b.UnderR b' := by
  subst h
  exact ⟨rfl, fun s rs gs t hy => ((guardMark_yes b' s t rs gs).1
    (VerifiableInference.Desc.guarded_under same hearsReply { marked b' name with place := a } s rs gs t hy)).1⟩

/-- **A block's step reads its rounds and its decision alone**: two blocks with the same rounds, of which the one's decision says yes just where the other's does and Q holds of the
records in front and behind: the like for their steps. (step_guards, Johnson/Desc/First/K8/LawSeated.lean, is this at Q := «no mark behind»: step_iff is general in Q, step_guards is its case «no mark behind».) -/
theorem step_iff {c d : Block S Cl} {Q : S → S → Prop} (hr : c.rounds = d.rounds)
    (hd : ∀ s rs gs t, c.decide s rs gs = .ok t ↔ d.decide s rs gs = .ok t ∧ Q s t) (ft : Nat)
    (s t : S) (k : Nat) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn) :
    c.step ft s rs cols = .ok (t, k) ↔ d.step ft s rs cols = .ok (t, k) ∧ Q s t := by
  unfold Block.step
  rw [hr]
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · simp
  · split
    · simp
    · generalize VerifiableInference.Desc.regroup _ _ = gs
      cases hc : c.decide s (rs.map VerifiableInference.Desc.noDigest) gs with
      | error e =>
        cases hb : d.decide s (rs.map VerifiableInference.Desc.noDigest) gs with
        | error e' => simp
        | ok u =>
          simp only [Except.ok.injEq, Prod.mk.injEq, false_iff, reduceCtorEq]
          rintro ⟨⟨rfl, -⟩, hq⟩
          rw [(hd s _ gs u).2 ⟨hb, hq⟩] at hc
          cases hc
      | ok u =>
        obtain ⟨h1, h2⟩ := (hd s _ gs u).1 hc
        rw [h1]
        simp only [Except.ok.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, hk⟩
          exact ⟨⟨rfl, hk⟩, h2⟩
        · rintro ⟨hk, -⟩
          exact hk

/-- **THE GUARDS OFF, AT THE STEP**: alone, at an address that is not K7's. -/
theorem step_alone (h : LaidAlone same b b' name a) (hk : a.kind ≠ KindName.K7) (ft : Nat) (s t : S)
    (k : Nat) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn) :
    b.step ft s rs cols = .ok (t, k) ↔
      b'.step ft s rs cols = .ok (t, k) ∧ t.failed = none ∧ same s t = true :=
  step_iff (Q := fun s t => t.failed = none ∧ same s t = true) (alone_rounds h)
    (fun s rs gs t => yes_alone h hk s t rs gs) ft s t k rs cols

/-- The guard around a run of claims. -/
def guardRun (same : S → S → Bool) (r : Nat → S → Except String (List Cl × S)) :
    Nat → S → Except String (List Cl × S) :=
  fun n t => (r n t).bind fun y => (seatSame same t y.2).map fun _ => y

/-- The guard around a run behind the batching. -/
def guardAfter (same : S → S → Bool) (r : S → Except String S) : S → Except String S :=
  fun t => (r t).bind (seatSame same t)

/-- **The seated block's runs of claims are the lot's block's, name by name, each behind the guard.** -/
theorem claims_alone (h : LaidAlone same b b' name a) :
    b.claims = b'.claims.map fun c => (c.1, guardRun same c.2) := by subst h; rfl

theorem after_alone (h : LaidAlone same b b' name a) :
    b.after = b'.after.map fun c => (c.1, guardAfter same c.2) := by subst h; rfl

/-- By the guard's own law (Johnson/Desc/Sound/SeatGuardChain.lean: guarded_lookup_claims). -/
theorem claims_lookup (h : LaidAlone same b b' name a) (n : String) :
    b.claims.lookup n = (b'.claims.lookup n).map (guardRun same) := by
  subst h
  exact VerifiableInference.Desc.guarded_lookup_claims same hearsReply
    { marked b' name with place := a } n

theorem after_lookup (h : LaidAlone same b b' name a) (n : String) :
    b.after.lookup n = (b'.after.lookup n).map (guardAfter same) := by
  subst h
  exact VerifiableInference.Desc.guarded_lookup_after same hearsReply
    { marked b' name with place := a } n

theorem guardRun_yes (r : Nat → S → Except String (List Cl × S)) (n : Nat) (t : S) (y : List Cl × S) :
    guardRun same r n t = .ok y ↔ r n t = .ok y ∧ same t y.2 = true := by
  unfold guardRun
  cases hr : r n t with
  | error e =>
    constructor
    · intro h; cases h
    · intro h; cases h.1
  | ok z =>
    show (seatSame same t z.2).map (fun _ => z) = .ok y ↔ _
    unfold seatSame
    by_cases e : same t z.2 = true
    · rw [if_pos e]
      constructor
      · intro h
        obtain rfl : z = y := Except.ok.inj h
        exact ⟨rfl, e⟩
      · rintro ⟨h1, -⟩
        obtain rfl : z = y := Except.ok.inj h1
        rfl
    · rw [if_neg e]
      constructor
      · intro h; cases h
      · rintro ⟨h1, h2⟩
        obtain rfl : z = y := Except.ok.inj h1
        exact absurd h2 e

theorem guardAfter_yes (r : S → Except String S) (t u : S) :
    guardAfter same r t = .ok u ↔ r t = .ok u ∧ same t u = true := by
  unfold guardAfter
  cases hr : r t with
  | error e =>
    constructor
    · intro h; cases h
    · intro h; cases h.1
  | ok z =>
    show seatSame same t z = .ok u ↔ _
    unfold seatSame
    by_cases e : same t z = true
    · rw [if_pos e]
      constructor
      · intro h
        obtain rfl : z = u := Except.ok.inj h
        exact ⟨rfl, e⟩
      · rintro ⟨h1, -⟩
        obtain rfl : z = u := Except.ok.inj h1
        rfl
    · rw [if_neg e]
      constructor
      · intro h; cases h
      · rintro ⟨h1, h2⟩
        obtain rfl : z = u := Except.ok.inj h1
        exact absurd h2 e

/-- **A run of claims that the frame looks up in the seated block**: it is the guard around the run of that name that is looked up in
the lot's block; its yes is that run's yes, with the reply as it was. -/
theorem claim_yes (h : LaidAlone same b b' name a) {n : String}
    {r : Nat → S → Except String (List Cl × S)} (hr : b.claims.lookup n = some r) :
    ∃ r', b'.claims.lookup n = some r' ∧ r = guardRun same r' ∧
      ∀ k t y, r k t = .ok y ↔ r' k t = .ok y ∧ same t y.2 = true := by
  rw [claims_lookup h] at hr
  obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.1 hr
  exact ⟨r', h', rfl, fun k t y => guardRun_yes r' k t y⟩

theorem after_yes (h : LaidAlone same b b' name a) {n : String} {r : S → Except String S}
    (hr : b.after.lookup n = some r) :
    ∃ r', b'.after.lookup n = some r' ∧ r = guardAfter same r' ∧
      ∀ t u, r t = .ok u ↔ r' t = .ok u ∧ same t u = true := by
  rw [after_lookup h] at hr
  obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.1 hr
  exact ⟨r', h', rfl, fun t u => guardAfter_yes r' t u⟩

/-- **At either arm, with the record behind tied**: a yes of the chain's block gives the lot's block's yes at the front of the rounds and
groups, no mark behind it, and, at the second arm, the joined block's yes from that record on. -/
theorem yes_laid (h : Laid same b b' name a) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hy : b.decide s rs gs = .ok t) :
    (LaidAlone same b b' name a ∧ b'.decide s rs gs = .ok t ∧ t.failed = none) ∨
      ∃ (q : Block S Cl) (t' : S), b = seatedWith same b' q name a ∧
        b'.decide s (rs.take b'.rounds.length) (gs.take b'.openings) = .ok t' ∧ t'.failed = none ∧
        q.decide t' (rs.drop b'.rounds.length) (gs.drop b'.openings) = .ok t ∧ same t' t = true := by
  rcases h with h | ⟨q, rfl⟩
  · refine Or.inl ⟨h, ?_⟩
    subst h
    exact (guardMark_yes b' s t rs gs).1
      (VerifiableInference.Desc.guarded_under same hearsReply { marked b' name with place := a } s rs gs t hy)
  · refine Or.inr ⟨q, ?_⟩
    have hy1 := VerifiableInference.Desc.guarded_under same hearsReply
      { (marked b' name).andThen name (q.guarded same fun _ => false) with place := a } s rs gs t hy
    have hy' : ((ProofFile.guardMark b').decide s (rs.take b'.rounds.length) (gs.take b'.openings)).bind
        (fun s' => (q.guarded same fun _ => false).decide s' (rs.drop b'.rounds.length)
          (gs.drop b'.openings)) = .ok t := hy1
    cases hd : (ProofFile.guardMark b').decide s (rs.take b'.rounds.length) (gs.take b'.openings) with
    | error e =>
      rw [hd] at hy'
      cases hy'
    | ok u =>
      rw [hd] at hy'
      obtain ⟨h1, h2⟩ := (guardMark_yes b' s u _ _).1 hd
      obtain ⟨h3, h4⟩ := (VerifiableInference.Desc.guarded_yes same (fun _ => false) q rfl u _ _ t).1 hy'
      exact ⟨u, rfl, h1, h2, h3, h4⟩

end

/-- onlineDescription's guard's test, as an equation: the heard reply's one seat holds behind what it held in front. -/
theorem sameReply_eq {s t : S} (h : ProofFile.sameReply s t = true) : s.out.reply = t.out.reply := by
  unfold ProofFile.sameReply at h
  exact eq_of_beq h

end IM

#print axioms IM.step_alone
#print axioms IM.sameReply_eq
#print axioms IM.yes_alone
#print axioms IM.yes_alone_K7
#print axioms IM.claim_yes
#print axioms IM.after_yes
#print axioms IM.yes_laid
