-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/Laws.lean: the kind «the code switch»: WHAT A YES OF ITS OWN decide MEANS, AS
FAR AS THAT HANGS ON NO LETTER OF THE TYPED WORLD: THEOREMS ABOUT K2C/Kind.lean's TEXT ITSELF, AT
EVERY RECORD, EVERY ROUNDS, EVERY
COLUMNS AND EVERY SENDING snd. No Mathlib. No soundness is claimed: these are small parts of the
kind's law («two rounds» · «the rounds' numbers» · one bound) and a premise that a law on a switch
needs (each drawn position below the range).
  Two            a yes ⇒ the stretch has just two rounds
  InRange        a yes ⇒ every position that round 2 drew lies below 2 ^ logN
  NothingWaits   a yes ⇒ nothing was owed in front of the block (S.noneWaits), and nothing is owed
  behind it (rowsOwed = none)
  Stands         a yes ⇒ the record stood at the sort of place at which the block stands
  Groups         a yes ⇒ there was a group of columns for each tree that is read
  Keeps          a yes ⇒ the mark of a failed test, what goes out, and the request's public words
  are as they were
  roundsAre      the block's declared rounds are «SEND seed», then «LOC», with the place's numbers
  planBounds     planOk ⇒ at least one position; as many sent trees as roots; the trees that are
  read stand in increasing order; logN ≤ 32: ALL FOUR CLAUSES
  beforeIsRead   «before» names just the trees that the block opens, in their order
EACH STATEMENT IS A CLOSED Prop BY NAME, WITH A THEOREM OF JUST THAT TYPE. THE FIRST SIX ARE
PROPERTIES OF ANY decide OF THE KIND's TYPE (‹·›Of), AND ARE TRIED IN THIS FILE AGAINST TWO SILLY
MEMBERS, BY THEOREMS: yesAll (says yes to all, turns nothing) FAILS TwoOf · InRangeOf ·
NothingWaitsOf · StandsOf · GroupsOf (it meets KeepsOf: a frame condition, rightly); of noAll (says
no to all) all six hold emptily (noAll_all): THEY ARE NECESSARY CONDITIONS OF A YES, NOT THE LAW.

-/
import Johnson.Top.H0.Tw.K2C.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)

theorem bindOk {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b)
    :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ### the body's forms -/

theorem switchE_settled {behind P send} {s : _root_.Tw.K2.S9} {x rS rL cols r}
    (h : _root_.Tw.K2.switchE behind P send s x rS rL cols = .ok r) : s.settled = true := by
  cases hs : s.settled with
  | true => rfl
  | false =>
    unfold _root_.Tw.K2.switchE at h
    simp [hs] at h
    cases h

theorem firstEW_two {behind P send s rounds cols r}
    (h : _root_.Tw.K2.firstEW behind P send s rounds cols = .ok r) : rounds.length = 2 := by
  unfold _root_.Tw.K2.firstEW at h
  split at h
  · rfl
  · cases h

theorem firstEW_settled {behind P send} {s : _root_.Tw.K2.S9} {rounds cols r}
    (h : _root_.Tw.K2.firstEW behind P send s rounds cols = .ok r) : s.settled = true := by
  unfold _root_.Tw.K2.firstEW at h
  split at h
  · obtain ⟨x, _, h⟩ := bindOk h
    dsimp only at h
    split at h
    · cases h
    · obtain ⟨_, _, h⟩ := bindOk h
      obtain ⟨w, hw, _⟩ := bindOk h
      exact switchE_settled hw
  · cases h

theorem switchAloneEW_two {behind P send s x rounds cols r}
    (h : _root_.Tw.K2.switchAloneEW behind P send s x rounds cols = .ok r) : rounds.length = 2 := by
  unfold _root_.Tw.K2.switchAloneEW at h
  split at h
  · rfl
  · cases h

theorem switchAloneEW_settled {behind P send} {s : _root_.Tw.K2.S9S} {x rounds cols r}
    (h : _root_.Tw.K2.switchAloneEW behind P send s x rounds cols = .ok r) : s.settled = true := by
  unfold _root_.Tw.K2.switchAloneEW at h
  split at h
  · obtain ⟨w, hw, _⟩ := bindOk h
    exact switchE_settled hw
  · cases h

theorem chainFirstEW_both {behind P send} {s : _root_.Tw.K2.S9C} {rounds cols r}
    (h : _root_.Tw.K2.chainFirstEW behind P send s rounds cols = .ok r) : rounds.length = 2 ∧
        s.settled = true := by
  unfold _root_.Tw.K2.chainFirstEW at h
  split at h
  · cases h
  · obtain ⟨t, ht, _⟩ := bindOk h
    exact ⟨firstEW_two ht, firstEW_settled ht⟩

theorem headSwitchEW_both {behind P send} {s : _root_.Tw.K2.S9S} {f0 fr rounds cols r}
    (h : _root_.Tw.K2.headSwitchEW behind P send s f0 fr rounds cols = .ok r) : rounds.length = 2 ∧
        s.settled = true := by
  unfold _root_.Tw.K2.headSwitchEW at h
  split at h
  · cases h
  · exact ⟨switchAloneEW_two h, switchAloneEW_settled h⟩

theorem finishSwitchEW_both {behind P send} {s : _root_.Tw.K2.S9S} {fr T rounds cols r}
    (h : _root_.Tw.K2.finishSwitchEW behind P send s fr T rounds cols = .ok r) : rounds.length = 2 ∧
        s.settled = true :=
  ⟨switchAloneEW_two h, switchAloneEW_settled h⟩

theorem allTaken_groups {p : P2} {gs left} (h : allTaken p gs left = .ok ()) : gs.length =
    p.read.length := by
  unfold allTaken at h
  split at h
  · rename_i c
    simp at c
    exact c.2
  · cases h

/-! ### decide -/

/-- All that a yes of decide says here, in one. -/
structure Yes (p : P2) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (s' : S) :
    Prop where
  inRange : inRange p rs = true
  two : rs.length = 2
  waits : s.noneWaits = true
  owes : s'.rowsOwed = none
  stands : (p.stands = .link ∧ s.here = .between) ∨ (p.stands = .head ∧ ∃ a,
      s.here = .head a) ∨ (p.stands = .finish ∧ ∃ a, s.here = .fin a)
  groups : gs.length = p.read.length
  keeps : s'.failed = s.failed ∧ s'.out = s.out ∧ s'.req = s.req

theorem decideWith_yes {snd p s rs gs s'} (h : decideWith snd p s rs gs = .ok s') : Yes p s rs gs
    s' := by
  unfold decideWith at h
  simp only at h
  split at h
  · cases h
  · rename_i hr
    have hr' : inRange p rs = true := by simpa using hr
    split at h
    · obtain ⟨x, hx, h⟩ := bindOk h
      obtain ⟨_, ha, h⟩ := bindOk h
      obtain ⟨_, _, h⟩ := bindOk h
      cases h
      have := chainFirstEW_both hx
      exact ⟨hr', this.1, this.2, rfl, .inl ⟨by assumption, by
          assumption⟩, allTaken_groups ha, rfl, rfl, rfl⟩
    · obtain ⟨_, _, h⟩ := bindOk h
      obtain ⟨x, hx, h⟩ := bindOk h
      obtain ⟨_, ha, h⟩ := bindOk h
      cases h
      have := headSwitchEW_both hx
      exact ⟨hr', this.1, this.2, rfl, .inr (.inl ⟨by assumption, _, by
          assumption⟩), allTaken_groups ha, rfl, rfl, rfl⟩
    · obtain ⟨_, _, h⟩ := bindOk h
      obtain ⟨_, _, h⟩ := bindOk h
      obtain ⟨x, hx, h⟩ := bindOk h
      obtain ⟨_, ha, h⟩ := bindOk h
      cases h
      have := finishSwitchEW_both hx
      exact ⟨hr', this.1, this.2, rfl, .inr (.inr ⟨by assumption, _, by
          assumption⟩), allTaken_groups ha, rfl, rfl, rfl⟩
    · cases h

/-! ### the statements: each a property of ANY decide of the kind's type; then, closed, of the
kind's own at every sending -/

/-- The type of the kind's decide at a place's numbers. -/
abbrev Dec : Type := P2 → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Except String S

def TwoOf (d : Dec) : Prop := ∀ p s rs gs s', d p s rs gs = .ok s' → rs.length = 2
def InRangeOf (d : Dec) : Prop :=
    ∀ p s r₁ r₂ gs s', d p s [r₁, r₂] gs = .ok s' → ∀ x ∈ r₂.drawn.poss, x < 2 ^ p.logN
def NothingWaitsOf (d : Dec) : Prop :=
    ∀ p s rs gs s', d p s rs gs = .ok s' → s.noneWaits = true ∧ s'.rowsOwed = none
def StandsOf (d : Dec) : Prop := ∀ p s rs gs s', d p s rs gs = .ok s' →
  (p.stands = .link ∧ s.here = .between) ∨ (p.stands = .head ∧ ∃ a,
      s.here = .head a) ∨ (p.stands = .finish ∧ ∃ a, s.here = .fin a)
def GroupsOf (d : Dec) : Prop := ∀ p s rs gs s', d p s rs gs = .ok s' → gs.length = p.read.length
def KeepsOf (d : Dec) : Prop :=
    ∀ p s rs gs s', d p s rs gs = .ok s' → s'.failed = s.failed ∧ s'.out = s.out ∧ s'.req = s.req

def Two : Prop := ∀ snd, TwoOf (decideWith snd)
theorem two : Two := fun _ _ _ _ _ _ h => (decideWith_yes h).two

def InRange : Prop := ∀ snd, InRangeOf (decideWith snd)
theorem inRangeOfYes : InRange := fun _ p _ r₁ r₂ _ _ h x hx => by
  have := (decideWith_yes h).inRange
  simp [inRange] at this
  exact this x hx

def NothingWaits : Prop := ∀ snd, NothingWaitsOf (decideWith snd)
theorem nothingWaits : NothingWaits := fun _ _ _ _ _ _ h =>
    ⟨(decideWith_yes h).waits, (decideWith_yes h).owes⟩

def Stands : Prop := ∀ snd, StandsOf (decideWith snd)
theorem stands : Stands := fun _ _ _ _ _ _ h => (decideWith_yes h).stands

def Groups : Prop := ∀ snd, GroupsOf (decideWith snd)
theorem groups : Groups := fun _ _ _ _ _ _ h => (decideWith_yes h).groups

def Keeps : Prop := ∀ snd, KeepsOf (decideWith snd)
theorem keeps : Keeps := fun _ _ _ _ _ _ h => (decideWith_yes h).keeps

def RoundsAre : Prop := ∀ (p : P2), ((codeSwitchKind p : Block S Unit).rounds.map fun r =>
    (r.entry.name, r.entry.drawE, r.entry.drawNZ, r.entry.answers, r.entry.poss, r.entry.logN,
        r.entry.trits, r.entry.roots, r.entry.rows)) =
  [("SEND seed", p.seeds, p.nonZero, 0, 0, 0, 0, p.roots, 0), ("LOC", 0, 0, p.answers, p.positions,
      p.logN, 0, 0, 0)]
theorem roundsAre : RoundsAre := fun _ => rfl

/-- The two declared entries WHOLE, every field: the bits of proof of work and the message's bytes
among them (RoundsAre names nine fields and leaves these two and «count» out). -/
def EntriesAre : Prop := ∀ (p : P2), ((codeSwitchKind p : Block S Unit).rounds.map (·.entry)) =
  [{ name := "SEND seed", work := p.work₁, msg := 32 * p.roots, roots := p.roots, drawE := p.seeds,
     drawNZ := p.nonZero },
   { name := "LOC", work := p.work₂, msg := 24 * p.answers, answers := p.answers,
     poss := p.positions, logN := p.logN }]
theorem entriesAre : EntriesAre := fun _ => rfl

def PlanBounds : Prop := ∀ (p : P2), (codeSwitchKind p : Block S Unit).planOk = true →
  0 < p.positions ∧ p.sent.length = p.roots ∧ increasing (p.read.map (·.1)) = true ∧ p.logN ≤ 32
theorem planBounds : PlanBounds := fun p h => by
  simp [codeSwitchKind] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

def BeforeIsRead : Prop := ∀ (p : P2), (codeSwitchKind p : Block S Unit).before = p.read.map (fun r =>
                (p.place.chain, r.1)) ∧
  ((codeSwitchKind p : Block S Unit).rounds.flatMap fun r => r.opens.map (·.2)) = p.read.map fun r => .own r.1
theorem beforeIsRead : BeforeIsRead := fun p => ⟨rfl, by simp [codeSwitchKind, rounds]⟩

/-! ### the two silly members (a statement that either of them meets in a way that it should not is
the wrong statement) -/

/-- Says yes to all and turns nothing. -/
def yesAll : Dec := fun _ s _ _ => .ok s
/-- Says no to all. -/
def noAll : Dec := fun _ _ _ _ => .error "no"

/-- Numbers of a made-up place: one tree is read; the range is 2 ^ 0. -/
def toyP : P2 :=
  { name := "", place := ⟨1, none, 1, .K2⟩, stands := .link, grp := 0, firstTree := 0, samples := 0,
    work₁ := 0, roots := 0, seeds := 0, nonZero := 0,
    work₂ := 0, answers := 0, positions := 1, logN := 0, sent := [], read := [(0, 0, 0)] }

theorem yesAll_not_two : ¬ TwoOf yesAll := fun h => by
  have := h toyP S.blank [] [] S.blank rfl
  cases this

theorem yesAll_not_inRange : ¬ InRangeOf yesAll := fun h => by
  have :=
      h toyP S.blank ⟨[], ⟨[], [], [], none⟩⟩ ⟨[], ⟨[], [1], [], none⟩⟩ [] S.blank rfl 1 (by simp)
  simp [toyP] at this

theorem yesAll_not_nothingWaits : ¬ NothingWaitsOf yesAll := fun h => by
  have := (h toyP { S.blank with rowsOwed := some 1 } [] [] _ rfl).2
  cases this

theorem yesAll_not_stands : ¬ StandsOf yesAll := fun h => by
  have := h toyP { S.blank with here := .mem { msg := #[], ids := #[], lin := none } } [] [] _ rfl
  simp [toyP] at this

theorem yesAll_not_groups : ¬ GroupsOf yesAll := fun h => by
  have := h toyP S.blank [] [] S.blank rfl
  simp [toyP] at this

/-- Of a decide that says no to all, all six hold emptily: THEY ARE NECESSARY CONDITIONS OF A YES,
NOT THE LAW. -/
theorem noAll_all : TwoOf noAll ∧ InRangeOf noAll ∧ NothingWaitsOf noAll ∧ StandsOf noAll ∧ GroupsOf
    noAll ∧ KeepsOf noAll :=
  ⟨fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ h =>
      (by cases h), fun _ _ _ _ _ h => (by cases h),
   fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.two
#print axioms VerifiableInference.Desc.First.K2.inRangeOfYes
#print axioms VerifiableInference.Desc.First.K2.nothingWaits
#print axioms VerifiableInference.Desc.First.K2.stands
#print axioms VerifiableInference.Desc.First.K2.groups
#print axioms VerifiableInference.Desc.First.K2.keeps
#print axioms VerifiableInference.Desc.First.K2.roundsAre
#print axioms VerifiableInference.Desc.First.K2.entriesAre
#print axioms VerifiableInference.Desc.First.K2.planBounds
#print axioms VerifiableInference.Desc.First.K2.beforeIsRead
#print axioms VerifiableInference.Desc.First.K2.yesAll_not_two
#print axioms VerifiableInference.Desc.First.K2.yesAll_not_inRange
#print axioms VerifiableInference.Desc.First.K2.yesAll_not_nothingWaits
#print axioms VerifiableInference.Desc.First.K2.yesAll_not_stands
#print axioms VerifiableInference.Desc.First.K2.yesAll_not_groups
#print axioms VerifiableInference.Desc.First.K2.noAll_all
