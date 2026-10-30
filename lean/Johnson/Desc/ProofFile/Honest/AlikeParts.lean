-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AlikeParts.lean: from two lists of moves to the relation `AlikeTo`
(Honest/Alike.lean) between the rounds of two parts that differ in their moves alone, and in the
type of the value that these pass on. Definitions, and lemmas with their proofs.

  1  `tellBy`, `hearBy`, `tell_by`, `hear_by`   `Step.tell` and `Step.hear` at a round that has a
     move, written as functions of the stops' answer and of what the move says
  2  `Step.Twin`, `cons_twin`   two rounds that differ in their moves alone
  3  `MovesTo`   the relation between two lists of moves: move by move they say the same, from two
     states; after the last move `Post` holds of the two states
  4  `Part.reMove`, `stepsFrom`, `steps_from`, `stepsFrom_alike`, `stepsFrom_faced`, `steps_alike`,
     `steps_faced`   a part with other moves; its rounds are related to the part's own
  5  `lift_movesTo`   one part placed in two wider states by `Part.lift`

Why `Part.reMove`. A part's moves are typed at the part's own counts of coins. That two arbitrary
parts are given the same coins would be an equation between types. `p.reMove mvs` has the counts,
stops and stated shares of `p` by construction, so both are given one type of coins.

Limits.
  * One part's rounds. A chain's rounds are joined by `AlikeTo.append`.
  * `MovesTo` asks that the two moves say the same whatever was shown in the rounds since the first
    move, and at every value of the columns opened (`Seen.opened`): more than a play needs. `MidBy`
    and the premise hs ask the same rounds shown and the same columns opened (`Mid.shown`).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Alike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Oracle OpenedColumn)

variable {V V' W W' X X' Y C : Type}

/-! ## 1 A round that has a move -/

/-- `Step.tell` at a round that has a move. `g`: the stops' answer. `r`: what the move says. -/
def tellBy (g : Option Refusal) (nm : String) (dcl : Fmt.DeclaredRound) (os : List Oracle)
    (r : Except String Sending) : Except Refusal Told :=
  match g with
  | some e => .error e
  | none =>
    match r with
    | .error e => .error ⟨.unfit, nm ++ ": " ++ e⟩
    | .ok x =>
      if !x.fits dcl os then
        .error ⟨.unfit, nm ++ ": the message has another shape than the sub-protocol states"⟩
      else .ok ⟨x.vals.map Said.got, x.tables.map some, true⟩

/-- `Step.hear` at a round that has a move. `g`: the stops' answer. `m₁`: the next state. -/
def hearBy (g : Option Refusal) (m₁ : Mid W X) : Except Refusal (Mid W X) :=
  match g with
  | some e => .error e
  | none => .ok m₁

theorem tell_by (s : Step W X) (mv : Move Unit W X) (hm : s.move = some mv) (back : Option Fmt.RoundView)
    (m : Mid W X) :
    s.tell back m =
      tellBy (s.stop m.loc s.nth) s.name s.decl s.oracles (mv.say () m.shown m.st) := by
  cases s with
  | mk name addr decl oracles bad hid nth last move =>
    have e : move = some mv := hm
    subst e
    rfl

theorem hear_by (s : Step W X) (mv : Move Unit W X) (hm : s.move = some mv) (x : Told)
    (d : Fmt.Drawn) (m : Mid W X) :
    s.hear x d m =
      hearBy (if s.last then s.stop (m.loc ++ [d]) (s.nth + 1) else none)
        ⟨{ m.st.hears d with own := mv.hand (m.st.hears d) }, m.loc ++ [d],
          m.seen ++ [⟨x.vals, d⟩], m.opened⟩ := by
  cases s with
  | mk name addr decl oracles bad hid nth last move =>
    have e : move = some mv := hm
    subst e
    rfl

/-! ## 2 Two rounds that differ in their moves alone -/

structure Step.Twin (s : Step W X) (s' : Step W X') : Prop where
  name : s.name = s'.name
  addr : s.addr = s'.addr
  decl : s.decl = s'.decl
  oracles : s.oracles = s'.oracles
  bad : s.bad = s'.bad
  hid : s.hid = s'.hid
  nth : s.nth = s'.nth
  last : s.last = s'.last

theorem Step.Twin.faced {s : Step W X} {s' : Step W X'} (h : s.Twin s') : s.Faced s' :=
  ⟨h.name, h.addr, h.decl, h.oracles⟩

theorem Step.Twin.stop {s : Step W X} {s' : Step W X'} (h : s.Twin s') (l : List Fmt.Drawn)
    (n : Nat) : s.stop l n = s'.stop l n := by
  unfold Step.stop
  rw [h.bad, h.hid, h.name]

/-- **One round of each, before two lists**: where the two moves say the same, the relation holds of
the longer lists, if it holds of the two lists from the next states, whatever the challenge is,
whatever was shown, and whatever columns are read before the next round. -/
theorem cons_twin {Post : Mid W X → Mid W X' → Prop} {s : Step W X} {s' : Step W X'}
    (ss : List (Step W X)) (ss' : List (Step W X')) (h : s.Twin s') {mv : Move Unit W X}
    {mv' : Move Unit W X'} (hm : s.move = some mv) (hm' : s'.move = some mv') (m : Mid W X)
    (m' : Mid W X') (hl : m.loc = m'.loc)
    (hsay : mv.say () m.shown m.st = mv'.say () m'.shown m'.st)
    (hP : ∀ (d : Fmt.Drawn) (e : Fmt.RoundView), TookAll (AlikeTo Post ss ss')
      ⟨{ m.st.hears d with own := mv.hand (m.st.hears d) }, m.loc ++ [d], m.seen ++ [e], m.opened⟩
      ⟨{ m'.st.hears d with own := mv'.hand (m'.st.hears d) }, m'.loc ++ [d], m'.seen ++ [e],
        m'.opened⟩) :
    AlikeTo Post (s :: ss) (s' :: ss') m m' := by
  show ∀ back, AnsAlike _ (s.tell back m) (s'.tell back m')
  intro back
  have eT : s'.tell back m' = s.tell back m := by
    rw [tell_by s' mv' hm', tell_by s mv hm, ← hsay, ← h.stop, ← hl, ← h.nth, ← h.name, ← h.decl,
      ← h.oracles]
  rw [eT]
  cases s.tell back m with
  | error e => exact rfl
  | ok x =>
    refine ⟨rfl, fun d => ?_⟩
    have eG : (if s'.last then s'.stop (m'.loc ++ [d]) (s'.nth + 1) else none) =
        (if s.last then s.stop (m.loc ++ [d]) (s.nth + 1) else none) := by
      rw [← h.stop, ← hl, ← h.nth, ← h.last]
    rw [hear_by s mv hm, hear_by s' mv' hm', eG]
    generalize (if s.last then s.stop (m.loc ++ [d]) (s.nth + 1) else none) = g
    cases g with
    | some e => exact rfl
    | none => exact hP d _

/-! ## 3 Two lists of moves -/

/-- **Move by move the two lists say the same**, at the coins `c`, from the states `t` and `t'`, at
the rounds shown, `seen`, at every value `o` of the columns opened, reached or not; for moves that
do not read them this is the old clause; then from the two next states, whatever the round's
challenge is and whatever is shown of the round. After the last move `Post` holds of the two
states. -/
def MovesTo (c : C) (Post : State W X → State W X' → Prop) :
    List (Move C W X) → List (Move C W X') → State W X → State W X' → List Fmt.RoundView → Prop
  | [], [], t, t', _ => Post t t'
  | mv :: mvs, mv' :: mvs', t, t', seen =>
    (∀ o, mv.say c ⟨seen, o⟩ t = mv'.say c ⟨seen, o⟩ t') ∧
      ∀ d e, MovesTo c Post mvs mvs' { t.hears d with own := mv.hand (t.hears d) }
        { t'.hears d with own := mv'.hand (t'.hears d) } (seen ++ [e])
  | _, _, _, _, _ => False

/-! ## 4 A part with other moves -/

/-- **The part with other moves**, which may pass on another type of value. Its counts of coins, its
stops and its stated shares are the part's. -/
def Part.reMove (p : Part V W X) (mvs : List (Move p.Coins W X')) : Part V W X' :=
  { takes := p.takes, spends := p.spends, carries := p.carries, bad := p.bad, hid := p.hid
    badShare := p.badShare, hidShare := p.hidShare, moves := mvs }

/-- A part's rounds from round number `n` on. `len`: how many moves the part has. -/
def stepsFrom (nm : String) (a : Addr) (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String)
    (len : Nat) (c : C) :
    List (Fmt.DeclaredRound × List Oracle) → List (Move C W X) → Nat → List (Step W X)
  | r :: rs, mv :: mvs, n =>
    ⟨nm, a, r.1, r.2, bad, hid, n, n + 1 == len, some ⟨fun _ => mv.say c, mv.hand⟩⟩ ::
      stepsFrom nm a bad hid len c rs mvs (n + 1)
  | _, _, _ => []

theorem stepsFrom_eq (nm : String) (a : Addr)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (len : Nat) (c : C) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (mvs : List (Move C W X)) (n : Nat),
      ((rs.zip mvs).zipIdx n).map (fun r =>
        (⟨nm, a, r.1.1.1, r.1.1.2, bad, hid, r.2, r.2 + 1 == len,
          some ⟨fun _ => r.1.2.say c, r.1.2.hand⟩⟩ : Step W X)) =
        stepsFrom nm a bad hid len c rs mvs n
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: rs, _ :: mvs, n => congrArg (List.cons _) (stepsFrom_eq nm a bad hid len c rs mvs (n + 1))

theorem steps_from (p : Part V W X) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    p.steps nm a rs v c =
      stepsFrom nm a p.bad (fun f o => v.bind fun w => p.hid w f o) p.moves.length c rs p.moves 0 :=
  stepsFrom_eq nm a p.bad (fun f o => v.bind fun w => p.hid w f o) p.moves.length c rs p.moves 0

/-- Two states of a run that differ at most in the prover's carried state. -/
def MidBy (Post : State W X → State W X' → Prop) (a : Mid W X) (b : Mid W X') : Prop :=
  a.loc = b.loc ∧ a.shown = b.shown ∧ Post a.st b.st

theorem stepsFrom_alike (nm : String) (a : Addr)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (len : Nat) (c : C)
    (Post : State W X → State W X' → Prop) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (mvs : List (Move C W X))
      (mvs' : List (Move C W X')) (n : Nat) (m : Mid W X) (m' : Mid W X'),
      rs.length = mvs.length → m.loc = m'.loc → m.shown = m'.shown →
      MovesTo c Post mvs mvs' m.st m'.st m.seen →
      AlikeTo (MidBy Post) (stepsFrom nm a bad hid len c rs mvs n)
        (stepsFrom nm a bad hid len c rs mvs' n) m m'
  | [], [], [], _, _, _, _, hl, hs, q => ⟨hl, hs, q⟩
  | [], [], _ :: _, _, _, _, _, _, _, q => False.elim q
  | [], _ :: _, _, _, _, _, hn, _, _, _ => (Nat.succ_ne_zero _ hn.symm).elim
  | _ :: _, [], _, _, _, _, hn, _, _, _ => (Nat.succ_ne_zero _ hn).elim
  | _ :: _, _ :: _, [], _, _, _, _, _, _, q => False.elim q
  | r :: rs, mv :: mvs, mv' :: mvs', n, m, m', hn, hl, hs, q =>
    cons_twin (X := X) (X' := X') (Post := MidBy Post)
      (s := ⟨nm, a, r.1, r.2, bad, hid, n, n + 1 == len, some ⟨fun _ => mv.say c, mv.hand⟩⟩)
      (s' := ⟨nm, a, r.1, r.2, bad, hid, n, n + 1 == len, some ⟨fun _ => mv'.say c, mv'.hand⟩⟩)
      (stepsFrom nm a bad hid len c rs mvs (n + 1)) (stepsFrom nm a bad hid len c rs mvs' (n + 1))
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl m m' hl
      (by rw [← hs]; exact q.1 m.opened)
      (fun d e cols => stepsFrom_alike nm a bad hid len c Post rs mvs mvs' (n + 1) _ _
        (Nat.succ.inj hn) (congrArg (· ++ [d]) hl)
        (congrArg (fun s : Seen => (⟨s.rounds ++ [e], s.opened.map (· ++ cols)⟩ : Seen)) hs)
        (q.2 d e))

theorem stepsFrom_faced (nm : String) (a : Addr)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (len : Nat) (c : C) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (mvs : List (Move C W X))
      (mvs' : List (Move C W X')) (n : Nat), mvs.length = mvs'.length →
      FacedAll (stepsFrom nm a bad hid len c rs mvs n) (stepsFrom nm a bad hid len c rs mvs' n)
  | [], _, _, _, _ => True.intro
  | _ :: _, [], [], _, _ => True.intro
  | _ :: _, [], _ :: _, _, hn => (Nat.succ_ne_zero _ hn.symm).elim
  | _ :: _, _ :: _, [], _, hn => (Nat.succ_ne_zero _ hn).elim
  | _ :: rs, _ :: mvs, _ :: mvs', n, hn =>
    ⟨⟨rfl, rfl, rfl, rfl⟩, stepsFrom_faced nm a bad hid len c rs mvs mvs' (n + 1) (Nat.succ.inj hn)⟩

/-- **The rounds of a part and of the part with other moves are related**, where the two lists of
moves are. -/
theorem steps_alike (p : Part V W X) (mvs' : List (Move p.Coins W X')) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins)
    (Post : State W X → State W X' → Prop) (m : Mid W X) (m' : Mid W X')
    (hn : mvs'.length = p.moves.length) (hr : rs.length = p.moves.length) (hl : m.loc = m'.loc)
    (hs : m.shown = m'.shown) (q : MovesTo c Post p.moves mvs' m.st m'.st m.seen) :
    AlikeTo (MidBy Post) (p.steps nm a rs v c) ((p.reMove mvs').steps nm a rs v c) m m' := by
  rw [steps_from, steps_from]
  show AlikeTo (MidBy Post) _
    (stepsFrom nm a p.bad (fun f o => v.bind fun w => p.hid w f o) mvs'.length c rs mvs' 0) m m'
  rw [hn]
  exact stepsFrom_alike nm a p.bad _ p.moves.length c Post rs p.moves mvs' 0 m m' hr hl hs q

theorem steps_faced (p : Part V W X) (mvs' : List (Move p.Coins W X')) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins)
    (hn : mvs'.length = p.moves.length) :
    FacedAll (p.steps nm a rs v c) ((p.reMove mvs').steps nm a rs v c) := by
  rw [steps_from, steps_from]
  show FacedAll _
    (stepsFrom nm a p.bad (fun f o => v.bind fun w => p.hid w f o) mvs'.length c rs mvs' 0)
  rw [hn]
  exact stepsFrom_faced nm a p.bad _ p.moves.length c rs p.moves mvs' 0 hn.symm

/-! ## 5 One part in two wider states -/

/-- Two carried states with the same input and challenges, their passed-on values related. -/
def StateBy (r : X → X' → Prop) (a : State W X) (b : State W X') : Prop :=
  a.input = b.input ∧ a.heard = b.heard ∧ r a.own b.own

/-- **One list of moves, placed in two wider states**: related, where the two readers read the same
of related values and the two writers keep them related. -/
theorem lift_movesTo (wit : W → W') (get : X → Y) (set : X → Y → X) (get' : X' → Y)
    (set' : X' → Y → X') (r : X → X' → Prop) (hg : ∀ x x', r x x' → get x = get' x')
    (hr : ∀ x x' y, r x x' → r (set x y) (set' x' y)) (c : C) :
    ∀ (mvs : List (Move C W' Y)) (t : State W X) (t' : State W X') (seen : List Fmt.RoundView),
      StateBy r t t' →
      MovesTo c (StateBy r) (mvs.map (Move.lift wit get set)) (mvs.map (Move.lift wit get' set')) t
        t' seen
  | [], _, _, _, q => q
  | mv :: mvs, ⟨i, hd, x⟩, ⟨i', hd', x'⟩, seen, q => by
    obtain ⟨q1, q2, q3⟩ := q
    have e1 : i = i' := q1
    have e2 : hd = hd' := q2
    have e3 : r x x' := q3
    subst e1 e2
    have eg : get x = get' x' := hg x x' e3
    refine ⟨fun o => ?_, fun d e => ?_⟩
    · show mv.say c ⟨seen, o⟩ ⟨wit i, hd, get x⟩ = mv.say c ⟨seen, o⟩ ⟨wit i, hd, get' x'⟩
      rw [eg]
    · refine lift_movesTo wit get set get' set' r hg hr c mvs _ _ _ ⟨rfl, rfl, ?_⟩
      show r (set x (mv.hand ⟨wit i, hd ++ [d], get x⟩))
        (set' x' (mv.hand ⟨wit i, hd ++ [d], get' x'⟩))
      rw [eg]
      exact hr x x' _ e3

end ProofFile.Honest

#print axioms ProofFile.Honest.tell_by
#print axioms ProofFile.Honest.hear_by
#print axioms ProofFile.Honest.cons_twin
#print axioms ProofFile.Honest.steps_from
#print axioms ProofFile.Honest.steps_alike
#print axioms ProofFile.Honest.steps_faced
#print axioms ProofFile.Honest.lift_movesTo
#print axioms ProofFile.Honest.Step.Twin.faced
#print axioms ProofFile.Honest.Step.Twin.stop
#print axioms ProofFile.Honest.stepsFrom_eq
#print axioms ProofFile.Honest.stepsFrom_alike
#print axioms ProofFile.Honest.stepsFrom_faced
#print axioms ProofFile.Honest.tellBy
#print axioms ProofFile.Honest.hearBy
#print axioms ProofFile.Honest.Step.Twin
#print axioms ProofFile.Honest.MovesTo
#print axioms ProofFile.Honest.Part.reMove
#print axioms ProofFile.Honest.stepsFrom
#print axioms ProofFile.Honest.MidBy
#print axioms ProofFile.Honest.StateBy
