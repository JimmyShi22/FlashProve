-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndTakes.lean: which entries of the plan a routine of the verifier on bytes uses
up: a kit, and the law for the lookup's routine.

Definitions and theorems with their proofs. A context holds the plan's entries that are still to
come (`Chan.entries`, OnBytes/Iop/Ground.lean). Of the calls of a run one alone turns that list:
`Blk.close`, which takes the first entry off and fails unless its name is the name under which the
round is closed; it does so in a dry run and on a view alike. (By a search for "entries :=": beside
it only the making of a context at a run's start writes the field; no statement below rests on
this.) So of a routine one can say, as a list of names, which
entries it uses up, and the lists go along «x, then f» by ++. OnBytes/Tie/Pv/Req/Names.lean says the
same of the planner's routines (`Says x N`: x adds rounds with just the names N). Where both lists
are one term, the routine of the verifier uses up just as many entries as the planner's routine has
laid.

Main names:
  `TookN N c c'`: the entries of c are some entries with the names N, in this order, and then those
    of c'.
  `Takes x N`: wherever the routine x returns, `TookN N` holds from the context before to the
    context after. For blocks, routines of a sub-proof and routines of a link alike.
  `Takes.pure`, `bind`, `after`, `before`, `of_eq`, `lift`, `foldlM`; `Takes.must`, `Takes.get`:
    laws; `takes_of_leaves`: a routine that leaves the channel takes nothing.
  `takes_close`, `takes_closeAs`; `takes_read`, `takes_readSum`; `takes_answer`,
    `takes_answerNotZero`, `takes_empty`, `takes_point`: the calls on the channel.
  `pscNames`, `levelNames`, `forestNames`: the names of the rounds of a masked sumcheck, of a level
    of a product tree, and of a lookup, from the sizes that the planner takes.
  `takes_pscBegin`, `takes_roundIn`, `takes_roundsIn`, `takes_pscEnds`, `takes_levelIn`,
    `takes_tie`.
  `takes_pad`: `Forest.pad` uses up entries with the names `forestNames (forestSize h)`, h the
    lookup's shape.
  `TookN.drop`, `TookN.take`: the number of entries used up is the length of the list.

Limits: names alone: nothing on an entry's other fields. One direction: from a run that returns.


-/
import OnBytes.Model.RoundSizes
import OnBytes.Tie.Pv.Head.TailsSub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Used
open OnBytes OnBytes.Model OnBytes.L5
open OnBytes.Tie.Pv.Keeps.Cut (LeavesCh)
open OnBytes.Tie.Pv.HeadLink

/-- The entries of c are some entries with the names N and then those of c'. -/
def TookN (N : List String) (c c' : Ctx) : Prop :=
  ∃ es, c.ch.entries = es ++ c'.ch.entries ∧ es.map (·.name) = N

/-- Nothing is used up between a context and itself. -/
theorem TookN.refl (c : Ctx) : TookN [] c c := ⟨[], rfl, rfl⟩

/-- One stretch behind another. -/
theorem TookN.trans {N M : List String} {a b c : Ctx} (h : TookN N a b) (k : TookN M b c) :
    TookN (N ++ M) a c := by
  obtain ⟨es, e1, e2⟩ := h
  obtain ⟨fs, f1, f2⟩ := k
  exact ⟨es ++ fs, by rw [e1, f1, List.append_assoc], by rw [List.map_append, e2, f2]⟩

/-- What is left is what was there without the first entries, as many as there are names. -/
theorem TookN.drop {N : List String} {c c' : Ctx} (h : TookN N c c') :
    c'.ch.entries = c.ch.entries.drop N.length := by
  obtain ⟨es, e1, e2⟩ := h
  rw [e1, ← e2, List.length_map, List.drop_left]

/-- The entries that were used up have the names N. -/
theorem TookN.take {N : List String} {c c' : Ctx} (h : TookN N c c') :
    (c.ch.entries.take N.length).map (·.name) = N := by
  obtain ⟨es, e1, e2⟩ := h
  rw [e1, ← e2, List.length_map, List.take_left]

section Laws
variable {m : Type → Type} [Monad m] [HasRuns m] {α β σ : Type}

/-- Wherever the routine returns it has used up entries with just the names N, in this order. -/
def Takes (x : m α) (N : List String) : Prop :=
  ∀ s a s', Runs x s a s' → TookN N (HasRuns.ctx s) (HasRuns.ctx s')

/-- A value uses up nothing. -/
theorem Takes.pure (a : α) : Takes (pure a : m α) [] := fun s b s' h => by
  rw [(HasRuns.runs_pure h).2]
  exact TookN.refl _

/-- «x, then f». -/
theorem Takes.bind {x : m α} {f : α → m β} {N M : List String} (hx : Takes x N)
    (hf : ∀ a, Takes (f a) M) : Takes (x >>= f) (N ++ M) := fun s b s' h => by
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind h
  exact (hx s a s1 h1).trans (hf a s1 b s' h2)

/-- «x, then f», where f may use a fact on what x has returned. -/
theorem Takes.bindOn {x : m α} {f : α → m β} {N M : List String} {P : α → Prop} (hx : Takes x N)
    (hp : ∀ s a s', Runs x s a s' → P a) (hf : ∀ a, P a → Takes (f a) M) :
    Takes (x >>= f) (N ++ M) := fun s b s' h => by
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind h
  exact (hx s a s1 h1).trans (hf a (hp s a s1 h1) s1 b s' h2)

/-- «x, then f», where x takes nothing. -/
theorem Takes.after {x : m α} {f : α → m β} {N : List String} (hx : Takes x [])
    (hf : ∀ a, Takes (f a) N) : Takes (x >>= f) N := Takes.bind hx hf

/-- «x, then f», where f takes nothing. -/
theorem Takes.before {x : m α} {f : α → m β} {N : List String} (hx : Takes x N)
    (hf : ∀ a, Takes (f a) []) : Takes (x >>= f) N := by
  have h := Takes.bind hx hf
  rwa [List.append_nil] at h

/-- The list, written otherwise. -/
theorem Takes.of_eq {x : m α} {N M : List String} (h : Takes x N) (e : N = M) : Takes x M := e ▸ h

/-- A routine that leaves the channel takes nothing. -/
theorem takes_of_leaves {x : m α} (h : LeavesCh x) : Takes x [] := fun s a s' hr =>
  ⟨[], by rw [h s a s' hr]; rfl, rfl⟩

/-- A routine of the layer below. -/
theorem Takes.lift {x : m α} {N : List String} (hx : Takes x N) :
    Takes (StateT.lift x : StateT σ m α) N := fun s a s' h => hx s.2 a s'.2 (runs_lift h).1

/-- A fold over a list: the members' lists in a row. -/
theorem Takes.foldlM [LawfulMonad m] {γ : Type} {f : β → γ → m β} {g : γ → List String}
    (hf : ∀ b a, Takes (f b a) (g a)) : ∀ (l : List γ) (b : β), Takes (l.foldlM f b) (l.flatMap g)
  | [], b => by
    rw [List.foldlM_nil]
    exact Takes.pure b
  | a :: l, b => by
    rw [List.foldlM_cons, List.flatMap_cons]
    exact Takes.bind (hf b a) fun b1 => Takes.foldlM hf l b1

end Laws

/-! ## The calls on the channel -/

/-- The closing of a round takes the one entry of its name. -/
theorem takes_close (name : String) (kind : Fmt.Kind) (nz : Nat) :
    Takes (Blk.close name kind nz) [name] := fun c d c' h => by
  have h' : Blk.close name kind nz c = .ok (d, c') := h
  unfold Blk.close at h'
  cases he : c.ch.entries with
  | nil => rw [he] at h'; simp at h'
  | cons e es =>
    rw [he] at h'
    dsimp only at h'
    split at h'
    · cases h'
    · rename_i hn
      have hname : e.name = name := by
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or, not_not] at hn
        exact hn.1.1
      have hes : c'.ch.entries = es := by
        split at h'
        · cases h'
          rfl
        · split at h'
          · cases h'
          · split at h'
            · cases h'
              rfl
            · cases h'
      exact ⟨[e], by show c.ch.entries = [e] ++ c'.ch.entries; rw [he, hes]; rfl, by simp [hname]⟩

/-- An item of a message is taken: no entry is. -/
theorem takes_item (i : Fmt.Item) (dflt : Fmt.ItemValue) : Takes (Blk.item i dflt) [] :=
  fun c g c' h => by
    have h' : Blk.item i dflt c = .ok (g, c') := h
    unfold Blk.item at h'
    refine ⟨[], ?_, rfl⟩
    show c.ch.entries = c'.ch.entries
    split at h'
    · cases h'
      rfl
    · dsimp only at h'
      split at h'
      · cases h'
      · split at h'
        · cases h'
        · cases h'
          rfl

/-- A block that leaves the channel. -/
theorem takes_same {α : Type} (b : Blk α) [OnBytes.L5.Open.SameCh b] : Takes b [] :=
  takes_of_leaves (LeavesCh.same b)

/-- An element is received: no entry is taken. -/
theorem takes_recvE : Takes Blk.recvE [] := by
  unfold Blk.recvE
  refine Takes.after (takes_item _ _) fun g => ?_
  split
  · exact Takes.pure _
  · exact fun _ _ _ h => by cases h

/-- Receiving n elements uses up nothing. -/
theorem takes_trReadLoop : ∀ (n : Nat) (a : Array E), Takes (trReadLoop n a) []
  | 0, a => by
    unfold trReadLoop
    exact Takes.pure a
  | n + 1, a => by
    unfold trReadLoop
    exact Takes.after takes_recvE fun x => takes_trReadLoop n (a.push x)

/-- `SubM.read` takes nothing. -/
theorem takes_read (n : Nat) : Takes (SubM.read n) [] := Takes.lift (takes_trReadLoop n _)

/-- `SubM.readSum` takes nothing. -/
theorem takes_readSum : Takes SubM.readSum [] := Takes.lift takes_recvE

/-- A round is closed against the plan. -/
theorem takes_closeAs (name : String) (kind : Fmt.Kind) (elems notZero entries : Nat) :
    Takes (closeAs name kind elems notZero entries) [name] := by
  unfold closeAs
  refine Takes.after (takes_same _) fun _ => ?_
  refine Takes.before (takes_close _ _ _) fun _ => ?_
  refine Takes.after (fun c e c' h => ?_) fun _ => Takes.after (takes_same _) fun _ => Takes.pure _
  have h' : Blk.lastEntry c = .ok (e, c') := h
  unfold Blk.lastEntry at h'
  split at h'
  · cases h'
    exact TookN.refl _
  · cases h'

/-- One element out of what was drawn. -/
theorem takes_oneOf (d : Fmt.Drawn) : Takes (oneOf d) [] := by
  unfold oneOf
  split
  · exact Takes.pure _
  · exact fun _ _ _ h => by cases h

/-- A public condition under a name. -/
theorem takes_mustAs (n : String) (b : Bool) : Takes (Model.mustAs n b) [] :=
  takes_of_leaves (LeavesCh.mustAs n b)

/-- `SubM.answer` takes the entry of the round's name. -/
theorem takes_answer (r : RoundName) : Takes (SubM.answer r) [r.name] := by
  refine Takes.lift ?_
  unfold trAnswer noBatching
  exact Takes.after (takes_mustAs _ _) fun _ =>
    Takes.before (takes_closeAs _ _ _ _ _) fun _ => takes_oneOf _

/-- The same for an element that is drawn by the rule that never gives 0. -/
theorem takes_trAnswerNotZero (r : RoundName) : Takes (trAnswerNotZero r) [r.name] := by
  unfold trAnswerNotZero noBatching
  exact Takes.after (takes_mustAs _ _) fun _ =>
    Takes.before (takes_closeAs _ _ _ _ _) fun _ => takes_oneOf _

/-- `SubM.empty` takes the entry of the round's name. -/
theorem takes_empty (r : RoundName) : Takes (SubM.empty r) [r.name] := by
  refine Takes.lift ?_
  unfold trEmpty
  exact Takes.before (takes_closeAs _ _ _ _ _) fun _ => Takes.pure _

/-- `SubM.point` takes the entry of the round's name. -/
theorem takes_point (r : RoundName) (n : Nat) : Takes (SubM.point r n) [r.name] := by
  refine Takes.lift ?_
  unfold trPoint noBatching
  exact Takes.after (takes_mustAs _ _) fun _ =>
    Takes.before (takes_closeAs _ _ _ _ _) fun _ => Takes.pure _

/-- What a closing returns has as many elements as the entry that it has taken says. -/
theorem close_elems (name : String) (kind : Fmt.Kind) (nz : Nat) (c c' : Ctx) (d : Fmt.Drawn)
    (h : Blk.close name kind nz c = .ok (d, c')) :
    ∃ e, c'.ch.last = some e ∧ d.elems.length = e.drawE := by
  unfold Blk.close at h
  cases he : c.ch.entries with
  | nil => rw [he] at h; simp at h
  | cons e es =>
    rw [he] at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
        exact ⟨e, rfl, by simp [Blk.dryDrawn]⟩
      · split at h
        · cases h
        · split at h
          · rename_i hq
            simp only [Bool.and_eq_true, beq_iff_eq] at hq
            cases h
            exact ⟨e, rfl, hq.1.1.2⟩
          · cases h

/-- `SubM.point` returns as many elements as it asks for. -/
theorem point_size (r : RoundName) (n : Nat) (s : HasRuns.St SubM) (v : Array E)
    (s' : HasRuns.St SubM) (h : Runs (SubM.point r n) s v s') : v.size = n := by
  have h1 : Runs (trPoint r n) s.2 v s'.2 := (runs_lift (σ := Fork) h).1
  unfold trPoint closeAs at h1
  obtain ⟨_, c1, -, h2⟩ := HasRuns.runs_bind (m := Blk) h1
  obtain ⟨d, c2, h3, h4⟩ := HasRuns.runs_bind (m := Blk) h2
  obtain ⟨ev, -⟩ := HasRuns.runs_pure (m := Blk) h4
  obtain ⟨_, c3, -, h5⟩ := HasRuns.runs_bind (m := Blk) h3
  obtain ⟨d1, c4, h6, h7⟩ := HasRuns.runs_bind (m := Blk) h5
  obtain ⟨e, hl, hn⟩ := close_elems _ _ _ _ _ _ h6
  obtain ⟨e', c5, h8, h9⟩ := HasRuns.runs_bind (m := Blk) h7
  have h8' : Blk.lastEntry c4 = .ok (e', c5) := h8
  unfold Blk.lastEntry at h8'
  rw [hl] at h8'
  obtain ⟨rfl, rfl⟩ : e = e' ∧ c4 = c5 := by simpa using h8'
  obtain ⟨_, c6, h10, h11⟩ := HasRuns.runs_bind (m := Blk) h9
  obtain ⟨ed, -⟩ := HasRuns.runs_pure (m := Blk) h11
  have hm : (e.drawE == n && e.trits == 0 && e.poss == 0) = true :=
    ((PscRun.mustB_ok _ _ _ _).1 h10).1
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  rw [ev, ed]
  simp [hn, hm.1.1]

/-- A public condition, then f: f may use it. -/
theorem Takes.must {β : Type} {b : Bool} {f : Unit → SubM β} {N : List String}
    (hf : b = true → Takes (f ()) N) : Takes (SubM.must b >>= f) N := fun s a s' h => by
  obtain ⟨u, s1, h1, h2⟩ := HasRuns.runs_bind h
  have h1' : SubM.must b s.1 s.2 = .ok ((u, s1.1), s1.2) := h1
  obtain ⟨hb, e⟩ := (PscRun.must_ok b s.1 s.2 _).1 h1'
  have e1 : s1 = s := Prod.ext (congrArg (fun z : (Unit × Fork) × Ctx => z.1.2) e)
    (congrArg (fun z : (Unit × Fork) × Ctx => z.2) e)
  rw [e1] at h2
  exact hf hb s a s' h2

/-- A value that must be there, then f: f may use what it is. -/
theorem Takes.get {α β : Type} {x : Option α} {f : α → SubM β} {N : List String}
    (hf : ∀ a, x = some a → Takes (f a) N) : Takes (SubM.get x >>= f) N := fun s b s' h => by
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind h
  unfold SubM.get at h1
  obtain ⟨k1, eF⟩ := runs_lift (σ := Fork) h1
  obtain ⟨hx, eC⟩ := runs_blkGet k1
  have e1 : s1 = s := Prod.ext eF eC
  rw [e1] at h2
  exact hf a hx s b s' h2

/-- Proves that a routine which leaves the channel takes nothing. -/
macro "calm" : tactic => `(tactic| exact takes_of_leaves (by leavesW))

/-! ## Masked sumchecks -/

/-- The names of the rounds of a masked sumcheck. -/
def pscNames (rounds : Nat) (withY : Bool) : List String :=
  "PSC epsilon" :: (List.replicate rounds "PSC round" ++
    (if withY = true then ["PSC Y", "PSC values"] else []))

/-- The names of the rounds of a level of a product tree. -/
def levelNames (mu : Nat) : List String := pscNames mu true ++ ["LINE"]

/-- The names of the rounds that tie the roots of a lookup's two sides: 31 sumchecks without a
variable. -/
def tieNames : List String := (List.range 31).flatMap fun _ => pscNames 0 true

/-- The names of the rounds of a lookup, from the sizes that the planner takes: the shift, if there
is one, and the challenge; the tie and its point; the levels of the keys' tree; those of the
table's; the sumcheck on the leaves; a point; the sumcheck on the bits. -/
def forestNames (z : Params.ForestSize) : List String :=
  ((if z.shifted = true then ["LKP shift"] else []) ++ ["LKP"]) ++ ((tieNames ++ ["JOIN"]) ++
    ((List.range z.v).flatMap levelNames ++
      ((List.range z.d).flatMap (fun l => levelNames (5 + l)) ++
      (["PSC epsilon"] ++ (List.replicate (5 + z.d) "PSC round" ++ (["ZERO"] ++ (["PSC epsilon"] ++
        (List.replicate (5 + z.d) "PSC round" ++ ["PSC Y", "PSC values"]))))))))

/-- `pscBeginAt` uses up entries with just the names of the statement, in this order. -/
theorem takes_pscBeginAt (target : E) : Takes (pscBeginAt target) ["PSC epsilon"] := by
  unfold pscBeginAt
  exact Takes.after (by calm) fun _ => Takes.after takes_readSum fun _ =>
    Takes.before (takes_answer .pscEpsilon) fun _ => Takes.pure _

/-- `pscBegin` uses up entries with just the names of the statement, in this order. -/
theorem takes_pscBegin (C : Aff) : Takes (pscBegin C) ["PSC epsilon"] := by
  unfold pscBegin
  exact Takes.after (by calm) fun _ => Takes.before (takes_pscBeginAt _) fun _ => Takes.pure _

/-- A round of a masked sumcheck takes what its draw takes. -/
theorem takes_pscRound (p : Psc) (w : OnBytes.Psc.Weight) {draw : Blk E} {N : List String}
    (hd : Takes draw N) : Takes (pscRound p w draw) N := by
  unfold pscRound
  exact Takes.after (by calm) fun _ => Takes.after (takes_read _) fun _ =>
    Takes.after (by calm) fun _ => Takes.before (Takes.lift hd) fun _ =>
      Takes.after (by calm) fun _ => Takes.pure _

/-- `roundDraw` uses up entries with just the names of the statement, in this order. -/
theorem takes_roundDraw : Takes roundDraw ["PSC round"] := by
  unfold roundDraw trAnswer noBatching
  exact Takes.after (takes_mustAs _ _) fun _ =>
    Takes.before (takes_closeAs _ _ _ _ _) fun _ => takes_oneOf _

/-- `roundIn` uses up entries with just the names of the statement, in this order. -/
theorem takes_roundIn (form : RoundForm) (p : Psc) (z : E) (degree : Nat) :
    Takes (roundIn form p z degree) ["PSC round"] := by
  unfold roundIn
  exact Takes.after (by calm) fun _ => Takes.after (by calm) fun _ =>
    takes_pscRound _ _ takes_roundDraw

/-- `pscEnds` uses up entries with just the names of the statement, in this order. -/
theorem takes_pscEnds (p : Psc) (degreeInY n : Nat) :
    Takes (pscEnds p degreeInY n) ["PSC Y", "PSC values"] := by
  unfold pscEnds
  refine Takes.after (by calm) fun _ => ?_
  refine Takes.bind (N := ["PSC Y"]) (takes_pscRound _ _ (takes_trAnswerNotZero .pscY)) fun x => ?_
  obtain ⟨beta, q⟩ := x
  dsimp only
  exact Takes.after (takes_read _) fun _ => Takes.after (by calm) fun _ =>
    Takes.before (takes_empty .pscValues) fun _ => by calm

/-- One and the same one-member list for each member of l, in a row: that member, as often as l is
long. -/
theorem flatMap_const {γ : Type} (l : List γ) (s : String) :
    l.flatMap (fun _ => [s]) = List.replicate l.length s := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih, List.length_cons, List.replicate_succ]; rfl

/-- `roundsIn` uses up entries with just the names of the statement, in this order. -/
theorem takes_roundsIn (form : RoundForm) (p : Psc) (zs : List (E × Nat)) :
    Takes (roundsIn form p zs) (List.replicate zs.length "PSC round") := by
  unfold roundsIn
  refine (Takes.foldlM (g := fun _ => ["PSC round"]) (fun s z => ?_) zs _).of_eq (flatMap_const _ _)
  refine Takes.before (takes_roundIn _ _ _ _) fun x => ?_
  obtain ⟨r, q⟩ := x
  exact Takes.pure _

/-- The rounds of a level use up one entry named PSC round for each member of the order. -/
theorem takes_levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p : Psc),
    Takes (levelRounds mu rho order r p) (List.replicate order.length "PSC round")
  | [], r, p => by
    unfold levelRounds
    exact Takes.pure _
  | v :: order, r, p => by
    unfold levelRounds
    refine Takes.after (by calm) fun _ => ?_
    refine Takes.bind (N := ["PSC round"]) (takes_roundIn _ _ _ _) fun x => ?_
    obtain ⟨y, q⟩ := x
    exact takes_levelRounds mu rho order _ q

/-- `levelIn` uses up entries with just the names of the statement, in this order. -/
theorem takes_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Takes (levelIn mu rho C order) (levelNames mu) := by
  unfold levelIn
  refine Takes.must fun hm => ?_
  have hl : order.length = mu := by simpa using hm
  refine (Takes.bind (takes_pscBegin C) fun p => ?_).of_eq
    (M := levelNames mu) (N := ["PSC epsilon"] ++ (List.replicate order.length "PSC round" ++
      (["PSC Y", "PSC values"] ++ ["LINE"]))) (by simp [levelNames, pscNames, hl])
  refine Takes.bind (takes_levelRounds mu rho order _ p) fun x => ?_
  obtain ⟨r, q⟩ := x
  dsimp only
  refine Takes.bind (takes_pscEnds q 2 2) fun y => ?_
  obtain ⟨sL, q2⟩ := y
  dsimp only
  exact Takes.before (takes_answer .line) fun _ => by calm

/-! ## The lookup -/

theorem takes_draws (h : Forest.Shape) :
    Takes (Forest.draws h)
      ((if decide (1 < h.NC) = true then ["LKP shift"] else []) ++ ["LKP"]) := by
  unfold Forest.draws
  dsimp only
  by_cases hn : h.NC > 1
  · simp only [hn, if_true, decide_true]
    exact Takes.bind (takes_answer .lkpShift) fun _ =>
      Takes.before (takes_answer .lkp) fun _ => Takes.pure _
  · simp only [hn, if_false, decide_false, Bool.false_eq_true, List.nil_append]
    exact Takes.after (Takes.pure _) fun _ =>
      Takes.before (takes_answer .lkp) fun _ => Takes.pure _

/-- `Forest.tieStep` uses up entries with just the names of the statement, in this order. -/
theorem takes_tieStep (a : E) (s : Forest.TieStep) (j : Nat) :
    Takes (Forest.tieStep a s j) (pscNames 0 true) := by
  unfold Forest.tieStep
  refine (Takes.bind (takes_pscBegin _) fun p => ?_).of_eq
    (N := ["PSC epsilon"] ++ ["PSC Y", "PSC values"]) (by simp [pscNames])
  refine Takes.before (takes_pscEnds _ _ _) fun x => ?_
  obtain ⟨first, q⟩ := x
  dsimp only
  calm

/-- `Forest.tie` uses up entries with just the names of the statement, in this order. -/
theorem takes_tie (a : E) :
    Takes (Forest.tie a) (tieNames ++ ["JOIN"]) := by
  unfold Forest.tie tieNames
  refine Takes.bind (Takes.foldlM (fun s j => takes_tieStep a s j) _ _) fun s => ?_
  exact Takes.before (takes_point .lkpPlanes 5) fun _ => Takes.pure _

/-- `Forest.level` uses up entries with just the names of the statement, in this order. -/
theorem takes_level (s : Forest.Descent) (mu : Nat) (order : List Nat) :
    Takes (Forest.level s mu order) (levelNames mu) := by
  unfold Forest.level
  exact Takes.before (takes_levelIn _ _ _ _) fun _ => Takes.pure _

/-- **The lookup's routine uses up the entries of the planner's lookup, by their names.** -/
theorem takes_pad (calls : Array Call) (pub : Array Nat) (lid : Nat) (h0 : Forest.Shape)
    (hs : (Forest.shape calls lid).toOption = some h0) :
    Takes (Forest.pad calls pub lid) (forestNames (forestSize h0)) := by
  unfold Forest.pad
  refine Takes.get fun h1 e1 => ?_
  obtain rfl : h0 = h1 := Option.some.inj (hs.symm.trans e1)
  refine Takes.after (by calm) fun _ => ?_
  dsimp only
  refine Takes.after (by calm) fun _ => Takes.after (by calm) fun _ =>
    Takes.after (by calm) fun _ => Takes.after (by calm) fun _ => ?_
  unfold forestNames forestSize
  dsimp only
  refine Takes.bind (takes_draws _) fun x => ?_
  obtain ⟨theta, alpha, a⟩ := x
  dsimp only
  refine Takes.bind (takes_tie a) fun t => ?_
  refine Takes.bind (Takes.foldlM (g := levelNames) (fun s mu => takes_level s mu _) _ _)
    fun keys => ?_
  refine Takes.bind (Takes.foldlM (g := fun l => levelNames (5 + l))
    (fun s l => takes_level s (5 + l) _) _ _) fun table => ?_
  refine Takes.after (by calm) fun _ => ?_
  refine Takes.bind (takes_pscBegin _) fun leaves => ?_
  refine Takes.bind ((takes_roundsIn _ _ _).of_eq (M := List.replicate (5 + h0.d) "PSC round")
    (by simp; rfl)) fun y => ?_
  obtain ⟨zb0, leaves2⟩ := y
  dsimp only
  refine Takes.bindOn (takes_point .zero _) (point_size .zero _) fun r5 h5 => ?_
  refine Takes.bind (takes_pscBegin _) fun bits => ?_
  refine Takes.bind ((takes_roundsIn _ _ _).of_eq (M := List.replicate (5 + h0.d) "PSC round")
    (by simp [h5]; rfl)) fun y => ?_
  obtain ⟨zb1, bits2⟩ := y
  dsimp only
  refine Takes.before (takes_pscEnds _ _ _) fun y => ?_
  obtain ⟨sBit, bits3⟩ := y
  dsimp only
  calm

end OnBytes.Tie.Pv.Tail.Used

#print axioms OnBytes.Tie.Pv.Tail.Used.takes_pad
