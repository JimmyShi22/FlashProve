-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Alike.lean: when two lists of a chain's rounds, whose parts pass on
values of two different types, get the same answer from this folder's two players (`play`,
Honest/Frame.lean; `walk`, Honest/Walk.lean). Definitions, and lemmas with their proofs.

Why. A prover whose parts keep something between rounds passes on another type of value than the
prover whose parts keep nothing. So the two provers' states cannot be equal.

  1  `AnsAlike`, `OptAlike`   two answers, or two options, that are related
  2  `Mid.took_nil`, `Mid.took_took`, `TookAll`, `Step.go`, `Step.Faced`, `FacedAll`, `AlikeTo`,
     `AlikeTo.go`   a relation that holds whatever columns are read next; one round; what a player
     reads of a round beside its move; the relation: at every state that a play reaches, the two
     rounds return the same error or send the same message; and then, at every challenge, what
     follows it returns the same error or leads to states that are related whatever columns are read
     before the next round, the same by both
  3  `AlikeTo.mono`, `AlikeTo.append`, `AlikeTo.trans`   the relation is proved part by part, and
     through a list in the middle
  4  `play_alike`   `play` returns the same rounds, or the same error
  5  `ChainProgress.Like`, `settle_like`, `start_like`, `walk_alike`   the same for `walk`, which asks the
     description's own step between the rounds

Why the relation has two stages. `play` and `walk` end at any error, so for them one answer for a
whole round (`Step.go`) would do. A speaker (`tellC`, `progressAfterChallenge`, Honest/StratC.lean) sends a round's
message before the challenge, and produces it even where what follows the challenge returns an
error. So the two messages have to be equal also where both rounds return an error afterwards.


How it is meant to be used. Choose a relation `R` that holds between two parts. For each part prove
`R m m' → AlikeTo R steps steps' m m'`. `AlikeTo.append` joins these along the chain. After a part's
last round `R` is asked of the two states with any columns read (`Mid.took`): so `R` has to be kept
by that, as `MidBy` (Honest/AlikeParts.lean) is.

Why «whatever columns are read». Between two rounds `ChainProgress.settle` (Honest/Walk.lean) asks the
sub-protocols whose rounds are all produced, and lengthens the field `opened` of the state of the
run by the columns that they read. A part may read that field. So a relation that `walk` is to
carry across `ChainProgress.settle` has to speak of the states behind it. `play` reads no columns: there the
clause is used at the empty list (`TookAll.here`).

Limits.
  * The relation asks for every list of columns, the same in both runs, not only for those that a
    walk reads: more than either player needs.
  * Where both states hand no columns (`opened = none`) the clause is free: `Mid.took` changes
    nothing there. Where they hand some, it speaks of states that no `play` from `m`, `m'` reaches:
    so the relation does not follow from what `play` returns from the two states.
  * The relations `Post`, `P` and `Q` here are between two states of a run (`Mid`), so they run over
    the field `opened` too: what a relation needs of that field it has to say itself, as `MidBy`
    (Honest/AlikeParts.lean) does, which asks that both states show the same (`Mid.shown`).
  * Lists of rounds with the coins put in (`Step`). How two provers' sides give such lists
    (`chainSteps`, `ready`) is not treated here; nor is `runC` as a whole.
  * "The same message" is equality of `Told`. Its field `tables` holds functions (`Table.sym`). So
    for a round that sends a table one has to prove that two functions are equal: by `funext`, from
    the same symbol at every position and word. A round of the masked sumcheck sends scalars and no
    table (`mvOf`, Honest/SumLaw/Said.lean): there the equality of two lists of scalars is enough,
    which is what `AgreeAt` (Honest/SumKeepLaw.lean) states.
  * What mentions the type of the passed-on value in its own type (`midAt`, `midAtW` and their
    shared twins; the parameters `A`, `B`, `On` of a list of parts; so `Good` and `Owed`,
    Honest/Side.lean, Honest/Rule.lean,
    Honest/Owed.lean) is not reached: no lemma about `Owed` is carried from one prover to the other
    by this file.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl W X X' : Type}

/-! ## 1 Two answers, two options -/

/-- Both are answers, and related; or both are the same error. -/
def AnsAlike {α β : Type} (P : α → β → Prop) : Except Refusal α → Except Refusal β → Prop
  | .ok a, .ok b => P a b
  | .error e, .error e' => e = e'
  | _, _ => False

/-- Both are values, and related; or both are `none`. -/
def OptAlike {α β : Type} (P : α → β → Prop) : Option α → Option β → Prop
  | some a, some b => P a b
  | none, none => True
  | _, _ => False

theorem AnsAlike.mono {α β : Type} {P Q : α → β → Prop} (h : ∀ a b, P a b → Q a b) :
    ∀ {x : Except Refusal α} {y : Except Refusal β}, AnsAlike P x y → AnsAlike Q x y
  | .ok _, .ok _, q => h _ _ q
  | .error _, .error _, q => q
  | .ok _, .error _, q => q
  | .error _, .ok _, q => q

theorem AnsAlike.bind {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {f : α → Except Refusal γ} {g : β → Except Refusal δ}
    (hfg : ∀ a b, P a b → AnsAlike Q (f a) (g b)) :
    ∀ {x : Except Refusal α} {y : Except Refusal β}, AnsAlike P x y →
      AnsAlike Q (x.bind f) (y.bind g)
  | .ok _, .ok _, q => hfg _ _ q
  | .error _, .error _, q => q
  | .ok _, .error _, q => False.elim q
  | .error _, .ok _, q => False.elim q

theorem AnsAlike.map {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (hfg : ∀ a b, P a b → Q (f a) (g b)) :
    ∀ {x : Except Refusal α} {y : Except Refusal β}, AnsAlike P x y →
      AnsAlike Q (x.map f) (y.map g)
  | .ok _, .ok _, q => hfg _ _ q
  | .error _, .error _, q => q
  | .ok _, .error _, q => False.elim q
  | .error _, .ok _, q => False.elim q

theorem AnsAlike.comp {α β γ : Type} {P : α → β → Prop} {Q : β → γ → Prop} :
    ∀ {x : Except Refusal α} {y : Except Refusal β} {z : Except Refusal γ}, AnsAlike P x y →
      AnsAlike Q y z → AnsAlike (fun a c => ∃ b, P a b ∧ Q b c) x z
  | .ok _, .ok _, .ok _, p, q => ⟨_, p, q⟩
  | .error _, .error _, .error _, p, q => Eq.trans p q
  | .ok _, .error _, _, p, _ => False.elim p
  | .error _, .ok _, _, p, _ => False.elim p
  | .ok _, .ok _, .error _, _, q => False.elim q
  | .error _, .error _, .ok _, _, q => False.elim q

/-- Related by equality: equal. -/
theorem AnsAlike.eq {α : Type} :
    ∀ {x y : Except Refusal α}, AnsAlike (fun a b => a = b) x y → x = y
  | .ok _, .ok _, q => congrArg Except.ok q
  | .error _, .error _, q => congrArg Except.error q
  | .ok _, .error _, q => False.elim q
  | .error _, .ok _, q => False.elim q

theorem OptAlike.mono {α β : Type} {P Q : α → β → Prop} (h : ∀ a b, P a b → Q a b) :
    ∀ {x : Option α} {y : Option β}, OptAlike P x y → OptAlike Q x y
  | some _, some _, q => h _ _ q
  | none, none, _ => True.intro
  | some _, none, q => q
  | none, some _, q => q

theorem OptAlike.isSome {α β : Type} {P : α → β → Prop} :
    ∀ {x : Option α} {y : Option β}, OptAlike P x y → x.isSome = y.isSome
  | some _, some _, _ => rfl
  | none, none, _ => rfl
  | some _, none, q => False.elim q
  | none, some _, q => False.elim q

theorem OptAlike.map {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (hfg : ∀ a b, P a b → Q (f a) (g b)) :
    ∀ {x : Option α} {y : Option β}, OptAlike P x y → OptAlike Q (x.map f) (y.map g)
  | some _, some _, q => hfg _ _ q
  | none, none, _ => True.intro
  | some _, none, q => False.elim q
  | none, some _, q => False.elim q

theorem OptAlike.keep {α β : Type} {P : α → β → Prop} {x : Option α} {y : Option β} (c : Bool)
    (h : OptAlike P x y) : OptAlike P (if c then x else none) (if c then y else none) := by
  cases c
  · exact True.intro
  · exact h

/-! ## 2 The relation -/

/-- Where no column is read the state is as it was. -/
theorem Mid.took_nil (m : Mid W X) : m.took [] = m := by
  obtain ⟨st, loc, seen, opened⟩ := m
  cases opened with
  | none => rfl
  | some l => show (⟨st, loc, seen, some (l ++ [])⟩ : Mid W X) = _; rw [List.append_nil]

/-- Columns read twice over are columns read once. -/
theorem Mid.took_took (m : Mid W X) (a b : List OpenedColumn) : (m.took a).took b = m.took (a ++ b) := by
  obtain ⟨st, loc, seen, opened⟩ := m
  cases opened with
  | none => rfl
  | some l =>
    show (⟨st, loc, seen, some ((l ++ a) ++ b)⟩ : Mid W X) = ⟨st, loc, seen, some (l ++ (a ++ b))⟩
    rw [List.append_assoc]

/-- **The relation holds whatever columns are read next**, the same by both. Between two rounds
`ChainProgress.settle` (Honest/Walk.lean) lengthens the field `opened` of the state of the run
(`Mid.took`). -/
def TookAll (Q : Mid W X → Mid W X' → Prop) (a : Mid W X) (b : Mid W X') : Prop :=
  ∀ cols, Q (a.took cols) (b.took cols)

theorem TookAll.here {Q : Mid W X → Mid W X' → Prop} {a : Mid W X} {b : Mid W X'}
    (h : TookAll Q a b) : Q a b := by
  have t := h []
  rwa [Mid.took_nil, Mid.took_nil] at t

theorem TookAll.took {Q : Mid W X → Mid W X' → Prop} (a : Mid W X) (b : Mid W X')
    (cols : List OpenedColumn) (h : TookAll Q a b) : TookAll Q (a.took cols) (b.took cols) := by
  intro c
  rw [Mid.took_took, Mid.took_took]
  exact h _

/-- **One round**: its message, then what follows its challenge. `back`: as in `Step.tell`. -/
def Step.go (s : Step W X) (back : Option Fmt.RoundView) (d : Fmt.Drawn) (m : Mid W X) :
    Except Refusal (Told × Mid W X) :=
  (s.tell back m).bind fun x => (s.hear x d m).map fun m' => (x, m')

/-- What a player reads of a round beside its stops and its move. -/
def Step.Faced (s : Step W X) (s' : Step W X') : Prop :=
  s.name = s'.name ∧ s.addr = s'.addr ∧ s.decl = s'.decl ∧ s.oracles = s'.oracles

/-- Round by round; and the two lists are equally long. -/
def FacedAll : List (Step W X) → List (Step W X') → Prop
  | [], [] => True
  | s :: ss, s' :: ss' => s.Faced s' ∧ FacedAll ss ss'
  | _, _ => False

/-- **The relation.** From the states `m` and `m'`: the two first rounds' messages return the same
error, or are the same message; and then, at every challenge, what follows it returns the same
error, or the rest is related from the two new states, whatever columns are read before the next
round, the same by both (`TookAll`). After the last round `Post` holds of the two states, whatever
columns are read then; of two empty lists, of `m` and `m'` themselves. -/
def AlikeTo (Post : Mid W X → Mid W X' → Prop) :
    List (Step W X) → List (Step W X') → Mid W X → Mid W X' → Prop
  | [], [], m, m' => Post m m'
  | s :: ss, s' :: ss', m, m' =>
    ∀ back, AnsAlike
      (fun x x' => x = x' ∧
        ∀ d, AnsAlike (fun a b => ∀ cols, AlikeTo Post ss ss' (a.took cols) (b.took cols))
          (s.hear x d m) (s'.hear x' d m'))
      (s.tell back m) (s'.tell back m')
  | _, _, _, _ => False

/-- The relation in one stage: a whole round's two answers. -/
theorem AlikeTo.go {Post : Mid W X → Mid W X' → Prop} {s : Step W X} {ss : List (Step W X)}
    {s' : Step W X'} {ss' : List (Step W X')} {m : Mid W X} {m' : Mid W X'}
    (h : AlikeTo Post (s :: ss) (s' :: ss') m m') (back : Option Fmt.RoundView) (d : Fmt.Drawn) :
    AnsAlike (fun a b => a.1 = b.1 ∧ TookAll (AlikeTo Post ss ss') a.2 b.2) (s.go back d m)
      (s'.go back d m') :=
  AnsAlike.bind (fun _ _ r => AnsAlike.map (fun _ _ t => ⟨r.1, t⟩) (r.2 d)) (h back)

/-! ## 3 Part by part -/

theorem AlikeTo.mono {P Q : Mid W X → Mid W X' → Prop} (h : ∀ a b, P a b → Q a b) :
    ∀ (ss : List (Step W X)) (ss' : List (Step W X')) (m : Mid W X) (m' : Mid W X'),
      AlikeTo P ss ss' m m' → AlikeTo Q ss ss' m m'
  | [], [], _, _, q => h _ _ q
  | _ :: ss, _ :: ss', _, _, q => fun back =>
    AnsAlike.mono (fun _ _ r => ⟨r.1, fun d =>
      AnsAlike.mono (fun _ _ t cols => AlikeTo.mono h ss ss' _ _ (t cols)) (r.2 d)⟩) (q back)
  | [], _ :: _, _, _, q => q
  | _ :: _, [], _, _, q => q

/-- **Two lists one after the other.** -/
theorem AlikeTo.append (Post : Mid W X → Mid W X' → Prop) (b : List (Step W X))
    (b' : List (Step W X')) :
    ∀ (a : List (Step W X)) (a' : List (Step W X')) (m : Mid W X) (m' : Mid W X'),
      AlikeTo (AlikeTo Post b b') a a' m m' → AlikeTo Post (a ++ b) (a' ++ b') m m'
  | [], [], _, _, q => q
  | _ :: ss, _ :: ss', _, _, q => fun back =>
    AnsAlike.mono (fun _ _ r => ⟨r.1, fun d =>
      AnsAlike.mono (fun _ _ t cols => AlikeTo.append Post b b' ss ss' _ _ (t cols))
        (r.2 d)⟩) (q back)
  | [], _ :: _, _, _, q => False.elim q
  | _ :: _, [], _, _, q => False.elim q

/-- **Through a list in the middle.** -/
theorem AlikeTo.trans {X'' : Type} (P : Mid W X → Mid W X' → Prop)
    (Q : Mid W X' → Mid W X'' → Prop) :
    ∀ (ss : List (Step W X)) (ss' : List (Step W X')) (ss'' : List (Step W X'')) (m : Mid W X)
      (m' : Mid W X') (m'' : Mid W X''), AlikeTo P ss ss' m m' → AlikeTo Q ss' ss'' m' m'' →
      AlikeTo (fun a c => ∃ b, P a b ∧ Q b c) ss ss'' m m''
  | [], [], [], _, _, _, p, q => ⟨_, p, q⟩
  | _ :: ss, _ :: ss', _ :: ss'', _, _, _, p, q => fun back =>
    AnsAlike.mono
      (fun _ _ r =>
        match r with
        | ⟨_, r₁, r₂⟩ =>
          ⟨r₁.1.trans r₂.1, fun d =>
            AnsAlike.mono
              (fun _ _ t cols =>
                match t with
                | ⟨_, t₁, t₂⟩ => AlikeTo.trans P Q ss ss' ss'' _ _ _ (t₁ cols) (t₂ cols))
              (AnsAlike.comp (r₁.2 d) (r₂.2 d))⟩)
      (AnsAlike.comp (p back) (q back))
  | [], [], _ :: _, _, _, _, _, q => False.elim q
  | [], _ :: _, _, _, _, _, p, _ => False.elim p
  | _ :: _, [], _, _, _, _, p, _ => False.elim p
  | _ :: _, _ :: _, [], _, _, _, _, q => False.elim q

theorem FacedAll.append :
    ∀ (a : List (Step W X)) (a' : List (Step W X')) (b : List (Step W X)) (b' : List (Step W X')),
      FacedAll a a' → FacedAll b b' → FacedAll (a ++ b) (a' ++ b')
  | [], [], _, _, _, q => q
  | _ :: ss, _ :: ss', b, b', p, q => ⟨p.1, FacedAll.append ss ss' b b' p.2 q⟩
  | [], _ :: _, _, _, p, _ => False.elim p
  | _ :: _, [], _, _, p, _ => False.elim p

/-! ## 4 `play` -/

theorem play_cons (s : Step W X) (ss : List (Step W X)) (d : Fmt.Drawn) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) :
    play (s :: ss) (d :: ds) back m =
      (s.go back.head? d m).bind fun a =>
        (play ss ds back.tail a.2).map fun y =>
          (⟨s.name, s.addr.place, if a.1.told then s.addr.part else 0, a.1.told, a.1.vals,
            a.1.tables, d⟩ :: y.1, y.2) := by
  cases h1 : s.tell back.head? m with
  | error e => simp only [play, Step.go, h1, Except.bind]
  | ok x =>
    cases h2 : s.hear x d m with
    | error e => simp only [play, Step.go, h1, h2, Except.bind, Except.map]
    | ok m' => simp only [play, Step.go, h1, h2, Except.bind, Except.map]

/-- **`play` returns the same rounds and related states, or the same error.** -/
theorem play_alike (Post : Mid W X → Mid W X' → Prop) :
    ∀ (ss : List (Step W X)) (ss' : List (Step W X')) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
      (m : Mid W X) (m' : Mid W X'), FacedAll ss ss' → AlikeTo Post ss ss' m m' →
      AnsAlike (fun a b => a.1 = b.1 ∧ Post a.2 b.2) (play ss ds back m) (play ss' ds back m')
  | [], [], [], _, _, _, _, q => ⟨rfl, q⟩
  | [], [], _ :: _, _, _, _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _, _, _, _ => rfl
  | s :: ss, s' :: ss', d :: ds, back, m, m', hF, q => by
    rw [play_cons, play_cons]
    refine AnsAlike.bind (fun a b r => ?_) (AlikeTo.go q back.head? d)
    have ih := play_alike Post ss ss' ds back.tail a.2 b.2 hF.2 r.2.here
    obtain ⟨f1, f2, _, _⟩ := hF.1
    rw [← f1, ← f2, ← r.1]
    revert ih
    cases play ss ds back.tail a.2 with
    | error e =>
      cases play ss' ds back.tail b.2 with
      | error e' => exact fun ih => ih
      | ok y' => exact fun ih => False.elim ih
    | ok y =>
      cases play ss' ds back.tail b.2 with
      | error e' => exact fun ih => False.elim ih
      | ok y' => exact fun ih => ⟨congrArg _ ih.1, ih.2⟩
  | [], _ :: _, _, _, _, _, hF, _ => False.elim hF
  | _ :: _, [], _, _, _, _, hF, _ => False.elim hF

/-! ## 5 `walk` -/

/-- **Two walks that differ at most in the state of the prover's run.** -/
structure ChainProgress.Like (P : Mid W X → Mid W X' → Prop) (z : ChainProgress S Cl W X) (z' : ChainProgress S Cl W X') :
    Prop where
  ver : z.ver = z'.ver
  refused : z.refused = z'.refused
  laid : z.laid = z'.laid
  reads : z.reads = z'.reads
  cols : z.cols = z'.cols
  todo : z.todo = z'.todo
  own : z.own = z'.own
  mid : OptAlike P z.mid z'.mid

theorem ChainProgress.Like.mono {P Q : Mid W X → Mid W X' → Prop} (h : ∀ a b, P a b → Q a b)
    {z : ChainProgress S Cl W X} {z' : ChainProgress S Cl W X'} (q : ChainProgress.Like P z z') : ChainProgress.Like Q z z' :=
  ⟨q.ver, q.refused, q.laid, q.reads, q.cols, q.todo, q.own, q.mid.mono h⟩

/-- The sub-protocols are asked alike: `ChainProgress.settle` reads what has been produced, not the state of
the run; of that state it lengthens the field `opened`, by the same columns in both walks. hP: the
relation is kept by that. -/
theorem settle_like (L : Lay) (P : Mid W X → Mid W X' → Prop)
    (hP : ∀ a b cols, P a b → P (a.took cols) (b.took cols)) :
    ∀ (bs : List (Block S Cl)) (z : ChainProgress S Cl W X) (z' : ChainProgress S Cl W X'), ChainProgress.Like P z z' →
      AnsAlike (ChainProgress.Like P) (ChainProgress.settle L bs z) (ChainProgress.settle L bs z')
  | [], _, _, h => ⟨h.ver, h.refused, h.laid, h.reads, h.cols, rfl, h.own, h.mid⟩
  | b :: bs, ⟨mid, ver, refused, laid, reads, cols, todo, own⟩,
      ⟨mid', ver', refused', laid', reads', cols', todo', own'⟩, h => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    have e1 : ver = ver' := h1
    have e2 : refused = refused' := h2
    have e3 : laid = laid' := h3
    have e4 : reads = reads' := h4
    have e5 : cols = cols' := h5
    have e6 : todo = todo' := h6
    have e7 : own = own' := h7
    have e8 : OptAlike P mid mid' := h8
    subst e1 e2 e3 e4 e5 e6 e7
    by_cases hc : own.length < b.rounds.length
    · simp only [ChainProgress.settle, if_pos hc]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, e8⟩
    · simp only [ChainProgress.settle, if_neg hc]
      refine AnsAlike.bind (P := fun a b => a = b) (fun cs cs' e => ?_) ?_
      · subst e
        exact settle_like L P hP bs _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          OptAlike.keep _ (OptAlike.map (fun a b q => hP a b cs q) e8)⟩
      · cases unfit (fillCols (readsOf L.chain L.firstTree L.stored (L.tree laid) b.rounds
          (own.map (·.drawn))) []) with
        | error e => exact rfl
        | ok cs => exact rfl

/-- h: the relation holds of the two states with the columns `front` laid, as `ChainProgress.start` lays
them. -/
theorem start_like (L : Lay) (P : Mid W X → Mid W X' → Prop)
    (hP : ∀ a b cols, P a b → P (a.took cols) (b.took cols)) (bs : List (Block S Cl))
    {m : Option (Mid W X)} {m' : Option (Mid W X')} (v : Option S) (front : List OpenedColumn)
    (h : OptAlike (fun a b => P { a with opened := some front } { b with opened := some front })
      m m') :
    AnsAlike (ChainProgress.Like P) (ChainProgress.start L bs m v front) (ChainProgress.start L bs m' v front) :=
  settle_like L P hP bs _ _
    ⟨by show (if m.isSome then v else none) = (if m'.isSome then v else none); rw [h.isSome],
      rfl, rfl, rfl, rfl, rfl, rfl,
      OptAlike.keep _ (OptAlike.map (Q := P)
        (f := fun a : Mid W X => { a with opened := some front })
        (g := fun b : Mid W X' => { b with opened := some front }) (fun _ _ q => q) h)⟩

/-- The round as `ChainProgress.heard` produces it. -/
def Step.laid (s : Step W X) (x : Told) (d : Fmt.Drawn) : Played :=
  ⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩

theorem walk_some (L : Lay) (s : Step W X) (ss : List (Step W X)) (d : Fmt.Drawn)
    (ds : List Fmt.Drawn) (m : Mid W X) (ver : Option S) (refused : Option Place)
    (laid : List Played) (reads : List Read) (cols : List OpenedColumn)
    (todo : List (Block S Cl)) (own : List Played) :
    walk L (s :: ss) (d :: ds) ⟨some m, ver, refused, laid, reads, cols, todo, own⟩ =
      (s.go none d m).bind fun a =>
        (ChainProgress.settle L todo ⟨some a.2, ver, refused, laid ++ [s.laid a.1 d], reads, cols, todo,
                   own ++ [s.laid a.1 d]⟩).bind fun z₁ => walk L ss ds z₁ := by
  cases h1 : s.tell none m with
  | error e => simp only [walk, ChainProgress.say, Step.go, h1, Except.bind]
  | ok x =>
    cases h2 : s.hear x d m with
    | error e =>
      simp only [walk, ChainProgress.say, ChainProgress.heard, Step.go, h1, h2, Except.bind, Except.map]
    | ok m' =>
      simp only [walk, ChainProgress.say, ChainProgress.heard, Step.go, Step.laid, h1, h2, Except.bind, Except.map]

theorem walk_none (L : Lay) (s : Step W X) (ss : List (Step W X)) (d : Fmt.Drawn)
    (ds : List Fmt.Drawn) (ver : Option S) (refused : Option Place)
    (laid : List Played) (reads : List Read) (cols : List OpenedColumn)
    (todo : List (Block S Cl)) (own : List Played) :
    walk L (s :: ss) (d :: ds) ⟨none, ver, refused, laid, reads, cols, todo, own⟩ =
      (ChainProgress.settle L todo ⟨none, ver, refused, laid ++ [s.laid (subTold s.decl s.oracles) d], reads,
                 cols, todo, own ++ [s.laid (subTold s.decl s.oracles) d]⟩).bind fun z₁ =>
          walk L ss ds z₁ := by
  simp only [walk, ChainProgress.say, ChainProgress.heard, Step.laid, Except.bind]

theorem Step.Faced.laid {s : Step W X} {s' : Step W X'} (h : s.Faced s') (x : Told)
    (d : Fmt.Drawn) : s.laid x d = s'.laid x d := by
  obtain ⟨f1, f2, _, _⟩ := h
  unfold Step.laid
  rw [f1, f2]

/-- **`walk` returns walks that differ at most in the state of the run, or the same error.** The
verifier's state, the place of the first rejection, the rounds produced, what was read and the
columns are equal. -/
theorem walk_alike (L : Lay) (Post : Mid W X → Mid W X' → Prop) :
    ∀ (ss : List (Step W X)) (ss' : List (Step W X')) (ds : List Fmt.Drawn) (z : ChainProgress S Cl W X)
      (z' : ChainProgress S Cl W X'), FacedAll ss ss' → ChainProgress.Like (AlikeTo Post ss ss') z z' →
      AnsAlike (ChainProgress.Like Post) (walk L ss ds z) (walk L ss' ds z')
  | [], [], [], _, _, _, h => h.mono fun _ _ q => q
  | [], [], _ :: _, _, _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _, _, _ => rfl
  | s :: ss, s' :: ss', d :: ds, ⟨mid, ver, refused, laid, reads, cols, todo, own⟩,
      ⟨mid', ver', refused', laid', reads', cols', todo', own'⟩, hF, h => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    have e1 : ver = ver' := h1
    have e2 : refused = refused' := h2
    have e3 : laid = laid' := h3
    have e4 : reads = reads' := h4
    have e5 : cols = cols' := h5
    have e6 : todo = todo' := h6
    have e7 : own = own' := h7
    have e8 : OptAlike (AlikeTo Post (s :: ss) (s' :: ss')) mid mid' := h8
    subst e1 e2 e3 e4 e5 e6 e7
    cases mid with
    | none =>
      cases mid' with
      | some _ => exact False.elim e8
      | none =>
        rw [walk_none, walk_none, ← hF.1.2.2.1, ← hF.1.2.2.2, ← hF.1.laid]
        exact AnsAlike.bind
          (fun z₁ z₁' hz => walk_alike L Post ss ss' ds z₁ z₁' hF.2 (hz.mono fun _ _ q => q.here))
          (settle_like L (TookAll (AlikeTo Post ss ss')) TookAll.took todo _ _
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩)
    | some m =>
      cases mid' with
      | none => exact False.elim e8
      | some m' =>
        rw [walk_some, walk_some]
        have q : AlikeTo Post (s :: ss) (s' :: ss') m m' := e8
        refine AnsAlike.bind (fun a b r => ?_) (AlikeTo.go q none d)
        rw [← hF.1.laid, ← r.1]
        exact AnsAlike.bind
          (fun z₁ z₁' hz => walk_alike L Post ss ss' ds z₁ z₁' hF.2 (hz.mono fun _ _ q => q.here))
          (settle_like L (TookAll (AlikeTo Post ss ss')) TookAll.took todo _ _
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, r.2⟩)
  | [], _ :: _, _, _, _, hF, _ => False.elim hF
  | _ :: _, [], _, _, _, hF, _ => False.elim hF

end ProofFile.Honest

#print axioms ProofFile.Honest.Mid.took_nil
#print axioms ProofFile.Honest.Mid.took_took
#print axioms ProofFile.Honest.TookAll
#print axioms ProofFile.Honest.TookAll.here
#print axioms ProofFile.Honest.TookAll.took
#print axioms ProofFile.Honest.OptAlike.map
#print axioms ProofFile.Honest.AlikeTo.append
#print axioms ProofFile.Honest.AlikeTo.mono
#print axioms ProofFile.Honest.AlikeTo.go
#print axioms ProofFile.Honest.AlikeTo.trans
#print axioms ProofFile.Honest.play_alike
#print axioms ProofFile.Honest.settle_like
#print axioms ProofFile.Honest.start_like
#print axioms ProofFile.Honest.walk_alike
#print axioms ProofFile.Honest.AnsAlike.mono
#print axioms ProofFile.Honest.AnsAlike.bind
#print axioms ProofFile.Honest.AnsAlike.map
#print axioms ProofFile.Honest.AnsAlike.comp
#print axioms ProofFile.Honest.AnsAlike.eq
#print axioms ProofFile.Honest.OptAlike.mono
#print axioms ProofFile.Honest.OptAlike.isSome
#print axioms ProofFile.Honest.OptAlike.keep
#print axioms ProofFile.Honest.FacedAll.append
#print axioms ProofFile.Honest.play_cons
#print axioms ProofFile.Honest.ChainProgress.Like.mono
#print axioms ProofFile.Honest.walk_some
#print axioms ProofFile.Honest.walk_none
#print axioms ProofFile.Honest.Step.Faced.laid
#print axioms ProofFile.Honest.AnsAlike
#print axioms ProofFile.Honest.OptAlike
#print axioms ProofFile.Honest.Step.go
#print axioms ProofFile.Honest.Step.Faced
#print axioms ProofFile.Honest.FacedAll
#print axioms ProofFile.Honest.AlikeTo
#print axioms ProofFile.Honest.ChainProgress.Like
#print axioms ProofFile.Honest.Step.laid
