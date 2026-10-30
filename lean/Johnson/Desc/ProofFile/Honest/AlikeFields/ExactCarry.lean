-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AlikeFields/ExactCarry.lean: the field `exact` of `Good`
(Honest/Side.lean), under its name at one member (`ExactMember`, Honest/Small/Field.lean), is
carried from a part to the same part with other moves (`Part.reMove`, Honest/AlikeParts.lean), where
the relation that is asked in front of the part is parted from what is asked behind its last move;
and so to the masked sumcheck's part with a kept state (`keepPart`, Honest/SumKeep.lean), at every
job. Free of any kind of sub-protocol. One definition; theorems.

Written with the lookups (K3), on the shelf that the frame named for it.


Never to be retold as "a part with a kept state is simulated". One sentence, had of a part, is
carried to the same part with other moves. The simulator is the earlier member's own, unturned.
Coins are bound under "for all" and never opened. The measures on both sides are the earlier
member's: the function under the left one is replaced by an equal function (`shows_re`,
Honest/AlikeExact.lean).

Terms. "One input": of two carried states a and b: a.input = b.input; it is written out in every
statement. `MovesTo`, `StateBy`: Honest/AlikeParts.lean. `lastHandMoves`, `Part.lastHand`,
`quietLay`: Honest/K3/RowKeepParts.lean: three definitions that are general in their types; they
stand in the lookups' folder, and that file is imported.

What is defined.
  `made J`: for a job with a kept state: the earlier job's shape, points and lead; its three other
    functions return what the kept job's functions return at the kept state computed from the start
    (`KeepJob.madeAt`). It stands in proofs, and in the statements of `made_faithful`,
    `keepPart_made`, `exact_made_moves` and `keep_made_movesTo`.

What is shown.
  `movesTo_mono`: `MovesTo` is monotone in what it asks behind the last move.
  `movesTo_lastHand`: two lists of moves in `MovesTo` at `StateBy r` are in `MovesTo` at "one input"
    when the second list's last move passes on something else.
  `lastHandMoves_len`, `lastHandMoves_lift`: such a list is as long; seating it (`Move.lift`) gives
    the seated list whose last move passes on the seated value.
  `made_faithful`: the kept job with `made J` as its earlier job meets `KeepJob.Faithful`.
  `keepPart_made`: `keepPart` at that job is `keepPart` at J.
  `exactMember_pre`: the sentence at one member, carried. `Pre`: the relation in front. `hM`: from
    every two states in `Pre`, at all coins, whatever rounds were shown and, as `MovesTo` has it, at
    every value of the columns opened, reached or not, the two lists of moves say the same, and
    behind the last move the two states have one input. `hOn`: wherever the second entry sentence
    holds, a stand of the first run with the same challenges, rounds shown and columns opened, whose
    state is in `Pre`, has the first.
  `exact_made_moves`: the sentence at the seated `sumPart` at `made J` with other moves.
  `keep_made_movesTo`: the frame's authors' `Keep.keep_movesTo` (Honest/AlikeKeep.lean), called at
    `made J`: the seated moves of `sumPart` at `made J` and of `keepPart` at J say the same from
    every two states with one input, one list of challenges heard and one value in front of the kept
    state. Conditional on `hgs`.
  `exact_keepPart_lift`: **the sentence at the seated `keepPart`, at every job J, entry sentence and
    budget.**
  `exact_keepPart_lastHand_lift`: the same where the part's last move passes on something else.
  `exact_quietLay_lift`: the sentence at a seated part of one move that sends nothing, whatever it
    passes on.

Kin. `exactMember_pre` is `exactMember_re` (Honest/AlikeExact.lean, by the authors of the honest
side of the output head's own rounds, K6) with the one relation T parted in two. Statement and proof
follow that theorem (at sha256): 8 lines of the statement and 9 of the proof's 16 stand
there sign for sign; 7 lines of the proof are turned or new
(counted by a program).
`shows_re` and `stopAt_re` of that file are called, the first at "one input". `exactMember_re` stays
as it is. `lastHandMoves_len` is the statement of the lookups' `lastHandMoves_length`
(Honest/K3/Law/Keep/Bridge.lean), typed anew so that this file need not import that one.

Hypotheses that remain.
  In `exactMember_pre`: `hb`: one sub-protocol; `hP`: `Pre` keeps the input; `hn`, `hr`: as many
    moves as the part has, and as many rounds; `hM`; `hOn`; `he`: the sentence at u.
  In the three on `keepPart`: `hgs`, `hsg`: get reads what set has laid; laying what get reads turns
    nothing. `hk`, `hr`, `hb`: those of `exact_sumPart_field` (Honest/SumLaw/SumExact.lean) at the
    earlier job's shape: the test on the shape; the declared rounds state the shape's scalars; the
    mark on beta. In `exact_made_moves` besides: `hn`, `hM`, on the other moves.
  In `exact_quietLay_lift`: `hrs`: one declared round, which states nothing.
No `KeepJob.FaithfulOn` and no condition on the state in front is asked: the three stand at jobs
right or wrong.

What is passed on holds no coin, by the type of `Move.hand`. The frame's authors' own line
(Honest/Frame.lean, at `Move.hand`; sha256): "It is given no coin and nothing that was
sent: so by type `own` is computed from the input and the challenges alone".

How the proofs go. `keepPart` reads of its earlier job the shape, the points and the lead alone; so
with `made J` as earlier job the part is the same and the job is faithful by unfolding; the frame's
authors' `Keep.keep_movesTo` (Honest/AlikeKeep.lean) then holds from every two states with one
input, one list of challenges heard and one value in front of the kept state. The sentence at
`sumPart` at `made J` is `exact_sumPart_field`, which stands at every job. The two sides are one
side, and every stand is related to itself.

Built over. Honest/AlikeExact.lean · AlikeKeep.lean · AlikeParts.lean · AlikeRow.lean · SumKeep.lean
· Small/Field.lean · Small/Quiet.lean · SumLaw/SumExact.lean · Frame.lean ·
Honest/K3/RowKeepParts.lean. The line on `Move.hand` is quoted as it stands in
Frame.lean.

Limits. It shows `exact` of no new kind of part. The earlier members are of no row that a prover
runs: they are a device of proof. Of `Good`'s other fields (`fits`, `plays`, `acc`, `fresh`) nothing
is carried. That a prover's side has a row with such parts is not said. Nothing on what a part
sends: at jobs right or wrong. One part: nothing on a chain, a run or a prover as a whole. No
instance of the hypotheses is exhibited in this file; Honest/AlikeFields/Test/ExactCarryTooth.lean
has moves at which `hM` holds and moves at which it fails.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.AlikeExact
import Johnson.Desc.ProofFile.Honest.AlikeKeep
import Johnson.Desc.ProofFile.Honest.SumLaw.SumExact
import Johnson.Desc.ProofFile.Honest.Small.Quiet
import Johnson.Desc.ProofFile.Honest.K3.RowKeepParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.AlikeFields
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)
open ProofFile.Honest.Small (ExactMember quietPart_exact_lift statedOf stated_quiet)
open ProofFile.Honest.SumLaw (StatedBy betaMarked exact_sumPart_field statedBy_len)
open ProofFile.Honest.K3 (lastHandMoves quietLay)

variable {S Cl V W X X' Pb V' W' Y K C : Type}

/-! ## 1 Two lists of moves -/

/-- **`MovesTo` is monotone in what it asks behind the last move.** -/
theorem movesTo_mono {P P' : State W X → State W X' → Prop} (h : ∀ a b, P a b → P' a b) (c : C) :
    ∀ (l : List (Move C W X)) (l' : List (Move C W X')) (t : State W X) (t' : State W X')
      (seen : List Fmt.RoundView), MovesTo c P l l' t t' seen → MovesTo c P' l l' t t' seen
  | [], [], _, _, _, q => h _ _ q
  | _ :: l, _ :: l', _, _, _, q => ⟨q.1, fun d e => movesTo_mono h c l l' _ _ _ (q.2 d e)⟩
  | [], _ :: _, _, _, _, q => False.elim q
  | _ :: _, [], _, _, _, q => False.elim q

/-- Where the second list's last move passes on something else, the two lists still say the same;
behind the last move the two states have one input. -/
theorem movesTo_lastHand (c : C) (r : X → X' → Prop) (g : State W X' → X') :
    ∀ (l : List (Move C W X)) (l' : List (Move C W X')) (t : State W X) (t' : State W X')
      (seen : List Fmt.RoundView), MovesTo c (StateBy r) l l' t t' seen →
      MovesTo c (fun (a : State W X) (b : State W X') => a.input = b.input) l (lastHandMoves g l') t
        t' seen
  | [], [], _, _, _, q => q.1
  | [], _ :: _, _, _, _, q => False.elim q
  | _ :: _, [], _, _, _, q => False.elim q
  | [_], [_], _, _, _, q => ⟨q.1, fun d e => (q.2 d e).1⟩
  | [_], _ :: _ :: _, _, _, _, q => ⟨q.1, fun d e => False.elim (q.2 d e)⟩
  | _ :: _ :: _, [_], _, _, _, q => ⟨q.1, fun d e => False.elim (q.2 d e)⟩
  | _ :: mv :: l, _ :: mv' :: l', _, _, _, q =>
    ⟨q.1, fun d e => movesTo_lastHand c r g (mv :: l) (mv' :: l') _ _ _ (q.2 d e)⟩

/-- Such a list is as long. -/
theorem lastHandMoves_len (g : State W X → X) :
    ∀ l : List (Move C W X), (lastHandMoves g l).length = l.length
  | [] => rfl
  | [_] => rfl
  | _ :: mv :: l => congrArg (· + 1) (lastHandMoves_len g (mv :: l))

/-- Seating such a list gives the seated list whose last move passes on the seated value. -/
theorem lastHandMoves_lift (wit : W → W') (get : X → Y) (set : X → Y → X) (g : State W' Y → Y) :
    ∀ l : List (Move C W' Y), (lastHandMoves g l).map (Move.lift wit get set) =
      lastHandMoves (fun t => set t.own (g (t.narrow wit get))) (l.map (Move.lift wit get set))
  | [] => rfl
  | [_] => rfl
  | mv₀ :: mv :: l =>
    congrArg (Move.lift wit get set mv₀ :: ·) (lastHandMoves_lift wit get set g (mv :: l))

/-! ## 2 The job that computes the kept state from the start -/

/-- **The earlier job's shape, points and lead; the three other functions as the kept job's return
them at the kept state computed from the start.** -/
def made (J : KeepJob W X K) : SumJob W X :=
  { J.base with
    round := fun w f rs => J.round (J.madeAt w f.heard f.own rs)
    inY := fun w f rs m => J.inY (J.madeAt w f.heard f.own rs) m
    ends := fun w f rs => J.ends (J.madeAt w f.heard f.own rs) }

/-- With `made J` as its earlier job the kept job is faithful. -/
theorem made_faithful (J : KeepJob W X K) : ({ J with base := made J } : KeepJob W X K).Faithful :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- The part does not read what was replaced. -/
theorem keepPart_made (name endName : String) (J : KeepJob W X K) :
    keepPart (V := V) name endName { J with base := made J } = keepPart name endName J :=
  rfl

/-! ## 3 The sentence at one member -/

/-- Conditional: hb, hP, hn, hr, hM, hOn, he: see the head. **The sentence at the member with other
moves.** Its simulator is u's. hOn asks of the stand that is found the second stand's columns opened
too, not its rounds shown alone: so the law says less than it would with the rounds alone. Its three
callers (`exact_made_moves`, `exact_quietLay_lift`; `seven_exact` in Test/ExactCarryTooth2.lean) pay
that by `rfl`: each lays the second stand itself. -/
theorem exactMember_pre (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (σ' : Side S Cl V W X' Pb)
    (hb : σ'.block = σ.block) (u : Member V W X Pb) (mvs : List (Move u.part.Coins W X'))
    (Pre : State W X → State W X' → Prop) (hP : ∀ t t', Pre t t' → t.input = t'.input)
    (hn : mvs.length = u.part.moves.length) (hr : u.rounds.length = u.part.moves.length)
    (hM : ∀ c t t' seen, Pre t t' →
      MovesTo c (fun (a : State W X) (b : State W X') => a.input = b.input) u.part.moves mvs t t'
        seen)
    (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (On' : (u : Member V W X' Pb) → CsAll u.part.carries → Mid W X' → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hOn : ∀ ca m' front, On' ⟨u.number, u.rounds, u.part.reMove mvs, u.sim⟩ ca m' front →
      ∃ m, m.loc = m'.loc ∧ m.shown = m'.shown ∧ Pre m.st m'.st ∧ On u ca m front)
    (he : ExactMember φ σ chain firstTree On bud u) :
    ExactMember φ σ' chain firstTree On' bud ⟨u.number, u.rounds, u.part.reMove mvs, u.sim⟩ := by
  intro ca m' front ds asks hO hs hd hbd hh hst
  obtain ⟨m, hl, hsn, hp, hOm⟩ := hOn ca m' front hO
  have hi : m.st.input = m'.st.input := hP _ _ hp
  have hst' : u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid := by
    rw [hi, hl, ← stopAt_re u.part mvs hn]
    exact hst
  have k := he ca m front ds asks hOm ((congrArg Seen.rounds hsn).trans hs) hd hbd hh hst'
  have fe : (fun c : Cs u.part.takes × CsAll u.part.spends =>
        σ.shows φ u (c.1, c.2, ca) m ds asks) =
      fun c => σ'.shows φ ⟨u.number, u.rounds, u.part.reMove mvs, u.sim⟩ (c.1, c.2, ca) m' ds
        asks :=
    funext fun c => shows_re φ σ σ' hb u mvs
      (fun (a : State W X) (b : State W X') => a.input = b.input) (fun _ _ q => q) hn hr
      (c.1, c.2, ca) m m' ⟨hl, hsn, hi⟩ (hM _ _ _ _ hp) ds asks
  rw [fe, hi] at k
  exact k

/-! ## 4 The masked sumcheck's part with a kept state -/

/-- Conditional: hgs, hsg, hk, hr, hb, hn, hM: see the head. The sentence at the seated `sumPart` at
`made J` with other moves. -/
theorem exact_made_moves (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (see : V → V') (wit : W → W')
    (get : X → Y × Option K) (set : X → Y × Option K → X) (hgs : ∀ x y, get (set x y) = y)
    (hsg : ∀ x, set x (get x) = x) (name endName : String) (J : KeepJob W' Y K)
    (hk : shapeOk J.base.shape = true) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.base.shape) rs) (hb : betaMarked J.base.shape rs = true) (j : Nat)
    (a' : Addr)
    (mvs : List (Move ((sumPart (V := V') name endName (made J)).lift see wit (fun x => (get x).1)
      fun x y => set x (y, (get x).2)).Coins W X))
    (hn : mvs.length = (scalarsOf J.base.shape).length)
    (hM : ∀ c t t' seen, StateBy (fun x x' => (get x).1 = (get x').1) t t' →
      MovesTo c (fun (a : State W X) (b : State W X) => a.input = b.input)
        ((sumPart (V := V') name endName (made J)).lift see wit (fun x => (get x).1)
          fun x y => set x (y, (get x).2)).moves mvs t t' seen) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, ((sumPart (V := V') name endName (made J)).lift see wit (fun x => (get x).1)
        fun x y => set x (y, (get x).2)).reMove mvs, sumSim a' J.base.shape⟩ := by
  have hlen : ((sumPart (V := V') name endName (made J)).lift see wit (fun x => (get x).1)
      fun x y => set x (y, (get x).2)).moves.length = (scalarsOf J.base.shape).length :=
    (List.length_map _).trans (Keep.sumPart_rounds name endName (made J))
  exact exactMember_pre φ σ σ rfl
    ⟨j, rs, (sumPart (V := V') name endName (made J)).lift see wit (fun x => (get x).1)
      fun x y => set x (y, (get x).2), sumSim a' J.base.shape⟩
    mvs (StateBy fun x x' => (get x).1 = (get x').1) (fun _ _ q => q.1) (hn.trans hlen.symm)
    ((statedBy_len _ _ hr).trans hlen.symm) hM chain firstTree (fun _ _ _ _ => True) On bud
    (fun _ m' _ _ => ⟨m', rfl, rfl, ⟨rfl, rfl, rfl⟩, True.intro⟩)
    (exact_sumPart_field φ σ chain firstTree (fun _ _ _ _ => True) bud see wit
      (fun x => (get x).1) (fun x y => set x (y, (get x).2))
      (fun x y => by show (get (set x (y, (get x).2))).1 = y; rw [hgs]) (fun x => hsg x) name
      endName (made J) hk rs hr hb j a')

/-- The frame's authors' law on the two lists of moves, at `made J`: from every two states with one
input, one list of challenges heard and one value in front of the kept state. -/
theorem keep_made_movesTo (wit : W → W') (get : X → Y × Option K) (set : X → Y × Option K → X)
    (hgs : ∀ x y, get (set x y) = y) (J : KeepJob W' Y K) {name endName : String}
    (c : SumLaw.SumCoins name endName (made J)) (t t' : State W X) (seen : List Fmt.RoundView)
    (q : StateBy (fun x x' => (get x).1 = (get x').1) t t') :
    MovesTo (C := SumLaw.SumCoins name endName (made J)) c
      (StateBy fun x x' => (get x).1 = (get x').1)
      ((sumPart (V := V') name endName (made J)).moves.map
        (Move.lift wit (fun x => (get x).1) fun x y => set x (y, (get x).2)))
      ((keepPart (V := V') name endName J).moves.map (Move.lift wit get set)) t t' seen :=
  Keep.keep_movesTo wit (fun x => (get x).1) (fun x y => set x (y, (get x).2)) get set
    (fun x x' => (get x).1 = (get x').1) hgs (fun _ _ h => h)
    (fun x x' k h => by
      show (get (set x ((get x).1, (get x).2))).1 = (get (set x' ((get x').1, k))).1
      rw [hgs, hgs]
      exact h)
    ({ J with base := made J } : KeepJob W' Y K) c (fun _ _ _ => True) (made_faithful J).on t t'
    seen q True.intro

/-- Never to be retold as "the part with a kept state is simulated". Conditional: hgs, hsg, hk, hr,
hb: see the head. **The sentence at the seated `keepPart`, at every job, entry sentence and
budget.** -/
theorem exact_keepPart_lift (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (see : V → V') (wit : W → W')
    (get : X → Y × Option K) (set : X → Y × Option K → X) (hgs : ∀ x y, get (set x y) = y)
    (hsg : ∀ x, set x (get x) = x) (name endName : String) (J : KeepJob W' Y K)
    (hk : shapeOk J.base.shape = true) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.base.shape) rs) (hb : betaMarked J.base.shape rs = true) (j : Nat)
    (a' : Addr) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, (keepPart (V := V') name endName J).lift see wit get set, sumSim a' J.base.shape⟩ :=
  exact_made_moves φ σ chain firstTree On bud see wit get set hgs hsg name endName J hk rs hr hb j
    a' ((keepPart (V := V') name endName J).moves.map (Move.lift wit get set))
    ((List.length_map _).trans (Keep.keepPart_rounds name endName J))
    fun c t t' seen q =>
      movesTo_mono (fun _ _ h => h.1) c _ _ t t' seen
        (keep_made_movesTo wit get set hgs J c t t' seen q)

/-- Conditional: as `exact_keepPart_lift`. The same where the part's last move passes on what g
says. -/
theorem exact_keepPart_lastHand_lift (φ : Face V W Pb) (σ : Side S Cl V W X Pb)
    (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (see : V → V') (wit : W → W')
    (get : X → Y × Option K) (set : X → Y × Option K → X) (hgs : ∀ x y, get (set x y) = y)
    (hsg : ∀ x, set x (get x) = x) (name endName : String) (J : KeepJob W' Y K)
    (hk : shapeOk J.base.shape = true) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.base.shape) rs) (hb : betaMarked J.base.shape rs = true) (j : Nat)
    (a' : Addr) (g : State W' (Y × Option K) → Y × Option K) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, ((keepPart (V := V') name endName J).lastHand g).lift see wit get set,
        sumSim a' J.base.shape⟩ :=
  exact_made_moves φ σ chain firstTree On bud see wit get set hgs hsg name endName J hk rs hr hb j
    a' ((lastHandMoves g (keepPart (V := V') name endName J).moves).map (Move.lift wit get set))
    ((List.length_map _).trans ((lastHandMoves_len g _).trans
      (Keep.keepPart_rounds name endName J)))
    fun c t t' seen q =>
      Eq.mpr
        (congrArg
          (fun z => MovesTo c (fun (a : State W X) (b : State W X) => a.input = b.input)
            ((sumPart (V := V') name endName (made J)).moves.map
              (Move.lift wit (fun x => (get x).1) fun x y => set x (y, (get x).2))) z t t' seen)
          (lastHandMoves_lift wit get set g (keepPart (V := V') name endName J).moves))
        (movesTo_lastHand c _ _ _ _ t t' seen (keep_made_movesTo wit get set hgs J c t t' seen q))

/-! ## 5 A part of one move that sends nothing -/

/-- Conditional: hrs: one declared round, which states nothing. **The sentence at a seated part of
one move that sends nothing, whatever it passes on.** -/
theorem exact_quietLay_lift (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (a : Addr) (see : V → V') (wit : W → W')
    (get : X → Y) (set : X → Y → X) (g : State W' Y → Y) (hrs : statedOf rs = [([], [])]) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, (quietLay g : Part V' W' Y).lift see wit get set, quietSim a 1⟩ :=
  exactMember_pre φ σ σ rfl
    ⟨j, rs, (quietPart 1 : Part V' W' Y).lift see wit get set, quietSim a 1⟩
    ((quietLay g : Part V' W' Y).moves.map (Move.lift wit get set))
    (fun t t' => t.input = t'.input) (fun _ _ h => h) rfl (stated_quiet (n := 1) hrs).1
    (fun _ _ _ _ h => ⟨fun _ => rfl, fun _ _ => h⟩) chain firstTree (fun _ _ _ _ => True) On bud
    (fun _ m' _ _ => ⟨m', rfl, rfl, rfl, True.intro⟩)
    (quietPart_exact_lift φ σ chain firstTree (fun _ _ _ _ => True) bud j 1 rs a see wit get set
      hrs)

end ProofFile.Honest.AlikeFields

#print axioms ProofFile.Honest.AlikeFields.movesTo_mono
#print axioms ProofFile.Honest.AlikeFields.movesTo_lastHand
#print axioms ProofFile.Honest.AlikeFields.lastHandMoves_len
#print axioms ProofFile.Honest.AlikeFields.lastHandMoves_lift
#print axioms ProofFile.Honest.AlikeFields.made_faithful
#print axioms ProofFile.Honest.AlikeFields.keepPart_made
#print axioms ProofFile.Honest.AlikeFields.exactMember_pre
#print axioms ProofFile.Honest.AlikeFields.exact_made_moves
#print axioms ProofFile.Honest.AlikeFields.keep_made_movesTo
#print axioms ProofFile.Honest.AlikeFields.exact_keepPart_lift
#print axioms ProofFile.Honest.AlikeFields.exact_keepPart_lastHand_lift
#print axioms ProofFile.Honest.AlikeFields.exact_quietLay_lift
