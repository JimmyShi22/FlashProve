-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumKeepLift.lean: the masked sumcheck's part with a kept state
(`keepPart`, Honest/SumKeep.lean), placed in a wider input and state by `Part.lift`
(Honest/Frame.lean). `play` on its rounds returns the rounds that `sumPart` at the earlier job plays
at the narrowed state, and the wide state after it is known. Lemmas with their proofs.

How it relates to its neighbours. `plays_lift_sumPart` (Honest/SumLaw/PlaysSum.lean) is the same
statement for `sumPart`. Its proof uses that every move of `sumPart` passes on what it was given
(`lift_stateFrom_same`, Honest/SumLaw/Lift.lean). The moves of `keepPart` do not, so the wide state
needs a proof of its own, and one more hypothesis about `get` and `set`. The two lemmas on `play`
stand at every state of the run `m`: the part is handed what `m` shows (`Mid.shown`: its rounds
and its columns opened), and `sumPart`'s two premises are asked at that same value.

The three hypotheses about `get` and `set`.
  * `get (set x y) = y`: what was put is what is read.
  * `set (set x a) b = set x b`: the second put overwrites the first. Without it the wide state
    after the part is not determined: take pairs of a value and a number, let `get` read the value,
    and let `set` raise the number whenever the value changes. The first and the third hypothesis
    hold, and the number has changed after the part.
  * `set x (get x) = x`: putting what was read changes nothing. It is needed only for
    `plays_lift_keep_same`.
For a field of a structure, with `set` the structure update, all three hold by `rfl`.

  1  `lift_own_from`, `lift_own`   what lifted moves pass on, in the wide state
  2  `withPass_length`, `keepPart_rounds`, `state_keep_lift`   the wide state after the lifted part
  3  `plays_lift_keep`, `plays_lift_keep_same`   `play` on the lifted part's rounds

Limits.
  * The hypotheses about `get` and `set`, `KeepJob.FaithfulOn` and `Ok` at the narrowed state have
    to be proved by whoever places the part.
  * One part's rounds. Lists of several parts are joined by `play_append` (Honest/Law/Play.lean).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeepAny
import Johnson.Desc.ProofFile.Honest.SumLaw.Lift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Keep
open OnBytes (E)
open VerifiableInference.Desc (Oracle)
open ProofFile.Honest.SumLaw

variable {V V' W W' X Y K C : Type}

/-! ## 1 What lifted moves pass on -/

/-- From a wide state whose passed-on value is `set x₀ y`: after lifted moves it is `set x₀` of what
the moves themselves pass on from `y`. -/
theorem lift_own_from (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (hss : ∀ x a b, set (set x a) b = set x b) (x₀ : X) :
    ∀ (mvs : List (Move C W' Y)) (i : W) (hd : List Fmt.Drawn) (y : Y) (ds : List Fmt.Drawn),
      (stateFrom (mvs.map (Move.lift wit get set)) ⟨i, hd, set x₀ y⟩ ds).own =
        set x₀ (stateFrom mvs ⟨wit i, hd, y⟩ ds).own
  | [], _, _, _, _ => rfl
  | _ :: _, _, _, _, [] => rfl
  | mv :: mvs, i, hd, y, d :: ds => by
    show (stateFrom (mvs.map (Move.lift wit get set))
        ⟨i, hd ++ [d], set (set x₀ y) (mv.hand ⟨wit i, hd ++ [d], get (set x₀ y)⟩)⟩ ds).own =
      set x₀ (stateFrom mvs ⟨wit i, hd ++ [d], mv.hand ⟨wit i, hd ++ [d], y⟩⟩ ds).own
    rw [hss, hgs]
    exact lift_own_from wit get set hgs hss x₀ mvs i (hd ++ [d]) _ ds

/-- **What lifted moves pass on**: `set`, at the wide value before them, of what the moves
themselves pass on from the narrowed state. At least one move and one challenge. -/
theorem lift_own (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (hss : ∀ x a b, set (set x a) b = set x b) :
    ∀ (mvs : List (Move C W' Y)) (t : State W X) (ds : List Fmt.Drawn), mvs ≠ [] → ds ≠ [] →
      (stateFrom (mvs.map (Move.lift wit get set)) t ds).own =
        set t.own (stateFrom mvs (t.narrow wit get) ds).own
  | mv :: mvs, t, d :: ds, _, _ => by
    show (stateFrom (mvs.map (Move.lift wit get set))
        ⟨t.input, t.heard ++ [d],
          set t.own (mv.hand ⟨wit t.input, t.heard ++ [d], get t.own⟩)⟩ ds).own =
      set t.own (stateFrom mvs
        ⟨wit t.input, t.heard ++ [d], mv.hand ⟨wit t.input, t.heard ++ [d], get t.own⟩⟩ ds).own
    exact lift_own_from wit get set hgs hss t.own mvs t.input (t.heard ++ [d]) _ ds
  | [], _, _, h, _ => absurd rfl h
  | _ :: _, _, [], _, h => absurd rfl h

/-! ## 2 The wide state after the lifted part -/

theorem withPass_length (pass : Nat → State W Y → Y) :
    ∀ (n : Nat) (l : List (Move C W Y)), (withPass pass n l).length = l.length
  | _, [] => rfl
  | n, _ :: l => congrArg (· + 1) (withPass_length pass (n + 1) l)

/-- The part has as many moves as its call has rounds. -/
theorem keepPart_rounds (name endName : String) (J : KeepJob W X K) :
    (keepPart (V := V) name endName J).moves.length = (scalarsOf J.base.shape).length := by
  have e : (withPass J.pass 0 ((sumGs name endName J.job).map mvOf)).length =
      (scalarsOf J.base.shape).length := by
    rw [withPass_length, List.length_map]
    exact sumGs_rounds name endName J.job
  rw [keepPart_moves]
  exact e

/-- **The wide state after the lifted part**: the part's own challenges are heard, and the wide
passed-on value is `set`, at the value before the part, of the narrowed value's first component and
no kept state. -/
theorem state_keep_lift (wit : W → W') (get : X → Y × Option K) (set : X → Y × Option K → X)
    (hgs : ∀ x y, get (set x y) = y) (hss : ∀ x a b, set (set x a) b = set x b)
    (name endName : String) (J : KeepJob W' Y K) (t : State W X) (ds : List Fmt.Drawn)
    (hl : ds.length = (scalarsOf J.base.shape).length) :
    stateFrom ((keepPart (V := V') name endName J).moves.map (Move.lift wit get set)) t ds =
      ⟨t.input, t.heard ++ ds, set t.own ((get t.own).1, none)⟩ := by
  have hp := rounds_pos name endName J.base
  have hm : (keepPart (V := V') name endName J).moves.length = ds.length :=
    (keepPart_rounds name endName J).trans hl.symm
  have hd : ds ≠ [] := by
    intro e
    rw [e] at hl
    simp only [List.length_nil] at hl
    omega
  have hne : (keepPart (V := V') name endName J).moves ≠ [] := by
    intro e
    rw [e] at hm
    simp only [List.length_nil] at hm
    omega
  have hm' : ((keepPart (V := V') name endName J).moves.map (Move.lift wit get set)).length =
      ds.length := by
    rw [List.length_map]
    exact hm
  have e1 := stateFrom_input ((keepPart (V := V') name endName J).moves.map
    (Move.lift wit get set)) t ds
  have e2 := stateFrom_heard ((keepPart (V := V') name endName J).moves.map
    (Move.lift wit get set)) t ds hm'
  have e4 : stateFrom (keepPart (V := V') name endName J).moves (t.narrow wit get) ds =
      ⟨wit t.input, t.heard ++ ds, ((get t.own).1, none)⟩ :=
    state_keep_any name endName J (wit t.input) t.heard (get t.own).1 (get t.own).2 ds hl
  have e3 : (stateFrom ((keepPart (V := V') name endName J).moves.map
      (Move.lift wit get set)) t ds).own = set t.own ((get t.own).1, none) :=
    (lift_own wit get set hgs hss _ t ds hne hd).trans
      (congrArg (fun s : State W' (Y × Option K) => set t.own s.own) e4)
  calc stateFrom ((keepPart (V := V') name endName J).moves.map (Move.lift wit get set)) t ds
      = ⟨(stateFrom ((keepPart (V := V') name endName J).moves.map
            (Move.lift wit get set)) t ds).input,
          (stateFrom ((keepPart (V := V') name endName J).moves.map
            (Move.lift wit get set)) t ds).heard,
          (stateFrom ((keepPart (V := V') name endName J).moves.map
            (Move.lift wit get set)) t ds).own⟩ := rfl
    _ = ⟨t.input, t.heard ++ ds, set t.own ((get t.own).1, none)⟩ := by rw [e1, e2, e3]

/-! ## 3 `play` on the lifted part's rounds -/

/-- **`play` on the rounds of the lifted part**: where `sumPart` at the earlier job, at the narrowed
state, passes the test on shapes and plays the rounds `l`, `play` returns `l`; whatever kept state
the narrowed state holds before the part. The columns opened (`Mid.opened`) stay as they were. -/
theorem plays_lift_keep (see : V → V') (wit : W → W') (get : X → Y × Option K)
    (set : X → Y × Option K → X) (hgs : ∀ x y, get (set x y) = y)
    (hss : ∀ x a b, set (set x a) b = set x b) (name endName : String) (J : KeepJob W' Y K)
    (Ok : W' → List Fmt.Drawn → Y → Prop) (hJ : J.FaithfulOn Ok)
    (c : SumCoins name endName J.base) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (l : List Played)
    (hOk : Ok (wit m.st.input) m.st.heard (get m.st.own).1)
    (hf : fitsFrom (C := SumCoins name endName J.base) c rs
      (sumPart (V := V') name endName J.base).moves
      ⟨wit m.st.input, m.st.heard, (get m.st.own).1⟩ m.shown ds = true)
    (hp : playedFrom (C := SumCoins name endName J.base) nm a c
      (sumPart (V := V') name endName J.base).moves
      ⟨wit m.st.input, m.st.heard, (get m.st.own).1⟩ m.shown ds = some l) :
    play (((keepPart (V := V') name endName J).lift see wit get set).steps nm a rs v c) ds back m =
      .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, set m.st.own ((get m.st.own).1, none)⟩,
        m.loc ++ ds, m.seen ++ roundsOf l, m.opened⟩) := by
  have hl : ds.length = (scalarsOf J.base.shape).length :=
    (fits_lengths c rs _ _ m.shown ds hf).2.trans (sumPart_rounds name endName J.base)
  have f' : fitsFrom (C := SumCoins name endName J.base) c rs
      ((keepPart (V := V') name endName J).moves.map (Move.lift wit get set)) m.st m.shown ds =
      true :=
    (lift_fitsFrom wit get set hgs c rs _ m.st m.shown ds).trans
      ((fits_keep_any (V := V') name endName J Ok hJ c rs (wit m.st.input) m.st.heard
        (get m.st.own).1 (get m.st.own).2 hOk m.shown ds).trans hf)
  have p' : playedFrom (C := SumCoins name endName J.base) nm a c
      ((keepPart (V := V') name endName J).moves.map (Move.lift wit get set)) m.st m.shown ds =
      some l :=
    (lift_playedFrom wit get set hgs nm a c _ m.st m.shown ds).trans
      ((played_keep_any (V := V') name endName J Ok hJ c nm a (wit m.st.input) m.st.heard
        (get m.st.own).1 (get m.st.own).2 hOk m.shown ds).trans hp)
  have hst := state_keep_lift (V' := V') wit get set hgs hss name endName J m.st ds hl
  have q := play_steps_whole ((keepPart (V := V') name endName J).lift see wit get set)
    (fun _ _ => rfl) (fun _ _ _ => rfl) nm a rs v c ds back m l f' p'
  exact q.trans (by rw [← hst]; rfl)

/-- **The same, where no kept state is there before the part and putting what was read changes
nothing**: the wide passed-on value is unchanged. -/
theorem plays_lift_keep_same (see : V → V') (wit : W → W') (get : X → Y × Option K)
    (set : X → Y × Option K → X) (hgs : ∀ x y, get (set x y) = y)
    (hss : ∀ x a b, set (set x a) b = set x b) (hsg : ∀ x, set x (get x) = x)
    (name endName : String) (J : KeepJob W' Y K) (Ok : W' → List Fmt.Drawn → Y → Prop)
    (hJ : J.FaithfulOn Ok) (c : SumCoins name endName J.base) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (l : List Played) (h0 : (get m.st.own).2 = none)
    (hOk : Ok (wit m.st.input) m.st.heard (get m.st.own).1)
    (hf : fitsFrom (C := SumCoins name endName J.base) c rs
      (sumPart (V := V') name endName J.base).moves
      ⟨wit m.st.input, m.st.heard, (get m.st.own).1⟩ m.shown ds = true)
    (hp : playedFrom (C := SumCoins name endName J.base) nm a c
      (sumPart (V := V') name endName J.base).moves
      ⟨wit m.st.input, m.st.heard, (get m.st.own).1⟩ m.shown ds = some l) :
    play (((keepPart (V := V') name endName J).lift see wit get set).steps nm a rs v c) ds back m =
      .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds, m.seen ++ roundsOf l,
        m.opened⟩) := by
  have e0 : ((get m.st.own).1, (none : Option K)) = get m.st.own := Prod.ext rfl h0.symm
  have e : set m.st.own ((get m.st.own).1, none) = m.st.own := by rw [e0, hsg]
  have q := plays_lift_keep see wit get set hgs hss name endName J Ok hJ c nm a rs v ds back m l
    hOk hf hp
  rw [e] at q
  exact q

end ProofFile.Honest.Keep

#print axioms ProofFile.Honest.Keep.lift_own_from
#print axioms ProofFile.Honest.Keep.lift_own
#print axioms ProofFile.Honest.Keep.keepPart_rounds
#print axioms ProofFile.Honest.Keep.state_keep_lift
#print axioms ProofFile.Honest.Keep.plays_lift_keep
#print axioms ProofFile.Honest.Keep.plays_lift_keep_same
#print axioms ProofFile.Honest.Keep.withPass_length
