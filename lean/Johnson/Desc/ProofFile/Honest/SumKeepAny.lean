-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumKeepAny.lean: two facts about the masked sumcheck's part with a
kept state (`keepPart`, Honest/SumKeep.lean). First: whatever kept state is there before the part,
the part shows the same rounds and leaves the same state as from no kept state. Second: a state is
kept: after every round of the part but the last, the state holds the kept state computed from the
start.
Lemmas with their proofs, and one definition that they need.

How it relates to its neighbours. The lemmas of Honest/SumKeepLaw.lean and Honest/SumKeepPlays.lean
start at a state `(x, none)`. Here they are carried over to `(x, o)` for every `o`: the part's first
message does not read the kept state, and what is passed on after the first round does not depend on
it. So whoever places the part in a list of parts need not prove that no kept state is there. The
second fact is not implied by those lemmas: they would hold as well of a part that never passes a
kept state on and computes it again in every round. What the part is handed before its rounds
(`Seen`, Honest/Frame.lean: the rounds shown and the columns opened) is a bound letter in
every lemma that names it, the same value on both sides; `play_keep_any` starts at a state of the
run that shows it.

  1  `restGs`, `sumGs_cons`, `pass_zero`   the part's first move and the others; what is passed on
     after the first round
  2  `aloneFrom_any`, `fitsFrom_any`, `playedFrom_any`, `stateFrom_any`   the moves at `(x, o)` and
     at `(x, none)`
  3  `alone_keep_any`, `fits_keep_any`, `played_keep_any`, `state_keep_any`, `play_keep_any`   the
     lemmas about the part, at every `o`
  4  `pass_some`, `stateFrom_some`, `withPass_take`, `kept_keep`   a state is kept

Limits.
  * `kept_keep` says which value the state holds. It says nothing about the cost of a run.
  * As in Honest/SumKeepLaw.lean, the hypothesis `KeepJob.FaithfulOn` has to be proved by whoever
    supplies the job. It is asked at every `Front`, so at every value of the columns opened too: a
    job whose `round`, `inY` or `ends` depends on `Front.seen` where `Ok` holds cannot meet it.
    `state_keep_any` and `kept_keep` do not need it.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeepPlays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Keep
open OnBytes (E zeroE)
open VerifiableInference.Desc (Oracle)
open ProofFile.Honest.SumLaw

variable {V W X K : Type}

/-! ## 1 The first move and the others -/

/-- What the part's moves after the first say. -/
def restGs (name endName : String) (J : SumJob W X) :
    List (SumCoins name endName J → Seen → State W X → List E) :=
  ((List.range J.shape.vs.length).map fun i => askG name endName J (saidVar J i) (i + 1)) ++
    ((J.shape.ends.map fun e =>
      [askG name endName J (saidY J e) (J.shape.vs.length + 1),
        askG name endName J (saidEnds J e) (J.shape.vs.length + 2)]).getD [])

theorem sumGs_cons (name endName : String) (J : SumJob W X) :
    sumGs name endName J = askG name endName J (saidFirst J) 0 :: restGs name endName J :=
  rfl

/-- What is passed on after the first round does not depend on the kept state before it. -/
theorem pass_zero (J : KeepJob W X K) (w : W) (l : List Fmt.Drawn) (x : X) (o : Option K) :
    J.pass 0 ⟨w, l, (x, o)⟩ = J.pass 0 ⟨w, l, (x, none)⟩ := by
  by_cases h1 : (0 + 1 == (scalarsOf J.base.shape).length) = true
  · exact (if_pos h1).trans (if_pos h1).symm
  · exact ((if_neg h1).trans (if_neg (Nat.not_lt_zero _))).trans
      ((if_neg h1).trans (if_neg (Nat.not_lt_zero _))).symm

/-! ## 2 The moves at any kept state -/

section
variable (J : KeepJob W X K) {name endName : String} (c : SumCoins name endName J.base)
  (gs : List (SumCoins name endName J.job → Seen → State W (X × Option K) → List E))
  (w : W) (h : List Fmt.Drawn) (x : X) (o : Option K) (seen : Seen)

theorem aloneFrom_any (ds : List Fmt.Drawn) :
    aloneFrom (C := SumCoins name endName J.base) c
        (withPass J.pass 0 ((askG name endName J.job (saidFirst J.job) 0 :: gs).map mvOf))
        ⟨w, h, (x, o)⟩ seen ds =
      aloneFrom (C := SumCoins name endName J.base) c
        (withPass J.pass 0 ((askG name endName J.job (saidFirst J.job) 0 :: gs).map mvOf))
        ⟨w, h, (x, none)⟩ seen ds := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    show (aloneFrom (C := SumCoins name endName J.base) c (withPass J.pass (0 + 1) (gs.map mvOf))
        ⟨w, h ++ [d], J.pass 0 ⟨w, h ++ [d], (x, o)⟩⟩
        (seen.plus
            [rvSaid (askG name endName J.job (saidFirst J.job) 0 c seen ⟨w, h, (x, none)⟩) d])
        ds).map
          (rvSaid (askG name endName J.job (saidFirst J.job) 0 c seen ⟨w, h, (x, none)⟩) d :: ·) = _
    rw [pass_zero]
    rfl

theorem fitsFrom_any (rs : List (Fmt.DeclaredRound × List Oracle)) (ds : List Fmt.Drawn) :
    fitsFrom (C := SumCoins name endName J.base) c rs
        (withPass J.pass 0 ((askG name endName J.job (saidFirst J.job) 0 :: gs).map mvOf))
        ⟨w, h, (x, o)⟩ seen ds =
      fitsFrom (C := SumCoins name endName J.base) c rs
        (withPass J.pass 0 ((askG name endName J.job (saidFirst J.job) 0 :: gs).map mvOf))
        ⟨w, h, (x, none)⟩ seen ds := by
  cases rs with
  | nil => cases ds <;> rfl
  | cons r rs =>
    cases ds with
    | nil => rfl
    | cons d ds =>
      show ((sayE (askG name endName J.job (saidFirst J.job) 0 c seen ⟨w, h, (x, none)⟩)).fits r.1
          r.2 &&
        fitsFrom (C := SumCoins name endName J.base) c rs (withPass J.pass (0 + 1) (gs.map mvOf))
          ⟨w, h ++ [d], J.pass 0 ⟨w, h ++ [d], (x, o)⟩⟩
          (seen.plus
            [rvSaid (askG name endName J.job (saidFirst J.job) 0 c seen ⟨w, h, (x, none)⟩) d])
          ds) = _
      rw [pass_zero]
      rfl

theorem playedFrom_any (nm : String) (ad : Addr) (ds : List Fmt.Drawn) :
    playedFrom (C := SumCoins name endName J.base) nm ad c
        (withPass J.pass 0 ((askG name endName J.job (saidFirst J.job) 0 :: gs).map mvOf))
        ⟨w, h, (x, o)⟩ seen ds =
      playedFrom (C := SumCoins name endName J.base) nm ad c
        (withPass J.pass 0 ((askG name endName J.job (saidFirst J.job) 0 :: gs).map mvOf))
        ⟨w, h, (x, none)⟩ seen ds := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    show (playedFrom (C := SumCoins name endName J.base) nm ad c
        (withPass J.pass (0 + 1) (gs.map mvOf))
        ⟨w, h ++ [d], J.pass 0 ⟨w, h ++ [d], (x, o)⟩⟩
        (seen.plus
            [rvSaid (askG name endName J.job (saidFirst J.job) 0 c seen ⟨w, h, (x, none)⟩) d])
        ds).map
          ((⟨nm, ad.place, ad.part, true,
            (sayE (askG name endName J.job (saidFirst J.job) 0 c seen
              ⟨w, h, (x, none)⟩)).vals.map Said.got,
            (sayE (askG name endName J.job (saidFirst J.job) 0 c seen
              ⟨w, h, (x, none)⟩)).tables.map some, d⟩ : Played) :: ·) = _
    rw [pass_zero]
    rfl

theorem stateFrom_any (ds : List Fmt.Drawn) (hd : ds ≠ []) :
    stateFrom (C := SumCoins name endName J.base)
        (withPass J.pass 0 ((askG name endName J.job (saidFirst J.job) 0 :: gs).map mvOf))
        ⟨w, h, (x, o)⟩ ds =
      stateFrom (C := SumCoins name endName J.base)
        (withPass J.pass 0 ((askG name endName J.job (saidFirst J.job) 0 :: gs).map mvOf))
        ⟨w, h, (x, none)⟩ ds := by
  cases ds with
  | nil => exact absurd rfl hd
  | cons d ds =>
    show stateFrom (C := SumCoins name endName J.base) (withPass J.pass (0 + 1) (gs.map mvOf))
      ⟨w, h ++ [d], J.pass 0 ⟨w, h ++ [d], (x, o)⟩⟩ ds = _
    rw [pass_zero]
    rfl

end

/-! ## 3 The part at any kept state -/

/-- **The rounds are `sumPart`'s, whatever kept state is there before the part.** -/
theorem alone_keep_any (name endName : String) (J : KeepJob W X K)
    (Ok : W → List Fmt.Drawn → X → Prop) (hJ : J.FaithfulOn Ok) (c : SumCoins name endName J.base)
    (w : W) (h : List Fmt.Drawn) (x : X) (o : Option K) (hOk : Ok w h x) (seen : Seen)
    (ds : List Fmt.Drawn) :
    alone (keepPart (V := V) name endName J) c ⟨w, h, (x, o)⟩ seen ds =
      alone (sumPart (V := V) name endName J.base) c ⟨w, h, x⟩ seen ds := by
  refine Eq.trans ?_ (alone_keep_on (V := V) name endName J Ok hJ c w h x hOk seen ds)
  show aloneFrom (C := SumCoins name endName J.base) c (keepPart (V := V) name endName J).moves
      ⟨w, h, (x, o)⟩ seen ds =
    aloneFrom (C := SumCoins name endName J.base) c (keepPart (V := V) name endName J).moves
      ⟨w, h, (x, none)⟩ seen ds
  rw [keepPart_moves, sumGs_cons]
  exact aloneFrom_any J c _ w h x o seen ds

/-- **The test on the messages' shapes**, at any kept state. -/
theorem fits_keep_any (name endName : String) (J : KeepJob W X K)
    (Ok : W → List Fmt.Drawn → X → Prop) (hJ : J.FaithfulOn Ok) (c : SumCoins name endName J.base)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (w : W) (h : List Fmt.Drawn) (x : X) (o : Option K)
    (hOk : Ok w h x) (seen : Seen) (ds : List Fmt.Drawn) :
    fitsFrom (C := SumCoins name endName J.base) c rs (keepPart (V := V) name endName J).moves
        ⟨w, h, (x, o)⟩ seen ds =
      fitsFrom (C := SumCoins name endName J.base) c rs
        (sumPart (V := V) name endName J.base).moves ⟨w, h, x⟩ seen ds := by
  refine Eq.trans ?_ (fits_keep_on (V := V) name endName J Ok hJ c rs w h x hOk seen ds)
  rw [keepPart_moves, sumGs_cons]
  exact fitsFrom_any J c _ w h x o seen rs ds

/-- **The rounds as played**, at any kept state. -/
theorem played_keep_any (name endName : String) (J : KeepJob W X K)
    (Ok : W → List Fmt.Drawn → X → Prop) (hJ : J.FaithfulOn Ok) (c : SumCoins name endName J.base)
    (nm : String) (ad : Addr) (w : W) (h : List Fmt.Drawn) (x : X) (o : Option K) (hOk : Ok w h x)
    (seen : Seen) (ds : List Fmt.Drawn) :
    playedFrom (C := SumCoins name endName J.base) nm ad c
        (keepPart (V := V) name endName J).moves ⟨w, h, (x, o)⟩ seen ds =
      playedFrom (C := SumCoins name endName J.base) nm ad c
        (sumPart (V := V) name endName J.base).moves ⟨w, h, x⟩ seen ds := by
  refine Eq.trans ?_ (played_keep_on (V := V) name endName J Ok hJ c nm ad w h x hOk seen ds)
  rw [keepPart_moves, sumGs_cons]
  exact playedFrom_any J c _ w h x o seen nm ad ds

/-- A call has at least one round. -/
theorem rounds_pos (name endName : String) (J : SumJob W X) :
    (scalarsOf J.shape).length = (restGs name endName J).length + 1 := by
  exact (sumGs_rounds name endName J).symm.trans
    (congrArg List.length (sumGs_cons name endName J))

/-- **After the part no kept state is left**, whatever kept state was there before it. No hypothesis
on the job. -/
theorem state_keep_any (name endName : String) (J : KeepJob W X K) (w : W) (h : List Fmt.Drawn)
    (x : X) (o : Option K) (ds : List Fmt.Drawn)
    (hl : ds.length = (scalarsOf J.base.shape).length) :
    stateFrom (keepPart (V := V) name endName J).moves ⟨w, h, (x, o)⟩ ds =
      ⟨w, h ++ ds, (x, none)⟩ := by
  have hd : ds ≠ [] := by
    intro e
    rw [e, rounds_pos name endName J.base] at hl
    exact Nat.succ_ne_zero _ hl.symm
  refine Eq.trans ?_ (state_keep (V := V) name endName J w h x ds hl)
  rw [keepPart_moves, sumGs_cons]
  exact stateFrom_any J (name := name) (endName := endName) _ w h x o ds hd

/-- **`play` on the part's rounds**, at any kept state. The columns opened (`seen.opened`) stay as
they were. -/
theorem play_keep_any (name endName : String) (J : KeepJob W X K)
    (Ok : W → List Fmt.Drawn → X → Prop) (hJ : J.FaithfulOn Ok) (c : SumCoins name endName J.base)
    (nm : String) (ad : Addr) (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (w : W)
    (h : List Fmt.Drawn) (x : X) (o : Option K) (hOk : Ok w h x) (loc : List Fmt.Drawn)
    (seen : Seen) (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (l : List Played)
    (hf : fitsFrom (C := SumCoins name endName J.base) c rs
      (sumPart (V := V) name endName J.base).moves ⟨w, h, x⟩ seen ds = true)
    (hp : playedFrom (C := SumCoins name endName J.base) nm ad c
      (sumPart (V := V) name endName J.base).moves ⟨w, h, x⟩ seen ds = some l) :
    play ((keepPart (V := V) name endName J).steps nm ad rs v c) ds back
        ⟨⟨w, h, (x, o)⟩, loc, seen.rounds, seen.opened⟩ =
      .ok (l, ⟨⟨w, h ++ ds, (x, none)⟩, loc ++ ds, seen.rounds ++ roundsOf l, seen.opened⟩) := by
  have hl : ds.length = (scalarsOf J.base.shape).length :=
    (fits_lengths c rs _ _ seen ds hf).2.trans (sumPart_rounds name endName J.base)
  have f' := (fits_keep_any (V := V) name endName J Ok hJ c rs w h x o hOk seen ds).trans hf
  have p' := (played_keep_any (V := V) name endName J Ok hJ c nm ad w h x o hOk seen ds).trans hp
  have q := play_steps_whole (keepPart (V := V) name endName J) (fun _ _ => rfl)
    (fun _ _ _ => rfl) nm ad rs v c ds back ⟨⟨w, h, (x, o)⟩, loc, seen.rounds, seen.opened⟩ l f' p'
  refine q.trans ?_
  show (Except.ok (l, (⟨stateFrom (keepPart (V := V) name endName J).moves ⟨w, h, (x, o)⟩ ds,
    loc ++ ds, seen.rounds ++ roundsOf l, seen.opened⟩ : Mid W (X × Option K))) :
      Except Refusal (List Played × Mid W (X × Option K))) = _
  rw [state_keep_any name endName J w h x o ds hl]

/-! ## 4 A state is kept -/

/-- **After a round that is not the part's last, the kept state computed from the start is passed
on**: after the first round whatever was there; after a later round where the kept state before it
was the one computed from the start. -/
theorem pass_some (J : KeepJob W X K) (w : W) (H : List Fmt.Drawn) (x : X) (n : Nat)
    (own : List Fmt.Drawn) (d : Fmt.Drawn) (k : Option K) (ho : own.length = n)
    (hN : n + 1 ≠ (scalarsOf J.base.shape).length)
    (hk : n = 0 ∨ k = some (J.madeAt w H x (varsAt J own))) :
    J.pass n ⟨w, (H ++ own) ++ [d], (x, k)⟩ =
      (x, some (J.madeAt w H x (varsAt J (own ++ [d])))) := by
  have h1 : ¬ (n + 1 == (scalarsOf J.base.shape).length) = true := fun e => hN (beq_iff_eq.1 e)
  have key : ∀ k₀ : Option K, Kept J w H x own k₀ → (k₀ = none → ¬ J.base.shape.vs.length < n) →
      J.pass n ⟨w, (H ++ own) ++ [d], (x, k₀)⟩ =
        (x, some (J.madeAt w H x (varsAt J (own ++ [d])))) := by
    intro k₀ hk₀ hz
    obtain ⟨k', hp, hk'⟩ := pass_kept J w H x n own d k₀ ho hk₀
    rw [hp]
    rcases hk' with e | e
    · exfalso
      subst e
      by_cases h2 : J.base.shape.vs.length < n
      · have q : J.pass n ⟨w, (H ++ own) ++ [d], (x, k₀)⟩ = (x, k₀) :=
          (if_neg h1).trans (if_pos h2)
        have r := congrArg Prod.snd (q.symm.trans hp)
        exact hz r h2
      · have q : J.pass n ⟨w, (H ++ own) ++ [d], (x, k₀)⟩ = (x, some _) :=
          (if_neg h1).trans (if_neg h2)
        have r := congrArg Prod.snd (q.symm.trans hp)
        exact Option.some_ne_none _ r
    · rw [e]
  rcases hk with e | e
  · subst e
    rw [pass_zero]
    exact key none (Or.inl rfl) (fun _ => Nat.not_lt_zero _)
  · subst e
    exact key _ (Or.inr rfl) (fun r => absurd r (Option.some_ne_none _))

/-- Moves none of which is the part's last: after them the state holds the kept state computed from
the start. -/
theorem stateFrom_some (J : KeepJob W X K) {C : Type} (w : W) (H : List Fmt.Drawn) (x : X) :
    ∀ (l : List (Move C W (X × Option K))) (n : Nat) (own : List Fmt.Drawn) (k : Option K)
      (ds : List Fmt.Drawn), l.length = ds.length → own.length = n →
      n + l.length < (scalarsOf J.base.shape).length →
      (k = some (J.madeAt w H x (varsAt J own)) ∨ (n = 0 ∧ l ≠ [])) →
      stateFrom (withPass J.pass n l) ⟨w, H ++ own, (x, k)⟩ ds =
        ⟨w, H ++ (own ++ ds), (x, some (J.madeAt w H x (varsAt J (own ++ ds))))⟩
  | [], _, own, k, [], _, _, _, hk => by
    have e : k = some (J.madeAt w H x (varsAt J own)) := by
      rcases hk with e | e
      · exact e
      · exact absurd rfl e.2
    subst e
    show (⟨w, H ++ own, (x, some (J.madeAt w H x (varsAt J own)))⟩ : State W (X × Option K)) = _
    rw [List.append_nil]
  | mv :: l, n, own, k, d :: ds, hl, ho, hn, hk => by
    have a1 : l.length = ds.length := by
      simp only [List.length_cons] at hl
      omega
    have a2 : n + 1 + l.length < (scalarsOf J.base.shape).length := by
      simp only [List.length_cons] at hn
      omega
    have a3 : n + 1 ≠ (scalarsOf J.base.shape).length := by
      simp only [List.length_cons] at hn
      omega
    have a4 : (own ++ [d]).length = n + 1 := by
      rw [List.length_append, ho]
      rfl
    have a5 : n = 0 ∨ k = some (J.madeAt w H x (varsAt J own)) := by
      rcases hk with e | e
      · exact Or.inr e
      · exact Or.inl e.1
    show stateFrom (withPass J.pass (n + 1) l)
      ⟨w, (H ++ own) ++ [d], J.pass n ⟨w, (H ++ own) ++ [d], (x, k)⟩⟩ ds = _
    rw [pass_some J w H x n own d k ho a3 a5, List.append_assoc H,
      stateFrom_some J w H x l (n + 1) (own ++ [d]) _ ds a1 a4 a2 (Or.inl rfl),
      List.append_assoc own]
    rfl
  | [], _, _, _, _ :: _, hl, _, _, _ => by
    simp only [List.length_cons, List.length_nil] at hl
    omega
  | _ :: _, _, _, _, [], hl, _, _, _ => by
    simp only [List.length_cons, List.length_nil] at hl
    omega

theorem withPass_take {C Y : Type} (pass : Nat → State W Y → Y) :
    ∀ (m n : Nat) (l : List (Move C W Y)),
      (withPass pass n l).take m = withPass pass n (l.take m)
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | m + 1, n, mv :: l =>
    congrArg ((⟨mv.say, pass n⟩ : Move C W Y) :: ·) (withPass_take pass m (n + 1) l)

/-- **A state is kept.** After as many rounds of the part as `ds` has challenges, at least one and
fewer than the part has rounds, the state holds the kept state computed from the start, at the
variables' challenges so far; whatever kept state was there before the part. No hypothesis on the
job. -/
theorem kept_keep (name endName : String) (J : KeepJob W X K) (w : W) (h : List Fmt.Drawn) (x : X)
    (o : Option K) (ds : List Fmt.Drawn) (h0 : 0 < ds.length)
    (hN : ds.length < (scalarsOf J.base.shape).length) :
    stateFrom ((keepPart (V := V) name endName J).moves.take ds.length) ⟨w, h, (x, o)⟩ ds =
      ⟨w, h ++ ds, (x, some (J.madeAt w h x (varsAt J ds)))⟩ := by
  have hg : ((sumGs name endName J.job).map mvOf).length = (scalarsOf J.base.shape).length := by
    rw [List.length_map]
    exact sumGs_rounds name endName J.job
  have ht : (((sumGs name endName J.job).map mvOf).take ds.length).length = ds.length := by
    rw [List.length_take, hg]
    exact Nat.min_eq_left (Nat.le_of_lt hN)
  have hne : ((sumGs name endName J.job).map mvOf).take ds.length ≠ [] := by
    intro e
    rw [e] at ht
    simp only [List.length_nil] at ht
    omega
  have q := stateFrom_some J w h x (((sumGs name endName J.job).map mvOf).take ds.length) 0 [] o ds
    ht rfl (by rw [ht, Nat.zero_add]; exact hN) (Or.inr ⟨rfl, hne⟩)
  rw [List.append_nil, List.nil_append] at q
  have e := withPass_take J.pass ds.length 0 ((sumGs name endName J.job).map mvOf)
  rw [keepPart_moves]
  exact (congrArg (fun l : List (Move (SumCoins name endName J.job) W (X × Option K)) =>
    stateFrom l ⟨w, h, (x, o)⟩ ds) e).trans q

end ProofFile.Honest.Keep

#print axioms ProofFile.Honest.Keep.pass_zero
#print axioms ProofFile.Honest.Keep.alone_keep_any
#print axioms ProofFile.Honest.Keep.fits_keep_any
#print axioms ProofFile.Honest.Keep.played_keep_any
#print axioms ProofFile.Honest.Keep.state_keep_any
#print axioms ProofFile.Honest.Keep.play_keep_any
#print axioms ProofFile.Honest.Keep.pass_some
#print axioms ProofFile.Honest.Keep.stateFrom_some
#print axioms ProofFile.Honest.Keep.kept_keep
#print axioms ProofFile.Honest.Keep.sumGs_cons
#print axioms ProofFile.Honest.Keep.aloneFrom_any
#print axioms ProofFile.Honest.Keep.fitsFrom_any
#print axioms ProofFile.Honest.Keep.playedFrom_any
#print axioms ProofFile.Honest.Keep.stateFrom_any
#print axioms ProofFile.Honest.Keep.rounds_pos
#print axioms ProofFile.Honest.Keep.withPass_take
#print axioms ProofFile.Honest.Keep.restGs
