-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the attacker's (E2) at a run: the front's columns are treesL's.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/TreesL.lean: at a run of the frame's walking prover, at a
called second part of the first chain's last proximity test, the columns that the front lists of the
tree that the first round of positions opens are, at every listed position, the column of the job's
own tree (treesL, AtProof/JobL.lean): the clause trees of OnFreeTD, under the name TreesAt
(Sim2/Clauses.lean). The words of the first fresh mask's rows are among them: they come out of the
test's own state (fM, fT), and the tie is the sender's table against that state. This is the
attacker's clause on K12, with F_0's rows among the rows.

  finishPart, switch_says   the finish's part; what its first move says
  block_rounds_at_first, mid_back, switch_in_front   the tables of the finish's first round, as
                   played, in front of a later round of a walk
  freshWordOf, sameEntry, bookTiesAtFinish, bookTiesAtFinish_parts   a public test on the book
  cut_of_cut, stretches_same, lent_is_cut   what two lent entries of one run hand
  take_three, rows_count, tables_at   small facts
  trees_first      the statement
  bendColumns, treeCols_bendColumns, putColumn, trees_tooth   the tooth: a column laid anew at one
                   listed position fails the clause

By what. column_at_finish (Sim2/TreesLCol.lean); frame_at_first, played_at_first
(Sim/FrameAtFirst.lean); treeCols_first (Sim2/DoorTrue.lean); carryRows_by_carried, carried_asK2,
begins_runs (AtProof/SeamL.lean); lend_cut, carried_of_lendPart (CutOfBook.lean).

Limits.
- A conditional on a run: nothing here shows that ready or runC returns, or that the part is called.
- On the filling and the book: hgK, hT. On public numbers: hfit, hW, hos, hsrc, hj
  (Sim2/TreesLAt.lean pays all but where the finish stands, at the written plan). hT: under the
  stronger head (`P5J.AtMgA`, at the format's second hash function), where the maker returns, at its
  book, at the written finish and the two written places: ties_at_maker (Sim2/TreesLBook.lean).
- That the sender's text returns is no premise: it is read off the run, whose walk has gone on.
- The tooth is general in the job: it needs TreesAt to hold at the front that is bent.
- The clause reads the input and the carried values: no later law may take it as a hypothesis on a
  run and then speak of the random values as sampled anew.
- No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesLCol
import Johnson.Desc.ProofFile.Honest.K12.Sim2.Clauses
import Johnson.Desc.ProofFile.Honest.K12.Sim2.DoorTrue
import Johnson.Desc.ProofFile.Honest.K12.FirstPlayAtFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim.SenderInFront
import Johnson.Desc.ProofFile.Honest.Law.BackAt
import Johnson.Desc.ProofFile.Honest.Law.WalkMid
import Johnson.Desc.ProofFile.Honest.Law.RunMid
import Johnson.Desc.ProofFile.Honest.K12.LiveField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block FileDescription Oracle)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open Johnson.Prover.Send (col Rows)

/-! ## 1 The finish's first move -/

/-- The finish's one part, as its half lays it. -/
abbrev finishPart {W₀ Rc Xi Tr Y : Type} (Sd : K2.Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace) :
    Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y :=
  (K2.switchPart Sd p.sizes p.others p.foldVars p.carries).lift (fun _ => ())
    (K2.switchWit D readers closing p) (fun _ => ()) fun x _ => x

/-- What the first move of a switch's part says, where it returns. -/
theorem switch_says {W₀ Rc Xi Tr Y : Type} (Sd : K2.Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace)
    (c : (finishPart Sd D readers closing p : Part _ _ Y).Coins) (sn : Seen)
    (t : State (Local W₀ Rc Xi Tr) Y) :
    ∃ mv, (finishPart Sd D readers closing p : Part _ _ Y).moves[0]? = some mv ∧
      ∀ z, mv.say c sn t = .ok z →
        ∃ Dt Ts, K2.switchRowsAt p.sizes p.carries c.2.2
              (t.narrow (K2.switchWit D readers closing p) fun _ => ()) 0 = .ok Dt ∧
          Sd.tables p.sizes.codes (K2.switchSent p.sizes p.others)
              (K2.switchFresh p.sizes p.others p.foldVars) Dt c.1 = .ok Ts ∧
          z.tables = Ts := by
  refine ⟨_, rfl, fun z h => ?_⟩
  simp only [Move.lift] at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨Dt, e1, h⟩ := exBind_ok h
  obtain ⟨Ts, e2, e3⟩ := exMap_ok h
  subst e3
  exact ⟨Dt, Ts, e1, e2, rfl⟩

/-- The sub-protocol has as many rounds as the side that the prover's list holds at its place. -/
theorem block_rounds_at_first {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R)
    (pre : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl) (t : List (Block F.S₁ F.Cl))
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)
    (hg : (P.first.find? fun g => g.place == b.place) = some g) : g.rounds = b.rounds.length := by
  obtain ⟨-, tr, -, -, -, s1, -, -⟩ := ready_ok hR
  rw [hcut, chainSteps_append] at s1
  obtain ⟨l₁, h1, h2⟩ := exBind_ok s1
  obtain ⟨l', h3, e'⟩ := exMap_ok h2
  obtain ⟨ho, l₂, -, hcase⟩ := chainSteps_cons_ok h3
  rcases hcase with ⟨hn, -⟩ | ⟨g', c, hg', hr, -, -, -⟩
  · rw [hg] at hn
    cases hn
  · obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
    exact hr

/-- A run that goes on at the end of a walk went on at its start. -/
theorem mid_back {S Cl W Y : Type} (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L ss ds z = .ok z' → z'.mid.isSome = true → z.mid.isSome = true
  | [], [], z, z', h, hm => by
    rw [walk_nil_ok h] at hm
    exact hm
  | [], _ :: _, _, _, h, _ => by simp [walk] at h
  | _ :: _, [], _, _, h, _ => by simp [walk] at h
  | s :: ss, d :: ds, z, z', h, hm => by
    obtain ⟨x, z₁, hx, hz, hw⟩ := walk_cons_ok h
    have h1 := mid_back L ss ds z₁ z' hw hm
    obtain ⟨m, o, e1, -⟩ := heard_mid hz h1
    cases hz' : z.mid with
    | some m₀ => rfl
    | none =>
      rw [hz'] at e1
      cases e1

/-- **The tables of the finish's first round, as played, in front of a later round of the first
chain**: the twin of sender_in_front (Sim/SenderInFront.lean), at a walk. -/
theorem switch_in_front {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R)
    (pre : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl) (t : List (Block F.S₁ F.Cl))
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (hb : b.rounds ≠ [])
    (Sd : K2.Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (pl : K2.SwitchPlace)
    (hg : (P.first.find? fun g => g.place == b.place) =
      some ⟨pl.place, [finishPart Sd D readers closing pl]⟩)
    (n : ℕ) (hn : (pre.flatMap (·.rounds)).length < n) (L : Lay)
    (a₁ y : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) Y) (hal : a₁.laid = [])
    (hn₂ : n ≤ R.first.length)
    (hw : walk L (R.first.take n) (ρ.first.take n) a₁ = .ok y)
    (hsome : y.mid.isSome = true) :
    ∃ (zᵢ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) Y) (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (c : (finishPart Sd D readers closing pl : Part _ _ Y).Coins) (q : Played)
      (Dt : ℕ → ℕ → ℕ → Cb.Gl.E) (Ts : List Table),
      walk L (R.first.take (pre.flatMap (·.rounds)).length)
          (ρ.first.take (pre.flatMap (·.rounds)).length) a₁ = .ok zᵢ ∧
      zᵢ.mid = some mᵢ ∧
      lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨b.place, 0⟩ (finishPart Sd D readers closing pl) =
        .ok c ∧
      y.laid[(pre.flatMap (·.rounds)).length]? = some q ∧
      q.tables = Ts.map some ∧
      K2.switchRowsAt pl.sizes pl.carries c.2.2
          (mᵢ.st.narrow (K2.switchWit D readers closing pl) fun _ => ()) 0 = .ok Dt ∧
      Sd.tables pl.sizes.codes (K2.switchSent pl.sizes pl.others)
          (K2.switchFresh pl.sizes pl.others pl.foldVars) Dt c.1 = .ok Ts := by
  obtain ⟨c, l₁, l₂, hl, hsh, hl₁, hor⟩ := block_steps_at_first hR pre b t hcut _ hg
  obtain ⟨hlp, -⟩ := lendRow_cons_ok hl
  obtain ⟨d, ds, hd⟩ : ∃ d ds, b.rounds = d :: ds := by
    cases hr : b.rounds with
    | nil => exact absurd hr hb
    | cons d ds => exact ⟨d, ds, rfl⟩
  obtain ⟨o, os, ho⟩ : ∃ o os, b.oracles = o :: os := by
    cases hr : b.oracles with
    | nil =>
      rw [hr, hd] at hor
      cases hor
    | cons o os => exact ⟨o, os, rfl⟩
  have e1 : (⟨pl.place, [finishPart Sd D readers closing pl]⟩ :
      Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps b (Face.own.sees R.own) c =
      (finishPart Sd D readers closing pl : Part _ _ Y).steps b.name ⟨b.place, 0⟩
          ((b.rounds.zip b.oracles).take 2) (Face.own.sees R.own) c.1 ++ [] := rfl
  obtain ⟨s, rest, e2⟩ : ∃ s rest,
      (finishPart Sd D readers closing pl : Part _ _ Y).steps b.name ⟨b.place, 0⟩
          ((b.rounds.zip b.oracles).take 2) (Face.own.sees R.own) c.1 = s :: rest := by
    rw [hd, ho]
    exact ⟨_, _, rfl⟩
  have hs0 : ((finishPart Sd D readers closing pl : Part _ _ Y).steps b.name ⟨b.place, 0⟩
        ((b.rounds.zip b.oracles).take 2) (Face.own.sees R.own) c.1)[0]? = some s := by
    rw [e2]
    rfl
  have hs : (R.first.take n)[(pre.flatMap (·.rounds)).length]? = some s := by
    rw [List.getElem?_take_of_lt hn, hsh, e1, e2, ← hl₁,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  -- the cut of the walk
  have hlen := walk_len L _ _ a₁ y hw
  obtain ⟨hi, hsi⟩ := List.getElem?_eq_some_iff.1 hs
  obtain ⟨zᵢ, w1, w2, -, -⟩ := walk_cut hal hw (pre.flatMap (·.rounds)).length (Nat.le_of_lt hi)
  have hdrop : (R.first.take n).drop (pre.flatMap (·.rounds)).length =
      s :: (R.first.take n).drop ((pre.flatMap (·.rounds)).length + 1) := by
    rw [← hsi, List.getElem_cons_drop]
  have hid : (pre.flatMap (·.rounds)).length < (ρ.first.take n).length := by
    rw [hlen]
    exact hi
  have ddrop : (ρ.first.take n).drop (pre.flatMap (·.rounds)).length =
      (ρ.first.take n)[(pre.flatMap (·.rounds)).length] ::
        (ρ.first.take n).drop ((pre.flatMap (·.rounds)).length + 1) := by
    rw [List.getElem_cons_drop]
  rw [hdrop, ddrop] at w2
  obtain ⟨x', z₁, hx, hz, hw'⟩ := walk_cons_ok w2
  have hs₁ : zᵢ.mid.isSome = true := mid_back L _ _ zᵢ y w2 hsome
  obtain ⟨mᵢ, hmi⟩ := Option.isSome_iff_exists.1 hs₁
  have h2 : s.tell none mᵢ = .ok x' := by
    unfold ChainProgress.say at hx
    rw [hmi] at hx
    exact hx
  obtain ⟨mv, hmv, hsay⟩ := switch_says (Y := Y) Sd D readers closing pl c.1 mᵢ.shown mᵢ.st
  obtain ⟨z, hz', -, hzt, -, -⟩ := tell_move _ _ _ _ _ c.1 0 s hs0 mv hmv mᵢ x' h2
  obtain ⟨Dt, Ts, f1, f2, f3⟩ := hsay z hz'
  have hlaidz := walk_laid_drawn L _ _ a₁ zᵢ w1
  rw [hal, List.map_nil, List.nil_append] at hlaidz
  have hzl : zᵢ.laid.length = (pre.flatMap (·.rounds)).length := by
    have := congrArg List.length hlaidz
    rw [List.length_map, List.length_take, List.length_take] at this
    have h5 : (ρ.first.take n).length = (R.first.take n).length := hlen
    rw [List.length_take] at h5 hi
    omega
  obtain ⟨tl, htl⟩ := walk_laid_prefix L _ _ z₁ y hw'
  have hq := heard_laid hz
  refine ⟨zᵢ, mᵢ, c.1, ⟨s.name, s.addr.place, s.addr.part, x'.told, x'.vals, x'.tables,
    (ρ.first.take n)[(pre.flatMap (·.rounds)).length]⟩, Dt, Ts, ?_, hmi, hlp, ?_, ?_, f1, f2⟩
  · rw [List.take_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hn)] at w1
    exact w1
  · have gen : ∀ (a b : List Played) (e : Played) (i : ℕ), a.length = i →
        (a ++ ([e] ++ b))[i]? = some e := by
      intro a b e i h
      subst h
      simp
    rw [← htl, hq, List.append_assoc]
    exact gen _ _ _ _ hzl
  · show x'.tables = _
    rw [hzt, f3]

/-! ## 2 The book -/

/-- The word on the fresh message. -/
abbrev freshWordOf (p : K2.SwitchPlace) : Option (ℕ × ℕ) :=
  K2.switchFresh p.sizes p.others p.foldVars

/-- Two entries of the book name one run of one owner's coins. -/
def sameEntry (a b : Ahead) : Bool :=
  a.owner == b.owner && a.start == b.start && a.count == b.count

/-- Of an entry of the book: its owner, where it starts, its count. -/
def entryRun (e : Ahead) : Addr × Due × Due := (e.owner, e.start, e.count)

/-- **A public test on the book**: a: the test's second part; s: the finish's part. The entries by
which a carries the stretches that s carries are s's; the next is the carrying message's, from the
start of s's coins; the next the fresh message's, where the sending lays it. -/
def bookTiesAtFinish (Bk : ProverCoinCounts) (a s : Addr) (p : K2.SwitchPlace) : Bool :=
  decide (p.front.length ≤ (carriedOf Bk a).length) &&
  decide (p.front.length ≤ (carriedOf Bk s).length) &&
  ((carriedOf Bk a).take p.front.length).map entryRun ==
    ((carriedOf Bk s).take p.front.length).map entryRun &&
  (match (carriedOf Bk a)[p.front.length]? with
   | some e => e.owner == s && e.start == ⟨0, 0⟩ &&
       e.count == K2.messageDue p.sizes.codes (shapeL p) none
   | none => false) &&
  (match (carriedOf Bk a)[p.front.length + 1]? with
   | some e => e.owner == s && e.start == K2.dueBefore p.sizes.codes (sentL p) (freshWordOf p) 1 &&
       e.count == K2.messageDue p.sizes.codes (freshShapeL p) (some p.foldVars)
   | none => false)

theorem bookTiesAtFinish_parts {Bk : ProverCoinCounts} {a s : Addr} {p : K2.SwitchPlace}
    (h : bookTiesAtFinish Bk a s p = true) :
    (∀ n < p.front.length, ∃ e e', (carriedOf Bk a)[n]? = some e ∧ (carriedOf Bk s)[n]? = some e' ∧
      sameEntry e e' = true) ∧
    (∃ e, (carriedOf Bk a)[p.front.length]? = some e ∧ e.owner = s ∧ e.start = ⟨0, 0⟩ ∧
      e.count = K2.messageDue p.sizes.codes (shapeL p) none) ∧
    (∃ e, (carriedOf Bk a)[p.front.length + 1]? = some e ∧ e.owner = s ∧
      e.start = K2.dueBefore p.sizes.codes (sentL p) (freshWordOf p) 1 ∧
      e.count = K2.messageDue p.sizes.codes (freshShapeL p) (some p.foldVars)) := by
  unfold bookTiesAtFinish at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨la, ls⟩, h1⟩, h2⟩, h3⟩ := h
  refine ⟨fun n hn => ?_, ?_, ?_⟩
  · have ha : n < (carriedOf Bk a).length := by omega
    have hs : n < (carriedOf Bk s).length := by omega
    refine ⟨_, _, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hs, ?_⟩
    have e : (((carriedOf Bk a).take p.front.length).map entryRun)[n]? =
        (((carriedOf Bk s).take p.front.length).map entryRun)[n]? := by rw [h1]
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_take_of_lt hn,
      List.getElem?_take_of_lt hn, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hs] at e
    have e' := Option.some.inj e
    unfold entryRun at e'
    obtain ⟨e1, e2⟩ := Prod.mk.inj e'
    obtain ⟨e2, e3⟩ := Prod.mk.inj e2
    unfold sameEntry
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨e1, e2⟩, e3⟩
  · cases e1 : (carriedOf Bk a)[p.front.length]? with
    | none =>
      rw [e1] at h2
      cases h2
    | some e =>
      rw [e1] at h2
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact ⟨e, rfl, h2.1.1, h2.1.2, h2.2⟩
  · cases e1 : (carriedOf Bk a)[p.front.length + 1]? with
    | none =>
      rw [e1] at h3
      cases h3
    | some e =>
      rw [e1] at h3
      simp only [Bool.and_eq_true, beq_iff_eq] at h3
      exact ⟨e, rfl, h3.1.1, h3.1.2, h3.2⟩

/-- A cut of a cut from 0 is a cut. -/
theorem cut_of_cut {d t a n : Due} (c : Cs d) (own : Cs t) (h : c.cut ⟨0, 0⟩ t = some own)
    (x : Cs n) (hx : own.cut a n = some x) : c.cut a n = some x := by
  unfold Cs.cut at h hx ⊢
  split at h
  · rename_i h1
    have h1f : t.f ≤ d.f := by simpa using h1.1
    have h1e : t.e ≤ d.e := by simpa using h1.2
    obtain rfl := Option.some.inj h
    split at hx
    · rename_i h2
      obtain rfl := Option.some.inj hx
      rw [dif_pos ⟨by have := h2.1; omega, by have := h2.2; omega⟩]
      refine congrArg some ?_
      congr 1 <;>
        · funext i
          exact congrArg _ (Fin.ext (Nat.zero_add _).symm)
    · cases hx
  · cases h

/-- Two lent lists at entries that name one run hand one stretch. -/
theorem stretches_same {look : Addr → (d : Due) × Cs d} {ds ds' : List (String × Due)}
    {l l' : List Ahead} {y : CsAll ds} {y' : CsAll ds'} (h : lend look ds l = .ok y)
    (h' : lend look ds' l' = .ok y') (n : ℕ) (e e' : Ahead) (he : l[n]? = some e)
    (he' : l'[n]? = some e') (hs : sameEntry e e' = true) :
    stretches ds y n = stretches ds' y' n := by
  obtain ⟨x, hx, ex⟩ := lend_cut look ds l y h n e he
  obtain ⟨x', hx', ex'⟩ := lend_cut look ds' l' y' h' n e' he'
  unfold sameEntry at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  rw [ex, ex']
  obtain ⟨en, eo, es, ec, ep, eb⟩ := e
  obtain ⟨en', eo', es', ec', ep', eb'⟩ := e'
  dsimp only at h1 h2 h3 hx hx'
  subst h1 h2 h3
  rw [hx] at hx'
  rw [Option.some.inj hx']

/-- The stretch that the book lends from a run of the owner's coins is the cut of the owner's own
coins at that run. -/
theorem lent_is_cut {look : Addr → (d : Due) × Cs d} {ds : List (String × Due)} {l : List Ahead}
    {y : CsAll ds} (h : lend look ds l = .ok y) (n : ℕ) (e : Ahead) (he : l[n]? = some e)
    (s : Addr) (A N : Due) (ho : e.owner = s) (hs : e.start = A) (hc : e.count = N) {t : Due}
    (own : Cs t) (hown : (look s).2.cut ⟨0, 0⟩ t = some own) (st : K2.Stretch)
    (hst : (K2.Stretch.of own).cut A N = .ok st) :
    st = asK2 N (stretches ds y n) ∧ stretchOf st.coins = stretches ds y n := by
  obtain ⟨x, hx, ex⟩ := lend_cut look ds l y h n e he
  unfold K2.Stretch.cut at hst
  split at hst
  · rename_i z hz
    have hst' := Except.ok.inj hst
    subst hst'
    have hz' : own.cut A N = some z := hz
    have hc' := cut_of_cut _ own hown z hz'
    rw [ex]
    obtain ⟨en, eo, es, ec, ep, eb⟩ := e
    dsimp only at ho hs hc hx
    subst ho hs hc
    rw [hx] at hc'
    obtain rfl := Option.some.inj hc'
    exact ⟨(asK2_stretchOf x).symm, rfl⟩
  · cases hst

/-! ## 3 Small facts -/

/-- Three cuts of a list's end. -/
theorem take_three {α : Type} (l : List α) (i a b n : ℕ) (hn : n = i + a + b) (hl : n ≤ l.length) :
    ((l.take n).take ((l.take n).length - b)).take
      (((l.take n).take ((l.take n).length - b)).length - a) = l.take i := by
  have e1 : (l.take n).length = n := by simp [hl]
  have e2 : ((l.take n).take (n - b)).length = n - b := by
    rw [List.length_take, e1]
    omega
  rw [e1, e2, List.take_take, List.take_take]
  congr 1
  omega

/-- How many oracle messages the rounds of the blocks in front declare. -/
theorem rows_count {S Cl : Type} (pre : List (Block S Cl))
    (hs : ∀ y ∈ pre, y.oracles.length = y.rounds.length) (rest : List (Block S Cl)) :
    (((rowsOfChain (pre ++ rest)).take (pre.flatMap (·.rounds)).length).map (·.2.length)).sum =
      (pre.flatMap fun y => y.oracles.flatMap id).length := by
  induction pre with
  | nil => simp
  | cons y pre ih =>
    have hy := hs y (by simp)
    have hz : (y.rounds.zip y.oracles).length = y.rounds.length := by simp [hy]
    have e1 : rowsOfChain ((y :: pre) ++ rest) =
        y.rounds.zip y.oracles ++ rowsOfChain (pre ++ rest) := by
      unfold rowsOfChain
      simp [List.flatMap_cons]
    have e2 : ((y :: pre).flatMap (·.rounds)).length =
        (y.rounds.zip y.oracles).length + (pre.flatMap (·.rounds)).length := by
      rw [hz]
      simp [List.flatMap_cons]
    have e3 : ((y.rounds.zip y.oracles).map (·.2.length)).sum = (y.oracles.flatMap id).length := by
      have e4 : (y.rounds.zip y.oracles).map (·.2.length) =
          ((y.rounds.zip y.oracles).map Prod.snd).map List.length := by
        rw [List.map_map]
        rfl
      rw [e4, List.map_snd_zip (by omega), List.length_flatMap]
      rfl
    rw [e1, e2, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      List.map_append, List.sum_append, ih fun z hz' => hs z (by simp [hz']), e3, List.flatMap_cons,
      List.length_append]

/-- The tree that a round in front sends stands at the number of trees in front of it. -/
theorem tables_at (l : List Played) (i : ℕ) (qd : Played) (hq : l[i]? = some qd)
    (T : Option Table) (hT : qd.tables[0]? = some T) :
    (allTabs l)[(allTabs (l.take i)).length]? = some T := by
  obtain ⟨hi, hh⟩ := List.getElem?_eq_some_iff.1 hq
  have e : l = l.take i ++ qd :: l.drop (i + 1) := by
    rw [← hh, List.getElem_cons_drop, List.take_append_drop]
  have e2 : allTabs l = allTabs (l.take i) ++ (qd.tables ++ allTabs (l.drop (i + 1))) := by
    conv_lhs => rw [e]
    unfold allTabs
    rw [List.flatMap_append, List.flatMap_cons]
  rw [e2, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  obtain ⟨h0, h1⟩ := List.getElem?_eq_some_iff.1 hT
  rw [List.getElem?_append_left h0]
  exact hT

/-! ## 4 The clause at a run -/

section Main
variable {Xi W₀ Rc Ky Tr X₀ Y Pb : Type}

local notation "JL" => jobL (W₀ := W₀) (Rc := Rc) (Xi := Xi) (Tr := Tr) (X := Y)

/-- **The attacker's (E2) at a run.** At a called second part of the test that stands right behind
the finish of the code switch: every column that the front lists of the tree that the first round
of positions opens is the column of the job's own tree there, the rows of the first fresh mask
among what it encodes. Conditional on the run's returning and on three public premises, which this
theorem does not pay: hW (the count of a column's words), hT (the book's entries), hj and hsrc (the
tree's number). No premise on a value, a coin or a refusal: that the sender's text returns is read
off the run. -/
theorem trees_first {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (q : VerifiableInference.Desc.K12.P12)
    (door : Local W₀ Rc Xi Tr → Front Y → VerifiableInference.Desc.K12.T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (Js : SimJob Pb)
    (σ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Pb)
    (pre : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl) (t : List (Block F.S₁ F.Cl))
    (S : StandsAt F.first.blocksInOrder R.first σ (restMember (JL q door D readers closing pl) Js)
      (pre ++ [b]) t (firstLen q.nums.stages))
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hgK : (P.first.find? fun g => g.place == b.place) =
      some (K2.switchHalf (K2.coreSender K2.freshTable) D readers closing pl))
    (hfit : fitsL q pl = true)
    (hW : columnWidth (finishSending pl) 0 = ((finishTrees pl).shapes.getD 0 default).mainWidth +
      ((finishTrees pl).shapes.getD 0 default).maskWidth)
    (hT : bookTiesAtFinish Bk ⟨σ.block.place, 1⟩ ⟨b.place, 0⟩ pl = true)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hos : os = q.nums.first) (j : ℕ)
    (hsrc : ∀ o ∈ os, o.2 = Fmt.TreeSource.own j)
    (hj : treesTo F.first.blocksInOrder pre.length = j)
    (st : List (ℕ × ℕ × List UInt64)) (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
    (hm : midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m))
    (ca : CsAll (restPart (JL q door D readers closing pl) :
      Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).carries)
    (hca : carriedAt Bk k 0 ⟨σ.block.place, 1⟩ (restPart (JL q door D readers closing pl) :
      Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y) = .ok ca) :
    TreesAt (JL q door D readers closing pl) 0 os (stretches _ ca) m
      (r.run.beforeAt st ⟨σ.block.place, 1⟩) := by
  have F' := fitsL_facts hfit
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨lS, -, -⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  -- the stand
  obtain ⟨m', hm', hin, hheard, -, -, hbf, -, -, -, -⟩ :=
    frame_at_first hpl hR hrun σ (restMember (JL q door D readers closing pl) Js) (pre ++ [b]) t _ _
      S rfl hc st
  obtain rfl : m = m' := Option.some.inj (Except.ok.inj (hm.symm.trans hm'))
  obtain ⟨a₁, y, m₂, ha₁, hw, hyl, hym, -⟩ :=
    played_at_first hpl hR hrun σ (restMember (JL q door D readers closing pl) Js) (pre ++ [b]) t _ _
      S rfl hc
  have hcut : F.first.blocksInOrder = pre ++ b :: (σ.block :: t) := by
    rw [S.cut]
    simp
  have hb : b.rounds.length = 2 := (block_rounds_at_first hR pre b _ hcut _ hgK).symm
  have hlenpre : ((pre ++ [b]).flatMap (·.rounds)).length = (pre.flatMap (·.rounds)).length + 2 := by
    simp [List.flatMap_append, hb]
  obtain ⟨zᵢ, mᵢ, c₂, qd, Dt, Ts, hpi, hmi, hlend, hq, hqT, hDt, hTs⟩ :=
    switch_in_front hR pre b (σ.block :: t) hcut
      (fun h => by rw [h] at hb; cases hb) (K2.coreSender K2.freshTable) D readers closing pl hgK _
      (by rw [hlenpre]; omega) _ a₁ y (start_laid ha₁) (by have := S.fits; simp only [restMember] at this; omega) hw
      (by rw [hym]; rfl)
  -- the challenges and the input
  have hlenR : ((pre ++ [b]).flatMap (·.rounds)).length + firstLen q.nums.stages ≤
      ρ.first.length := by
    have e := lS.1
    have := S.fits
    omega
  have hh : mᵢ.st.heard = ρ.first.take (pre.flatMap (·.rounds)).length := by
    have a3 := walk_hears _ _ _ _ a₁ zᵢ (start_hears ha₁) hpi mᵢ hmi
    have a4 := walk_laid_drawn _ _ _ a₁ zᵢ hpi
    rw [start_laid ha₁, List.map_nil, List.nil_append] at a4
    rw [a4] at a3
    exact a3.trans (List.nil_append _)
  have hinp : mᵢ.st.input = m.st.input := by
    rw [hin]
    exact (walk_mid ha₁ hpi hmi).1
  have hheardL : heardL (restFront (JL q door D readers closing pl) m) = mᵢ.st.heard := by
    rw [hh]
    show ((m.st.heard.take (m.st.heard.length - firstLen q.nums.stages))).take
      ((m.st.heard.take (m.st.heard.length - firstLen q.nums.stages)).length - 2) = _
    rw [hheard]
    exact take_three _ _ _ _ _ (by rw [hlenpre]) hlenR
  -- the coins
  have hown := own_of_lendPart hlend
  have hcar₂ := carried_of_lendPart _ _ _ _ _ c₂ hlend
  unfold carriedAt at hca
  obtain ⟨c₁, hl₁, e₁⟩ := exMap_ok hca
  subst e₁
  have hcar₁ := carried_of_lendPart _ _ _ _ _ c₁ hl₁
  obtain ⟨tA, tB, tC⟩ := bookTiesAtFinish_parts hT
  -- the sender's rows
  unfold K2.switchRowsAt at hDt
  obtain ⟨Wl, hWl, eD⟩ := exMap_ok hDt
  simp only [K2.coreSender] at hTs
  obtain ⟨VS, hVS, eT⟩ := exMap_ok hTs
  have h2 : (K2.switchSent pl.sizes pl.others).size = 2 := F'.two
  obtain ⟨s₀, hs₀, hr₀⟩ := rowsAll_at hVS 0 (by omega)
  obtain ⟨s₁, hs₁, hr₁⟩ := rowsAll_at hVS 1 (by omega)
  have hf0 : K2.foldAt (K2.switchFresh pl.sizes pl.others pl.foldVars) 0 = none := by
    simp [K2.foldAt, K2.switchFresh, h2]
  have hf1 : K2.foldAt (K2.switchFresh pl.sizes pl.others pl.foldVars) 1 = some pl.foldVars := by
    simp [K2.foldAt, K2.switchFresh, h2]
  have hsh1 : ((K2.switchSent pl.sizes pl.others).getD 1 default).shape = freshShapeL pl := by
    show _ = (((K2.switchSent pl.sizes pl.others).getD
      ((K2.switchSent pl.sizes pl.others).size - 1) default).shape)
    rw [h2]
  rw [hf0] at hs₀ hr₀
  rw [hf1, hsh1] at hs₁ hr₁
  have hd0 : K2.dueBefore pl.sizes.codes (K2.switchSent pl.sizes pl.others)
      (K2.switchFresh pl.sizes pl.others pl.foldVars) 0 = ⟨0, 0⟩ := by
    simp [K2.dueBefore]
  rw [hd0] at hs₀
  have hJm : (JL q door D readers closing pl : TestJob (Local W₀ Rc Xi Tr) Y).members.length =
      pl.front.length + 1 := by
    simp [jobL, membersL]
  obtain ⟨e₀, he₀, ho₀, hst₀, hc₀⟩ := tB
  obtain ⟨e₁', he₁, ho₁, hst₁, hc₁⟩ := tC
  have A0 := lent_is_cut hcar₁ _ e₀ he₀ _ _ _ ho₀ hst₀ hc₀ c₂.1 hown s₀ hs₀
  have A1 := lent_is_cut hcar₁ _ e₁' he₁ _ _ _ ho₁ hst₁ hc₁ c₂.1 hown s₁ hs₁
  have hmem : ∀ n < pl.front.length, stretches _ c₁.2.2 n = stretches pl.carries c₂.2.2 n := by
    intro n hn
    obtain ⟨e, e', a1, a2, a3⟩ := tA n hn
    exact stretches_same hcar₁ hcar₂ n e e' a1 a2 a3
  have hWl' : closing pl (D mᵢ.st.input.x) (readers mᵢ.st.input) mᵢ.st.heard
      (K2.Stretch.carried pl.carries c₂.2.2) = .ok Wl :=
    (congrArg (fun l => closing pl (D mᵢ.st.input.x) (readers mᵢ.st.input) l
      (K2.Stretch.carried pl.carries c₂.2.2)) (by simp; rfl)).trans hWl
  subst eD
  have hcarry : carryRows D readers closing pl m.st.input
      (heardL (restFront (JL q door D readers closing pl) m)) (stretches _ c₁.2.2) =
      .ok (VS 0) := by
    have hbeg : Begins (membersL pl) (restPart (JL q door D readers closing pl) :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).carries :=
      begins_runs (JL q door D readers closing pl) _ _
    have hfun : (fun n => if n < pl.front.length then K2.Stretch.carried _ c₁.2.2 n
        else (Except.error "a stretch is asked beyond the list" : Except String K2.Stretch)) =
        K2.Stretch.carried pl.carries c₂.2.2 := by
      funext n
      by_cases hn : n < pl.front.length
      · have hx : pl.carries[n]? = some (carriedName pl.front[n].1 pl.front[n].2.1 ⟨pl.place, 0⟩,
            pl.front[n].2.2) := by
          simp [K2.SwitchPlace.carries, hn]
        obtain ⟨s', hs'⟩ := hbeg n pl.front[n] (by simp [membersL, List.getElem?_append_left hn])
        rw [if_pos hn, carried_asK2 pl.carries _ n _ hx, carried_asK2 _ _ n _ hs', hmem n hn]
      · rw [if_neg hn]
        exact (carried_beyond pl.carries _ n
          (by simp [K2.SwitchPlace.carries]; omega)).1.symm
    obtain ⟨s'', hs''⟩ := hbeg pl.front.length
      (⟨pl.place, 0⟩, 0, K2.messageDue pl.sizes.codes (shapeL pl) none) (by simp [membersL])
    rw [carryRows_by_carried D readers closing pl _ _ _ hbeg c₁.2.2]
    unfold carryBy
    rw [hfun, ← hinp, hheardL, hWl', carried_asK2 _ _ _ _ hs'']
    show K2.messageRows K2.freshTable pl.sizes.codes (shapeL pl) none _
      (asK2 _ (stretches _ c₁.2.2 pl.front.length)) = .ok (VS 0)
    rw [← A0.1]
    exact hr₀
  have hRz : (carryRows D readers closing pl m.st.input
      (heardL (restFront (JL q door D readers closing pl) m)) (stretches _ c₁.2.2)).toOption.getD
      K2.zeroMessage = VS 0 := by
    rw [hcarry]
    rfl
  have hTr : (JL q door D readers closing pl).trees₀ m.st.input
      (restFront (JL q door D readers closing pl) m) (stretches _ c₁.2.2)
      (rowsAt (JL q door D readers closing pl) (stretches _ c₁.2.2) m) =
      [(((finishTrees pl).shapes.getD 0 default).logN, col (finishSending pl) (messagesOfJob pl (VS 0)
        (rowsAt (JL q door D readers closing pl) (stretches _ c₁.2.2) m)) 0)] := by
    show treesL D readers closing pl _ _ _ _ = _
    unfold treesL
    dsimp only
    rw [hRz]
    rfl
  have hLm : (carriedCoins (JL q door D readers closing pl) (stretches _ c₁.2.2)).hide =
      (stretchOf s₁.coins).e := by
    show (stretches _ c₁.2.2
      (JL q door D readers closing pl : TestJob (Local W₀ Rc Xi Tr) Y).members.length).e = _
    rw [hJm, A1.2]
  have hfM : (rowsAt (JL q door D readers closing pl) (stretches _ c₁.2.2) m).fM =
      Johnson.Prover.Link.packedN (H2K.Pub.sgOf (firstStageOf q))
        (hideAt ((H2K.Pub.sgOf (firstStageOf q)).h + (H2K.Pub.sgOf (firstStageOf q)).g)
          (stretchOf s₁.coins).e) := by
    rw [← hLm]
    rfl
  have hfT : (rowsAt (JL q door D readers closing pl) (stretches _ c₁.2.2) m).fT =
      tailsIn (firstStageOf q) (stretchOf s₁.coins).e := by
    rw [← hLm]
    rfl
  -- the one tree
  obtain ⟨t0, ht0⟩ : ∃ t0, (finishTrees pl).shapes.toList = [t0] :=
    List.length_eq_one_iff.1 (by simpa using F'.alone)
  have hget : (finishTrees pl).shapes.getD 0 default = t0 := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ht0]
    rfl
  have hTs1 : Ts = [⟨t0.logN, t0.mainWidth + t0.maskWidth, fun x w =>
      OnBytes.Slice.toF ((col (finishSending pl) VS 0 x).getD w.val 0)⟩] := by
    rw [← eT]
    show (finishTrees pl).shapes.toList.zipIdx.map _ = _
    rw [ht0]
    rfl
  have e2 : (R.first.take (pre.flatMap (·.rounds)).length).map (·.oracles.length) =
      ((rowsOfChain F.first.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length) := by
    rw [← steps_pairs s1, ← List.map_take, List.map_map]
    rfl
  have hjl : (allTabs ((r.run.played.1.take (((pre ++ [b]).flatMap (·.rounds)).length +
      firstLen q.nums.stages)).take (pre.flatMap (·.rounds)).length)).length = j := by
    have hsh : ∀ y ∈ pre, y.oracles.length = y.rounds.length := fun y hy => by
      have h1 := planOk_shaped_first hpl y (by rw [hcut]; simp [hy])
      unfold Block.shaped at h1
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      exact h1.1
    have hc' := rows_count pre hsh (b :: (σ.block :: t))
    rw [← hcut] at hc'
    have ht : treesTo F.first.blocksInOrder pre.length =
        (pre.flatMap fun y => y.oracles.flatMap id).length := by
      unfold treesTo
      rw [hcut, List.take_left']
      rfl
    rw [allTabs_len, ← hj, ht, ← hc', ← e2, List.take_take,
      Nat.min_eq_left (by rw [hlenpre]; omega), List.map_take, laidAs_tables lS, List.map_take]
  rw [← hyl] at hjl
  have htab := tables_at _ _ qd hq _ (by rw [hqT, hTs1]; rfl)
  rw [hjl, hyl] at htab
  subst hos
  refine ⟨?_, ?_⟩
  · rw [hTr]
    have e := congrArg (List.map Prod.fst) F'.tree
    rw [List.map_map, List.map_map, ht0] at e
    show [((finishTrees pl).shapes.getD 0 default).logN] = _
    rw [hget]
    exact e.symm
  · intro i' o T ho hTi
    rw [hTr] at hTi
    cases i' with
    | succ i' => simp at hTi
    | zero =>
      have hTe := Option.some.inj hTi
      subst hTe
      have ho' : o ∈ q.nums.first := List.mem_of_getElem? ho
      rw [hsrc o ho']
      refine ⟨colsOfT (some ⟨t0.logN, t0.mainWidth + t0.maskWidth, fun x w =>
        OnBytes.Slice.toF ((col (finishSending pl) VS 0 x).getD w.val 0)⟩) (treeAsks F ρ 0 j), ?_, ?_⟩
      · have hbf' : r.run.beforeAt st ⟨σ.block.place, 1⟩ = _ := hbf
        rw [hbf']
        show (⟨shownBy 0 (treeAsks F ρ 0) _ 0, st⟩ : Before).treeCols 0 j = _
        rw [treeCols_first, htab]
        rfl
      · intro q' hq'
        obtain ⟨x', -, rfl⟩ := List.mem_map.1 hq'
        show Table.col _ x' = col (finishSending pl) (messagesOfJob pl (VS 0) _) 0 x'
        rw [table_column _ _ (col (finishSending pl) VS 0) x' (by rw [column_length, hW, hget])
          (column_words_canonical _ _ _ _)]
        exact column_at_finish F' _ VS (VS 0) s₁ _ rfl hr₁ hfM hfT x'

end Main

/-! ## 5 The tooth -/

/-- A chain's rounds with every list of columns changed by g. -/
def bendColumns (ch : ℕ) (g : List (ℕ × List UInt64) → List (ℕ × List UInt64)) (f : Before) :
    Before :=
  { f with rounds := f.rounds.map fun r =>
      if r.1 == ch then (r.1, ⟨r.2.1.vals, r.2.1.cols.map g⟩, r.2.2) else r }

theorem treeCols_bendColumns (ch n : ℕ) (g : List (ℕ × List UInt64) → List (ℕ × List UInt64))
    (f : Before) : (bendColumns ch g f).treeCols ch n = (f.treeCols ch n).map g := by
  have key : ∀ l : List (ℕ × Shown × Fmt.Drawn),
      ((l.map fun r => if r.1 == ch then (r.1, (⟨r.2.1.vals, r.2.1.cols.map g⟩ : Shown), r.2.2)
          else r).filter fun r => r.1 == ch).flatMap (fun r => r.2.1.cols) =
        ((l.filter fun r => r.1 == ch).flatMap fun r => r.2.1.cols).map g := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      by_cases h : (a.1 == ch) = true
      · simp only [List.map_cons, h, if_true, List.filter_cons, List.flatMap_cons, List.map_append]
        rw [ih]
      · simp only [List.map_cons, h, List.filter_cons, if_false, Bool.false_eq_true]
        exact ih
  unfold Before.treeCols bendColumns
  dsimp only
  rw [key, List.getElem?_map]

/-- One position's column laid anew. -/
def putColumn (x : ℕ) (w : List UInt64) (l : List (ℕ × List UInt64)) : List (ℕ × List UInt64) :=
  l.map fun c => if c.1 == x then (x, w) else c

/-- **The tooth**: where TreesAt holds and the front lists the column w of a first tree at x, the
same front with another column at x, any word of it bent, the words of the first fresh mask's rows
among them, does not meet TreesAt. -/
theorem trees_tooth {W X : Type} (J : TestJob W X) (ch : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource))
    (mem : ℕ → Stretch) (m : ProofFile.Honest.Mid W X) (f : Before) (i : ℕ)
    (o : Fmt.Shape × Fmt.TreeSource) (T : Tree) (ho : os[i]? = some o)
    (hT : (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m))[i]? = some T)
    (hc : (srcOf ch o.2).1 = ch) (cols : List (ℕ × List UInt64))
    (hf : f.treeCols ch (srcOf ch o.2).2 = some cols) (x : ℕ) (w w' : List UInt64)
    (hw : (x, w) ∈ cols) (hne : w' ≠ w) (h : TreesAt J ch os mem m f) :
    ¬ TreesAt J ch os mem m (bendColumns ch (putColumn x w') f) := by
  intro h'
  obtain ⟨c1, e1, q1⟩ := h.2 i o T ho hT
  obtain ⟨c2, e2, q2⟩ := h'.2 i o T ho hT
  rw [hc] at e1 e2
  rw [treeCols_bendColumns, hf] at e2
  rw [hf] at e1
  obtain rfl := Option.some.inj e1
  have e3 : putColumn x w' cols = c2 := Option.some.inj e2
  have hw' : (x, w') ∈ c2 := by
    rw [← e3]
    exact List.mem_map.2 ⟨(x, w), hw, by simp⟩
  have a1 := q1 _ hw
  have a2 := q2 _ hw'
  exact hne (a2.trans a1.symm)

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.trees_first
#print axioms ProofFile.Honest.K12.Sim2.trees_tooth
#print axioms ProofFile.Honest.K12.Sim2.treeCols_bendColumns
#print axioms ProofFile.Honest.K12.Sim2.switch_says
#print axioms ProofFile.Honest.K12.Sim2.switch_in_front
