-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ThrRow.lean: a toy example that meets the hypotheses. A
`Thread` (Honest/Thread/Thr.lean) over three sub-protocols of the toy list of parts of
Honest/Law/ToyRow.lean, at which all six hypotheses of Honest/Thread/Pays.lean are proved, at every
run's coins, every input and every list of challenges that the rounds can draw. The invariant also
holds at the first border. Theorems about these files' own made-up objects. None is one of the
library's goals.

The three. `send₃`: a prover's side sends a tree: its word at p is the trace's word at p plus a coin
v. `tellB`: a first round draws a position and opens that tree there; a second round says the word
there; the verifier asks that the word said is the column's one word: this part carries v. `askQ`: a
third prover's side says one element; the verifier asks nothing. All values are elements of the
field, compared as the words that are read as them: so the verifier accepts at all coins. (The
toy example of Honest/Thread/ThrToy.lean, which is not in the sealed library, compares words as
natural numbers: so, by its definition, at a large coin its verifier rejects its own honest prover
(argued, not evaluated); it serves that file's own tests, at small values, and does not meet the
hypotheses.)

The parameters of the `Thread`. (H): the tree's table is a function of the run's coins and the
input. One item, `word`: the oracle string of the tree, at every position below its length, is the
witness's word there; the witness is that function. The first row owes it; the second asks and owes
it again; the third names it in no list: so it rides past. (P): the verifier's running total is 0.
`keeps`: the state is left as it was. (X): the first state is that of the toy example's description.

  1  `Table.same_refl`, `Table.same_elim`   on the test that two tables show the same
  2  `Ty` and its parameters; `hand_elim`, `word_of_hand`, `word_add`
  3  the three sub-protocols' runs: `send_moves`, `tell_runs`, `ask_runs`
  4  the hypotheses: `plays_row`, `behind_row`, `exchange_row`, `rides_row`, `made_row`,
     `accepted_row`
  5  `thr_zero`, `thr_succ`, `thr_last`   the invariant holds at the start, goes on, and holds at
     the end

Limits.
  * A toy example: three toy prover's sides, none of a kind of the protocol; no stop, no fall, one
    item, no stored table, nothing before the chain.
  * That the hypotheses can be met is proved at this `Thread` alone.
  * The run's start (`midR`) has `none` as its columns opened: no column is handed, and no part of
    the three reads that field: so the hypotheses, which are asked at every value of the field
    (`Thr` does not read it), are met here at `none` too. Of a `Thread` with a part that reads the
    columns this example shows nothing.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.Law.ToyExact
import Johnson.Desc.ProofFile.Honest.Law.Thread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-! ## 1 Two tables show the same -/

theorem Table.same_refl (t : Table) : t.same t = true := by
  simp [Table.same]

theorem Table.same_elim {t u : Table} (h : t.same u = true) :
    t.logLength = u.logLength ∧ ∀ x, x < 2 ^ t.logLength → t.col x = u.col x := by
  unfold Table.same at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, -⟩, h3⟩ := h
  exact ⟨beq_iff_eq.1 h1, fun x hx => beq_iff_eq.1 (List.all_eq_true.1 h3 x (List.mem_range.2 hx))⟩

namespace Toy
open VerifiableInference.Desc (Place Block OpenedColumn Strs foldBlocks step_iff)
open VerifiableInference.Desc.BlockToy (St send₃ tree₃ drawT orc)
open OnBytes.Slice (toF ofF)

/-! ## 2 The `Thread` -/

inductive RI where
  | word
  deriving DecidableEq, Repr

def rowY : Nat → FwdRow RI
  | 0 => .of [] [.word] []
  | 1 => .of [] [] [.word]
  | _ => {}

/-- The tree's word at a position: the trace's word there plus the second owner's coin. -/
def wordY (k : Coins By) (w : L) (p : Nat) : Cb.Gl.F := toF (w.trace.b p) + coinAt k 2 sSend 0

/-- The tree's table. -/
def tableY (k : Coins By) (w : L) : Table := ⟨2, 1, fun p _ => wordY k w p⟩

/-- The chain's first state. -/
def st₀ : St := ⟨0, none, 0⟩

/-- **The example's `Thread`.** -/
abbrev Ty : Thread By St Nat L L Nat Nat :=
  { φ := .own, chain := 2, ft := Fy.lastChainFirstTreeNumber, bs := [send₃, tellB, askQ], hs := Py.second
    ahead := [], near := 0, taken := []
    fixed := fun _ => 0, table := fun _ k w _ => (pSend, tableY k w)
    stored := fun _ _ _ => none, valid := fun _ => True
    ι := RI, dec := inferInstance, start := [], row := rowY
    P := Unit, handed := fun _ _ _ => (), Wt := Nat → Cb.Gl.F
    form := fun _ a => a.2.total == 0, formP := fun _ _ => True
    means := fun _ _ _ y v => ∀ p, p < 4 → y.col 0 p = [ofF (v p)]
    wit := fun k w _ => wordY k w
    strs := Env.strs 0 fun _ => some (.own 0)
    begun := fun _ _ _ s => s = st₀
    rides := fun _ _ _ => True
    keeps := fun _ s s' => s' = s }

theorem fits_row : Ty.fits 3 = true := by decide

theorem shaped_row : ∀ x ∈ Ty.bs, x.planOk = true ∧ x.shaped = true := by
  intro x hx
  have hx' : x ∈ [send₃, tellB, askQ] := hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl | rfl <;> exact ⟨rfl, by decide⟩

theorem hand_elim {k : Coins By} {m : Mid L Nat} {E : Env}
    (h : Ty.handAt (.own 0) k m E = true) :
    ∃ pl T, E.tree (.own 0) = some (pl, T) ∧ T.same (tableY k m.st.input) = true := by
  unfold Thread.handAt at h
  cases hE : E.tree (.own 0) with
  | none =>
    rw [hE] at h
    cases h
  | some u =>
    rw [hE] at h
    have h' : (u.1 == pSend && u.2.same (tableY k m.st.input)) = true := h
    rw [Bool.and_eq_true] at h'
    exact ⟨u.1, u.2, rfl, h'.2⟩

/-- What is read of the tree at a position below its length. -/
theorem col_of_hand {k : Coins By} {m : Mid L Nat} {T : Table}
    (hs : T.same (tableY k m.st.input) = true) (p : Nat) (hp : p < 4) :
    T.logLength = 2 ∧ T.col p = [ofF (wordY k m.st.input p)] := by
  obtain ⟨hlg, hcol⟩ := Table.same_elim hs
  have hlg' : T.logLength = 2 := hlg
  refine ⟨hlg', ?_⟩
  rw [hcol p (by rw [hlg']; exact hp)]
  rfl

/-- (H) gives the item. -/
theorem word_of_hand {k : Coins By} {m : Mid L Nat} {E : Env}
    (h : Ty.handAt (.own 0) k m E = true) (p : Nat) (hp : p < 4) :
    (Ty.strs E).col 0 p = [ofF (wordY k m.st.input p)] := by
  obtain ⟨pl, T, hT, hs⟩ := hand_elim h
  obtain ⟨hlg, hcol⟩ := col_of_hand hs p hp
  show (match E.tree (.own 0) with
    | some u => if p < 2 ^ u.2.logLength then u.2.col p else []
    | none => []) = _
  rw [hT]
  show (if p < 2 ^ T.logLength then T.col p else []) = _
  rw [hlg, if_pos (show p < 2 ^ 2 from hp), hcol]

/-- After further rounds the tree's string is as it was. -/
theorem word_add {E : Env} (ps : List Played) (h : 0 < E.sent) (p : Nat) :
    (Ty.strs (E.add ps)).col 0 p = (Ty.strs E).col 0 p := by
  have e : (E.add ps).tree (.own 0) = E.tree (.own 0) := by
    show (if 0 < E.sent then E.tree (.own 0) else _) = _
    rw [if_pos h]
  show (match (E.add ps).tree (.own 0) with
    | some u => if p < 2 ^ u.2.logLength then u.2.col p else []
    | none => []) = (match E.tree (.own 0) with
    | some u => if p < 2 ^ u.2.logLength then u.2.col p else []
    | none => [])
  rw [e]

/-! ## 3 The three runs -/

theorem find_send : (Py.second.find? fun g => g.place == send₃.place) = some ySide₂.half := rfl
theorem find_tell : (Py.second.find? fun g => g.place == tellB.place) = some ySide₃.half := rfl
theorem find_ask : (Py.second.find? fun g => g.place == askQ.place) = some ySide₄.half := rfl

/-- `send₃`, played. -/
theorem send_moves {k : Coins By} {m : Mid L Nat} {R : Fmt.Drawn} {l : List (Step L Nat)}
    (hl : chainSteps By (By.rowsOf 2) (k.look 2) (Face.own.sees m.st.input) [send₃] Py.second =
      .ok l) :
    ∃ m' : Mid L Nat, play l [R] [] m =
        .ok ([⟨"send", pSend, 0, true, [], [some (tableY k m.st.input)], R⟩], m') ∧
      m'.st.input = m.st.input := by
  obtain ⟨c, hc, rfl⟩ := steps_one_half find_send hl
  obtain ⟨c₀, hc₀, hv⟩ := lend_send k
  have ec : c = ((c₀, (), ()), ()) := Except.ok.inj (hc.symm.trans hc₀)
  subst ec
  obtain ⟨m', hy, hm'⟩ := play_sendRow c₀ m R
  rw [hv] at hy
  exact ⟨m', hy, hm'⟩

/-- `tellB`, played, read and stepped, where the available tree shows the function's word. -/
theorem tell_runs {k : Coins By} (s : St) {m : Mid L Nat}
    {st : Nat → Nat → Option (List UInt64)} {tre : Fmt.TreeSource → Option (Place × Table)}
    {pl : Place} {T : Table} {el : List Fmt.Ext} {x : Nat} {tr : List Int}
    {dg : Option ByteArray} {R₁ : Fmt.Drawn} {l : List (Step L Nat)}
    (hT : tre (.own 0) = some (pl, T))
    (hcol : T.col (x % 2 ^ 2) = [ofF (wordY k m.st.input (x % 2 ^ 2))])
    (h₀ : drawFit { entry := drawT, opens := [(tree₃, .own 0)] } ⟨el, [x], tr, dg⟩ = true)
    (h₁ : drawFit { entry := { name := "CS", msg := 24 } } R₁ = true)
    (hl : chainSteps By (By.rowsOf 2) (k.look 2) (Face.own.sees m.st.input) [tellB] Py.second =
      .ok l) :
    ∃ (y : List Played × Mid L Nat) (cols : List OpenedColumn),
      play l [⟨el, [x], tr, dg⟩, R₁] [] m = .ok y ∧
      fillCols (readsOf 2 Fy.lastChainFirstTreeNumber (Env.add ⟨st, tre, 1⟩ y.1).stored
        (Env.add ⟨st, tre, 1⟩ y.1).tree tellB.rounds [⟨el, [x], tr, dg⟩, R₁]) [] = .ok cols ∧
      tellB.step Fy.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s, cols.length) := by
  obtain ⟨c, hc, rfl⟩ := steps_one_half find_tell hl
  obtain ⟨c₀, cv, hc₀, hv⟩ := lend_tell k
  have ec : c = ((c₀, (), (cv, ())), ()) := Except.ok.inj (hc.symm.trans hc₀)
  subst ec
  obtain ⟨m', hy, -⟩ := play_tell c₀ cv m ⟨el, [x], tr, dg⟩ R₁
  rw [hv] at hy
  refine ⟨_, [(tree₃.tree - Fy.lastChainFirstTreeNumber, x % 2 ^ 2, [ofF (wordY k m.st.input (x % 2 ^ 2))])],
    hy, ?_, ?_⟩
  · refine (congrArg (fun q => fillCols q [])
      (reads_tell st tre _ Fy.lastChainFirstTreeNumber el x tr dg R₁)).trans ?_
    show fillCols [⟨tree₃.tree - Fy.lastChainFirstTreeNumber, x % 2 ^ 2, none, some (2, 0),
      (tre (.own 0)).map (·.1), (tre (.own 0)).map (·.2.col (x % 2 ^ 2)), 1⟩] [] = _
    rw [hT]
    show fillCols [⟨tree₃.tree - Fy.lastChainFirstTreeNumber, x % 2 ^ 2, none, some (2, 0), some pl,
      some (T.col (x % 2 ^ 2)), 1⟩] [] = _
    rw [hcol]
    rfl
  · exact VerifiableInference.Desc.Block.step_ok.2
      ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans
          ((roundsFit_cons (by with_unfolding_all rfl) h₁).trans (by with_unfolding_all rfl)),
        by with_unfolding_all rfl,
        tell_decide s _ _ _ _, by with_unfolding_all rfl⟩

/-- `askQ`, played, read and stepped. -/
theorem ask_runs {k : Coins By} (s : St) {m : Mid L Nat} (E : Env) {R : Fmt.Drawn}
    {l : List (Step L Nat)} (h₀ : drawFit { entry := { name := "CS", msg := 24 } } R = true)
    (hl : chainSteps By (By.rowsOf 2) (k.look 2) (Face.own.sees m.st.input) [askQ] Py.second =
      .ok l) :
    ∃ (y : List Played × Mid L Nat), play l [R] [] m = .ok y ∧
      fillCols (readsOf 2 Fy.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree askQ.rounds [R]) [] =
        .ok [] ∧
      askQ.step Fy.lastChainFirstTreeNumber s (roundsOf y.1) [] = .ok (s, 0) := by
  obtain ⟨c', hc, rfl⟩ := steps_one_half find_ask hl
  obtain ⟨c, ca, hc₀⟩ := lend_carry k
  have ec : c' = ((c, (), ca), ()) := Except.ok.inj (hc.symm.trans hc₀)
  subst ec
  obtain ⟨m', hy⟩ := play_cS m c ca R
  refine ⟨_, hy, by with_unfolding_all rfl, ?_⟩
  exact VerifiableInference.Desc.Block.step_ok.2
    ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
      by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-! ## 4 The hypotheses -/

theorem thr_parts {b : Nat} {k : Coins By} {s : St} {m : Mid L Nat} {E : Env}
    (h : Thr Ty b k s m E) :
    Ty.Trees (Ty.hand b) k m E ∧ Ty.Fit b m ∧ (s.total == 0) = true ∧ Ty.Made b k s m E := by
  unfold Thr Thread.Hand Thread.Form at h
  exact ⟨h.1.2, h.2.1, h.2.2.1.1, h.2.2.2.2.1⟩

theorem made_parts {b : Nat} {k : Coins By} {s : St} {m : Mid L Nat} {E : Env}
    (h : Ty.Made b k s m E) :
    E.sent = treesTo Ty.bs b ∧ ∀ n, E.sent ≤ n → E.tree (.own n) = none := by
  unfold Thread.Made at h
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- From "whatever `Step`s are prepared for the sub-protocol: it is played, read and stepped" to the
two forms in which the hypotheses are stated. -/
theorem moved_of_runs {blk : Block St Nat} {k : Coins By} {s s' : St} {m : Mid L Nat} {E : Env}
    {ds : List Fmt.Drawn} {l : List (Step L Nat)}
    (hl : chainSteps By (By.rowsOf 2) (k.look 2) (Face.own.sees m.st.input) [blk] Py.second =
      .ok l)
    (h : ∃ (y : List Played × Mid L Nat) (cols : List OpenedColumn), play l ds [] m = .ok y ∧
      fillCols (readsOf 2 Fy.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree blk.rounds ds) [] =
        .ok cols ∧ blk.step Fy.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s', cols.length)) :
    ∃ y cols, Ty.Moved blk k m E ds y cols := by
  obtain ⟨y, cols, hy, hc, -⟩ := h
  refine ⟨y, cols, ?_⟩
  unfold Thread.Moved
  exact ⟨⟨l, hl, hy⟩, hc⟩

theorem stepped_of_runs {blk : Block St Nat} {k : Coins By} {s s' : St} {m : Mid L Nat} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid L Nat} {cols : List OpenedColumn}
    (hMv : Ty.Moved blk k m E ds y cols)
    (h : ∀ l, chainSteps By (By.rowsOf 2) (k.look 2) (Face.own.sees m.st.input) [blk] Py.second =
        .ok l →
      ∃ (y : List Played × Mid L Nat) (cols : List OpenedColumn), play l ds [] m = .ok y ∧
        fillCols (readsOf 2 Fy.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree blk.rounds ds) [] =
          .ok cols ∧ blk.step Fy.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s', cols.length)) :
    Ty.Stepped blk k s m E ds y cols s' := by
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hMv'
  obtain ⟨y', cols', hy', hc', hs'⟩ := h l hl
  have ey : y' = y := Except.ok.inj (hy'.symm.trans hy)
  subst ey
  have ec : cols' = cols := Except.ok.inj (hc'.symm.trans hc)
  subst ec
  unfold Thread.Stepped
  exact ⟨hMv, hs'⟩

/-- `send₃`. -/
theorem runs_send {k : Coins By} {s : St} {m : Mid L Nat} {E : Env} {ds : List Fmt.Drawn}
    (hd : drawsFit send₃.rounds ds = true) (l : List (Step L Nat))
    (hl : chainSteps By (By.rowsOf 2) (k.look 2) (Face.own.sees m.st.input) [send₃] Py.second =
      .ok l) :
    ∃ (y : List Played × Mid L Nat) (cols : List OpenedColumn), play l ds [] m = .ok y ∧
      fillCols (readsOf 2 Fy.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree send₃.rounds ds) [] =
        .ok cols ∧ send₃.step Fy.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s, cols.length) := by
  have hd' : drawsFit [{ entry := { name := "CS", msg := 32, roots := 1 } }] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨m', hy, -⟩ := send_moves (R := R) hl
  refine ⟨_, [], hy, by with_unfolding_all rfl, ?_⟩
  exact VerifiableInference.Desc.Block.step_ok.2
    ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
      by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-- After `send₃` its tree is the function's table. -/
theorem send_trees {k : Coins By} {s : St} {m : Mid L Nat} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid L Nat} {cols : List OpenedColumn} (hA : Thr Ty 0 k s m E)
    (hd : drawsFit send₃.rounds ds = true) (hMv : Ty.Moved send₃ k m E ds y cols) :
    Ty.handAt (.own 0) k y.2 (E.add y.1) = true := by
  have hd' : drawsFit [{ entry := { name := "CS", msg := 32, roots := 1 } }] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  unfold Thread.Moved at hMv
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨m', hy', hm'⟩ := send_moves (R := R) hl
  have ey := Except.ok.inj (hy.symm.trans hy')
  subst ey
  have hs := (made_parts (thr_parts hA).2.2.2).1
  obtain ⟨st, tre, sent⟩ := E
  have hs' : sent = 0 := hs
  subst hs'
  show ((some (pSend, tableY k m.st.input) : Option (Place × Table)).any fun u =>
    u.1 == pSend && u.2.same (tableY k m'.st.input)) = true
  rw [hm']
  show (pSend == pSend && (tableY k m.st.input).same (tableY k m.st.input)) = true
  rw [Table.same_refl]
  rfl

/-- `tellB` from the invariant before it. -/
theorem runs_tell {k : Coins By} {s : St} {m : Mid L Nat} {E : Env} {ds : List Fmt.Drawn}
    (hA : Thr Ty 1 k s m E) (hd : drawsFit tellB.rounds ds = true) (l : List (Step L Nat))
    (hl : chainSteps By (By.rowsOf 2) (k.look 2) (Face.own.sees m.st.input) [tellB] Py.second =
      .ok l) :
    ∃ (y : List Played × Mid L Nat) (cols : List OpenedColumn), play l ds [] m = .ok y ∧
      fillCols (readsOf 2 Fy.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree tellB.rounds ds) [] =
        .ok cols ∧ tellB.step Fy.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s, cols.length) := by
  have hd' : drawsFit [{ entry := drawT, opens := [(tree₃, .own 0)] },
      { entry := { name := "CS", msg := 24 } }] ds = true := hd
  obtain ⟨R₀, R₁, rfl, h₀, h₁⟩ := drawsFit_two hd'
  obtain ⟨x, hx⟩ := one_of_length (poss_of_drawFit h₀)
  obtain ⟨el, ps, tr, dg⟩ := R₀
  have hx' : ps = [x] := hx
  subst hx'
  obtain ⟨hTr, -, -, hM⟩ := thr_parts hA
  have hs := (made_parts hM).1
  obtain ⟨pl, T, hT, hsame⟩ := hand_elim (hTr (.own 0) (by decide))
  obtain ⟨-, hcol⟩ := col_of_hand hsame (x % 2 ^ 2)
    (Nat.mod_lt _ (by decide))
  obtain ⟨st, tre, sent⟩ := E
  have hs' : sent = 1 := hs
  subst hs'
  exact tell_runs s hT hcol h₀ h₁ hl

/-- `askQ`. -/
theorem runs_ask {k : Coins By} {s : St} {m : Mid L Nat} {E : Env} {ds : List Fmt.Drawn}
    (hd : drawsFit askQ.rounds ds = true) (l : List (Step L Nat))
    (hl : chainSteps By (By.rowsOf 2) (k.look 2) (Face.own.sees m.st.input) [askQ] Py.second =
      .ok l) :
    ∃ (y : List Played × Mid L Nat) (cols : List OpenedColumn), play l ds [] m = .ok y ∧
      fillCols (readsOf 2 Fy.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree askQ.rounds ds) [] =
        .ok cols ∧ askQ.step Fy.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s, cols.length) := by
  have hd' : drawsFit [{ entry := { name := "CS", msg := 24 } }] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨y, hy, hc, hs⟩ := ask_runs s E h₀ hl
  exact ⟨y, [], hy, hc, hs⟩

/-- The three in one: whatever sub-protocol is after border number b. -/
theorem runs_member {b : Nat} {blk : Block St Nat} (hblk : Ty.bs[b]? = some blk) {k : Coins By}
    {s : St} {m : Mid L Nat} {E : Env} {ds : List Fmt.Drawn} (hA : Thr Ty b k s m E)
    (hd : drawsFit blk.rounds ds = true) (l : List (Step L Nat))
    (hl : chainSteps By (By.rowsOf 2) (k.look 2) (Face.own.sees m.st.input) [blk] Py.second =
      .ok l) :
    ∃ (y : List Played × Mid L Nat) (cols : List OpenedColumn), play l ds [] m = .ok y ∧
      fillCols (readsOf 2 Fy.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree blk.rounds ds) [] =
        .ok cols ∧ blk.step Fy.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s, cols.length) := by
  match b, hblk, hA with
  | 0, hblk, _ =>
    cases Option.some.inj hblk
    exact runs_send hd l hl
  | 1, hblk, hA =>
    cases Option.some.inj hblk
    exact runs_tell hA hd l hl
  | 2, hblk, _ =>
    cases Option.some.inj hblk
    exact runs_ask hd l hl
  | _ + 3, hblk, _ => cases hblk

/-- No sub-protocol of the three changes the verifier's state. -/
theorem step_same {blk : Block St Nat} (hb : blk ∈ Ty.bs) {s s' : St} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {n : Nat} (h : blk.step Fy.lastChainFirstTreeNumber s rs cols = .ok (s', n)) : s' = s := by
  have hdec := ((step_iff _ _ _ _ _ _ _).1 h).2.1
  have hb' : blk ∈ [send₃, tellB, askQ] := hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
  rcases hb' with rfl | rfl | rfl
  · exact (Except.ok.inj hdec).symm
  · have h' : (VerifiableInference.Desc.need "tell.the-word" (sameWord
        (tellB.shown Fy.lastChainFirstTreeNumber rs cols) ((rs.map VerifiableInference.Desc.noDigest).map
                        (·.vals)))).map (fun _ => s) = .ok s' := hdec
    cases hn : VerifiableInference.Desc.need "tell.the-word" (sameWord
        (tellB.shown Fy.lastChainFirstTreeNumber rs cols) ((rs.map VerifiableInference.Desc.noDigest).map
                        (·.vals))) with
    | error e =>
      rw [hn] at h'
      cases h'
    | ok u =>
      rw [hn] at h'
      exact (Except.ok.inj h').symm
  · exact (Except.ok.inj hdec).symm

/-- **`Plays`**, at every sub-protocol. -/
theorem plays_row (b : Nat) : Plays Ty b := by
  intro blk hblk k s m E ds l hA hd _ hl
  obtain ⟨y, cols, hMv⟩ := moved_of_runs hl (runs_member hblk hA hd l hl)
  refine ⟨y, cols, hMv, ?_⟩
  match b, hblk, hA, hMv with
  | 0, hblk, hA, hMv =>
    cases Option.some.inj hblk
    intro σ hσ
    have hσ' : σ ∈ [Fmt.TreeSource.own 0] := hσ
    cases List.mem_singleton.1 hσ'
    exact send_trees hA hd hMv
  | 1, _, _, _ =>
    intro σ hσ
    have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  | 2, _, _, _ =>
    intro σ hσ
    have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  | _ + 3, hblk, _, _ => cases hblk

/-- **`Behind`**, at every sub-protocol. -/
theorem behind_row (b : Nat) : Behind Ty b := by
  intro blk hblk k s m E ds y cols s' hA _ hS
  unfold Thread.Stepped at hS
  have e := step_same (List.mem_of_getElem? hblk) hS.2
  subst e
  exact ⟨⟨(thr_parts hA).2.2.1, trivial⟩, trivial, rfl⟩

/-- **`Exchange`**, at every sub-protocol. -/
theorem exchange_row (b : Nat) : Exchange Ty b := by
  intro blk hblk k s m E ds y cols s' hA hd hS
  have hS' := hS
  unfold Thread.Stepped at hS'
  match b, hblk, hA with
  | 0, hblk, hA =>
    cases Option.some.inj hblk
    intro _ _ _ p hp
    exact word_of_hand (send_trees hA hd hS'.1) p hp
  | 1, _, hA =>
    intro _ _ _ p hp
    have hMv := hS'.1
    unfold Thread.Moved at hMv
    obtain ⟨⟨l, -, hy⟩, -⟩ := hMv
    obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
    obtain ⟨hTr, -, -, hM⟩ := thr_parts hA
    exact word_of_hand (Ty.handAt_next ei (play_heard _ _ _ _ _ hy) (Nat.zero_le _)
      (made_parts hM).2 (hTr (.own 0) (by decide))) p hp
  | 2, _, _ =>
    intro _ i hi
    have hi' : i ∈ ([] : List RI) := hi
    cases hi'
  | _ + 3, hblk, _ => cases hblk

/-- **`RidesPast`**, at every sub-protocol. -/
theorem rides_row (b : Nat) : RidesPast Ty b := by
  intro k s m E s' ps i v hA _ hi _ ho hm
  match b, hA, hi, ho with
  | 0, _, hi, _ =>
    have hi' : i ∈ ([] : List RI) := hi
    cases hi'
  | 1, _, _, ho =>
    cases i
    exact absurd (show RI.word ∈ [RI.word] from List.mem_singleton.2 rfl) ho
  | n + 2, hA, _, _ =>
    intro p hp
    have hs := (made_parts (thr_parts hA).2.2.2).1
    have h1 : 0 < E.sent := by
      rw [hs]
      show 0 < treesTo [send₃, tellB, askQ] (n + 2)
      unfold treesTo
      simp [List.take, send₃]
    rw [word_add ps h1 p]
    exact hm p hp

/-- **`MadeNext`** (the clauses (F) and (X)), at every sub-protocol: by the general lemma. -/
theorem made_row (b : Nat) : MadeNext Ty b := made_next Ty fits_row shaped_row b

/-- **`Accepted`**, at every sub-protocol, with no fall at all. -/
theorem accepted_row (b : Nat) : Accepted Ty (fun _ _ _ => none) b := by
  intro blk hblk k s m E ds y cols hA hd _ _ hMv
  exact ⟨s, stepped_of_runs hMv (runs_member hblk hA hd)⟩

/-! ## 5 The invariant holds at the start, goes on, and holds at the end -/

/-- The state of a run of the three at its start. No columns are handed (`none`), as in the frame's
own `Ready.start₁` (Honest/Frame.lean). -/
def midR (w : L) (x₀ : Nat) : Mid L Nat := ⟨⟨w, [], x₀⟩, [], [], none⟩
def envR : Env := ⟨fun _ _ => none, fun _ => none, 0⟩

/-- **The invariant holds at the first border**: at every run's coins and every input. -/
theorem thr_zero (k : Coins By) (w : L) (x₀ : Nat) : Thr Ty 0 k st₀ (midR w x₀) envR := by
  unfold Thr Thread.Hand Thread.Fit Thread.Form Thread.Made
  refine ⟨⟨fun _ _ => rfl, fun σ hσ => ?_⟩, rfl, ⟨rfl, trivial⟩, fun _ i hi => ?_,
    ⟨rfl, rfl, rfl, fun _ _ => rfl, st₀, [], rfl, rfl, rfl⟩, trivial, trivial⟩
  · have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  · have hi' : i ∈ ([] : List RI) := hi
    cases hi'

/-- The book gives every sub-protocol's parts their coins, and nothing of the three stops. -/
theorem laid_row {b : Nat} {blk : Block St Nat} (hblk : Ty.bs[b]? = some blk) (k : Coins By)
    (m : Mid L Nat) (ds : List Fmt.Drawn) :
    (∃ l, chainSteps By (By.rowsOf 2) (k.look 2) (Face.own.sees m.st.input) [blk] Py.second =
      .ok l) ∧ chainStopAt (Face.own.sees m.st.input) [blk] Py.second m.loc ds = none := by
  match b, hblk with
  | 0, hblk =>
    cases Option.some.inj hblk
    exact ⟨⟨_, rfl⟩, rfl⟩
  | 1, hblk =>
    cases Option.some.inj hblk
    exact ⟨⟨_, rfl⟩, rfl⟩
  | 2, hblk =>
    cases Option.some.inj hblk
    exact ⟨⟨_, rfl⟩, rfl⟩
  | _ + 3, hblk => cases hblk

/-- **The invariant goes on**: from a border to the next, at every list that the sub-protocol's
rounds can draw (stated: some state at the next border that has heard these challenges too; the
proof takes the step's own, as `play` leaves it): from the six hypotheses and `thr_behind`. -/
theorem thr_succ {b : Nat} {blk : Block St Nat} (hb : b < 3) (hblk : Ty.bs[b]? = some blk)
    {k : Coins By} {s : St} {m : Mid L Nat} {E : Env} {ds : List Fmt.Drawn}
    (hA : Thr Ty b k s m E) (hd : drawsFit blk.rounds ds = true) :
    ∃ s' m' E', Thr Ty (b + 1) k s' m' E' ∧ m'.st.heard = m.st.heard ++ ds := by
  obtain ⟨⟨l, hl⟩, hst⟩ := laid_row hblk k m ds
  obtain ⟨y, cols, hMv, hT⟩ := plays_row b blk hblk k s m E ds l hA hd hst hl
  obtain ⟨s', hS⟩ := accepted_row b blk hblk k s m E ds y cols hA hd hst rfl hMv
  refine ⟨s', y.2, E.add y.1, thr_behind Ty fits_row hb hblk hA hd hS hT (behind_row b)
    (exchange_row b) (rides_row b) (made_row b), ?_⟩
  unfold Thread.Moved at hMv
  obtain ⟨⟨l', -, hy⟩, -⟩ := hMv
  exact play_heard _ _ _ _ _ hy

/-- **The invariant holds at the end**: at every run's coins, and every list of challenges that the
three sub-protocols' four rounds can draw (stated: some state at the last border that has heard
these; `w` and `x₀` are not tied to it). -/
theorem thr_last (k : Coins By) (w : L) (x₀ : Nat) (d₀ d₁ d₂ : List Fmt.Drawn)
    (h₀ : drawsFit send₃.rounds d₀ = true) (h₁ : drawsFit tellB.rounds d₁ = true)
    (h₂ : drawsFit askQ.rounds d₂ = true) :
    ∃ s m E, Thr Ty 3 k s m E ∧ m.st.heard = d₀ ++ d₁ ++ d₂ := by
  obtain ⟨s₁, m₁, E₁, t₁, e₁⟩ := thr_succ (b := 0) (by decide) rfl (thr_zero k w x₀) h₀
  obtain ⟨s₂, m₂, E₂, t₂, e₂⟩ := thr_succ (b := 1) (by decide) rfl t₁ h₁
  obtain ⟨s₃, m₃, E₃, t₃, e₃⟩ := thr_succ (b := 2) (by decide) rfl t₂ h₂
  refine ⟨s₃, m₃, E₃, t₃, ?_⟩
  rw [e₃, e₂, e₁]
  rfl

end Toy
end ProofFile.Honest

#print axioms ProofFile.Honest.Table.same_refl
#print axioms ProofFile.Honest.Table.same_elim
#print axioms ProofFile.Honest.Toy.fits_row
#print axioms ProofFile.Honest.Toy.shaped_row
#print axioms ProofFile.Honest.Toy.hand_elim
#print axioms ProofFile.Honest.Toy.col_of_hand
#print axioms ProofFile.Honest.Toy.word_of_hand
#print axioms ProofFile.Honest.Toy.word_add
#print axioms ProofFile.Honest.Toy.find_send
#print axioms ProofFile.Honest.Toy.find_tell
#print axioms ProofFile.Honest.Toy.find_ask
#print axioms ProofFile.Honest.Toy.send_moves
#print axioms ProofFile.Honest.Toy.tell_runs
#print axioms ProofFile.Honest.Toy.ask_runs
#print axioms ProofFile.Honest.Toy.thr_parts
#print axioms ProofFile.Honest.Toy.made_parts
#print axioms ProofFile.Honest.Toy.moved_of_runs
#print axioms ProofFile.Honest.Toy.stepped_of_runs
#print axioms ProofFile.Honest.Toy.runs_send
#print axioms ProofFile.Honest.Toy.send_trees
#print axioms ProofFile.Honest.Toy.runs_tell
#print axioms ProofFile.Honest.Toy.runs_ask
#print axioms ProofFile.Honest.Toy.runs_member
#print axioms ProofFile.Honest.Toy.step_same
#print axioms ProofFile.Honest.Toy.plays_row
#print axioms ProofFile.Honest.Toy.behind_row
#print axioms ProofFile.Honest.Toy.exchange_row
#print axioms ProofFile.Honest.Toy.rides_row
#print axioms ProofFile.Honest.Toy.made_row
#print axioms ProofFile.Honest.Toy.accepted_row
#print axioms ProofFile.Honest.Toy.thr_zero
#print axioms ProofFile.Honest.Toy.laid_row
#print axioms ProofFile.Honest.Toy.thr_succ
#print axioms ProofFile.Honest.Toy.thr_last
#print axioms ProofFile.Honest.Toy.RI
#print axioms ProofFile.Honest.Toy.rowY
#print axioms ProofFile.Honest.Toy.wordY
#print axioms ProofFile.Honest.Toy.tableY
#print axioms ProofFile.Honest.Toy.st₀
#print axioms ProofFile.Honest.Toy.Ty
#print axioms ProofFile.Honest.Toy.midR
#print axioms ProofFile.Honest.Toy.envR
