-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Driver/CutFront.lean: A LAW ON cutOf (Johnson/Desc/First/Driver/Cut.lean): THE
ROWS IN FRONT OF THE MEMBERS' PLACES TAKE JUST THE ROUNDS IN FRONT. cutOf reads the names of a
plan's entries by a small grammar and gives each step a row with the number of rounds that it takes.
Lean's kernel cannot walk it at a real plan (48,293 names: each step asks the length of all that is
left). HERE, ON THE TEXT OF cutOf ALONE, FOR EVERY LIST OF ENTRIES: each of its six functions
returns, as the names left, the names that it was given without the first n, n the sum of its rows'
rounds; no row in front of the members' is the step "M.0.call"; and the finish's own test says that
the last two names in front of the members' are "BASE lambda", "BASE". SO THE NUMBER OF THE ROUND AT
WHICH THE MEMBERS' BATCHING STARTS IS PINNED BY WHERE THE NAME "BASE lambda" STANDS: a fact that the
kernel walks by two loops.

  takes, Eats, NoM       the rounds that rows take · the rows take just the names in front of what
    is left · no row is the step "M.0.call".
  tailCut_eats · linkCut_eats · linksCut_eats · stagesCut_eats · finishCut_eats   one lemma a
    function.
  cutOf_front            **the law**: cs = front ++ endCuts pl q b
    (Johnson/Desc/First/Driver/CutEnd.lean) · NoM front · 2 ≤ takes front ≤ the entries' number ·
    the two names at takes front - 2 are "BASE lambda", "BASE".
  rounds_before_call     in such a table the step "M.0.call" is there, and the rounds of the rows in
    front of it sum to takes front.
  front_of_base          **the start**: general in the type of the plan's rounds: where "BASE
    lambda" stands neither among the first p rounds nor behind round p: takes front = p + 2.
What is not claimed. THAT cutOf RETURNS A TABLE AT ANY LIST: a premise throughout. That the names
are the planner's. Where "BASE lambda" stands in a real plan: closed facts of another file. Nothing
on what a step does. No soundness of a verifier.

-/
import Johnson.Desc.First.Driver.CutEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- The rounds that a list of rows takes. -/
def takes (rows : List Cut) : Nat := (rows.map (·.take)).sum

theorem takes_append (a b : List Cut) : takes (a ++ b) = takes a + takes b := by
  simp [takes]

/-- The rows take just the names in front of rest. -/
def Eats (rows : List Cut) (ns rest : List String) : Prop :=
  takes rows ≤ ns.length ∧ rest = ns.drop (takes rows)

/-- No row is the step "M.0.call". -/
def NoM (rows : List Cut) : Prop := ∀ c ∈ rows, c.look ≠ "M.0.call"

theorem NoM.append {a b : List Cut} (ha : NoM a) (hb : NoM b) : NoM (a ++ b) := fun c hc =>
  (List.mem_append.1 hc).elim (ha c) (hb c)

theorem Eats.then {a b : List Cut} {ns r₁ r₂ : List String} (h1 : Eats a ns r₁) (h2 : Eats b r₁ r₂)
    :
    Eats (a ++ b) ns r₂ := by
  obtain ⟨l1, rfl⟩ := h1
  obtain ⟨l2, rfl⟩ := h2
  rw [List.length_drop] at l2
  refine ⟨by rw [takes_append]; omega, ?_⟩
  rw [List.drop_drop, takes_append]

/-- A name whose first sign is not M, with whatever behind it, is not "M.0.call". -/
def NotM (L : String) : Prop := ∃ c r, L.toList = c :: r ∧ c ≠ 'M'

theorem NotM.ne {L : String} (h : NotM L) (t : String) : L ++ t ≠ "M.0.call" := by
  intro e
  obtain ⟨c, r, e1, hc⟩ := h
  have h2 := congrArg String.toList e
  simp [e1] at h2
  exact hc h2.1

theorem upTo_lt {s : String} {ns : List String} {a : Nat} (h : upTo s ns = some a) :
    a < ns.length := by
  unfold upTo at h
  dsimp only at h
  split at h
  · cases h
    assumption
  · cases h

theorem begins_le {l ns : List String} (h : begins l ns = true) : l.length ≤ ns.length := by
  have e := congrArg List.length (eq_of_beq h)
  rw [List.length_take] at e
  omega

theorem lookLen_le {ns : List String} {k : Nat} (h : lookLen ns = some k) : k ≤ ns.length := by
  unfold lookLen at h
  split at h
  · cases h
  · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
    have h1 := upTo_lt ha
    have h2 := upTo_lt hb
    rw [List.length_drop] at h2
    omega

theorem takeWhile_le {α : Type} (p : α → Bool) : ∀ l : List α, (l.takeWhile p).length ≤ l.length
  | [] => Nat.le_refl _
  | a :: l => by
    rw [List.takeWhile_cons]
    split
    · exact Nat.succ_le_succ (takeWhile_le p l)
    · exact Nat.zero_le _

theorem doorLen_le (ns : List String) : doorLen ns ≤ ns.length := by
  unfold doorLen
  split
  · rename_i h
    have h1 := begins_le h
    have h2 := takeWhile_le (fun x : String => x == "FOLD round") (ns.drop 2)
    rw [List.length_drop] at h2
    simp only [List.length_cons, List.length_nil] at h1
    omega
  · exact Nat.zero_le _

theorem takes_nil : takes [] = 0 := rfl

theorem takes_cons (a : Cut) (l : List Cut) : takes (a :: l) = a.take + takes l := by
  simp [takes]

theorem takes_zero_map {α : Type} (l : List α) (f : α → Cut) (h : ∀ x, (f x).take = 0) :
    takes (l.map f) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, takes_cons, h, ih]

theorem noM_nil : NoM [] := fun _ h => by cases h

theorem noM_cons {a : Cut} {l : List Cut} (ha : a.look ≠ "M.0.call") (hl : NoM l) : NoM (a :: l) :=
  fun c hc => by
    rcases List.mem_cons.1 hc with rfl | h
    · exact ha
    · exact hl c h

theorem noM_map {α : Type} (l : List α) (f : α → Cut) (h : ∀ x, (f x).look ≠ "M.0.call") :
    NoM (l.map f) := fun c hc => by
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hc
  exact h x

/-- Rows that take n rounds eat the first n names. -/
theorem eats_of {rows : List Cut} {ns : List String} {n : Nat} (h : takes rows = n)
    (hn : n ≤ ns.length) : Eats rows ns (ns.drop n) := ⟨by rw [h]; exact hn, by rw [h]⟩

theorem NotM.at' {L : String} (hL : NotM L) (j : Nat) (w : String) :
    L ++ "." ++ toString j ++ "." ++ w ≠ "M.0.call" := by
  rw [String.append_assoc, String.append_assoc, String.append_assoc]
  exact hL.ne _

theorem tailCut_eats {c L : String} {i pl : Nat} {head : Bool} {claims : List (String × String)}
    {ns : List String} {rows : List Cut} {pl' : Nat} {rest : List String} (hL : NotM L)
    (h : tailCut c L i pl head claims ns = some (rows, pl', rest)) :
    Eats rows ns rest ∧ NoM rows := by
  unfold tailCut at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, Option.bind_none] at h
  split at h
  · cases h
  rename_i h5
  obtain ⟨k, hk, h1⟩ := Option.bind_eq_some_iff.1 h
  clear h
  obtain ⟨m, hm, h2⟩ := Option.bind_eq_some_iff.1 h1
  clear h1
  split at h2
  · cases h2
  rename_i hc
  split at h2
  · cases h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, -, rfl⟩ := h2
  have l5 : 5 ≤ ns.length := by
    have := begins_le (l := ["SEND seed", "SEND answer", "RNG", "SEND seed", "SEND answer"])
      (ns := ns) (by simpa using h5)
    simpa using this
  have lk := lookLen_le hk
  have lm := upTo_lt hm
  have ld := doorLen_le (List.drop m (List.drop k (List.drop 5 ns)))
  simp only [List.length_drop] at lk lm ld
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, Bool.not_eq_true', not_or,
    not_and] at hc
  obtain ⟨⟨m0, -⟩, m1⟩ := hc
  generalize doorLen (List.drop m (List.drop k (List.drop 5 ns))) = dd at ld ⊢
  constructor
  · rw [List.drop_drop, List.drop_drop, List.drop_drop]
    apply eats_of _ (by omega)
    cases head
    · have e1 : m = 1 := by
        have := m1 rfl
        simpa using this
      subst e1
      simp only [takes_append, takes_cons, takes_nil, Bool.false_eq_true, if_false]
      rw [takes_zero_map _ _ (fun _ => rfl)]
      omega
    · simp only [takes_append, takes_cons, takes_nil, if_true]
      rw [takes_zero_map _ _ (fun _ => rfl)]
      omega
  · refine NoM.append (NoM.append (NoM.append (NoM.append ?_ ?_) ?_) ?_) ?_
    · exact noM_cons (hL.at' _ _) (noM_cons (hL.at' _ _) (noM_cons (hL.at' _ _) (noM_cons (hL.at' _
        _)
        (noM_cons (hL.at' _ _) (noM_cons (hL.at' _ _) noM_nil)))))
    · cases head
      · exact noM_nil
      · exact noM_cons (hL.at' _ _) (noM_cons (hL.at' _ _) noM_nil)
    · exact noM_cons (hL.at' _ _) noM_nil
    · exact noM_map _ _ fun x => hL.at' _ _
    · exact noM_cons (hL.at' _ _) (noM_cons (hL.at' _ _) noM_nil)

theorem notM_H : NotM "H" := ⟨'H', [], rfl, by decide⟩

theorem notM_A (a : Nat) : NotM ("A" ++ toString a) := ⟨'A', (toString a).toList, by simp,
    by decide⟩

theorem notM_G (g : Nat) : NotM ("G" ++ toString g) := ⟨'G', (toString g).toList, by simp,
    by decide⟩

theorem notM_F : NotM "F." := ⟨'F', ['.'], rfl, by decide⟩

theorem linkCut_eats {g a pl : Nat} {ns : List String} {rows : List Cut} {g' a' pl' : Nat}
    {wasHead : Bool} {rest : List String}
    (h : linkCut g a pl ns = some (rows, g', a', pl', wasHead, rest)) :
    Eats rows ns rest ∧ NoM rows := by
  unfold linkCut at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, Option.bind_none] at h
  generalize (if (pl == 0 && !ns.head? == some "REPLY") = true then "SEND answer" else "LOC") = w1
      at h
  generalize (if (pl == 0 && !ns.head? == some "REPLY") = true then "send" else "sendLoc") = fk at h
  generalize hn : (if (ns.head? == some "REPLY") = true then List.drop 1 ns else ns) = n₀ at h
  split at h
  · cases h
  rename_i hb
  obtain ⟨k, hk, h1⟩ := Option.bind_eq_some_iff.1 h
  clear h
  obtain ⟨o, ho, h2⟩ := Option.bind_eq_some_iff.1 h1
  clear h1
  split at h2
  · cases h2
  have lb : 2 ≤ n₀.length := by
    have := begins_le (l := ["SEND seed", w1]) (ns := n₀) (by simpa using hb)
    simpa using this
  have lk := lookLen_le hk
  have lo := upTo_lt ho
  simp only [List.length_drop] at lk lo
  split at h2
  · rename_i hH
    obtain ⟨⟨t, p, r⟩, ht, h3⟩ := Option.bind_eq_some_iff.1 h2
    clear h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, -, -, -, -, rfl⟩ := h3
    obtain ⟨et, nt⟩ := tailCut_eats notM_H ht
    rw [if_pos hH] at hn
    subst hn
    rw [List.length_drop] at lb lk lo
    refine ⟨Eats.then ?_ et, NoM.append ?_ nt⟩
    · rw [List.drop_drop, List.drop_drop, List.drop_drop]
      apply eats_of _ (by omega)
      simp only [takes_cons, takes_nil]
      omega
    · exact noM_cons (show ("H.0.front" : String) ≠ _ by decide)
        (noM_cons (show ("H.0.call" : String) ≠ _ by decide)
        (noM_cons (show ("H.1.call" : String) ≠ _ by decide)
        (noM_cons (show ("H.1.quiet" : String) ≠ _ by decide)
        (noM_cons (show ("H.2.call" : String) ≠ _ by decide)
        (noM_cons (show ("H.3.call" : String) ≠ _ by decide)
        (noM_cons (show ("H.3.quiet" : String) ≠ _ by decide) noM_nil))))))
  · rename_i hH
    rw [if_neg hH] at hn
    subst hn
    split at h2
    · obtain ⟨sc, hsc, h3⟩ := Option.bind_eq_some_iff.1 h2
      clear h2
      obtain ⟨zr, hzr, h4⟩ := Option.bind_eq_some_iff.1 h3
      clear h3
      split at h4
      · cases h4
      rename_i hcz
      obtain ⟨⟨t, p, r⟩, ht, h5⟩ := Option.bind_eq_some_iff.1 h4
      clear h4
      simp only [Option.some.injEq, Prod.mk.injEq] at h5
      obtain ⟨rfl, -, -, -, -, rfl⟩ := h5
      obtain ⟨et, nt⟩ := tailCut_eats (notM_A a) ht
      have hcz' : sc < zr ∧ zr < o := by simpa using hcz
      refine ⟨Eats.then ?_ et, NoM.append ?_ nt⟩
      · rw [List.drop_drop, List.drop_drop]
        apply eats_of _ (by omega)
        simp only [takes_cons, takes_nil]
        omega
      · exact noM_cons ((notM_A a).ne _) (noM_cons ((notM_A a).ne _) (noM_cons ((notM_A a).ne _)
          (noM_cons ((notM_A a).ne _) (noM_cons ((notM_A a).ne _) (noM_cons ((notM_A a).ne _)
          noM_nil)))))
    · obtain ⟨⟨t, p, r⟩, ht, h5⟩ := Option.bind_eq_some_iff.1 h2
      clear h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h5
      obtain ⟨rfl, -, -, -, -, rfl⟩ := h5
      obtain ⟨et, nt⟩ := tailCut_eats (notM_G g) ht
      refine ⟨Eats.then ?_ et, NoM.append ?_ nt⟩
      · rw [List.drop_drop, List.drop_drop]
        apply eats_of _ (by omega)
        simp only [takes_cons, takes_nil]
        omega
      · exact noM_cons ((notM_G g).ne _) (noM_cons ((notM_G g).ne _) (noM_cons ((notM_G g).ne _)
          (noM_cons ((notM_G g).ne _) (noM_cons ((notM_G g).ne _) noM_nil))))

theorem linksCut_eats : ∀ (fuel g a pl : Nat) (ns : List String) (rows : List Cut) (pl' : Nat)
    (rest : List String), linksCut fuel g a pl ns = some (rows, pl', rest) →
    Eats rows ns rest ∧ NoM rows
  | 0, _, _, _, _, _, _, _, h => by
    unfold linksCut at h
    cases h
  | fuel + 1, g, a, pl, ns, rows, pl', rest, h => by
    unfold linksCut at h
    simp only [Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨⟨r1, g1, a1, p1, wh, n1⟩, hl, h1⟩ := Option.bind_eq_some_iff.1 h
    clear h
    obtain ⟨e1, m1⟩ := linkCut_eats hl
    dsimp only at h1
    split at h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, -, rfl⟩ := h1
      exact ⟨e1, m1⟩
    · obtain ⟨⟨more, p2, n2⟩, hm, h2⟩ := Option.bind_eq_some_iff.1 h1
      clear h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -, rfl⟩ := h2
      obtain ⟨e2, m2⟩ := linksCut_eats fuel g1 a1 p1 n1 more p2 n2 hm
      exact ⟨e1.then e2, m1.append m2⟩

theorem notM_F' (i : Nat) (w : String) : "F." ++ toString i ++ w ≠ "M.0.call" := by
  rw [String.append_assoc]
  exact notM_F.ne _

theorem stagesCut_eats : ∀ (fuel i pl : Nat) (ns : List String) (rows : List Cut) (j : Nat)
    (rest : List String), stagesCut fuel i pl ns = some (rows, j, rest) →
    Eats rows ns rest ∧ NoM rows
  | 0, _, _, _, _, _, _, h => by
    unfold stagesCut at h
    cases h
  | fuel + 1, i, pl, ns, rows, j, rest, h => by
    unfold stagesCut at h
    split at h
    · simp only [Option.bind_eq_bind, Option.pure_def] at h
      obtain ⟨c, hc, h1⟩ := Option.bind_eq_some_iff.1 h
      clear h
      obtain ⟨⟨more, j2, n2⟩, hm, h2⟩ := Option.bind_eq_some_iff.1 h1
      clear h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -, rfl⟩ := h2
      obtain ⟨e2, m2⟩ := stagesCut_eats fuel (i + 1) pl _ more j2 n2 hm
      have lc := upTo_lt hc
      refine ⟨Eats.then (eats_of ?_ (by omega)) e2, NoM.append ?_ m2⟩
      · simp only [takes_cons, takes_nil]
      · exact noM_cons (notM_F' i _) (noM_cons (notM_F' i _) noM_nil)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact ⟨⟨Nat.zero_le _, rfl⟩, noM_nil⟩

/-- The finish: beside what it eats: its last two names are "BASE lambda", "BASE". -/
theorem finishCut_eats {pl : Nat} {ns : List String} {rows : List Cut} {pl' : Nat}
    {rest : List String} (h : finishCut pl ns = some (rows, pl', rest)) :
    Eats rows ns rest ∧ NoM rows ∧ 2 ≤ takes rows ∧
      (ns.drop (takes rows - 2)).take 2 = ["BASE lambda", "BASE"] := by
  unfold finishCut at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, Option.bind_none] at h
  split at h
  · cases h
  rename_i h3
  obtain ⟨⟨st, i, n1⟩, hs, h1⟩ := Option.bind_eq_some_iff.1 h
  clear h
  dsimp only at h1
  split at h1
  · cases h1
  rename_i hB
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, -, rfl⟩ := h1
  obtain ⟨⟨ls, rfl⟩, ms⟩ := stagesCut_eats _ _ _ _ _ _ _ hs
  have l3 : 3 ≤ ns.length := by
    have := begins_le (l := ["SEND seed", "LOC", "BAT"]) (ns := ns) (by simpa using h3)
    simpa using this
  have hB' : begins ["BASE lambda", "BASE"] (List.drop (takes st) (List.drop 3 ns)) = true := by
    simpa using hB
  have l2 := begins_le hB'
  simp only [List.length_drop, List.length_cons, List.length_nil] at ls l2
  have ht : takes ([⟨"F.0.front", "fFront", pl, "sendLoc", 0⟩, ⟨"F.0.call", "fSwitch", pl,
      "sendLoc", 2⟩,
      ⟨"F.0.quiet", "fSwitchQuiet", pl, "sendLoc", 0⟩,
      ⟨"F.1.front", "fBatFront", pl + 1, "test", 0⟩, ⟨"F.1.call", "fBat", pl + 1, "test", 1⟩,
      ⟨"F.1.quiet", "fBatQuiet", pl + 1, "test", 0⟩] ++ st ++
      [⟨"F." ++ toString i ++ ".call", "fBase", pl + 1, "test", 2⟩]) = 3 + takes st + 2 := by
    simp only [takes_append, takes_cons, takes_nil]
  refine ⟨?_, ?_, by rw [ht]; omega, ?_⟩
  · rw [List.drop_drop, List.drop_drop]
    exact eats_of ht (by omega)
  · refine NoM.append (NoM.append ?_ ms) (noM_cons (notM_F' i _) noM_nil)
    exact noM_cons (show ("F.0.front" : String) ≠ _ by decide)
      (noM_cons (show ("F.0.call" : String) ≠ _ by decide)
      (noM_cons (show ("F.0.quiet" : String) ≠ _ by decide)
      (noM_cons (show ("F.1.front" : String) ≠ _ by decide)
      (noM_cons (show ("F.1.call" : String) ≠ _ by decide)
      (noM_cons (show ("F.1.quiet" : String) ≠ _ by decide) noM_nil)))))
  · rw [ht, show 3 + takes st + 2 - 2 = 3 + takes st by omega, ← List.drop_drop]
    exact eq_of_beq hB'

/-- **THE LAW ON cutOf.** A table that cutOf returns is a front and the members' six rows; no row of
the front is the step "M.0.call"; the front's rows take just the names in front of the members'; and
the last two of these names are "BASE lambda", "BASE". -/
theorem cutOf_front {es : List Fmt.Entry} {cs : List Cut} (h : cutOf es = some cs) :
    ∃ front pl q b, cs = front ++ endCuts pl q b ∧ NoM front ∧ 2 ≤ takes front ∧
      takes front ≤ es.length ∧
      ((es.map (·.name)).drop (takes front - 2)).take 2 = ["BASE lambda", "BASE"] := by
  unfold cutOf at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨⟨a, pl, r₁⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨b, pl', r₂⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  obtain ⟨q, n, rfl, -⟩ := membersCut_eq hc
  obtain ⟨⟨la, rfl⟩, ma⟩ := linksCut_eats _ _ _ _ _ _ _ _ ha
  obtain ⟨⟨lb, -⟩, mb, b2, hB⟩ := finishCut_eats hb
  rw [List.length_drop] at lb
  rw [List.length_map] at la lb
  refine ⟨a ++ b, pl', q, n, rfl, ma.append mb, by rw [takes_append]; omega,
    by rw [takes_append]; omega, ?_⟩
  rw [List.drop_drop] at hB
  rw [takes_append, show takes a + takes b - 2 = takes a + (takes b - 2) by omega]
  exact hB

theorem foldl_takes (l : List Cut) : ∀ k : Nat, l.foldl (fun n c => n + c.take) k = k + takes l :=
    by
  induction l with
  | nil => intro k; rfl
  | cons a l ih =>
    intro k
    rw [List.foldl_cons, ih, takes_cons]
    omega

/-- **The rounds in front of the step "M.0.call" are the front's.** -/
theorem rounds_before_call {front : List Cut} (hN : NoM front) (pl q b : Nat) :
    ((front ++ endCuts pl q b).any fun c => c.look == "M.0.call") = true ∧
      ((front ++ endCuts pl q b).takeWhile fun c => c.look != "M.0.call").foldl
        (fun n c => n + c.take) 0 = takes front := by
  constructor
  · rw [List.any_append, Bool.or_eq_true]
    exact .inr rfl
  · rw [List.takeWhile_append_of_pos (fun c hc => by simpa using hN c hc), foldl_takes,
      takes_append]
    have e : takes ((endCuts pl q b).takeWhile fun c => c.look != "M.0.call") = 0 := rfl
    rw [e]
    omega

/-- **THE START, FROM WHERE "BASE lambda" STANDS.** ds: the plan's rounds, whatever their type; f:
a round's entry. Where the name "BASE lambda" stands neither among the first p rounds nor behind
round p, the front of the table takes just p + 2 rounds. -/
theorem front_of_base {α : Type} (ds : List α) (f : α → Fmt.Entry) {cs : List Cut}
    (h : cutOf (ds.map f) = some cs) (p : Nat)
    (hb : ((ds.take p).all fun d => (f d).name != "BASE lambda") = true)
    (ha : ((ds.drop (p + 1)).all fun d => (f d).name != "BASE lambda") = true) :
    ∃ front pl q b, cs = front ++ endCuts pl q b ∧ NoM front ∧ takes front = p + 2 := by
  obtain ⟨front, pl, q, b, e, hN, h2, -, hB⟩ := cutOf_front h
  refine ⟨front, pl, q, b, e, hN, ?_⟩
  have h0 : (((ds.map f).map (·.name)).drop (takes front - 2))[0]? = some "BASE lambda" := by
    have := congrArg (fun l => l[0]?) hB
    simpa [List.getElem?_take] using this
  rw [List.getElem?_drop, List.map_map, List.getElem?_map, Nat.add_zero] at h0
  obtain ⟨d, hd, hn⟩ := Option.map_eq_some_iff.1 h0
  have hn' : (f d).name = "BASE lambda" := hn
  have hlt := (List.getElem?_eq_some_iff.1 hd).1
  by_cases c1 : takes front - 2 < p
  · have hm : d ∈ ds.take p := by
      refine List.mem_iff_getElem?.2 ⟨takes front - 2, ?_⟩
      rw [List.getElem?_take_of_lt c1]
      exact hd
    have := List.all_eq_true.1 hb d hm
    simp [hn'] at this
  · by_cases c2 : p < takes front - 2
    · have hm : d ∈ ds.drop (p + 1) := by
        refine List.mem_iff_getElem?.2 ⟨takes front - 2 - (p + 1), ?_⟩
        rw [List.getElem?_drop, show p + 1 + (takes front - 2 - (p + 1)) = takes front - 2 by omega]
        exact hd
      have := List.all_eq_true.1 ha d hm
      simp [hn'] at this
    · omega

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.cutOf_front
#print axioms VerifiableInference.Desc.First.rounds_before_call
#print axioms VerifiableInference.Desc.First.front_of_base
