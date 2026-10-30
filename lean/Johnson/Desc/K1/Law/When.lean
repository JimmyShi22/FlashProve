-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/When.lean: on what the yes of the sending's decision hangs.

Main names: fit_facts (what the test of the rounds gives here); answers_sum, le_seeds (a seed is
there for each answer, at every place), fitB_true, fitB_length; pow_logEll, pad_isSome;
answers_len; whenLaw; yesAll_fails_when, noAll_fails_when.
The premise that every code's length is a power of two is used in one direction alone: that the
decision says yes. The kind's rows count a pad's places by 2 ^ logEll, the statement's page by the
length itself.
Plain records and pure functions of the verifier program are named, none that takes a context or
runs: Send.pad, Send.cube, Codes.lengthsOk, Blk.shapeOk.

What is not claimed. A decision that says yes on the right side and writes nothing meets WhenLaw:
WritesLaw excludes it. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain

variable {L : Type}

/-! ## Counts -/

theorem fold_sum (l : List OracleShape) : ∀ acc : Nat,
    (l.filter (·.answers != 0)).foldl (fun a s => a + s.answers) acc =
      acc + (l.map (·.answers)).sum := by
  induction l with
  | nil => intro acc; simp
  | cons s l ih =>
    intro acc
    by_cases h : s.answers = 0
    · simp [h, ih]
    · simp [h, ih, Nat.add_assoc]

theorem answers_sum (P : Par) : P.answers = ((shapesOf P).map (·.answers)).sum := by
  have := fold_sum (shapesOf P) 0
  simpa [Par.answers, Par.tuple, shapesOf] using this

theorem fold_max_ge (l : List OracleShape) : ∀ acc : Nat,
    acc ≤ l.foldl (fun a s => max a s.answers) acc ∧
      ∀ s ∈ l, s.answers ≤ l.foldl (fun a s => max a s.answers) acc := by
  induction l with
  | nil => intro acc; simp
  | cons t l ih =>
    intro acc
    have h := ih (max acc t.answers)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h.1, fun s hs => ?_⟩
    rcases List.mem_cons.1 hs with rfl | hs
    · exact Nat.le_trans (Nat.le_max_right _ _) h.1
    · exact h.2 s hs

/-- A seed is there for each answer, whatever the place. -/
theorem le_seeds (P : Par) (s : OracleShape) (hs : s ∈ shapesOf P) : s.answers ≤ P.seeds := by
  by_cases h : s.answers = 0
  · omega
  · refine (fold_max_ge P.tuple 0).2 s ?_
    simp only [Par.tuple, List.mem_filter]
    exact ⟨hs, by simpa using h⟩

theorem fitB_true (codes : Codes) (n : Nat) : ∀ (shapes : List OracleShape) (ys : List E),
    (∀ s ∈ shapes, s.answers ≠ 0 → s.answers ≤ n ∧ (Send.pad codes s).isSome = true) →
    ys.length = (shapes.map (·.answers)).sum → fitB codes n shapes ys = true
  | [], ys, _, hy => by
    simp only [List.map_nil, List.sum_nil, List.length_eq_zero_iff] at hy
    simp [fitB, hy]
  | s :: l, ys, h, hy => by
    simp only [List.map_cons, List.sum_cons] at hy
    by_cases h0 : s.answers = 0
    · simp only [fitB, h0, if_true]
      exact fitB_true codes n l ys (fun t ht => h t (List.mem_cons_of_mem _ ht)) (by omega)
    · have h1 := h s (List.mem_cons_self) h0
      have ih := fitB_true codes n l (ys.drop s.answers)
        (fun t ht => h t (List.mem_cons_of_mem _ ht)) (by rw [List.length_drop]; omega)
      have h2 : s.answers ≤ ys.length := by omega
      simp [fitB, h0, h1.1, h1.2, h2, ih]

/-- What fitB says of the number of answers. -/
theorem fitB_length (codes : Codes) (n : Nat) : ∀ (shapes : List OracleShape) (ys : List E),
    fitB codes n shapes ys = true → ys.length = (shapes.map (·.answers)).sum
  | [], ys, h => by
    simp only [fitB, List.isEmpty_iff] at h
    simp [h]
  | s :: l, ys, h => by
    by_cases h0 : s.answers = 0
    · simp only [fitB, h0, if_true] at h
      simp [h0, fitB_length codes n l ys h]
    · simp only [fitB, h0, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
      have := fitB_length codes n l _ h.2
      rw [List.length_drop] at this
      simp only [List.map_cons, List.sum_cons]
      omega

/-! ## The pad fits -/

theorem pow_logEll (A : Array Code) (i : Nat) (hi : i < A.size)
    (h : A.all (fun x => powerOfTwo x.ell) = true) :
    2 ^ (A.getD i default).logEll = (A.getD i default).ell := by
  have e : A.getD i default = A[i] := by simp [Array.getD_eq_getD_getElem?, hi]
  rw [e]
  have := Array.all_eq_true_iff_forall_mem.1 h A[i] (Array.getElem_mem hi)
  simp only [powerOfTwo, Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

theorem pad_isSome (codes : Codes) (s : OracleShape) (hl : codes.lengthsOk = true)
    (hs : Blk.shapeOk codes s = true) (hp : (Msg.of codes s).padFits = true) :
    (Send.pad codes s).isSome = true := by
  simp only [Codes.lengthsOk, Bool.and_eq_true] at hl
  simp only [Blk.shapeOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  simp only [Msg.padFits, Msg.of, Msg.e, decide_eq_true_eq] at hp
  unfold Send.pad Send.cube
  by_cases hz : s.maskRows = 0
  · have hm : s.code < codes.base.size := by
      rcases hs.1.1.2 with h | h
      · omega
      · exact h
    have e := pow_logEll codes.base s.code hm hl.1
    simp only [hz] at hp ⊢
    simp at hp ⊢
    rw [Array.getD_eq_getD_getElem?] at e
    rw [e] at hp
    exact hp
  · have hm : s.maskCode < codes.mask.size := by
      rcases hs.1.2 with h | h
      · exact absurd h hz
      · exact h
    have e := pow_logEll codes.mask s.maskCode hm hl.2
    have hz' : 0 < s.maskRows := Nat.pos_of_ne_zero hz
    simp [hz] at hp
    rw [Array.getD_eq_getD_getElem?] at e
    rw [e] at hp
    simp [hz', Nat.not_lt.2 hp]

/-! ## The rounds fit -/

theorem answers_of_items : ∀ (vals : List Fmt.ItemValue) (n : Nat),
    vals.map itemOf = List.replicate n .answer →
    (vals.filterMap fun | .answer x => some (E.ofTriple x) | _ => none).length = n
  | [], n, h => by
    cases n with
    | zero => rfl
    | succ n => simp [List.replicate_succ] at h
  | g :: l, n, h => by
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at h
      have ih := answers_of_items l n h.2
      cases g <;> simp_all [itemOf]

/-- What the test of the rounds gives here: how many elements the first round drew, and which items
the second holds. -/
theorem fit_facts (P : Par) (r₁ r₂ : Fmt.RoundView) (h : roundsFit (rounds P) [r₁, r₂] = true) :
    r₁.drawn.elems.length = (seedEntry P).drawE ∧
      r₂.vals.map itemOf =
        (Fmt.DeclaredRound.items { entry := answerEntry P }).filter (· != .root) := by
  simp only [rounds, roundsFit, Bool.and_eq_true, beq_iff_eq] at h
  tauto

theorem draw_len (P : Par) (r₁ r₂ : Fmt.RoundView) (h : roundsFit (rounds P) [r₁, r₂] = true) :
    (r₁.drawn.elems.map E.ofTriple).length = P.seeds * (P.coordinates + 1) := by
  rw [List.length_map, (fit_facts P r₁ r₂ h).1]
  rfl

theorem answers_len (P : Par) (r₁ r₂ : Fmt.RoundView) (h : roundsFit (rounds P) [r₁, r₂] = true) :
    (answersIn r₂).length = P.answers := by
  refine answers_of_items r₂.vals P.answers ?_
  rw [(fit_facts P r₁ r₂ h).2]
  simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, answerEntry]

theorem isOk_iff {α : Type} (x : Except String α) : x.isOk = true ↔ ∃ a, x = .ok a := by
  cases x <;> simp [Except.isOk, Except.toBool]

/-- **WHEN**, of the kind's own decision. -/
theorem whenLaw : WhenLaw fun _ => decideSend := by
  intro L P owed d r₁ r₂ hplan hlen hfit
  simp only [planOkOwn, planOk, Bool.and_eq_true] at hplan
  obtain ⟨⟨⟨hsh, hlay⟩, _⟩, hpad⟩ := hplan
  have hf : fitB P.codes P.seeds (shapesOf P) (answersIn r₂) = true := by
    refine fitB_true _ _ _ _ (fun s hs h0 => ⟨le_seeds P s hs, ?_⟩)
      (by rw [answers_len P r₁ r₂ hfit, answers_sum])
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hs
    refine pad_isSome _ _ hlen
      (Array.all_eq_true_iff_forall_mem.1 hsh n (Array.mem_toList_iff.1 hn)) ?_
    refine List.all_eq_true.1 hpad n.shape ?_
    simp only [Par.tuple, List.mem_filter]
    exact ⟨hs, by simpa using h0⟩
  rw [isOk_iff]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨⟨h1, h2, h3, h4, _⟩, _, _⟩ := (decideSend_iff P owed d x.2 r₁ r₂ x.1).1 hx
    refine ⟨h1, h2, ?_, h3⟩
    simp only [Ground.ok, Ground.recvL, Ground.sentL, List.cons_append, List.nil_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h4
    exact h4.2.2
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨_, (decideSend_iff P owed d _ r₁ r₂ _).2 ⟨⟨h1, h2, h4, ?_, hf⟩, rfl, rfl⟩⟩
    simp only [Ground.ok, Ground.recvL, Ground.sentL, List.cons_append, List.nil_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
    rw [h2]
    exact ⟨hsh, hlay, h3⟩

theorem toy_len : toyP.codes.lengthsOk = true := by
  simp [toyP, Codes.lengthsOk, powerOfTwo, ceilLog2]

theorem yesAll_fails_when : ¬ WhenLaw yesAll := fun h =>
  nomatch ((h Unit toyP (some 0) toyD toyR₁ toyR₂ toy_plan toy_len toy_fit).1 rfl).1

theorem noAll_fails_when : ¬ WhenLaw noAll := fun h =>
  nomatch (h Unit toyP none toyD toyR₁ toyR₂ toy_plan toy_len toy_fit).2
    ⟨rfl, rfl, rfl, toy_asks.2.2.1⟩

end VerifiableInference.Desc.K1
