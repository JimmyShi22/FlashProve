-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SkipRel.lean: the states of two experiments of deferred programming of which the second lacks
work that is never shown. The relation on states; lemmas on moves; no probability.

Rom/Skip.lean relates two programs of the language `Step`, the second of which leaves out work that
is never shown, through a correspondence w (which tokens correspond, which tokens of the first are
dead). Here is the matching relation on the states `DSt` of Rom/Defer.lean:

  `TokRel w v₁ v₂ s₁ s₂`   The stores v and the lists s of shown tokens: ρ and sl together are a
                           partial bijection between existing tokens that denote the same string; a
                           pair of ρ is shown on both sides or on neither, a sealed pair on neither;
                           a dead token exists, is outside the bijection and is not shown.
  `EvsRel w l₁ l₂`         The records of marked evaluations: l₂ is l₁ without some records that are
                           charged to hidden (dead or sealed) tokens, with the tokens renamed along
                           the bijection.
  `StRel w d₁ d₂`          Both, and: the same table, the same numbers of plain evaluations, and "if
                           the first experiment has seen no violation of the rules, neither has the
                           second".

Most of the lemmas are the parts from which `Skip.run` (Rom/SkipRun.lean) shows that each move
allowed by `Skip` preserves `StRel` (in mode I).
-/
import Rom.Skip
noncomputable section -- Lean tags what it cannot compile

namespace Rom

variable {S : OSpec}

/-! ## Tokens -/

structure TokRel (w : Wd) (v₁ v₂ : List Bits) (s₁ s₂ : List ℕ) : Prop where
  n₁ : w.n₁ ≤ v₁.length
  n₂ : w.n₂ ≤ v₂.length
  lt : ∀ a b : ℕ, w.rel a b → a < v₁.length ∧ b < v₂.length
  injL : ∀ a b b' : ℕ, w.rel a b → w.rel a b' → b = b'
  injR : ∀ a a' b : ℕ, w.rel a b → w.rel a' b → a = a'
  ddlt : ∀ a : ℕ, w.dd a → a < v₁.length
  ddρ : ∀ a b : ℕ, w.dd a → ¬ w.rel a b
  val : ∀ a b : ℕ, w.rel a b → v₁.getD a [] = v₂.getD b []
  shown : ∀ a b : ℕ, w.ρ a b → (a ∈ s₁ ↔ b ∈ s₂)
  slshown : ∀ a b : ℕ, w.sl a b → a ∉ s₁ ∧ b ∉ s₂
  slρ : ∀ a b : ℕ, w.sl a b → ¬ w.ρ a b
  ddshown : ∀ a : ℕ, w.dd a → a ∉ s₁
  shlt₁ : ∀ a ∈ s₁, a < v₁.length
  shlt₂ : ∀ b ∈ s₂, b < v₂.length

theorem getD_append_lt {l : List Bits} {a : ℕ} (h : a < l.length) (x : Bits) :
    (l ++ [x]).getD a [] = l.getD a [] := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left h]

theorem getD_append_length (l : List Bits) (x : Bits) : (l ++ [x]).getD l.length [] = x := by
  simp [List.getD_eq_getElem?_getD]

theorem Wd.rel_pair {w : Wd} {t₁ t₂ a b : ℕ} (h : (w.pair t₁ t₂).rel a b) :
    w.rel a b ∨ (a = t₁ ∧ b = t₂) := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr h
  · exact Or.inl (Or.inr h)

theorem Wd.rel_shut {w : Wd} {t₁ t₂ a b : ℕ} (h : (w.shut t₁ t₂).rel a b) :
    w.rel a b ∨ (a = t₁ ∧ b = t₂) := by
  rcases h with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

namespace TokRel

variable {w : Wd} {v₁ v₂ : List Bits} {s₁ s₂ : List ℕ}

theorem len_succ {l : List Bits} {a : ℕ} (x : Bits) (h : a < l.length) : a < (l ++ [x]).length := by
  simp only [List.length_append, List.length_singleton]
  omega

/-- what two new tokens with the same string need, whichever relation takes them up -/
theorem add (h : TokRel w v₁ v₂ s₁ s₂) (x : Bits) (w' : Wd) (hn₁ : w'.n₁ = v₁.length + 1)
    (hn₂ : w'.n₂ = v₂.length + 1)
    (hrel : ∀ a b : ℕ, w'.rel a b → w.rel a b ∨ (a = v₁.length ∧ b = v₂.length))
    (hdd : ∀ a : ℕ, w'.dd a → w.dd a)
    (hρ : ∀ a b : ℕ, w'.ρ a b → w.ρ a b ∨ (a = v₁.length ∧ b = v₂.length))
    (hsl : ∀ a b : ℕ, w'.sl a b → w.sl a b ∨ (a = v₁.length ∧ b = v₂.length))
    (hex : ∀ a b : ℕ, w'.sl a b → w'.ρ a b → w.sl a b ∧ w.ρ a b) :
    TokRel w' (v₁ ++ [x]) (v₂ ++ [x]) s₁ s₂ where
  n₁ := by rw [hn₁]; simp
  n₂ := by rw [hn₂]; simp
  lt := by
    intro a b hab
    rcases hrel a b hab with hab | ⟨rfl, rfl⟩
    · exact ⟨len_succ x (h.lt a b hab).1, len_succ x (h.lt a b hab).2⟩
    · simp
  injL := by
    intro a b b' hab hab'
    rcases hrel a b hab with hab | ⟨rfl, rfl⟩ <;> rcases hrel _ b' hab' with hab' | ⟨h1, rfl⟩
    · exact h.injL a b b' hab hab'
    · subst h1
      exact absurd (h.lt _ b hab).1 (lt_irrefl _)
    · exact absurd (h.lt _ b' hab').1 (lt_irrefl _)
    · rfl
  injR := by
    intro a a' b hab hab'
    rcases hrel a b hab with hab | ⟨rfl, rfl⟩ <;> rcases hrel a' _ hab' with hab' | ⟨rfl, h1⟩
    · exact h.injR a a' b hab hab'
    · subst h1
      exact absurd (h.lt a _ hab).2 (lt_irrefl _)
    · exact absurd (h.lt a' _ hab').2 (lt_irrefl _)
    · rfl
  ddlt := fun a ha => len_succ x (h.ddlt a (hdd a ha))
  ddρ := by
    intro a b ha hab
    rcases hrel a b hab with hab | ⟨rfl, rfl⟩
    · exact h.ddρ a b (hdd a ha) hab
    · exact absurd (h.ddlt _ (hdd _ ha)) (lt_irrefl _)
  val := by
    intro a b hab
    rcases hrel a b hab with hab | ⟨rfl, rfl⟩
    · rw [getD_append_lt (h.lt a b hab).1, getD_append_lt (h.lt a b hab).2]
      exact h.val a b hab
    · rw [getD_append_length, getD_append_length]
  shown := by
    intro a b hab
    rcases hρ a b hab with hab | ⟨rfl, rfl⟩
    · exact h.shown a b hab
    · exact ⟨fun h1 => absurd (h.shlt₁ _ h1) (lt_irrefl _),
        fun h1 => absurd (h.shlt₂ _ h1) (lt_irrefl _)⟩
  slshown := by
    intro a b hab
    rcases hsl a b hab with hab | ⟨rfl, rfl⟩
    · exact h.slshown a b hab
    · exact ⟨fun h1 => absurd (h.shlt₁ _ h1) (lt_irrefl _),
        fun h1 => absurd (h.shlt₂ _ h1) (lt_irrefl _)⟩
  slρ := fun a b h1 h2 => h.slρ a b (hex a b h1 h2).1 (hex a b h1 h2).2
  ddshown := fun a ha => h.ddshown a (hdd a ha)
  shlt₁ := fun a ha => len_succ x (h.shlt₁ a ha)
  shlt₂ := fun a ha => len_succ x (h.shlt₂ a ha)

/-- two new tokens with the same string -/
theorem pair (h : TokRel w v₁ v₂ s₁ s₂) (x : Bits) :
    TokRel (w.pair v₁.length v₂.length) (v₁ ++ [x]) (v₂ ++ [x]) s₁ s₂ :=
  h.add x _ rfl rfl (fun _ _ => Wd.rel_pair) (fun _ ha => ha) (fun _ _ hab => hab)
      (fun _ _ hab => Or.inl hab) fun a b h1 h2 => by
    rcases h2 with h2 | ⟨rfl, rfl⟩
    · exact ⟨h1, h2⟩
    · exact absurd (h.lt _ _ (Or.inr h1)).1 (lt_irrefl _)

/-- two new sealed tokens with the same string -/
theorem shut (h : TokRel w v₁ v₂ s₁ s₂) (x : Bits) :
    TokRel (w.shut v₁.length v₂.length) (v₁ ++ [x]) (v₂ ++ [x]) s₁ s₂ :=
  h.add x _ rfl rfl (fun _ _ => Wd.rel_shut) (fun _ ha => ha) (fun _ _ hab => Or.inl hab)
      (fun _ _ hab => hab) fun a b h1 h2 => by
    rcases h1 with h1 | ⟨rfl, rfl⟩
    · exact ⟨h1, h2⟩
    · exact absurd (h.lt _ _ (Or.inl h2)).1 (lt_irrefl _)

/-- a new dead token of the first experiment -/
theorem dead (h : TokRel w v₁ v₂ s₁ s₂) (x : Bits) :
    TokRel (w.dead v₁.length) (v₁ ++ [x]) v₂ s₁ s₂ where
  n₁ := by simp [Wd.dead]
  n₂ := h.n₂
  lt := fun a b hab => ⟨len_succ x (h.lt a b hab).1, (h.lt a b hab).2⟩
  injL := h.injL
  injR := h.injR
  ddlt := by
    rintro a (ha | rfl)
    · exact len_succ x (h.ddlt a ha)
    · simp
  ddρ := by
    rintro a b (ha | rfl) hab
    · exact h.ddρ a b ha hab
    · exact absurd (h.lt _ b hab).1 (lt_irrefl _)
  val := fun a b hab => by
    rw [getD_append_lt (h.lt a b hab).1]
    exact h.val a b hab
  shown := h.shown
  slshown := h.slshown
  slρ := h.slρ
  ddshown := by
    rintro a (ha | rfl)
    · exact h.ddshown a ha
    · exact fun h1 => absurd (h.shlt₁ _ h1) (lt_irrefl _)
  shlt₁ := fun a ha => len_succ x (h.shlt₁ a ha)
  shlt₂ := h.shlt₂

/-- under `TokRel`: related tokens are shown on both sides or on neither -/
theorem shown_rel (h : TokRel w v₁ v₂ s₁ s₂) {a b : ℕ} (hab : w.rel a b) : a ∈ s₁ ↔ b ∈ s₂ := by
  rcases hab with hab | hab
  · exact h.shown a b hab
  · exact ⟨fun h1 => absurd h1 (h.slshown a b hab).1, fun h1 => absurd h1 (h.slshown a b hab).2⟩

/-- under `TokRel`: a hidden token is not shown -/
theorem hid_shown (h : TokRel w v₁ v₂ s₁ s₂) {a : ℕ} (ha : w.hid a) : a ∉ s₁ := by
  rcases ha with ha | ⟨b, hab⟩
  · exact h.ddshown a ha
  · exact (h.slshown a b hab).1

theorem mem_left {R : ℕ → ℕ → Prop} {l₁ l₂ : List ℕ}
    (hl : List.Forall₂ R l₁ l₂) {a : ℕ} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction hl with
  | nil => cases ha
  | cons hab _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem mem_right {R : ℕ → ℕ → Prop} {l₁ l₂ : List ℕ}
    (hl : List.Forall₂ R l₁ l₂) {b : ℕ} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction hl with
  | nil => cases hb
  | cons hab _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

/-- membership in related lists -/
theorem mem_iff (h : TokRel w v₁ v₂ s₁ s₂) {l₁ l₂ : List ℕ} (hl : List.Forall₂ w.rel l₁ l₂)
    {a b : ℕ} (hab : w.rel a b) : a ∈ l₁ ↔ b ∈ l₂ := by
  constructor
  · intro ha
    obtain ⟨b', hb', h'⟩ := mem_left hl ha
    rwa [h.injL a b b' hab h']
  · intro hb
    obtain ⟨a', ha', h'⟩ := mem_right hl hb
    rwa [h.injR a a' b hab h']

/-- tokens related by ρ are shown (the rule `Skip.reveal`) -/
theorem reveal (h : TokRel w v₁ v₂ s₁ s₂) {ts₁ ts₂ : List ℕ} (hts : List.Forall₂ w.ρ ts₁ ts₂) :
    TokRel w v₁ v₂ (s₁ ++ ts₁) (s₂ ++ ts₂) where
  n₁ := h.n₁
  n₂ := h.n₂
  lt := h.lt
  injL := h.injL
  injR := h.injR
  ddlt := h.ddlt
  ddρ := h.ddρ
  val := h.val
  shown := fun a b hab => by
    rw [List.mem_append, List.mem_append, h.shown a b hab,
      h.mem_iff (Skip.forall₂_rel hts) (Or.inl hab)]
  slshown := fun a b hab => by
    refine ⟨fun h1 => ?_, fun h1 => ?_⟩
    · rcases List.mem_append.1 h1 with h1 | h1
      · exact (h.slshown a b hab).1 h1
      · obtain ⟨b', _, hab'⟩ := mem_left hts h1
        have e := h.injL a b b' (Or.inr hab) (Or.inl hab')
        exact h.slρ a b hab (e ▸ hab')
    · rcases List.mem_append.1 h1 with h1 | h1
      · exact (h.slshown a b hab).2 h1
      · obtain ⟨a', _, hab'⟩ := mem_right hts h1
        have e := h.injR a a' b (Or.inr hab) (Or.inl hab')
        exact h.slρ a b hab (e ▸ hab')
  slρ := h.slρ
  ddshown := fun a ha h1 => by
    rcases List.mem_append.1 h1 with h1 | h1
    · exact h.ddshown a ha h1
    · obtain ⟨b, _, hab⟩ := mem_left hts h1
      exact h.ddρ a b ha (Or.inl hab)
  shlt₁ := fun a ha => by
    rcases List.mem_append.1 ha with ha | ha
    · exact h.shlt₁ a ha
    · obtain ⟨b, _, hab⟩ := mem_left hts ha
      exact (h.lt a b (Or.inl hab)).1
  shlt₂ := fun b hb => by
    rcases List.mem_append.1 hb with hb | hb
    · exact h.shlt₂ b hb
    · obtain ⟨a, _, hab⟩ := mem_right hts hb
      exact (h.lt a b (Or.inl hab)).2

theorem map_val (h : TokRel w v₁ v₂ s₁ s₂) {l₁ l₂ : List ℕ} (hl : List.Forall₂ w.rel l₁ l₂) :
    (l₁.map fun t => v₁.getD t []) = l₂.map fun t => v₂.getD t [] := by
  induction hl with
  | nil => rfl
  | cons hab _ ih => rw [List.map_cons, List.map_cons, ih, h.val _ _ hab]

end TokRel

/-! ## Records of marked evaluations -/

/-- the record e with other tokens -/
def Ev.ren (e : Ev S) (c : Tok) (us : List Tok) (t : Tok) : Ev S :=
  ⟨e.o, e.pt, e.ans, c, us, t, e.released⟩

inductive EvsRel (w : Wd) : List (Ev S) → List (Ev S) → Prop
  | nil : EvsRel w [] []
  | both {e₁ : Ev S} {l₁ l₂ : List (Ev S)} {c : Tok} {us : List Tok} {t : Tok}
      (hc : w.rel e₁.charged c) (hus : List.Forall₂ w.rel e₁.others us)
      (ht : w.rel e₁.tail t) (h : EvsRel w l₁ l₂) :
      EvsRel w (e₁ :: l₁) (e₁.ren c us t :: l₂)
  | left {e₁ : Ev S} {l₁ l₂ : List (Ev S)} (hc : w.hid e₁.charged) (h : EvsRel w l₁ l₂) :
      EvsRel w (e₁ :: l₁) l₂

namespace EvsRel

variable {w w' : Wd} {l₁ l₂ : List (Ev S)}

theorem mono (hw : w ≤ w') (h : EvsRel w l₁ l₂) : EvsRel w' l₁ l₂ := by
  induction h with
  | nil => exact .nil
  | both hc hus ht _ ih =>
    exact .both (hw.rel _ _ hc) (Skip.forall₂_rel_mono hw hus) (hw.rel _ _ ht) ih
  | left hc _ ih => exact .left (hw.hid _ hc) ih

theorem snoc_both (h : EvsRel w l₁ l₂) {e₁ : Ev S} {c : Tok} {us : List Tok} {t : Tok}
    (hc : w.rel e₁.charged c) (hus : List.Forall₂ w.rel e₁.others us) (ht : w.rel e₁.tail t) :
    EvsRel w (l₁ ++ [e₁]) (l₂ ++ [e₁.ren c us t]) := by
  induction h with
  | nil => exact .both hc hus ht .nil
  | both hc' hus' ht' _ ih => exact .both hc' hus' ht' ih
  | left hc' _ ih => exact .left hc' ih

theorem snoc_left (h : EvsRel w l₁ l₂) {e₁ : Ev S} (hc : w.hid e₁.charged) :
    EvsRel w (l₁ ++ [e₁]) l₂ := by
  induction h with
  | nil => exact .left hc .nil
  | both hc' hus' ht' _ ih => exact .both hc' hus' ht' ih
  | left hc' _ ih => exact .left hc' ih

/-- under `EvsRel`: every record of the second list comes from one of the first -/
theorem exists_left (h : EvsRel w l₁ l₂) :
    ∀ e₂ ∈ l₂, ∃ e₁ ∈ l₁,
      w.rel e₁.charged e₂.charged ∧
      List.Forall₂ w.rel e₁.others e₂.others ∧
      w.rel e₁.tail e₂.tail ∧
      e₂ = e₁.ren e₂.charged e₂.others e₂.tail := by
  induction h with
  | nil => intro e₂ he; cases he
  | both hc hus ht _ ih =>
    intro e₂ he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨_, List.mem_cons_self, hc, hus, ht, rfl⟩
    · obtain ⟨e₁, h1, h2⟩ := ih e₂ he
      exact ⟨e₁, List.mem_cons_of_mem _ h1, h2⟩
  | left _ _ ih =>
    intro e₂ he
    obtain ⟨e₁, h1, h2⟩ := ih e₂ he
    exact ⟨e₁, List.mem_cons_of_mem _ h1, h2⟩

/-- under `EvsRel`: the second list has at most as many records of each oracle -/
theorem count_le (h : EvsRel w l₁ l₂) (o : S.ι) :
    (l₂.filter fun v => decide (v.o = o)).length ≤
      (l₁.filter fun v => decide (v.o = o)).length := by
  induction h with
  | nil => exact Nat.le_refl _
  | @both e₁ l₁ l₂ c us t _ _ _ _ ih =>
    by_cases ho : e₁.o = o
    · have h2 : (e₁.ren c us t).o = o := ho
      simp only [List.filter_cons, ho, h2, decide_true, if_true, List.length_cons]
      omega
    · have h2 : ¬ (e₁.ren c us t).o = o := ho
      simp only [List.filter_cons, ho, h2, decide_false, Bool.false_eq_true, if_false]
      exact ih
  | @left e₁ l₁ l₂ _ _ ih =>
    by_cases ho : e₁.o = o
    · simp only [List.filter_cons, ho, decide_true, if_true, List.length_cons]
      omega
    · simp only [List.filter_cons, ho, decide_false, Bool.false_eq_true, if_false]
      exact ih

end EvsRel

/-- what the release of one evaluation does to the table, in mode I -/
def wrI (T : Table S) (o : S.ι) (pt : S.Dom o) (ans : S.Rng o) : Table S :=
  match T o pt with
  | none => T.set o pt ans
  | some _ => T

theorem releaseAll_pos {shown : List ℕ} {e : Ev S}
    (h : (!e.released && shown.contains e.charged) = true) (es : List (Ev S)) (T : Table S) :
    releaseAll true shown (e :: es) T =
      ({ e with released := true } :: (releaseAll true shown es (wrI T e.o e.pt e.ans)).1,
        (releaseAll true shown es (wrI T e.o e.pt e.ans)).2) := by
  rw [releaseAll, if_pos h]
  cases hT : T e.o e.pt <;> simp only [wrI, hT, if_true]

theorem releaseAll_neg {shown : List ℕ} {e : Ev S}
    (h : ¬ (!e.released && shown.contains e.charged) = true) (es : List (Ev S)) (T : Table S) :
    releaseAll true shown (e :: es) T =
      (e :: (releaseAll true shown es T).1, (releaseAll true shown es T).2) := by
  rw [releaseAll, if_neg h]

/-- Under `TokRel`, `EvsRel`, in mode I, from one table: a release does the same to both tables, and
preserves the relation of the records. -/
theorem releaseAll_rel {w : Wd} {v₁ v₂ : List Bits} {s₁ s₂ : List Tok} (ht : TokRel w v₁ v₂ s₁ s₂)
    {l₁ l₂ : List (Ev S)} (h : EvsRel w l₁ l₂) :
    ∀ T : Table S,
      (releaseAll true s₁ l₁ T).2 = (releaseAll true s₂ l₂ T).2 ∧
      EvsRel w (releaseAll true s₁ l₁ T).1 (releaseAll true s₂ l₂ T).1 := by
  induction h with
  | nil => intro T; exact ⟨rfl, .nil⟩
  | @both e₁ l₁ l₂ c us t hc hus htl _ ih =>
    intro T
    have hs : s₂.contains c = s₁.contains e₁.charged := by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
      exact (ht.shown_rel hc).symm
    by_cases hr : (!e₁.released && s₁.contains e₁.charged) = true
    · have hr2 : (!(e₁.ren c us t).released && s₂.contains (e₁.ren c us t).charged) = true := by
        show (!e₁.released && s₂.contains c) = true
        rw [hs]; exact hr
      rw [releaseAll_pos hr, releaseAll_pos hr2]
      have h1 := ih (wrI T e₁.o e₁.pt e₁.ans)
      exact ⟨h1.1, .both (e₁ := { e₁ with released := true }) hc hus htl h1.2⟩
    · have hr2 : ¬ (!(e₁.ren c us t).released && s₂.contains (e₁.ren c us t).charged) = true := by
        show ¬ (!e₁.released && s₂.contains c) = true
        rw [hs]; exact hr
      rw [releaseAll_neg hr, releaseAll_neg hr2]
      exact ⟨(ih T).1, .both hc hus htl (ih T).2⟩
  | @left e₁ l₁ l₂ hc _ ih =>
    intro T
    have hr : ¬ (!e₁.released && s₁.contains e₁.charged) = true := by
      intro h1
      rw [Bool.and_eq_true, List.contains_iff_mem] at h1
      exact ht.hid_shown hc h1.2
    rw [releaseAll_neg hr]
    exact ⟨(ih T).1, .left hc (ih T).2⟩

/-- under `TokRel`, `EvsRel`: if all released records of the first list have their tokens shown, so
have those of the second -/
theorem closedUnder_rel {w : Wd} {v₁ v₂ : List Bits} {s₁ s₂ : List Tok} (ht : TokRel w v₁ v₂ s₁ s₂)
    {l₁ l₂ : List (Ev S)} (h : EvsRel w l₁ l₂) (hc : closedUnder s₁ l₁ = true) :
    closedUnder s₂ l₂ = true := by
  unfold closedUnder at hc ⊢
  rw [List.all_eq_true] at hc ⊢
  intro e₂ he₂
  obtain ⟨e₁, he₁, -, hus, htl, heq⟩ := h.exists_left e₂ he₂
  have h1 := hc e₁ he₁
  have hrel : e₂.released = e₁.released := by rw [heq]; rfl
  rw [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at h1 ⊢
  rw [hrel]
  rcases h1 with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨?_, fun u hu => ?_⟩
    · rw [List.contains_iff_mem] at h1 ⊢
      exact (ht.shown_rel htl).1 h1
    · obtain ⟨a, ha, hab⟩ := TokRel.mem_right hus hu
      have := h2 a ha
      rw [List.contains_iff_mem] at this ⊢
      exact (ht.shown_rel hab).1 this

/-! ## States -/

structure StRel (w : Wd) (d₁ d₂ : DSt S) : Prop where
  tok : TokRel w d₁.vals d₂.vals d₁.shown d₂.shown
  table : d₁.table = d₂.table
  evs : EvsRel w d₁.evs d₂.evs
  nPlain : d₁.nPlain = d₂.nPlain
  viol : d₁.viol = false → d₂.viol = false

/-- the test of Rom.Step.run for a marked evaluation -/
def markBad (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) : Bool :=
  decide (d.vals.length ≤ t) || us.any (fun u => decide (d.vals.length ≤ u)) || us.contains t ||
    d.shown.contains t ||
    d.evs.any fun e => decide (e.o = o) && (e.charged == t || e.others.contains t)

/-- under `StRel`, on related tokens: a marked evaluation that the first experiment allows is
allowed in the second -/
theorem markBad_rel {w : Wd} {d₁ d₂ : DSt S} (h : StRel w d₁ d₂) (o : S.ι)
    {t₁ t₂ : Tok} {us₁ us₂ : List Tok} (ht : w.rel t₁ t₂)
    (hus : List.Forall₂ w.rel us₁ us₂) (hb : markBad d₁ o t₁ us₁ = false) :
    markBad d₂ o t₂ us₂ = false := by
  unfold markBad at hb ⊢
  simp only [Bool.or_eq_false_iff] at hb ⊢
  obtain ⟨⟨⟨⟨-, -⟩, h3⟩, h4⟩, h5⟩ := hb
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have := (h.tok.lt _ _ ht).2
    simp only [decide_eq_false_iff_not]
    omega
  · rw [List.any_eq_false]
    intro u hu
    obtain ⟨a, _, hab⟩ := TokRel.mem_right hus hu
    have := (h.tok.lt _ _ hab).2
    simp only [decide_eq_true_eq]
    omega
  · rw [Bool.eq_false_iff] at h3 ⊢
    intro h6
    rw [List.contains_iff_mem] at h6
    exact h3 (List.contains_iff_mem.2 ((h.tok.mem_iff hus ht).2 h6))
  · rw [Bool.eq_false_iff] at h4 ⊢
    intro h6
    rw [List.contains_iff_mem] at h6
    exact h4 (List.contains_iff_mem.2 ((h.tok.shown_rel ht).2 h6))
  · rw [List.any_eq_false] at h5 ⊢
    intro e₂ he₂ h6
    obtain ⟨e₁, he₁, hc, hos, -, heq⟩ := h.evs.exists_left e₂ he₂
    refine h5 e₁ he₁ ?_
    have ho : e₂.o = e₁.o := by rw [heq]; rfl
    rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq, List.contains_iff_mem] at h6 ⊢
    refine ⟨ho ▸ h6.1, ?_⟩
    rcases h6.2 with h7 | h7
    · exact Or.inl (h.tok.injR _ _ _ hc (h7 ▸ ht))
    · exact Or.inr ((h.tok.mem_iff hos ht).2 h7)

end Rom
