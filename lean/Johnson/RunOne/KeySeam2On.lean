-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySeam2On.lean, OVER KeyRows23At.lean (Free₃'s shown from Free₂'s · maskW from mask₁: the last chain's book begins as the first chain's · lin₀ | seatW out of the start's own yes (start₃E_lin · firstOut_numbers · seatW_of_numbers) · seatOmega₀ from Free₂.seatOmega) (Free₃'s order | order₀ at the first border are paid from Free₂'s order₁ | order) (borderB's clause on the codes is paid by the start's own two tests on the codes) (Free₃.reads at the first border is paid from Free₂.reads: the two readings lay and seat alike) (Free₃'s fence on the rows' content at the first border is paid from Free₂'s) (a further clause of borderB is paid: the border's row weights are the pending row's, of which the first chain's last book-keeping says that each is Tensor.ok) (Free₃'s fields at the first border are paid: ArrOk by Agree.arr · I's and V's places: the own book IS the first chain's last (under OffOk: off₃ leaves the first chain's trees' numbers) · Omega's: the border's copy of the book IS the shared chain's last) (the last chain's first promise is a Bool ON ITS OWN RECORD: paid here by unfolding the start: the counts off w · own · firstTree ARE the first chain's last statement's; V's number is the plan's (out of the first chain's last book-keeping, last₁); the border's copy holds Omega as the shared chain's last book-keeping has it) (the last chain's first promise says that the record IS what the start returns at what was handed: paid here by the seam's own premise) (at two frames, as KeySeams23.lean; with the seam and the end in the form that the top's RowsOwed asks: seam₂_rows · ends_rows). THE SEAM BETWEEN THE KEY FILE's SHARED AND LAST CHAIN, THE PROMISES' HALF: the shared chain's last promise and the start's yes give the last chain's first promise at the record that the start returns.
  firstOutFrom_spec · start₃_full   PROVED, in KeySeams23.lean: what the start's yes gives of its first record, field by field, at a shape whose masks go ahead: the statement and the book ARE the first chain's last; no root; W the last message but one, the mask the last, the own group the
                                    last group; the border lies; Omega has no number yet; the first own tree's number is the first chain's trees + 1
  form_of_shape₂                    PROVED: the shared chain's book-keeping Bool holds the shape's form as its first clause
  shape₃_first                      PROVED: so the last chain's book-keeping Bool of boundary 0, its counts read off what was handed over, holds at that record, GIVEN handedB (KeyHanded.lean) of the first chain's last state
  member_agree · seam₂On            PROVED: on₂ 12 at ((x, s₁), s₂) and start x s₁ s₂ = ok s₃ give on₃ 0 at ((x, s₁, s₂), s₃): the record and «no collision» pass by Agree.recOf; the open pins' samples and their «no collision» by Agree; the book-keeping by shape₃_first
Limits. Under Agree (a member: KeyOneReading.lean) and Starts (its member: starts_fkD). Whether on₂ 12 is ever met is not shown here. Nothing on soundness.

-/
import Johnson.RunOne.KeySeams23

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third (FirstOut SharedOut firstOutFrom start₃ start₃E)
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)

theorem form_of_shape₂ (S : LinShape) (a k : Nat) (d : St₂) (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a k d) = true) : LKFU.Shape23.formOk S = true := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, Bool.and_eq_true] at h
  exact h.1

/-- The shared chain's last book-keeping holds what the last chain's second boundary will want of Omega. -/
theorem omega_of_shape₂ (S : LinShape) (a : Nat) (d : St₂) (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 12 d) = true) : handed₂B a d = true := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, h11, -⟩ := h
  simp at h10 h11
  simp [handed₂B, h10.1, h11.1]

theorem shape₃_first (codes : Codes) (S : LinShape) (a : Nat) (idx : List Nat) (x : Xi) (s₁ : FirstState) (s₂ : St₂) (o : SharedOut) (s₃ : St₃) (l : LinFirst)
    (hf : LKFU.Shape23.formOk S = true) (hh : handedB a idx s₁ = true)
    (t1 : l.w + 2 = (firstOf s₁).1.oracles.size) (t2 : l.own + 1 = (firstOf s₁).1.groups.size) (t3 : l.mask = some (l.w + 1))
    (he : start₃E codes S (firstOf s₁).1 (firstOf s₁).2.1 (firstOf s₁).2.2.1 l.w l.own l.mask (firstOf s₁).2.2.2 o = .ok s₃) :
    LKFU.Shape23.ok (LKFU.Shape23.shape₃ S a (nOwn s₃) (gOwn s₃) (tOwn s₃) idx 0 s₃) = true := by
  have hm : S.masksAhead = true := by
    simp only [LKFU.Shape23.formOk, Bool.and_eq_true] at hf
    exact hf.1.1
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, h2, h1', -⟩ := start₃_full codes S _ _ _ _ _ _ _ o s₃ t1 t2 t3 he
  have en : nOwn s₃ = (firstOf s₁).1.oracles.size := by unfold nOwn; rw [e4]; omega
  have eg : gOwn s₃ = (firstOf s₁).1.groups.size := by unfold gOwn; rw [e5]; omega
  have et : tOwn s₃ = (firstOf s₁).2.1.trees.size := by unfold tOwn; rw [e9]; omega
  rw [en, eg, et]
  have hh' : LKFU.Shape23.msgIs (firstOf s₁).1 ((firstOf s₁).1.oracles.size - 2) (some a) false = true ∧
      LKFU.Shape23.msgIs (firstOf s₁).1 ((firstOf s₁).1.oracles.size - 1) none false = true ∧
      LKFU.Shape23.grpIs (firstOf s₁).1 ((firstOf s₁).1.groups.size - 1) (idx ++ [(firstOf s₁).1.oracles.size - 2]) 1 0 false = true := by
    have := hh
    simp only [handedB, handedSt, Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  obtain ⟨h1, h2'', h3⟩ := hh'
  simp [LKFU.Shape23.ok, LKFU.Shape23.shape₃, hf, e1, e2, e3, e4, e5, e6, e7, e8, e9, h1, h2'', h3]

section
variable {XI Cells M Smp Rec : Type} {F : FileDescription XI} {Fr₂ Fr₃ : Frame}
  {G₂ : Reading (P₂ × St₂) Cells M Smp Rec} {G₃ : Reading (P₃ × St₃) Cells M Smp Rec} {at_ : Where}
  {S : LinShape} {K₁ : KPlan} {R : KRead Cells M} {enc : (Nat → OnBytes.E) → Nat → OnBytes.E} {rad a : Nat} {idx : List Nat}
  {coll : Strs → Rec → Prop} {last₁ : FirstState → Bool} {src : St₃ → Bool} {off₂ off₃ : Nat → Nat} {t₁ : Nat}

theorem member_agree {start : Xi → FirstState → St₂ → Except String St₃} (A : Agree G₂ G₃ at_ start) (o : VerifiableInference.Desc.Oracle) (j t : Nat) (y : Strs) (z : Smp) (m : M)
    (h : Member F G₃ o j t y z m) : Member F G₂ o j t y z m := by
  unfold Member at h ⊢
  rw [A.enc, A.rad, A.meets] at h
  exact h

/-- The last chain's start asks in front that the shape is lawful at the codes. -/
theorem start₃E_lin (codes : Codes) (S : LinShape) (st₁ : Statement) (book₁ : TreeBook) (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : St₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) : OnBytes.linOk codes S = true := by
  unfold start₃E at h
  split at h
  · cases h
  · rename_i hc
    have h2 : (codes.lengthsOk && OnBytes.linOk codes S) = true := by simpa using hc
    simp only [Bool.and_eq_true] at h2
    exact h2.2

/-- What the first chain's end hands has passed the test on its numbers. -/
theorem firstOut_numbers (S : LinShape) (st : Statement) (book : TreeBook) (roots w own : Nat) (mask : Option Nat) (pile : List TensorRow) (f : FirstOut)
    (h : firstOutFrom S st book roots w own mask pile = some f) : VerifiableInference.Desc.Third.numbersOk S f = true := by
  unfold firstOutFrom at h
  split at h
  · split at h
    · dsimp only at h
      split at h
      · rename_i hn
        cases h
        exact hn
      · cases h
    · cases h
  · cases h

/-- That test asks W's shape. -/
theorem seatW_of_numbers (S : LinShape) (f : FirstOut) (h : VerifiableInference.Desc.Third.numbersOk S f = true) : (f.st.oracles[f.w]?).any (·.shape == S.w) = true := by
  unfold VerifiableInference.Desc.Third.numbersOk at h
  split at h
  · rename_i x G hx hG
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [hx]
    show (x.shape == S.w) = true
    rw [h.1.1.1.1.1]
    exact beq_self_eq_true _
  · cases h

/-- **The seam between the shared and the last chain, the promises' half.** start: the description's start₃. -/
theorem seam₂On (codes : Codes) (start : Xi → FirstState → St₂ → Except String St₃) (A : Agree G₂ G₃ at_ start) (hst : Starts S codes start)
    (hl : ∀ s, last₁ s = true → handedB a idx s = true ∧ K₁.orc 2 = some ((firstOf s).1.oracles.size - 2) ∧ (firstOf s).2.1.trees.size = t₁ ∧
      (∀ r, (firstOf s).2.2.2 = [r] → r.g.all (·.ok) = true) ∧ LinTie s)
    (hoff : ∀ k ∈ [0, 2], off₃ (at_ k).1 = (at_ k).1)
    (x : Xi) (s₁ : FirstState) (s₂ : St₂) (s₃ : St₃) (y₂ : Fr₂.E.Str) (y₃ : Fr₃.E.Str) (hy : strsOf Fr₃ y₃ = strsOf Fr₂ y₂) (hs : start x s₁ s₂ = .ok s₃)
    (h : on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 12 (((x, s₁), s₂), y₂)) :
    on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ 0 (((x, s₁, s₂), s₃), y₃) := by
  show onAt F G₃ at_ (meaning₃ S K₁ R) (shapeB₃ S K₁ a idx src t₁ 0) (Free₃ F G₃ at_ S K₁ R coll off₂ off₃ 0) (open₃ 0) ((x, s₁, s₂), s₃) (strsOf Fr₃ y₃)
  rw [hy]
  cases h with
  | inl hm => exact absurd trivial hm
  | inr hr =>
    obtain ⟨hsh, hsm, hfr, hnc⟩ := hr
    obtain ⟨r, hr', hc⟩ := hfr.record
    have hla := hfr.last
    rw [open₂_last] at hsm hnc
    obtain ⟨o, l, hlin₁, ⟨ho, hob, -, hoo⟩, he⟩ := hst x s₁ s₂ s₃ hs
    obtain ⟨hh, hw, ht, hgk, l', hl', t1, t2, t3⟩ := hl s₁ hla
    have el : l' = l := Option.some.inj (hl'.symm.trans hlin₁)
    subst el
    have hf := form_of_shape₂ S a 12 s₂ hsh
    have hm : S.masksAhead = true := by
      simp only [LKFU.Shape23.formOk, Bool.and_eq_true] at hf
      exact hf.1.1
    have hom := omega_of_shape₂ S a s₂ hsh
    obtain ⟨e1, e2, -, e4, e5, -, -, -, e9, -, -, f, hfo, eb, r₀, hr₀, hg₀⟩ := start₃_full codes S _ _ _ _ _ _ _ o s₃ t1 t2 t3 he
    have hB : shapeB₃ S K₁ a idx src t₁ 0 s₃ = true := by
      have h1 := shape₃_first codes S a idx x s₁ s₂ o s₃ _ hf hh t1 t2 t3 he
      have h2 : (K₁.orc 2 == some s₃.loc.w) = true := by rw [hw, e4]; exact beq_self_eq_true _
      have h3 : borderB a s₃ = true := by
        unfold borderB
        rw [eb]
        obtain ⟨f', -, e_st', -, -, c₁', c₂'⟩ := start₃_spec codes S _ _ _ _ _ _ _ o s₃ he
        have hcd : o.st.codes = s₃.st.codes := by rw [c₂', e_st', c₁']
        show (o.omega == 2 && LKFU.Shape23.msgIs o.st 2 (some a) false && f.g.all (·.ok) && decide (o.st.codes = s₃.st.codes)) = true
        rw [decide_eq_true hcd, Bool.and_true, hoo, ho, hg₀, hgk r₀ hr₀, Bool.and_true]
        exact hom
      have h4 : (s₃.loc.firstTree == t₁ + 1) = true := by rw [e9, ht]; exact beq_self_eq_true _
      unfold shapeB₃
      rw [h1, h2, h3, h4]
      rfl
    have hom2 : s₂.loc.oOmega = 2 := by
      have := hom
      simp only [handed₂B, Bool.and_eq_true, beq_iff_eq] at this
      exact this.1
    have hF : Free₃ F G₃ at_ S K₁ R coll off₂ off₃ 0 ((x, s₁, s₂), s₃) (strsOf Fr₂ y₂) :=
      { record := ⟨r, (A.recOf x s₁ s₂ s₃ hs).trans hr', hc⟩
        arr := fun k hk => by
          rw [A.arr]
          exact hfr.arr k (by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk ⊢
            rcases hk with rfl | rfl | rfl <;> simp)
        reads := fun w k hk => by
          unfold msgOf
          rw [A.arr, A.lay]
          exact hfr.reads w k (by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk ⊢
            rcases hk with rfl | rfl | rfl <;> simp)
        placed := fun _ k hk => by
          obtain ⟨o', t, h1, h2, h3⟩ := hfr.placed₁ k hk
          refine ⟨o', t, h1, ?_, ?_⟩
          · show s₃.book.place[o']? = some t
            rw [e2]
            exact h2
          · have e := hoff k hk
            rw [h3] at e ⊢
            exact Prod.ext e.symm rfl
        omega₀ := fun _ => ⟨_, eb, fun k hk => by
          have hk4 : k = 4 := by simpa using hk
          subst hk4
          obtain ⟨o', t, h1, h2, h3⟩ := hfr.placed 4 (by rw [open₂_last]; decide)
          have e1 : o' = 2 := by
            have : (plan₂ S).orc 4 = some 2 := rfl
            exact (Option.some.inj (h1.symm.trans this))
          subst e1
          refine ⟨2, t, ?_, ?_, h3⟩
          · show some o.omega = some 2
            rw [hoo, hom2]
          · show o.book.place[2]? = some t
            rw [hob]
            exact h2⟩
        omega := fun h1 => absurd h1 (by decide)
        in₀ := fun _ => ⟨_, eb, by
          show SampleIn o.st o.omega
          rw [ho, hoo, hom2]
          exact hfr.samples 4 (by rw [open₂_last]; decide) 2 rfl⟩
        inOwn := fun _ => by
          show (∀ k' ∈ [0, 2], ∀ o', K₁.orc k' = some o' → SampleIn s₃.st o') ∧ OpenIn s₃.st s₃.loc.own
          rw [e1, e5]
          exact hfr.in₁
        inOmega := fun h1 => absurd h1 (by decide)
        order := by
          show Means.InOrder s₃.st
          rw [e1]
          exact hfr.order₁
        order₀ := fun _ => ⟨_, eb, by
          show Means.InOrder o.st
          rw [ho]
          exact hfr.order⟩
        shown := fun j hj => hfr.shown j (by revert j; decide)
        maskW := by
          show MaskWith (fun i => s₃.book.place[i]?) s₃.loc.w (s₃.loc.w + 1)
          rw [e2]
          exact hfr.mask₁ s₃.loc.w (by rw [hw, e4])
        lin₀ := fun _ => by
          obtain ⟨f', -, e_st', -, -, c₁', -⟩ := start₃_spec codes S _ _ _ _ _ _ _ o s₃ he
          show OnBytes.linOk s₃.st.codes S = true
          rw [e_st', c₁']
          exact start₃E_lin codes S _ _ _ _ _ _ _ o s₃ he
        seatW := fun _ => by
          have hnum := seatW_of_numbers S f (firstOut_numbers S _ _ _ _ _ _ _ f hfo)
          obtain ⟨g1, -, -, g4, -⟩ := firstOutFrom_spec S _ _ _ _ _ _ _ f hfo
          obtain ⟨p1, -, p3, -⟩ := start₃_plain codes S _ _ _ _ _ _ _ o s₃ he
          show (s₃.st.oracles[s₃.loc.w]?).any (·.shape == S.w) = true
          rw [p1, p3, ← g4, ← g1]
          exact hnum
        seatOmega₀ := fun _ b hb => by
          have eb' : b = ⟨f.g, o⟩ := Option.some.inj (hb.symm.trans eb)
          subst eb'
          show (o.st.oracles[o.omega]?).any (·.shape == S.omega) = true
          rw [ho, hoo, hom2]
          exact hfr.seatOmega (by decide) }
    refine Or.inr ⟨hB, ?_, hF, ?_⟩
    · rw [open₃_first]
      refine List.all_eq_true.2 fun k hk => ?_
      have := List.all_eq_true.1 hsm k hk
      unfold hasSmp at this ⊢
      rw [A.smp x s₁ s₂ s₃ hs k hk]
      exact this
    · rw [open₃_first]
      intro k hk o' z ho hz m m' hm hm'
      exact hnc k hk o' z ho ((A.smp x s₁ s₂ s₃ hs k hk) ▸ hz) m m' (member_agree A o' _ _ _ z m hm) (member_agree A o' _ _ _ z m' hm')

/-- The shared chain's promise holds that what was handed is the first chain's last state. -/
theorem last_of_on₂ {k : Nat} {b : (P₂ × St₂) × Fr₂.E.Str} (h : on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k b) : last₁ b.1.1.2 = true := by
  cases h with
  | inl hm => exact absurd trivial hm
  | inr hr => exact hr.2.2.1.last

/-- The promise's book-keeping holds the form; the form says that the masks ride ahead. -/
theorem masks_of_on₂ {k : Nat} {b : (P₂ × St₂) × Fr₂.E.Str} (h : on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k b) : S.masksAhead = true := by
  cases h with
  | inl hm => exact absurd trivial hm
  | inr hr =>
    have hf := form_of_shape₂ S a k b.1.2 hr.1
    simp only [LKFU.Shape23.formOk, Bool.and_eq_true] at hf
    exact hf.1.1

theorem ok_of_toOption {α : Type} {e : Except String α} {s : α} (h : e.toOption = some s) : e = .ok s := by
  cases e with
  | error _ => cases h
  | ok t => exact congrArg Except.ok (Option.some.inj h)

/-- **The seam between the shared and the last chain, both halves, in the form that the top asks** (Johnson/Top/Fire/Code/KeyOfRows.lean: RowsOwed.seam₂; there the boundary's number is written 0 + 1 + the later blocks' number: 12 at twelve blocks). same: the two frames give one reading of the oracles: rfl at the maker's frames. -/
theorem seam₂_rows [Inhabited Cells] [Inhabited M] (codes : Codes) (start : Xi → FirstState → St₂ → Except String St₃) (A : Agree G₂ G₃ at_ start) (hlin : K₁.lin = S) (hst : Starts S codes start)
    (hl : ∀ s, last₁ s = true → handedB a idx s = true ∧ K₁.orc 2 = some ((firstOf s).1.oracles.size - 2) ∧ (firstOf s).2.1.trees.size = t₁ ∧
      (∀ r, (firstOf s).2.2.2 = [r] → r.g.all (·.ok) = true) ∧ LinTie s)
    (hoff : ∀ k ∈ [0, 2], off₃ (at_ k).1 = (at_ k).1)
    (x : Xi) (s₁ : FirstState) (s₂ : St₂) (y₂ : Fr₂.E.Str) (y₃ : Fr₃.E.Str) (hy : strsOf Fr₃ y₃ = strsOf Fr₂ y₂)
    (h : on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 12 (((x, s₁), s₂), y₂)) :
    (∀ s, (start x s₁ s₂).toOption = some s → on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ 0 (((x, s₁, s₂), s), y₃)) ∧
      ((∃ s, (start x s₁ s₂).toOption = some s ∧ L₃ F Fr₃ G₃ at_ S K₁ R 0 (((x, s₁, s₂), s), y₃)) → L₂ F Fr₂ G₂ at_ S K₁ R enc rad 12 (((x, s₁), s₂), y₂)) :=
  ⟨fun s hs => seam₂On codes start A hst hl hoff x s₁ s₂ s y₂ y₃ hy (ok_of_toOption hs) h,
    fun ⟨s, hs, hL⟩ => seam₂L codes start A hlin (masks_of_on₂ h) hst x s₁ s₂ s y₂ y₃ hy (hl s₁ (last_of_on₂ h)).2.2.2.2 (ok_of_toOption hs) hL⟩

/-- **The end, in that form**: behind the last block the last claim is true (of every statement: nothing is open but «unmarked»). -/
theorem ends_rows [Inhabited Cells] [Inhabited M] (b : (P₃ × St₃) × Fr₃.E.Str) (_ : on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ 4 b) : L₃ F Fr₃ G₃ at_ S K₁ R 4 b :=
  ends₃ F Fr₃ G₃ at_ S K₁ R b

/-- Two frames of one depth and one list of trees read the oracles alike. -/
theorem strs_same (Fr : Frame) (k' : Nat → Nat) (f' : Nat) (y : Fr.E.Str) : strsOf ⟨Fr.a, Fr.all, k', f'⟩ y = strsOf Fr y := rfl

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.shape₃_first
#print axioms Johnson.RunOne.KeyRows23.seam₂On
#print axioms Johnson.RunOne.KeyRows23.seam₂_rows
#print axioms Johnson.RunOne.KeyRows23.ends_rows
#print axioms Johnson.RunOne.KeyRows23.strs_same
