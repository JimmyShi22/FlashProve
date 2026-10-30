-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- ShownAt of Johnson/Desc/Sound/MsgSig.lean is written Sound.ShownAt, to tell it from the tables' own Key.ShownAt.
/-
Johnson/Desc/Key/KeyFillStrs.lean: STRINGS WHOSE WORD AT EVERY SEAT OF A FAMILY IS A GIVEN RAW WORD; AND THE FIRST MEMBERS. Over Johnson/Desc/Key/KeyFill.lean | KeyFillFam.lean | KeyFillOnto.lean (the filling of the plain reading, Johnson/Desc/Msg.lean).
  fit · blocks · colOf     a column laid as Msg.lean's Oracle.cut cuts it: all tenants' main words in order, then all tenants' mask words; each tenant's list made just as long as is told of it
  cut_colOf                LISTS ALONE: where the tenants' words add up to the tree's, the cut at tenant t of that column is tenant t's (fitted) symbol
  strsOfWords              strings out of a table tree, tenant, leaf ↦ symbol: a column at every leaf of every told tree, nothing elsewhere; the stored table's side (cell) a letter, laid as it is
  wordOf_strsOfWords       wordOf reads the symbol back, where its lists have the told lengths
  rawOf_lengths            the raw word of a word as sent (KeyFillOnto.rawOf) has rows × degree main words and rows × 3 mask words
  famStrs · wordOf_famStrs · exists_strs   UNDER SeatFits, WHOLE, AND seat INJECTIVE: ONE y : Strs SERVES ALL MEMBERS: below 2 ^ a its word at member i's seat is the raw word of f i; every leaf is shown; read by symsW it is f i
  fam_honest_member        a word that reads as a code word of m₀, with m₀'s answers in the record, has m₀'s table as a Member, AT famG
  fam_members_exist        ONE y, ONE record a: at every member a told tree, a sample and a Member
  fam_pins_together        and all PINs at one witness whose tables at the seats are the messages' (a premise)
  fill_member_exists       the same at fillG, one tenant
OBJECT: none: a rule over letters (Oracle.cut | wordOf | Member | PIN of Johnson/Desc/Msg.lean and SeatFits | ShownAt of Johnson/Desc/Sound/MsgSig.lean, by name) · USER: Johnson/Desc/Key/KeyFillSent.lean · LETTERS: F · cs · l · seat · cell · f · seedIs · a.
NOT SAID: that a run of the programs lays such strings or such a record; that SeatFits holds at a real description; that no two members meet one sample. At l := [] all is true for nothing.
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFillFam
import Johnson.Desc.Key.KeyFillOnto

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice Prob

/-! ## (a) Lists alone -/

theorem take_len {α : Type} : ∀ (l₁ l₂ : List α), (l₁ ++ l₂).take l₁.length = l₁
  | [], _ => rfl
  | a :: l₁, l₂ => congrArg (a :: ·) (take_len l₁ l₂)

theorem drop_len_add {α : Type} : ∀ (l₁ l₂ : List α) (k : ℕ), (l₁ ++ l₂).drop (l₁.length + k) = l₂.drop k
  | [], l₂, k => by simp
  | a :: l₁, l₂, k => by
    have h : (a :: l₁).length + k = (l₁.length + k) + 1 := by
      rw [List.length_cons]
      omega
    rw [h]
    exact drop_len_add l₁ l₂ k

/-- A list made just n words long: cut, or filled with zeros. -/
def fit (n : ℕ) (ws : List UInt64) : List UInt64 := (ws ++ List.replicate n 0).take n

theorem length_fit (n : ℕ) (ws : List UInt64) : (fit n ws).length = n := by
  unfold fit
  rw [List.length_take, List.length_append, List.length_replicate]
  omega

theorem fit_eq {n : ℕ} {ws : List UInt64} (h : ws.length = n) : fit n ws = ws := by
  subst h
  exact take_len ws _

/-- The tenants' lists one behind the other, each as long as w tells; g k: the list of tenant number k. -/
def blocks (w : SymbolComponent → ℕ) (g : ℕ → List UInt64) : ℕ → List SymbolComponent → List UInt64
  | _, [] => []
  | k, n :: ts => fit (w n) (g k) ++ blocks w g (k + 1) ts

theorem length_blocks (w : SymbolComponent → ℕ) (g : ℕ → List UInt64) : ∀ (k : ℕ) (ts : List SymbolComponent), (blocks w g k ts).length = (ts.map w).sum
  | _, [] => by simp [blocks]
  | k, n :: ts => by
    show (fit (w n) (g k) ++ blocks w g (k + 1) ts).length = ((n :: ts).map w).sum
    rw [List.length_append, length_fit, length_blocks w g (k + 1) ts, List.map_cons, List.sum_cons]

theorem seg_blocks (w : SymbolComponent → ℕ) (g : ℕ → List UInt64) : ∀ (ts : List SymbolComponent) (k t : ℕ) (n : SymbolComponent) (rest : List UInt64), ts[t]? = some n →
    ((blocks w g k ts ++ rest).drop ((ts.take t).map w).sum).take (w n) = fit (w n) (g (k + t))
  | [], _, _, _, _, h => by simp at h
  | m :: ts, k, 0, n, rest, h => by
    have e : m = n := by simpa using h
    subst e
    have h0 : (((m :: ts).take 0).map w).sum = 0 := by simp
    have h1 := take_len (fit (w m) (g k)) (blocks w g (k + 1) ts ++ rest)
    rw [length_fit] at h1
    show (((fit (w m) (g k) ++ blocks w g (k + 1) ts) ++ rest).drop (((m :: ts).take 0).map w).sum).take (w m) = fit (w m) (g k)
    rw [h0, List.drop_zero, List.append_assoc]
    exact h1
  | m :: ts, k, t + 1, n, rest, h => by
    have h' : ts[t]? = some n := by simpa using h
    have hs : (((m :: ts).take (t + 1)).map w).sum = (fit (w m) (g k)).length + ((ts.take t).map w).sum := by
      rw [length_fit]
      simp
    show (((fit (w m) (g k) ++ blocks w g (k + 1) ts) ++ rest).drop (((m :: ts).take (t + 1)).map w).sum).take (w n) = fit (w n) (g (k + (t + 1)))
    rw [hs, List.append_assoc, drop_len_add, seg_blocks w g ts (k + 1) t n rest h', show k + 1 + t = k + (t + 1) from by omega]

/-- **A column**, laid as Msg.lean's Oracle.cut cuts it. c t: the symbol of tenant number t. -/
def colOf (ts : List SymbolComponent) (c : ℕ → Sym) : List UInt64 :=
  blocks (fun n => n.main) (fun t => (c t).main) 0 ts ++ blocks (fun n => n.mask) (fun t => (c t).mask) 0 ts

theorem sum_main_mask (ts : List SymbolComponent) : (ts.map fun t => t.main + t.mask).sum = (ts.map fun n => n.main).sum + (ts.map fun n => n.mask).sum := by
  induction ts with
  | nil => simp
  | cons n ts ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem length_colOf (ts : List SymbolComponent) (c : ℕ → Sym) : (colOf ts c).length = (ts.map fun t => t.main + t.mask).sum := by
  unfold colOf
  rw [List.length_append, length_blocks, length_blocks, sum_main_mask]

/-- **LISTS ALONE: the cut at tenant t of the column is tenant t's symbol**, each list made as long as is told. -/
theorem cut_colOf (o : Oracle) (c : ℕ → Sym) (hsum : (o.tenants.map fun t => t.main + t.mask).sum = o.words) (t : ℕ) (n : SymbolComponent) (ht : o.tenants[t]? = some n) :
    o.cut t (colOf o.tenants c) = some ⟨fit n.main (c t).main, fit n.mask (c t).mask⟩ := by
  have hlen : (colOf o.tenants c).length = o.words := (length_colOf _ _).trans hsum
  have h1 : ((colOf o.tenants c).drop (o.mainSkip t)).take n.main = fit n.main (c t).main := by
    have h := seg_blocks (fun n => n.main) (fun t => (c t).main) o.tenants 0 t n (blocks (fun n => n.mask) (fun t => (c t).mask) 0 o.tenants) ht
    rw [Nat.zero_add] at h
    exact h
  have h2 : ((colOf o.tenants c).drop (o.maskSkip t)).take n.mask = fit n.mask (c t).mask := by
    have h := seg_blocks (fun n => n.mask) (fun t => (c t).mask) o.tenants 0 t n [] ht
    rw [Nat.zero_add, List.append_nil] at h
    have hd := drop_len_add (blocks (fun n => n.main) (fun t => (c t).main) 0 o.tenants) (blocks (fun n => n.mask) (fun t => (c t).mask) 0 o.tenants)
      ((o.tenants.take t).map fun n => n.mask).sum
    rw [length_blocks] at hd
    show ((blocks (fun n => n.main) (fun t => (c t).main) 0 o.tenants ++ blocks (fun n => n.mask) (fun t => (c t).mask) 0 o.tenants).drop
      ((o.tenants.map fun n => n.main).sum + ((o.tenants.take t).map fun n => n.mask).sum)).take n.mask = _
    rw [hd]
    exact h
  unfold Oracle.cut
  rw [ht]
  show (if (colOf o.tenants c).length = o.words then
    some (⟨((colOf o.tenants c).drop (o.mainSkip t)).take n.main, ((colOf o.tenants c).drop (o.maskSkip t)).take n.mask⟩ : Sym) else none) = _
  rw [if_pos hlen, h1, h2]

/-! ## (b) Strings -/

section
variable {XI : Type} (F : FileDescription XI)

/-- **Strings out of a table of symbols** (tree, tenant, leaf): a column at every leaf of every told tree, nothing elsewhere. -/
def strsOfWords (cell : ℕ → Option (ℕ × List UInt64)) (c : ℕ → ℕ → ℕ → Option Sym) : Strs where
  cell := cell
  col := fun j x => ((F.oracleAt j).map fun o =>
    if x < 2 ^ o.logLength then colOf o.tenants (fun t => (c j t x).getD ⟨[], []⟩) else []).getD []

/-- **wordOf reads the symbol back.** -/
theorem wordOf_strsOfWords (cell : ℕ → Option (ℕ × List UInt64)) (c : ℕ → ℕ → ℕ → Option Sym) {j t x : ℕ} {o : Oracle} {n : SymbolComponent} {σ : Sym}
    (ho : F.oracleAt j = some o) (hsum : (o.tenants.map fun t => t.main + t.mask).sum = o.words) (ht : o.tenants[t]? = some n) (hx : x < 2 ^ o.logLength)
    (hc : c j t x = some σ) (h1 : σ.main.length = n.main) (h2 : σ.mask.length = n.mask) : wordOf F (strsOfWords F cell c) j t x = some σ := by
  have hcol : (strsOfWords F cell c).col j x = colOf o.tenants (fun t => (c j t x).getD ⟨[], []⟩) := by
    show ((F.oracleAt j).map fun o => if x < 2 ^ o.logLength then colOf o.tenants (fun t => (c j t x).getD ⟨[], []⟩) else []).getD [] = _
    rw [ho]
    show (if x < 2 ^ o.logLength then colOf o.tenants (fun t => (c j t x).getD ⟨[], []⟩) else []) = _
    rw [if_pos hx]
  show ((F.oracleAt j).bind fun o => o.cut t ((strsOfWords F cell c).col j x)) = some σ
  rw [ho]
  show o.cut t ((strsOfWords F cell c).col j x) = some σ
  rw [hcol, cut_colOf o _ hsum t n ht]
  show some (⟨fit n.main ((c j t x).getD ⟨[], []⟩).main, fit n.mask ((c j t x).getD ⟨[], []⟩).mask⟩ : Sym) = some σ
  rw [hc]
  exact congrArg some (show (⟨fit n.main σ.main, fit n.mask σ.mask⟩ : Sym) = ⟨σ.main, σ.mask⟩ by rw [fit_eq h1, fit_eq h2])

end

/-! ## (c) The family -/

theorem length_wordsOfRows (b : Bool) (n : ℕ) (g : Fin n → RowTy b) (d : ℕ) (h : (b = true ∧ d = 1) ∨ (b = false ∧ d = 3)) : (wordsOfRows b n g).length = n * d := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [wordsOfRows]
  · simp [wordsOfRows, Nat.mul_comm]

variable (cs : OnBytes.Codes)

/-- The raw word of a word as sent has just the words that SeatFits asks of the tenant. -/
theorem rawOf_lengths (s : OnBytes.OracleShape) (e : ℕ) (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s) (hdeg : s.mainDeg = 1 ∨ s.mainDeg = 3)
    (f : (portOmZ cs s e).Str) (k : ℕ) (hk : k < 2 ^ aOf cs s) :
    ∃ σ, rawOf cs s e f k = some σ ∧ σ.main.length = s.mainRows * s.mainDeg ∧ σ.mask.length = s.maskRows * 3 := by
  classical
  unfold rawOf
  rw [dif_pos hk]
  refine ⟨_, rfl, ?_, ?_⟩
  · by_cases ha : (cMain cs s).a = aOf cs s
    · rw [dif_pos ha]
      exact length_wordsOfRows _ _ _ _ (hdeg.elim
        (fun h => Or.inl ⟨by show (s.mainDeg == 1) = true; simp [h], h⟩)
        (fun h => Or.inr ⟨by show (s.mainDeg == 1) = false; simp [h], h⟩))
    · rw [dif_neg ha]
      rcases hm with h0 | h
      · rw [h0, Nat.zero_mul]
        rfl
      · exact absurd h ha
  · dsimp only
    refine length_wordsOfRows _ _ _ _ (Or.inr ⟨?_, ?_⟩) <;> rfl

/-- Two words of symbols that agree below 2 ^ a read alike. -/
theorem symsW_of_agree (s : OnBytes.OracleShape) (e : ℕ) (c c' : ℕ → Option Sym) (h : ∀ k, k < 2 ^ aOf cs s → c k = c' k) : symsW cs s e c = symsW cs s e c' := by
  funext p
  match p with
  | .inl x => exact symsW_inl cs s e c c' x (h x.val (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (le_max_left _ _))))
  | .inr x => exact symsW_inr cs s e c c' x (h x.val x.isLt)

section
variable (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)

open Classical in
/-- The table of symbols of a family of words as sent: at a member's seat its raw word; nothing elsewhere. -/
def famWords (f : ∀ i : Fin l.length, (OmAt cs l i).Str) : ℕ → ℕ → ℕ → Option Sym := fun j t x =>
  if h : ∃ i : Fin l.length, seat i = (j, t) then rawOf cs (l.get h.choose).1 (l.get h.choose).2 (f h.choose) x else none

theorem famWords_seat (hinj : Function.Injective seat) (f : ∀ i : Fin l.length, (OmAt cs l i).Str) (i : Fin l.length) (x : ℕ) :
    famWords cs l seat f (seat i).1 (seat i).2 x = rawOf cs (l.get i).1 (l.get i).2 (f i) x := by
  classical
  have h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) := ⟨i, rfl⟩
  show (if h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) then rawOf cs (l.get h.choose).1 (l.get h.choose).2 (f h.choose) x else none) = _
  rw [dif_pos h]
  have hc := choose_seat l seat hinj i h
  generalize h.choose = i' at hc
  subst hc
  rfl

variable {XI : Type} (F : FileDescription XI)

/-- **The strings of a family of words as sent.** -/
def famStrs (cell : ℕ → Option (ℕ × List UInt64)) (f : ∀ i : Fin l.length, (OmAt cs l i).Str) : Strs := strsOfWords F cell (famWords cs l seat f)

/-- **Below 2 ^ a the word at member i's seat is the raw word of f i.** ALL EIGHT CLAUSES OF SeatFits ARE SPENT HERE. -/
theorem wordOf_famStrs (hinj : Function.Injective seat) (hS : SeatFits F cs l seat) (cell : ℕ → Option (ℕ × List UInt64)) (f : ∀ i : Fin l.length, (OmAt cs l i).Str)
    (i : Fin l.length) (k : ℕ) (hk : k < 2 ^ aOf cs (l.get i).1) :
    wordOf F (famStrs cs l seat F cell f) (seat i).1 (seat i).2 k = rawOf cs (l.get i).1 (l.get i).2 (f i) k := by
  obtain ⟨o, n, ho, ht, hlog, hmain, hmask, hm, hsum, hdeg⟩ := hS i
  obtain ⟨σ, hσ, h1, h2⟩ := rawOf_lengths cs _ _ hm hdeg (f i) k hk
  rw [hσ]
  exact wordOf_strsOfWords F cell _ ho hsum ht (by rw [hlog]; exact hk) ((famWords_seat cs l seat hinj f i k).trans hσ) (h1.trans hmain.symm) (h2.trans hmask.symm)

/-- **R1: ONE y SERVES ALL MEMBERS.** -/
theorem exists_strs (hinj : Function.Injective seat) (hS : SeatFits F cs l seat) (cell : ℕ → Option (ℕ × List UInt64)) (f : ∀ i : Fin l.length, (OmAt cs l i).Str) :
    ∃ y : Strs, y.cell = cell ∧ ∀ i : Fin l.length, Sound.ShownAt F cs l seat y i ∧
      (∀ k, k < 2 ^ aOf cs (l.get i).1 → wordOf F y (seat i).1 (seat i).2 k = rawOf cs (l.get i).1 (l.get i).2 (f i) k) ∧
      symsW cs (l.get i).1 (l.get i).2 (wordOf F y (seat i).1 (seat i).2) = f i := by
  refine ⟨famStrs cs l seat F cell f, rfl, fun i => ?_⟩
  have hw := wordOf_famStrs cs l seat F hinj hS cell f i
  obtain ⟨_, _, _, _, _, _, _, hm, _, _⟩ := hS i
  refine ⟨fun k hk => ?_, hw, ?_⟩
  · rw [hw k hk]
    exact rawOf_shown cs _ _ (f i) k hk
  · rw [symsW_of_agree cs _ _ _ _ hw]
    exact symsW_rawOf cs _ _ hm (f i)

/-! ## (d) The first members -/

variable {A Cells Rec : Type} (seedIs : ∀ i : Fin l.length, A → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
  (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec)

/-- **A word that reads as a code word of m₀, with m₀'s answers in the record, has m₀'s table as a Member: AT famG, at every member.** -/
theorem fam_honest_member (hinj : Function.Injective seat) (i : Fin l.length) (hlog : ∀ o, F.oracleAt (seat i).1 = some o → o.logLength = aOf cs (l.get i).1)
    (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniq : ∀ a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (a : A) (y : Strs) (o : Oracle) (z : Σ i : Fin l.length, (OmAt cs l i).Smp) (m₀ : (OmAt cs l i).Msg) (r₀ : (OmAt cs l i).Rnd) (ρ : (OmAt cs l i).Z.D)
    (ho : F.oracleAt (seat i).1 = some o) (hz : (famG cs l seat seedIs arr lay decT recOf).smp a (seat i).1 (seat i).2 = some z)
    (hs : seedIs i a ρ ((OmAt cs l i).Z.val ρ m₀)) (hsh : Sound.ShownAt F cs l seat y i)
    (hw : (OmAt cs l i).upW (symsW cs (l.get i).1 (l.get i).2 (wordOf F y (seat i).1 (seat i).2)) = (OmAt cs l i).C.enc m₀ r₀) :
    Member F (famG cs l seat seedIs arr lay decT recOf) o (seat i).1 (seat i).2 y z (ofU cs (l.get i).1 (l.get i).2 m₀) :=
  fam_member_of_cand cs l seat seedIs arr lay decT recOf hinj F i hlog hm uniq a y o z m₀ ρ _ ho hz hs hsh
    ⟨inList_of_sent cs _ _ _ m₀ r₀ hw, rfl⟩

/-- **ONE y, ONE RECORD: AT EVERY MEMBER A TOLD TREE, A SAMPLE AND A MEMBER.** -/
theorem fam_members_exist (hinj : Function.Injective seat) (hS : SeatFits F cs l seat)
    (uniq : ∀ i a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (cell : ℕ → Option (ℕ × List UInt64)) (a : A) (f : ∀ i : Fin l.length, (OmAt cs l i).Str) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hf : ∀ i, (OmAt cs l i).upW (f i) = (OmAt cs l i).C.enc (m₀ i) (r₀ i)) (hs : ∀ i, seedIs i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) :
    ∃ y : Strs, y.cell = cell ∧ ∀ i : Fin l.length, ∃ o z, F.oracleAt (seat i).1 = some o ∧
      (famG cs l seat seedIs arr lay decT recOf).smp a (seat i).1 (seat i).2 = some z ∧
      Member F (famG cs l seat seedIs arr lay decT recOf) o (seat i).1 (seat i).2 y z (ofU cs (l.get i).1 (l.get i).2 (m₀ i)) := by
  obtain ⟨y, hcell, hy⟩ := exists_strs cs l seat F hinj hS cell f
  refine ⟨y, hcell, fun i => ?_⟩
  obtain ⟨hsh, _, hsy⟩ := hy i
  obtain ⟨o, _, ho, _, hlog, _, _, hm, _, _⟩ := hS i
  have hhas := fam_has cs l seat seedIs arr lay decT recOf hinj i (ρ i, (OmAt cs l i).Z.val (ρ i) (m₀ i)) (hs i)
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hhas
  refine ⟨o, z, ho, hz, fam_honest_member cs l seat F seedIs arr lay decT recOf hinj i (fun o' ho' => ?_) hm (uniq i) a y o z (m₀ i) (r₀ i) (ρ i) ho hz (hs i) hsh ?_⟩
  · obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
    exact hlog
  · rw [hsy]
    exact hf i

/-- **AND ALL PINS TOGETHER**, at a witness whose tables at the seats are the messages' (a premise: arr and lay are letters). -/
theorem fam_pins_together {Tok : Type} (hinj : Function.Injective seat) (hS : SeatFits F cs l seat)
    (uniq : ∀ i a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (cell : ℕ → Option (ℕ × List UInt64)) (a : A) (f : ∀ i : Fin l.length, (OmAt cs l i).Str) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hf : ∀ i, (OmAt cs l i).upW (f i) = (OmAt cs l i).C.enc (m₀ i) (r₀ i)) (hs : ∀ i, seedIs i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i)))
    (W : Wit Cells Tok Tab) (hW : ∀ i, msgOf (famG cs l seat seedIs arr lay decT recOf) W (seat i).1 (seat i).2 = ofU cs (l.get i).1 (l.get i).2 (m₀ i)) :
    ∃ y : Strs, y.cell = cell ∧ ∀ i : Fin l.length, PIN F (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a y W := by
  obtain ⟨y, hcell, hy⟩ := fam_members_exist cs l seat F seedIs arr lay decT recOf hinj hS uniq cell a f m₀ r₀ ρ hf hs
  refine ⟨y, hcell, fun i => ?_⟩
  obtain ⟨o, z, ho, hz, hM⟩ := hy i
  refine ⟨o, z, ho, hz, ?_⟩
  rw [hW i]
  exact hM

end

/-- **THE SAME AT fillG, ONE TENANT.** -/
theorem fill_member_exists {A Cells Rec XI : Type} (s : OnBytes.OracleShape) (e j₀ t₀ : ℕ) (seedIs : A → (portOmZ cs s e).Z.D → ((portOmZ cs s e).Z.S → GE) → Prop)
    (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec) (F : FileDescription XI)
    (hS : SeatFits F cs [(s, e)] fun _ => (j₀, t₀))
    (uniq : ∀ a ρ v ρ' v', seedIs a ρ v → seedIs a ρ' v' → (portOmZ cs s e).Z.val ρ = (portOmZ cs s e).Z.val ρ' ∧ v = v')
    (cell : ℕ → Option (ℕ × List UInt64)) (a : A) (f : (portOmZ cs s e).Str) (m₀ : (portOmZ cs s e).Msg) (r₀ : (portOmZ cs s e).Rnd) (ρ : (portOmZ cs s e).Z.D)
    (hf : (portOmZ cs s e).upW f = (portOmZ cs s e).C.enc m₀ r₀) (hs : seedIs a ρ ((portOmZ cs s e).Z.val ρ m₀)) :
    ∃ y : Strs, y.cell = cell ∧ ∃ o z, F.oracleAt j₀ = some o ∧ (fillG cs s e j₀ t₀ seedIs arr lay decT recOf).smp a j₀ t₀ = some z ∧
      Member F (fillG cs s e j₀ t₀ seedIs arr lay decT recOf) o j₀ t₀ y z (ofU cs s e m₀) := by
  obtain ⟨o, n, ho, ht, hlog, hmain, hmask, hm, hsum, hdeg⟩ := hS ⟨0, by simp⟩
  have ho' : F.oracleAt j₀ = some o := ho
  have ht' : o.tenants[t₀]? = some n := ht
  have hlog' : o.logLength = aOf cs s := hlog
  have hmain' : n.main = s.mainRows * s.mainDeg := hmain
  have hmask' : n.mask = s.maskRows * 3 := hmask
  have hm' : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s := hm
  have hdeg' : s.mainDeg = 1 ∨ s.mainDeg = 3 := hdeg
  have hL : ∀ o', F.oracleAt j₀ = some o' → o'.logLength = aOf cs s := fun o' h' => by
    obtain rfl : o' = o := Option.some.inj (h'.symm.trans ho')
    exact hlog'
  have hw : ∀ k, k < 2 ^ aOf cs s → wordOf F (strsOfWords F cell fun _ _ x => rawOf cs s e f x) j₀ t₀ k = rawOf cs s e f k := fun k hk => by
    obtain ⟨σ, hσ, h1, h2⟩ := rawOf_lengths cs s e hm' hdeg' f k hk
    rw [hσ]
    exact wordOf_strsOfWords F cell _ ho' hsum ht' (by rw [hlog']; exact hk) hσ (h1.trans hmain'.symm) (h2.trans hmask'.symm)
  have hhas := (fill_seals cs s e j₀ t₀ seedIs arr lay decT recOf F (fun y : Strs => y) hL hm' uniq).has a ρ _ hs
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hhas
  refine ⟨strsOfWords F cell fun _ _ x => rawOf cs s e f x, rfl, o, z, ho', hz, honest_member cs s e j₀ t₀ seedIs arr lay decT recOf F hL hm' uniq a _ o z m₀ r₀ ρ ho' hz hs (fun k hk => ?_) ?_⟩
  · rw [hw k hk]
    exact rawOf_shown cs s e f k hk
  · rw [symsW_of_agree cs s e _ _ hw, symsW_rawOf cs s e hm' f]
    exact hf

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.cut_colOf
#print axioms VerifiableInference.Desc.Key.Fill.wordOf_strsOfWords
#print axioms VerifiableInference.Desc.Key.Fill.rawOf_lengths
#print axioms VerifiableInference.Desc.Key.Fill.wordOf_famStrs
#print axioms VerifiableInference.Desc.Key.Fill.exists_strs
#print axioms VerifiableInference.Desc.Key.Fill.fam_honest_member
#print axioms VerifiableInference.Desc.Key.Fill.fam_members_exist
#print axioms VerifiableInference.Desc.Key.Fill.fam_pins_together
#print axioms VerifiableInference.Desc.Key.Fill.fill_member_exists
