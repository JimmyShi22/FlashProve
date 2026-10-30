-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsWalk.lean: THE FRAME OF THE WALK; K8's DRAW; K1's LATER SENDING.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
The walk is adapted from LooksWalk.lean (beside this file): that file's theorems on the arrays'
looks, carried over by program to the two numbers, name by name (…looks… ↦ …slots…; else a letter S
behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.First.Link.Law.LooksAre
import Johnson.Desc.First.Link.Law.SlotsAre
import Johnson.Desc.K1.KeepsShapes
import Johnson.Desc.First.K8.LawFunsStay
import Johnson.Desc.Sound.FoldSteps
import Johnson.Desc.Sound.HearsOnce
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (step_ok_iff)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

/-! ## 1 The frame -/

section
variable (nsOf : ℕ → ℕ × ℕ)

/-- **Where a ledger and a link are open, the ledger has that link's two numbers.** -/
def SlotsInv (s : S) : Prop :=
  ∀ G L, s.fork? = some G → s.link? = some L → SlotsAre (nsOf L.link) G

/-- It passes from s to s'. -/
def KeepsSlots (s s' : S) : Prop := SlotsInv nsOf s → SlotsInv nsOf s'

theorem keeps_reflS (s : S) : KeepsSlots nsOf s s := id

theorem keeps_transS (a b c : S) (h : KeepsSlots nsOf a b) (k : KeepsSlots nsOf b c) :
    KeepsSlots nsOf a c := fun x => k (h x)

/-- **The tool**: a maker, or a keeper. -/
theorem keeps_of_casesS {s s' : S}
    (h : ∀ G' L', s'.fork? = some G' → s'.link? = some L' → SlotsAre (nsOf L'.link) G' ∨
      ∃ G L, s.fork? = some G ∧ s.link? = some L ∧ L.link = L'.link ∧
        sl G' = sl G) : KeepsSlots nsOf s s' := by
  intro hs G' L' hG hL
  rcases h G' L' hG hL with h1 | ⟨G, L, e1, e2, e3, e4⟩
  · exact h1
  · rw [← e3]
    exact slots_map e4 (hs G L e1 e2)

/-- The two readings are left. -/
theorem keeps_sameS {s s' : S} (hf : s'.fork? = s.fork?)
    (hl : s'.link?.map (·.link) = s.link?.map (·.link)) : KeepsSlots nsOf s s' := by
  refine keeps_of_casesS nsOf fun G' L' hG hL => Or.inr ?_
  rw [hL] at hl
  cases e : s.link? with
  | none =>
    rw [e] at hl
    exact nomatch hl
  | some L =>
    rw [e] at hl
    exact ⟨G', L, hf ▸ hG, rfl, (Option.some.inj hl).symm, rfl⟩

/-- No ledger is open behind. -/
theorem keeps_noneS {s s' : S} (hf : s'.fork? = none) : KeepsSlots nsOf s s' := by
  intro _ G' L' hG _
  rw [hf] at hG
  exact nomatch hG

end

/-- A writing of a context of the same number and of a ledger with the same two numbers. u: any
state
with s's two readings (what a kind lays back beside them). -/
theorem keeps_putsS (nsOf : ℕ → ℕ × ℕ) {s u : S} {L0 L : LinkCtx} {F0 F : Fork}
    (hL : s.link? = some L0) (hF : s.fork? = some F0) (uL : u.link? = some L0)
    (uF : u.fork? = some F0) (el : L.link = L0.link)
    (ef : sl F = sl F0) :
    KeepsSlots nsOf s ((u.putLink L).putFork F) := by
  obtain ⟨r1, r2⟩ := reads_puts u L0 F0 uL uF L F
  refine keeps_of_casesS nsOf fun G' L' hG hL' => Or.inr ⟨F0, L0, hF, hL, ?_, ?_⟩
  · rw [← Option.some.inj (r1.symm.trans hL'), el]
  · rw [← Option.some.inj (r2.symm.trans hG), ef]

/-- Where no ledger is open the property holds idly. -/
theorem slotsInv_none (nsOf : ℕ → ℕ × ℕ) {s : S} (h : s.fork? = none) : SlotsInv nsOf s := by
  intro G _ hG _
  rw [h] at hG
  exact nomatch hG

/-! ## 2 Three kinds' shares -/

/-- **K8: the approximate range proof's draw.** -/
theorem k8_stepsS {Cl : Type} (nsOf : ℕ → ℕ × ℕ) (p : First.K8.Par) :
    (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).Steps (KeepsSlots nsOf) := by
  intro s rs gs s' h
  obtain ⟨r, rfl⟩ := First.K8.decide_one First.K8.atS p s s' rs gs h
  obtain ⟨tl, _, hm⟩ := (First.K8.decide_atS_iff p s s' r gs).1 h
  rw [hm.2.2.2.2.2.2.2.2]
  exact keeps_sameS nsOf (First.K8.putTl_fork _ _) (by rw [First.K8.putTl_link])

theorem rootTaken_slots (F : Fork) (t w : ℕ) :
    sl (F.rootTaken t w) = sl F := rfl

theorem commitOne_slots {L : LinkCtx} {F F' : Fork} {t : ℕ} (h : L3.commitOne L F t = .ok F') :
    sl F' = sl F := by
  simp only [L3.commitOne] at h
  split at h <;> split at h <;> first
    | (injection h with h; subst h; exact rootTaken_slots _ _ _)
    | cases h

theorem commitAll_slots {L : LinkCtx} : ∀ (ts : List ℕ) (F F' : Fork),
    ts.foldlM (L3.commitOne L) F = .ok F' → sl F' = sl F
  | [], F, F', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact rfl
  | t :: ts, F, F', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases h1 : L3.commitOne L F t with
    | error e => simp [h1] at h
    | ok F₁ =>
      simp only [h1] at h
      exact (commitAll_slots ts F₁ F' h).trans (commitOne_slots h1)

theorem commitBehind_slots {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List ℕ}
    (h : L3.commitBehind L check F ts = .ok (L', F')) :
    L'.link = L.link ∧ sl F' = sl F := by
  simp only [L3.commitBehind, bind, Except.bind] at h
  cases h1 : ts.foldlM (L3.commitOne L) F with
  | error e => simp [h1] at h
  | ok F₁ =>
    simp only [h1] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      exact ⟨rfl, commitAll_slots ts F F₁ h1⟩
    · cases h

theorem commitStep_slots {W : Type} {send : L3.Send W} {ts : List ℕ} {s s' : L3.St W}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') :
    s'.L.link = s.L.link ∧ sl s'.F = sl s.F := by
  simp only [L3.commitStep, bind, Except.bind] at h
  cases h0 : L3.commitFront s.L with
  | error e => simp [h0] at h
  | ok u =>
    simp only [h0] at h
    cases h1 : send s.L.check s.w rs with
    | error e => simp [h1] at h
    | ok x =>
      simp only [h1] at h
      cases h2 : L3.commitBehind s.L x.1 s.F ts with
      | error e => simp [h2] at h
      | ok y =>
        simp only [h2, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact commitBehind_slots (L' := y.1) (F' := y.2) h2

theorem commitOwn_slots {Cl : Type} {P : K1.Par} {link moment : ℕ} {arrays : Option (List ℕ)}
    {x y : K1.Owing (L3.St (_root_.Desc.Plain.DState Unit))} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (K1.commitOwn (Cl := Cl) P link moment arrays).decide x rs gs = .ok y) :
    y.held.L.link = x.held.L.link ∧ sl y.held.F = sl x.held.F := by
  simp only [K1.commitOwn] at h
  split at h
  · split at h
    · cases h
    · rename_i ts
      cases h1 : L3.commitStep (K1.laterOwn P x.owed) ts x.held rs with
      | error e => simp [h1, Except.map] at h
      | ok z =>
        simp only [h1, Except.map, Except.ok.injEq] at h
        subst h
        exact commitStep_slots h1
  · cases h

/-- **K1: a segment's later sending.** -/
theorem k1_stepsS {Cl : Type} (nsOf : ℕ → ℕ × ℕ) (P : K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) :
    (K1.commitAtS (Cl := Cl) P link moment arrays).Steps (KeepsSlots nsOf) := by
  intro s rs gs s' h
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L F tl hL hF ht
    cases h1 : (K1.commitOwn (Cl := Cl) P link moment arrays).decide
        { owed := K1.owedOf s, held := { L := L, F := F, tl := tl, w := K1.stateOf s () } } rs
        gs with
    | error e => simp [h1, Except.map] at h
    | ok y =>
      simp only [h1, Except.map, Except.ok.injEq] at h
      obtain ⟨e1, e2⟩ := commitOwn_slots h1
      rw [← h]
      exact keeps_putsS nsOf hL hF (u := K1.laid s y.held.w) hL hF e1 e2
  · cases h

end VerifiableInference.Desc.LinkJoin
