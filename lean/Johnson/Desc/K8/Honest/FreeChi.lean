-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FreeChi.lean: THE FIRST CHAIN's STATE WITH THE BATCHING ELEMENT REPLACED; AND
WHAT DOES NOT READ IT. Definitions with code, statements and proofs. No prover. Lemmas; none of the
library's goals.

The states behind a segment's batching draw at two drawn elements, from one state in front, differ
in one field: the ledger's batching element. What never reads that field does the same at both.
  `reChiF θ F`, `reChi θ s`, `reBoth θ tl s`   the ledger, the state, and the state with the
      smallness test's data replaced too
  `reChi_*`      what the state's readers and writers do at the replaced state
  `shown_re`, `hide_re`, `hideRun_re`, `paid_re`   the ledger's own routines
  `FlOk m`       a routine on a ledger and a tape does the same at the replaced ledger, and leaves
      the ledger's sums (`SameSums`, Johnson/Desc/K8/Honest/FallFold.lean); closed under pure, bind,
      foldlM; holds of must, need, and of a change that goes through the replacing
  `drawn_re`     the draw's own part at two drawn elements
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallFold
import Johnson.Desc.K8.Honest.FallDraw
import Johnson.Desc.First.Batch.BlindFl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.K.Kc
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims

/-- The ledger with the batching element replaced. -/
def reChiF (θ : E) (F : Fork) : Fork := { F with theta := θ }

/-- The state with its open segment's ledger's batching element replaced. -/
def reChi (θ : E) (s : S) : S :=
  match s.fork? with
  | some F => s.putFork (reChiF θ F)
  | none => s

/-- The same, with the smallness test's data replaced too. -/
def reBoth (θ : E) (tl : HTailF2) (s : S) : S := (reChi θ s).putTl tl

/-! ## The state -/

theorem reChi_fork (θ : E) (s : S) : (reChi θ s).fork? = s.fork?.map (reChiF θ) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x => by_cases ho : x.opened = true <;> simp [reChi, S.fork?, S.putFork, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

/-- A reader that laying a ledger does not turn. -/
theorem reChi_read {α : Type} (g : S → α) (hg : ∀ s G, g (s.putFork G) = g s) (θ : E) (s : S) :
    g (reChi θ s) = g s := by
  unfold reChi
  cases s.fork? with
  | none => rfl
  | some F => exact hg s _

theorem tl_putFork' (s : S) (G : Fork) : (s.putFork G).tl? = s.tl? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x => by_cases ho : x.opened = true <;> simp [S.tl?, S.putFork, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem funs_putFork (s : S) (G : Fork) : (s.putFork G).funs? = s.funs? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x => by_cases ho : x.opened = true <;> simp [S.funs?, S.putFork, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem look_putFork (s : S) (G : Fork) : (s.putFork G).lookHeard? = s.lookHeard? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x => by_cases ho : x.opened = true <;> simp [S.lookHeard?, S.putFork, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem reChi_tl (θ : E) (s : S) : (reChi θ s).tl? = s.tl? := reChi_read S.tl? tl_putFork' θ s
theorem reChi_funs (θ : E) (s : S) : (reChi θ s).funs? = s.funs? :=
  reChi_read S.funs? funs_putFork θ s
theorem reChi_look (θ : E) (s : S) : (reChi θ s).lookHeard? = s.lookHeard? :=
  reChi_read S.lookHeard? look_putFork θ s

theorem reChi_putFork (θ : E) (s : S) (G : Fork) :
    reChi θ (s.putFork G) = (reChi θ s).putFork (reChiF θ G) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x => by_cases ho : x.opened = true <;> simp [reChi, S.fork?, S.putFork, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem reChi_putTl (θ : E) (s : S) (tl : HTailF2) :
    reChi θ (s.putTl tl) = (reChi θ s).putTl tl := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x => by_cases ho : x.opened = true <;> simp [reChi, S.fork?, S.putFork, S.putTl, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem putTl_putTl (s : S) (a b : HTailF2) : (s.putTl a).putTl b = s.putTl b := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x => by_cases ho : x.opened = true <;> simp [S.putTl, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem putTl_putFork (s : S) (a : HTailF2) (G : Fork) :
    (s.putFork G).putTl a = (s.putTl a).putFork G := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x => by_cases ho : x.opened = true <;> simp [S.putTl, S.putFork, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

/-- The batching's lens at the replaced state. -/
theorem reChi_get (θ : E) (s : S) (a : K9.Part) (h : K9.atS.get? s = some a) :
    ∃ b, K9.atS.get? (reChi θ s) = some b ∧ b.F = reChiF θ a.F := by
  have hF := K9.get_fork s a h
  obtain ⟨u, hb⟩ := K9.get_putFork' s a (reChiF θ a.F) h
  refine ⟨{ a with F := reChiF θ a.F, used := u }, ?_, rfl⟩
  unfold reChi
  rw [hF]
  exact hb

/-! ## The ledger's own routines -/

theorem shown_re (θ : E) (F : Fork) (j : Nat) : (reChiF θ F).shown j = F.shown j := rfl

theorem paid_re (θ : E) (F : Fork) (i : Nat) : (reChiF θ F).paid i = reChiF θ (F.paid i) := rfl

theorem hide_re (θ : E) {F G : Fork} {j : Nat} {s k : E} (h : F.hide j s k = some G) :
    (reChiF θ F).hide j s k = some (reChiF θ G) := by
  unfold Fork.hide at h ⊢
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    have hc' : (decide (j < (reChiF θ F).ns) && (reChiF θ F).gotF.size == (reChiF θ F).ns &&
        !(reChiF θ F).gotF.getD j true) = true := hc
    rw [if_pos hc']
    rfl
  · cases h

theorem hideSteps_re (θ : E) (k : E) : ∀ (l : List E) (j : Nat) (F : Fork) (x : Nat × Fork),
    l.foldlM (Fork.hideStep k) (j, F) = some x →
    l.foldlM (Fork.hideStep k) (j, reChiF θ F) = some (x.1, reChiF θ x.2)
  | [], j, F, x, h => by
    obtain rfl : (j, F) = x := by simpa using h
    rfl
  | v :: l, j, F, x, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨y, hy, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨H, hH, rfl⟩ := Option.map_eq_some_iff.1 (show (F.hide j v k).map _ = some y from hy)
    have e : Fork.hideStep k (j, reChiF θ F) v = some (j + 1, reChiF θ H) := by
      show ((reChiF θ F).hide j v k).map _ = _
      rw [hide_re θ hH]
      rfl
    exact Option.bind_eq_some_iff.2 ⟨_, e, hideSteps_re θ k l (j + 1) H x h2⟩

theorem hideRun_re (θ : E) {F G : Fork} {first : Nat} {v : Array E} {k : E}
    (h : F.hideRun first v k = some G) : (reChiF θ F).hideRun first v k = some (reChiF θ G) := by
  unfold Fork.hideRun at h ⊢
  rw [← Array.foldlM_toList] at h ⊢
  cases hq : v.toList.foldlM (Fork.hideStep k) (first, F) with
  | none => simp [hq] at h
  | some x =>
    rw [hq] at h
    obtain rfl : x.2 = G := Option.some.inj h
    rw [hideSteps_re θ k v.toList first F x hq]

theorem sameSums_re (θ : E) {F G : Fork} (h : SameSums F G) :
    SameSums (reChiF θ F) (reChiF θ G) :=
  ⟨h.trees, h.ns, h.LS, h.c0, h.nClaim, rfl, h.plan⟩

/-! ## Routines on a ledger and a tape -/

/-- The routine does the same at the replaced ledger, and leaves the ledger's sums. -/
structure FlOk {α : Type} (m : Fl α) : Prop where
  free : ∀ F u x θ, m F u = some x → m (reChiF θ F) u = some (x.1, reChiF θ x.2.1, x.2.2)
  same : ∀ F u x, m F u = some x → SameSums F x.2.1

theorem FlOk.pure {α : Type} (a : α) : FlOk (Pure.pure a : Fl α) :=
  ⟨fun F u x θ h => by
      obtain rfl : (a, F, u) = x := Option.some.inj h
      rfl,
    fun F u x h => by
      obtain rfl : (a, F, u) = x := Option.some.inj h
      exact SameSums.refl F⟩

theorem FlOk.bind {α β : Type} {m : Fl α} {f : α → Fl β} (hm : FlOk m) (hf : ∀ a, FlOk (f a)) :
    FlOk (m >>= f) := by
  constructor
  · intro F u x θ h
    have h' : (match m F u with
      | some (a, G, w) => f a G w
      | none => none) = some x := h
    cases hx : m F u with
    | none => rw [hx] at h'; cases h'
    | some y =>
      obtain ⟨a, G, w⟩ := y
      rw [hx] at h'
      show (match m (reChiF θ F) u with
        | some (a, G, w) => f a G w
        | none => none) = _
      rw [hm.free F u _ θ hx]
      exact (hf a).free G w x θ h'
  · intro F u x h
    have h' : (match m F u with
      | some (a, G, w) => f a G w
      | none => none) = some x := h
    cases hx : m F u with
    | none => rw [hx] at h'; cases h'
    | some y =>
      obtain ⟨a, G, w⟩ := y
      rw [hx] at h'
      exact (hm.same F u _ hx).trans ((hf a).same G w x h')

theorem FlOk.must (b : Bool) : FlOk (Fl.must b) := by
  constructor
  · intro F u x θ h
    unfold Fl.must at h ⊢
    cases b with
    | false => cases h
    | true =>
      obtain rfl : ((), F, u) = x := Option.some.inj h
      rfl
  · intro F u x h
    unfold Fl.must at h
    cases b with
    | false => cases h
    | true =>
      obtain rfl : ((), F, u) = x := Option.some.inj h
      exact SameSums.refl F

theorem FlOk.need {α : Type} (o : Option α) : FlOk (Fl.need o) := by
  constructor
  · intro F u x θ h
    unfold Fl.need at h ⊢
    cases o with
    | none => cases h
    | some a =>
      obtain rfl : (a, F, u) = x := Option.some.inj h
      rfl
  · intro F u x h
    unfold Fl.need at h
    cases o with
    | none => cases h
    | some a =>
      obtain rfl : (a, F, u) = x := Option.some.inj h
      exact SameSums.refl F

theorem FlOk.change {f : Fork → Option Fork}
    (h1 : ∀ F G θ, f F = some G → f (reChiF θ F) = some (reChiF θ G))
    (h2 : ∀ F G, f F = some G → SameSums F G) : FlOk (Fl.change f) := by
  constructor
  · intro F u x θ h
    unfold Fl.change at h ⊢
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [h1 F G θ hG]
    rfl
  · intro F u x h
    unfold Fl.change at h
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    exact h2 F G hG

theorem FlOk.foldlM {α β : Type} {f : β → α → Fl β} (hf : ∀ b a, FlOk (f b a)) :
    ∀ (l : List α) (b : β), FlOk (l.foldlM f b)
  | [], b => by
    rw [List.foldlM_nil]
    exact FlOk.pure b
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact FlOk.bind (hf b a) fun c => FlOk.foldlM hf l c

theorem FlOk.paid (i : Nat) : FlOk (Fl.change fun F => some (F.paid i)) :=
  FlOk.change (fun F G θ h => by
      obtain rfl : F.paid i = G := Option.some.inj h
      rfl)
    (fun F G h => by
      obtain rfl : F.paid i = G := Option.some.inj h
      exact SameSums.paid F i)

theorem FlOk.hideRun (first : Nat) (v : Array E) (k : E) :
    FlOk (Fl.change (·.hideRun first v k)) :=
  FlOk.change (fun _ _ θ h => hideRun_re θ h)
    (fun _ _ h => SameSums.ofCore (OnBytes.Desc.First.K4.hideRun_core h))

/-! ## The draw -/

/-- The draw's own part at two drawn elements. -/
theorem drawn_re (rows : Nat) (χ₁ χ₂ : E) (owed : Option Nat) (used : Nat) (L : LinkCtx) (F : Fork)
    (o₁ o₂ : K9.Drawn) (h₁ : K9.drawnClean rows χ₁ owed used L F = .ok o₁)
    (h₂ : K9.drawnClean rows χ₂ owed used L F = .ok o₂) :
    o₂.owed = o₁.owed ∧ o₂.L = o₁.L ∧ o₂.F = reChiF χ₂ o₁.F := by
  have key : ∀ (χ : E) (o : K9.Drawn), K9.drawnClean rows χ owed used L F = .ok o →
      K9.drawn rows χ owed used L F = .ok o := by
    intro χ o h
    unfold K9.drawnClean at h
    obtain ⟨o', ho, h⟩ := K9L.ok_bind h
    obtain ⟨_, _, h⟩ := K9L.ok_bind h
    obtain ⟨_, _, h⟩ := K9L.ok_bind h
    obtain ⟨_, _, h⟩ := K9L.ok_bind h
    obtain rfl : o' = o := Except.ok.inj h
    exact ho
  have d₁ := key χ₁ o₁ h₁
  have d₂ := key χ₂ o₂ h₂
  unfold K9.drawn at d₁ d₂
  obtain ⟨_, _, d₁⟩ := K9L.ok_bind d₁
  obtain ⟨_, _, d₁⟩ := K9L.ok_bind d₁
  obtain ⟨_, _, d₁⟩ := K9L.ok_bind d₁
  obtain ⟨_, _, d₁⟩ := K9L.ok_bind d₁
  obtain ⟨_, _, d₁⟩ := K9L.ok_bind d₁
  obtain ⟨_, _, d₂⟩ := K9L.ok_bind d₂
  obtain ⟨_, _, d₂⟩ := K9L.ok_bind d₂
  obtain ⟨_, _, d₂⟩ := K9L.ok_bind d₂
  obtain ⟨_, _, d₂⟩ := K9L.ok_bind d₂
  obtain ⟨_, _, d₂⟩ := K9L.ok_bind d₂
  have e₁ := Except.ok.inj d₁
  have e₂ := Except.ok.inj d₂
  rw [← e₁, ← e₂]
  exact ⟨rfl, rfl, rfl⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.reChi_putFork
#print axioms VerifiableInference.Desc.First.K8.Honest.reChi_get
#print axioms VerifiableInference.Desc.First.K8.Honest.hideRun_re
#print axioms VerifiableInference.Desc.First.K8.Honest.FlOk.bind
#print axioms VerifiableInference.Desc.First.K8.Honest.FlOk.foldlM
#print axioms VerifiableInference.Desc.First.K8.Honest.drawn_re
