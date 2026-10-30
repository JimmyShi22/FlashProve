-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoRd.lean.
Which claims a routine of a sub-proof adds, as a written list: the rules.

Some routines make their forms by readers that end in `uEnt` (OnBytes/Model/Look.lean), which
reads the number of columns of an array in the state. The list of the claims that such a routine
adds is then a function of the routine's arguments and of that one number K. The rules here walk
such a routine step by step and give the list as a written, total term.

Main names:
  `Rd t K r v`: from a state in which array t has K columns, the routine r, if it returns, leaves
    the state and returns v. `Rd.pure`, `Rd.bind`, `Rd.lift`, `Rd.unit`, `Rd.must`, `Rd.foldlM`,
    `Rd.forInList`, `Rd.forInRange`, `Rd.never`; `rd_uEnt`, `rd_getSome`; `refuse_never`,
    `getNone_never`: a refusal never returns.
  `AtK t K F`: array t has K columns in F, and F has one coefficient for each slot.
  `Ad t K r l`: from a state with `AtK` the routine r, if it returns, ends in such a state, which
    comes from the first by adding just the list l (`Adds`, OnBytes/Tie/Pv/Led/LedAdds.lean).
    `Ad.pure`, `Ad.lin`, `Ad.t2Lin`, `Ad.after`, `Ad.seq`, `Ad.then0`, `Ad.forInList`,
    `Ad.forInRange`, `Ad.forInArray`, `Ad.forM`, `Ad.bindV`; `ad_paid`, `ad_linsL`, `ad_forM_lin`.
  `AdV t K r v l`: as `Ad`, for a routine that returns the value v. `AdV.pure`, `AdV.seq`,
    `AdV.ofRd`, `AdV.bind`, `AdV.after`, `AdV.seq0`, `AdV.ite`, `AdV.foldlM`, `AdV.never`,
    `AdV.ad`, `Ad.adV`; `atK_hideRun`, `adV_pscRow`.
  `Ad.run`: a run in plain words, from `Ad` at every K and a first state with one coefficient for
    each slot: the list is the one at the first state's number of columns.
  `Ad.some`: the same in the form in which
    OnBytes/Tie/Pv/Led/LedLayerCut.lean [not in this library] states a stretch that reads the
    state: there is a list l with a relation at F, and `Adds F l G`.

What is lost against the routines: a value or a list here is total. It does not say where a
routine refuses. Off a run that returns it means nothing. Why the states' numbers of columns are
carried along here: `Keeps` (OnBytes/Tie/Pv/Led/LedAdds.lean), the step of `Adds` that adds
nothing, does not hold the arrays' numbers of columns, so "`Adds` keeps them" is no lemma. For
`SubM.lin` they are kept where the state has one coefficient for each slot: hence that premise.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed what the forms are worth.

-/
import OnBytes.Tie.Pv.Led.LedWalkSmall
import OnBytes.Tie.Pv.Lookup.Ends.FoFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- From a state in which array t has K columns, the routine leaves the state and returns v. -/
def Rd {α : Type} (t K : ℕ) (r : SubM α) (v : α) : Prop :=
  ∀ (F G : Fork) (c c' : Ctx) (a : α), colsOf F t = K → r F c = .ok ((a, G), c') → G = F ∧ a = v

/-- Array t has K columns, and there is one coefficient for each slot. -/
def AtK (t K : ℕ) (F : Fork) : Prop := colsOf F t = K ∧ F.LS.size = F.ns

/-- From a state with AtK the routine goes to such a state, by adding just the list l. -/
def Ad (t K : ℕ) (r : SubM Unit) (l : List Aff) : Prop :=
  ∀ (F G : Fork) (c c' : Ctx), AtK t K F → r F c = .ok (((), G), c') →
    AtK t K G ∧ OnBytes.Road.Rows.Adds F l G

section
variable {α β : Type} {t K : ℕ}

theorem Rd.pure (a : α) : Rd t K (Pure.pure a : SubM α) a := by
  intro F G c c' b _ h
  have e := (pure_ok a F c _).1 h
  simp only [Prod.mk.injEq] at e
  exact ⟨e.1.2, e.1.1⟩

theorem Rd.bind {r : SubM α} {k : α → SubM β} {v : α} {w : β} (h1 : Rd t K r v)
    (h2 : Rd t K (k v) w) : Rd t K (r >>= k) w := by
  intro F G c c' b hK h
  obtain ⟨a, F1, c1, k1, k2⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨rfl, rfl⟩ := h1 F F1 c c1 a hK k1
  exact h2 F1 G c1 c' b hK k2

/-- A call on the channel whose value is fixed. -/
theorem Rd.lift {b : Blk α} {v : α} (h : ∀ c a c', b c = .ok (a, c') → a = v) :
    Rd t K (StateT.lift b : SubM α) v := by
  intro F G c c' a _ hr
  obtain ⟨a', c1, h1, e⟩ := (lift_ok b F c _).1 hr
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, _⟩ := e
  exact ⟨rfl, h c a c1 h1⟩

theorem Rd.unit (b : Blk Unit) : Rd t K (StateT.lift b : SubM Unit) () :=
  Rd.lift fun _ _ _ _ => rfl

/-- A loop over a list that gathers a value. -/
theorem Rd.forInList {σ : Type} (f : α → σ → SubM (ForInStep σ)) (g : σ → α → σ)
    (hf : ∀ a s, Rd t K (f a s) (ForInStep.yield (g s a))) :
    ∀ (xs : List α) (s : σ), Rd t K (forIn xs s f) (xs.foldl g s)
  | [], s => by
    rw [List.forIn_nil]
    exact Rd.pure s
  | x :: xs, s => by
    rw [List.forIn_cons]
    exact Rd.bind (hf x s) (Rd.forInList f g hf xs (g s x))

/-- A loop over the numbers below n. -/
theorem Rd.forInRange {σ : Type} (n : ℕ) (f : ℕ → σ → SubM (ForInStep σ)) (g : σ → ℕ → σ)
    (hf : ∀ a s, Rd t K (f a s) (ForInStep.yield (g s a))) (s : σ) :
    Rd t K (forIn [:n] s f) ((List.range n).foldl g s) := by
  have e : List.range' ([:n] : Std.Legacy.Range).start ([:n] : Std.Legacy.Range).size
      ([:n] : Std.Legacy.Range).step = List.range n := by
    simp [Std.Legacy.Range.size, List.range_eq_range']
  rw [Std.Legacy.Range.forIn_eq_forIn_range', e]
  exact Rd.forInList f g hf _ s

theorem Ad.pure : Ad t K (Pure.pure () : SubM Unit) [] := by
  intro F G c c' hK h
  have e := (pure_ok () F c _).1 h
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨_, rfl⟩, _⟩ := e
  exact ⟨hK, OnBytes.Road.Rows.Adds.nil _⟩

theorem Ad.lin (f : Aff) : Ad t K (SubM.lin f) [f] := by
  intro F G c c' hK h
  obtain ⟨h1, _⟩ := (SubM.lin_run f F G c c').1 h
  have T := Fork.lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hK.2 h1
  refine ⟨⟨?_, T.2.2.2.2.1⟩, OnBytes.Road.Rows.Adds.lin (OnBytes.Road.Rows.Adds.nil F) h1⟩
  rw [cols_of_frame T.2.2.2.2.2]
  exact hK.1

/-- A reader in front. -/
theorem Ad.after {r : SubM α} {k : α → SubM Unit} {v : α} {l : List Aff} (h1 : Rd t K r v)
    (h2 : Ad t K (k v) l) : Ad t K (r >>= k) l := by
  intro F G c c' hK h
  obtain ⟨a, F1, c1, k1, k2⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨rfl, rfl⟩ := h1 F F1 c c1 a hK.1 k1
  exact h2 F1 G c1 c' hK k2

/-- One after the other. -/
theorem Ad.seq {r : SubM Unit} {k : Unit → SubM Unit} {l₁ l₂ : List Aff} (h1 : Ad t K r l₁)
    (h2 : Ad t K (k ()) l₂) : Ad t K (r >>= k) (l₁ ++ l₂) := by
  intro F G c c' hK h
  obtain ⟨_, F1, c1, k1, k2⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨hK1, A1⟩ := h1 F F1 c c1 hK k1
  obtain ⟨hK2, A2⟩ := h2 F1 G c1 c' hK1 k2
  exact ⟨hK2, A1.trans A2⟩

end

/-- A run, in plain words: the list is the one at the first state's number of columns. -/
theorem Ad.run {t : ℕ} {r : SubM Unit} {l : ℕ → List Aff} (H : ∀ K, Ad t K r (l K)) {F G : Fork}
    {c c' : Ctx} (h : r F c = .ok (((), G), c')) (hs : F.LS.size = F.ns) :
    OnBytes.Road.Rows.Adds F (l (colsOf F t)) G ∧ colsOf G t = colsOf F t ∧ G.LS.size = G.ns := by
  obtain ⟨hK, A⟩ := H (colsOf F t) F G c c' ⟨rfl, hs⟩ h
  exact ⟨A, hK.1, hK.2⟩

/-- In the form «there is a list with a relation at F». -/
theorem Ad.some {t : ℕ} {r : SubM Unit} {l : ℕ → List Aff} (H : ∀ K, Ad t K r (l K)) {F G : Fork}
    {c c' : Ctx} (h : r F c = .ok (((), G), c')) (hs : F.LS.size = F.ns) :
    ∃ l', l' = l (colsOf F t) ∧ OnBytes.Road.Rows.Adds F l' G :=
  ⟨_, rfl, (Ad.run H h hs).1⟩

theorem rd_uEnt {K : ℕ} (t x : ℕ) : Rd t K (uEnt t x) (u3Form t K x) := by
  intro F G c c' a hK h
  have e := uEnt_ok t x F c _ h
  simp only [Prod.mk.injEq] at e
  rw [hK] at e
  exact ⟨e.1.2, e.1.1⟩

/-- As `Ad`, for a routine that returns a value. -/
def AdV {α : Type} (t K : ℕ) (r : SubM α) (v : α) (l : List Aff) : Prop :=
  ∀ (F G : Fork) (c c' : Ctx) (a : α), AtK t K F → r F c = .ok ((a, G), c') →
    a = v ∧ AtK t K G ∧ OnBytes.Road.Rows.Adds F l G

section
variable {α : Type} {t K : ℕ}

theorem AdV.pure (v : α) : AdV t K (Pure.pure v : SubM α) v [] := by
  intro F G c c' a hK h
  have e := (pure_ok v F c _).1 h
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, _⟩ := e
  exact ⟨rfl, hK, OnBytes.Road.Rows.Adds.nil _⟩

theorem AdV.seq {r : SubM Unit} {k : Unit → SubM α} {v : α} {l₁ l₂ : List Aff} (h1 : Ad t K r l₁)
    (h2 : AdV t K (k ()) v l₂) : AdV t K (r >>= k) v (l₁ ++ l₂) := by
  intro F G c c' a hK h
  obtain ⟨_, F1, c1, k1, k2⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨hK1, A1⟩ := h1 F F1 c c1 hK k1
  obtain ⟨e, hK2, A2⟩ := h2 F1 G c1 c' a hK1 k2
  exact ⟨e, hK2, A1.trans A2⟩

/-- A loop over a list, each step of which adds a list. -/
theorem Ad.forInList (f : α → PUnit → SubM (ForInStep PUnit)) (g : α → List Aff)
    (hf : ∀ a, AdV t K (f a PUnit.unit) (ForInStep.yield PUnit.unit) (g a)) :
    ∀ xs : List α, Ad t K (forIn xs PUnit.unit f) (xs.flatMap g)
  | [] => by
    rw [List.forIn_nil]
    exact Ad.pure
  | x :: xs => by
    rw [List.forIn_cons]
    intro F G c c' hK h
    obtain ⟨s, F1, c1, k1, k2⟩ := (bind_ok _ _ F c _).1 h
    obtain ⟨rfl, hK1, A1⟩ := hf x F F1 c c1 s hK k1
    obtain ⟨hK2, A2⟩ := Ad.forInList f g hf xs F1 G c1 c' hK1 k2
    exact ⟨hK2, A1.trans A2⟩

theorem Ad.forInRange (n : ℕ) (f : ℕ → PUnit → SubM (ForInStep PUnit)) (g : ℕ → List Aff)
    (hf : ∀ a, AdV t K (f a PUnit.unit) (ForInStep.yield PUnit.unit) (g a)) :
    Ad t K (forIn [:n] PUnit.unit f) ((List.range n).flatMap g) := by
  have e : List.range' ([:n] : Std.Legacy.Range).start ([:n] : Std.Legacy.Range).size
      ([:n] : Std.Legacy.Range).step = List.range n := by
    simp [Std.Legacy.Range.size, List.range_eq_range']
  rw [Std.Legacy.Range.forIn_eq_forIn_range', e]
  exact Ad.forInList f g hf _

theorem Ad.forInArray (xs : Array α) (f : α → PUnit → SubM (ForInStep PUnit)) (g : α → List Aff)
    (hf : ∀ a, AdV t K (f a PUnit.unit) (ForInStep.yield PUnit.unit) (g a)) :
    Ad t K (forIn xs PUnit.unit f) (xs.toList.flatMap g) := by
  rw [← Array.forIn_toList]
  exact Ad.forInList f g hf _

end

theorem Ad.then0 {t K : ℕ} {r : SubM Unit} {k : Unit → SubM Unit} {l : List Aff} (h1 : Ad t K r l)
    (h2 : Ad t K (k ()) []) : Ad t K (r >>= k) l := by
  have h := Ad.seq h1 h2
  rwa [List.append_nil] at h

section
variable {α σ : Type} {t K : ℕ}

theorem Rd.must (b : Bool) : Rd t K (SubM.must b) () := by
  intro F G c c' a _ h
  obtain ⟨_, e⟩ := (must_ok b F c _).1 h
  simp only [Prod.mk.injEq] at e
  exact ⟨e.1.2, rfl⟩

theorem Rd.foldlM (f : σ → α → SubM σ) (g : σ → α → σ) (hf : ∀ s a, Rd t K (f s a) (g s a)) :
    ∀ (xs : List α) (s : σ), Rd t K (xs.foldlM f s) (xs.foldl g s)
  | [], s => by
    rw [List.foldlM_nil]
    exact Rd.pure s
  | x :: xs, s => by
    rw [List.foldlM_cons]
    exact Rd.bind (hf s x) (Rd.foldlM f g hf xs (g s x))

theorem AdV.ofRd {r : SubM α} {v : α} (h : Rd t K r v) : AdV t K r v [] := by
  intro F G c c' a hK hr
  obtain ⟨rfl, e⟩ := h F G c c' a hK.1 hr
  exact ⟨e, hK, OnBytes.Road.Rows.Adds.nil _⟩

theorem AdV.bind {β : Type} {r : SubM α} {k : α → SubM β} {v : α} {w : β} {l₁ l₂ : List Aff}
    (h1 : AdV t K r v l₁) (h2 : AdV t K (k v) w l₂) : AdV t K (r >>= k) w (l₁ ++ l₂) := by
  intro F G c c' b hK h
  obtain ⟨a, F1, c1, k1, k2⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨rfl, hK1, A1⟩ := h1 F F1 c c1 a hK k1
  obtain ⟨e, hK2, A2⟩ := h2 F1 G c1 c' b hK1 k2
  exact ⟨e, hK2, A1.trans A2⟩

theorem AdV.ad {r : SubM Unit} {l : List Aff} (h : AdV t K r () l) : Ad t K r l :=
  fun F G c c' hK hr => (h F G c c' () hK hr).2

theorem Ad.adV {r : SubM Unit} {l : List Aff} (h : Ad t K r l) : AdV t K r () l :=
  fun F G c c' _ hK hr => ⟨rfl, h F G c c' hK hr⟩

/-- Filling a run of slots keeps AtK. -/
theorem atK_hideRun {F G : Fork} {j : ℕ} {v : Array E} {f : E} (c0 : Ctx)
    (h : F.hideRun j v f = some G) (hK : AtK t K F) : AtK t K G := by
  obtain ⟨_, _, H⟩ := Fixed.hideRun j v f
  obtain ⟨_, A, e⟩ := H F c0 () G c0 ((change_ok _ F c0 _).2 ⟨G, h, rfl⟩) hK.2
  exact ⟨by rw [e]; exact hK.1, A.sized⟩

theorem adV_pscRow (p : Psc) (S0 : E) (kept : Aff) :
    AdV t K (pscRow p S0 kept) (p.rowForm S0 kept, { p with rowMade := true }) [] := by
  intro F G c c' a hK h
  obtain ⟨row, p'⟩ := a
  obtain ⟨_, _, _, _, _, hG, hrow, hp⟩ := pscRow_ok p S0 kept F G c c' row p' h
  exact ⟨by rw [hrow, hp], atK_hideRun c hG hK,
    OnBytes.Road.Rows.Adds.keep (OnBytes.Road.Rows.Adds.nil F) (OnBytes.Road.Rows.hideRun_keeps hG)⟩

theorem ad_paid (i : ℕ) : Ad t K (SubM.paid i) [] := by
  intro F G c c' hK h
  obtain ⟨_, l, el, A⟩ := OnBytes.Road.Rows.walks_paid i F G c c' () h
  obtain rfl := Option.some.inj el
  obtain ⟨_, _, H⟩ := Fixed.paid i
  obtain ⟨_, A', e⟩ := H F c () G c' h hK.2
  exact ⟨⟨by rw [e]; exact hK.1, A'.sized⟩, A⟩

theorem ad_linsL : ∀ l : List Aff,
    Ad t K (l.foldlM (fun (_ : PUnit) a => SubM.lin a) PUnit.unit : SubM PUnit) l
  | [] => by
    rw [List.foldlM_nil]
    exact Ad.pure
  | a :: l => by
    rw [List.foldlM_cons]
    exact Ad.seq (l₁ := [a]) (Ad.lin a) (ad_linsL l)

theorem ad_forM_lin (rows : Array Aff) : Ad t K (rows.forM SubM.lin) rows.toList := by
  unfold Array.forM
  rw [← Array.foldlM_toList]
  exact ad_linsL _

end

/-- One claim by a form and runs of entries. -/
theorem Ad.t2Lin {t K : ℕ} (a : Aff) (rs : Array Run2) :
    Ad t K (OnBytes.Model.t2Lin a rs) [OnBytes.Road.Rows.claimForm a rs] := by
  intro F G c c' hK h
  obtain ⟨_, l, el, A⟩ := OnBytes.Road.Rows.walks_t2Lin a rs F G c c' () h
  obtain rfl := Option.some.inj el
  obtain ⟨_, _, H⟩ := Fixed.t2Lin a rs
  obtain ⟨_, A', e⟩ := H F c () G c' h hK.2
  exact ⟨⟨by rw [e]; exact hK.1, A'.sized⟩, A⟩

/-! ### further rules -/

section
variable {α β σ : Type} {t K : ℕ}

/-- A routine that never returns has every value. -/
theorem Rd.never {r : SubM α} (h : ∀ F c x, r F c ≠ .ok x) (v : α) : Rd t K r v :=
  fun F _ c _ _ _ hr => absurd hr (h F c _)

theorem AdV.never {r : SubM α} (h : ∀ F c x, r F c ≠ .ok x) (v : α) (l : List Aff) :
    AdV t K r v l :=
  fun F _ c _ _ _ hr => absurd hr (h F c _)

theorem AdV.ite {p : Prop} [Decidable p] {x y : SubM α} {v w : α} {l m : List Aff}
    (h1 : AdV t K x v l) (h2 : AdV t K y w m) :
    AdV t K (if p then x else y) (if p then v else w) (if p then l else m) := by
  split
  · exact h1
  · exact h2

theorem AdV.foldlM (f : σ → α → SubM σ) (g : σ → α → σ) (L : α → List Aff)
    (hf : ∀ s a, AdV t K (f s a) (g s a) (L a)) :
    ∀ (xs : List α) (s : σ), AdV t K (xs.foldlM f s) (xs.foldl g s) (xs.flatMap L)
  | [], s => AdV.pure s
  | a :: xs, s => by
    rw [List.foldlM_cons, List.foldl_cons, List.flatMap_cons]
    exact AdV.bind (hf s a) (AdV.foldlM f g L hf xs (g s a))

theorem Ad.forM (f : α → SubM PUnit) (L : α → List Aff) (hf : ∀ a, Ad t K (f a) (L a)) :
    ∀ xs : List α, Ad t K (xs.forM f) (xs.flatMap L)
  | [] => Ad.pure
  | a :: xs => by
    rw [List.flatMap_cons]
    show Ad t K (f a >>= fun _ => xs.forM f) _
    exact Ad.seq (hf a) (Ad.forM f L hf xs)

theorem refuse_never {α : Type} (name : String) (F : Fork) (c : Ctx) (x : (α × Fork) × Ctx) :
    (liftM (refuse name : Blk α) : SubM α) F c ≠ .ok x := fun hr => by
  obtain ⟨_, _, h1, _⟩ := (lift_ok _ _ _ _).1 hr
  exact absurd h1 (by simp [Model.refuse, Blk.fail])

theorem rd_getSome (a : α) : Rd t K (SubM.get (some a)) a := fun F G c c' x _ hr => by
  obtain ⟨a', h1, e⟩ := (get_ok _ _ _ _).1 hr
  have e1 : x = a' := congrArg (fun y : (α × Fork) × Ctx => y.1.1) e
  have e2 : G = F := congrArg (fun y : (α × Fork) × Ctx => y.1.2) e
  exact ⟨e2, e1.trans (Option.some.inj h1).symm⟩

theorem getNone_never (k : α → SubM β) (F : Fork) (c : Ctx) (x : (β × Fork) × Ctx) :
    (SubM.get (none : Option α) >>= k) F c ≠ .ok x := fun hr => by
  obtain ⟨_, _, _, h1, _⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, h2, _⟩ := (get_ok _ _ _ _).1 h1
  cases h2

end

theorem AdV.after {α β : Type} {t K : ℕ} {r : SubM α} {k : α → SubM β} {v : α} {w : β}
    {l : List Aff} (h1 : Rd t K r v) (h2 : AdV t K (k v) w l) : AdV t K (r >>= k) w l :=
  AdV.bind (AdV.ofRd h1) h2

theorem AdV.seq0 {α : Type} {t K : ℕ} {r : SubM Unit} {k : Unit → SubM α} {v : α} {l : List Aff}
    (h1 : Ad t K r l) (h2 : AdV t K (k ()) v []) : AdV t K (r >>= k) v l := by
  have := AdV.seq h1 h2
  rwa [List.append_nil] at this

theorem Ad.bindV {α : Type} {t K : ℕ} {r : SubM α} {k : α → SubM Unit} {v : α}
    {l₁ l₂ : List Aff} (h1 : AdV t K r v l₁) (h2 : Ad t K (k v) l₂) :
    Ad t K (r >>= k) (l₁ ++ l₂) :=
  AdV.ad (AdV.bind h1 (Ad.adV h2))

end Fo
