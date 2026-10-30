-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/AddShape.lean: THE ADDING OF CLAIMS TO THE ONE EQUATION (K9.addOne,
K9.addList, Johnson/Desc/First/Batch/Add.lean) ON SHAPES: one function from the ledger's shape and
the claims' shapes (LedSh, ClaimSh: Johnson/Desc/First/Shape/Parts.lean) to the ledger's shape
behind; and the two laws. General laws; nothing is evaluated. NO TEST OF THIS TEXT READS A VALUE,
and there is no premise.

  `fold_sh`: a fold of steps that may refuse, each of which tests the shape alone and keeps it.
  `map_same`: a change of one member of an array that keeps the member's shape keeps the list of
    shapes.
  `entryS`, `runS`: K9.entry-there and K9.run-fits on shapes. `entry_sh`, `run_sh`: the same tests.
  `addEntry_law`, `addSlot_law`, `addRun_law`: each step returns just where its test accepts, and
    keeps the arrays' shapes (the number of the slots' coefficients).
  `nextB`: K9.equation-open, K9.chi-drawn, K9.number-free on the shape. `nextS`: the ledger's shape
    with one claim more counted and its number marked. `trees_same`, `next_law`, `ledSh_next`,
    `forms_law`: tools.
  **`addOneS`**: THE ADDING OF ONE CLAIM ON SHAPES: nextB; every entry is there; every slot is below
    the number of slots; every run fits: then one claim more is counted and its number is marked.
    NOTHING ELSE OF THE LEDGER's SHAPE TURNS.
  **`addOne_carries`**: addOne F cl = .ok G: then addOneS (ledSh F) (claimSh cl) = some (ledSh G).
  **`addOne_returns`**: addOneS returns at the shapes: then addOne returns.
  **`addListS`**, **`addList_carries`**, **`addList_returns`**: the same for a list, in order.

Limits. Nothing on what the sums mean. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Add
import Johnson.Desc.First.Batch.Shape.DoorCut
import Johnson.Desc.First.Shape.Parts
import OnBytes.Model.TreesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First.Shape

/-! ## 1 Two general laws -/

theorem fold_sh {α β γ : Type} (f : β → α → Ans β) (sh : β → γ) (ok : γ → α → Bool)
    (h1 : ∀ b x b', f b x = .ok b' → ok (sh b) x = true ∧ sh b' = sh b)
    (h2 : ∀ b x, ok (sh b) x = true → ∃ b', f b x = .ok b') :
    ∀ (l : List α) (b : β),
      (∀ b', l.foldlM f b = .ok b' → l.all (ok (sh b)) = true ∧ sh b' = sh b) ∧
        (l.all (ok (sh b)) = true → ∃ b', l.foldlM f b = .ok b')
  | [], b => ⟨fun b' h => by
      obtain rfl : b = b' := Except.ok.inj h
      exact ⟨rfl, rfl⟩, fun _ => ⟨b, rfl⟩⟩
  | x :: l, b => by
    constructor
    · intro b' h
      rw [List.foldlM_cons] at h
      obtain ⟨c, hc, hr⟩ := (ans_bind _ _ _).1 h
      obtain ⟨a1, a2⟩ := h1 b x c hc
      obtain ⟨a3, a4⟩ := (fold_sh f sh ok h1 h2 l c).1 b' hr
      rw [a2] at a3 a4
      exact ⟨by rw [List.all_cons, a1, a3]; rfl, a4⟩
    · intro h
      rw [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨c, hc⟩ := h2 b x h.1
      have a2 := (h1 b x c hc).2
      obtain ⟨b', hb'⟩ := (fold_sh f sh ok h1 h2 l c).2 (by rw [a2]; exact h.2)
      exact ⟨b', by rw [List.foldlM_cons, hc]; exact hb'⟩

theorem map_same {α β : Type} (a : Array α) (i : Nat) (f : α → α) (sh : α → β)
    (h : ∀ x, sh (f x) = sh x) : (a.modify i f).toList.map sh = a.toList.map sh := by
  refine List.ext_getElem (by simp) fun j j1 j2 => ?_
  simp only [List.getElem_map, Array.getElem_toList, Array.getElem_modify]
  split
  · exact h _
  · rfl

/-! ## 2 The three steps -/

/-- K9.entry-there, on shapes. -/
def entryS (trees : List TreeSh) (x : EntSh) : Bool :=
  match trees[x.1]? with
  | none => false
  | some X =>
    match X.rows[x.2.1]? with
    | none => false
    | some r => decide (r.col0 ≤ x.2.2) && decide (x.2.2 - r.col0 < r.entries)

theorem entry_sh (trees : Array HTree) (x : Ent) :
    entryThere trees x = entryS (trees.toList.map treeSh) (entSh x) := by
  unfold entryThere entryS
  show _ = (match (trees.toList.map treeSh)[x.tree]? with
    | none => false
    | some X =>
      match X.rows[x.row]? with
      | none => false
      | some r => decide (r.col0 ≤ x.idx) && decide (x.idx - r.col0 < r.entries))
  rw [List.getElem?_map, Array.getElem?_toList]
  cases trees[x.tree]? with
  | none => rfl
  | some X =>
    show (match X.rows[x.row]? with
      | none => false
      | some r => decide (r.L0 ≤ x.idx) && decide (x.idx - r.L0 < r.L.size)) =
      (match (X.rows.toList.map rowSh)[x.row]? with
      | none => false
      | some r => decide (r.col0 ≤ x.idx) && decide (x.idx - r.col0 < r.entries))
    rw [List.getElem?_map, Array.getElem?_toList]
    cases X.rows[x.row]? <;> rfl

/-- A change of one row's column weights that keeps their number keeps the arrays' shapes. -/
theorem trees_same (trees : Array HTree) (t r : Nat) (g : HRow → Array E)
    (hg : ∀ R, (g R).size = R.L.size) :
    (trees.modify t fun X =>
      { X with rows := X.rows.modify r fun R => { R with L := g R } }).toList.map treeSh =
      trees.toList.map treeSh := by
  refine map_same _ _ _ _ fun X => ?_
  show TreeSh.mk X.name (X.kind == .symbols) X.R X.K
    ((X.rows.modify r fun R => { R with L := g R }).toList.map rowSh) X.root.isSome = _
  rw [map_same X.rows r _ rowSh fun R => by
    show RowSh.mk R.coef.size (g R).size R.L0 R.rowForm R.rowOnes R.rowFirst = _
    rw [hg]
    rfl]
  rfl

theorem addEntry_law (w : E) (trees : Array HTree) (x : Ent) :
    (∀ trees', addEntry w trees x = .ok trees' →
      entryS (trees.toList.map treeSh) (entSh x) = true ∧
        trees'.toList.map treeSh = trees.toList.map treeSh) ∧
      (entryS (trees.toList.map treeSh) (entSh x) = true → ∃ trees', addEntry w trees x =
        .ok trees') := by
  unfold addEntry
  rw [← entry_sh]
  constructor
  · intro trees' h
    simp only [ans_bind, need_ok, exists_const] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := Except.ok.inj h2
    exact ⟨h1, trees_same trees x.tree x.row _ fun R => by simp⟩
  · intro h
    rw [h]
    exact ⟨_, rfl⟩

theorem addSlot_law (w : E) (ns : Nat) (LS : Array E) (x : Nat × E) :
    (∀ LS', addSlot w ns LS x = .ok LS' → decide (x.1 < ns) = true ∧ LS'.size = LS.size) ∧
      (decide (x.1 < ns) = true → ∃ LS', addSlot w ns LS x = .ok LS') := by
  unfold addSlot
  constructor
  · intro LS' h
    simp only [ans_bind, need_ok, exists_const] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := Except.ok.inj h2
    exact ⟨h1, by simp⟩
  · intro h
    rw [h]
    exact ⟨_, rfl⟩

/-- K9.run-fits, on shapes. -/
def runS (trees : List TreeSh) (r : RunSh) : Bool :=
  match trees[r.tree]? with
  | none => false
  | some X =>
    match X.rows[r.row]? with
    | none => false
    | some R =>
      decide (r.w0 ≤ r.weights) && decide (r.n ≤ r.weights - r.w0) && decide (R.col0 ≤ r.first) &&
        decide (r.first - R.col0 ≤ R.entries) && decide (r.n ≤ R.entries - (r.first - R.col0))

theorem run_sh (trees : Array HTree) (r : Run2) :
    runFitsRow trees r = runS (trees.toList.map treeSh) (runSh r) := by
  unfold runFitsRow runS
  show _ = (match (trees.toList.map treeSh)[r.tree]? with
    | none => false
    | some X =>
      match X.rows[r.row]? with
      | none => false
      | some R =>
        decide (r.w0 ≤ r.w.size) && decide (r.n ≤ r.w.size - r.w0) && decide (R.col0 ≤ r.first) &&
          decide (r.first - R.col0 ≤ R.entries) && decide (r.n ≤ R.entries - (r.first - R.col0)))
  rw [List.getElem?_map, Array.getElem?_toList]
  cases trees[r.tree]? with
  | none => rfl
  | some X =>
    show (match X.rows[r.row]? with
      | none => false
      | some R =>
        decide (r.w0 ≤ r.w.size) && decide (r.n ≤ r.w.size - r.w0) && decide (R.L0 ≤ r.first) &&
          decide (r.first - R.L0 ≤ R.L.size) && decide (r.n ≤ R.L.size - (r.first - R.L0))) =
      (match (X.rows.toList.map rowSh)[r.row]? with
      | none => false
      | some R =>
        decide (r.w0 ≤ r.w.size) && decide (r.n ≤ r.w.size - r.w0) && decide (R.col0 ≤ r.first) &&
          decide (r.first - R.col0 ≤ R.entries) && decide (r.n ≤ R.entries - (r.first - R.col0)))
    rw [List.getElem?_map, Array.getElem?_toList]
    cases X.rows[r.row]? <;> rfl

theorem addRun_law (w : E) (trees : Array HTree) (r : Run2) :
    (∀ trees', addRun w trees r = .ok trees' →
      runS (trees.toList.map treeSh) (runSh r) = true ∧
        trees'.toList.map treeSh = trees.toList.map treeSh) ∧
      (runS (trees.toList.map treeSh) (runSh r) = true → ∃ trees', addRun w trees r =
        .ok trees') := by
  unfold addRun
  rw [← run_sh]
  constructor
  · intro trees' h
    simp only [ans_bind, need_ok, exists_const] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := Except.ok.inj h2
    exact ⟨h1, trees_same trees r.tree r.row _ fun R => size_runLoop _ _ _ _ _ _ _⟩
  · intro h
    rw [h]
    exact ⟨_, rfl⟩

/-! ## 3 One claim -/

/-- K9.equation-open, K9.chi-drawn, K9.number-free, on the shape. -/
def nextB (L : LedSh) : Bool :=
  !L.shut && L.drawn &&
    (decide (L.claims < L.planClaims) && L.handed.length == L.planClaims &&
      !L.handed.getD L.claims true)

/-- The ledger's shape with one claim more counted and its number marked. -/
def nextS (L : LedSh) : LedSh :=
  LedSh.mk L.ns L.shown L.factors L.got L.owed L.planClaims L.trees L.next L.coefs (L.claims + 1)
    L.drawn (L.handed.set L.claims true) L.shut

/-- **THE ADDING OF ONE CLAIM ON SHAPES.** -/
def addOneS (L : LedSh) (c : ClaimSh) : Option LedSh :=
  if nextB L && c.form.ents.all (entryS L.trees) && c.form.slots.all (fun j => decide (j < L.ns)) &&
      c.runs.all (runS L.trees) then some (nextS L)
  else none

theorem next_law (F : Fork) :
    (∀ x, weightNext F = .ok x → nextB (ledSh F) = true ∧
      x.2 = { F with kapMapF := F.kapMapF.set! F.nClaim true, nClaim := F.nClaim + 1 }) ∧
      (nextB (ledSh F) = true → ∃ x, weightNext F = .ok x) := by
  have e : nextB (ledSh F) = (!F.doorShutF && F.thetaDrawnF &&
      (decide (F.nClaim < F.planClaimsF) && F.kapMapF.size == F.planClaimsF &&
        !F.kapMapF.getD F.nClaim true)) := by
    show (!F.doorShutF && F.thetaDrawnF &&
      (decide (F.nClaim < F.planClaimsF) && F.kapMapF.toList.length == F.planClaimsF &&
        !F.kapMapF.toList.getD F.nClaim true)) = _
    rw [Array.length_toList]
    congr 3
    by_cases h : F.nClaim < F.kapMapF.size <;>
      simp [Array.getD, List.getD, h]
  rw [e]
  unfold weightNext
  constructor
  · intro x h
    simp only [ans_bind, need_ok, exists_const] at h
    obtain ⟨a1, a2, a3, a4⟩ := h
    obtain rfl := Except.ok.inj a4
    exact ⟨by rw [a1, a2, a3]; rfl, rfl⟩
  · intro h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨a1, a2⟩, a3⟩ := h
    have a3' : (decide (F.nClaim < F.planClaimsF) && F.kapMapF.size == F.planClaimsF &&
        !F.kapMapF.getD F.nClaim true) = true := by
      simp only [Bool.and_eq_true]
      exact a3
    rw [a1, a2, a3']
    exact ⟨_, rfl⟩

theorem ledSh_next (F : Fork) (trees : Array HTree) (LS : Array E) (c0 : E)
    (h1 : trees.toList.map treeSh = F.trees.toList.map treeSh) (h2 : LS.size = F.LS.size) :
    ledSh { F with kapMapF := F.kapMapF.set! F.nClaim true, nClaim := F.nClaim + 1,
                   trees := trees, LS := LS, c0 := c0 } = nextS (ledSh F) := by
  show LedSh.mk F.ns F.vp.size F.mf.size F.gotF.toList (F.owed.toList.map (·.added)) F.planClaimsF
    (trees.toList.map treeSh) F.next LS.size (F.nClaim + 1) F.thetaDrawnF
    (F.kapMapF.set! F.nClaim true).toList F.doorShutF = _
  rw [h1, h2]
  show _ = LedSh.mk F.ns F.vp.size F.mf.size F.gotF.toList (F.owed.toList.map (·.added))
    F.planClaimsF (F.trees.toList.map treeSh) F.next F.LS.size (F.nClaim + 1) F.thetaDrawnF
    (F.kapMapF.toList.set F.nClaim true) F.doorShutF
  congr 1
  simp

/-- The three folds of one adding, at a ledger G: they return just where the three tests on shapes
accept; the arrays' shapes and the number of the slots' coefficients stay. -/
theorem forms_law (G : Fork) (w : E) (cl : Claim) :
    (∀ H, (addForm G w cl.form >>= fun G' => addRuns G' w cl.runs) = .ok H →
      ((claimSh cl).form.ents.all (entryS (G.trees.toList.map treeSh)) = true ∧
        (claimSh cl).form.slots.all (fun j => decide (j < G.ns)) = true ∧
        (claimSh cl).runs.all (runS (G.trees.toList.map treeSh)) = true) ∧
      ∃ trees LS c0, H = { G with trees := trees, LS := LS, c0 := c0 } ∧
        trees.toList.map treeSh = G.trees.toList.map treeSh ∧ LS.size = G.LS.size) ∧
      ((claimSh cl).form.ents.all (entryS (G.trees.toList.map treeSh)) = true →
        (claimSh cl).form.slots.all (fun j => decide (j < G.ns)) = true →
        (claimSh cl).runs.all (runS (G.trees.toList.map treeSh)) = true →
        ∃ H, (addForm G w cl.form >>= fun G' => addRuns G' w cl.runs) = .ok H) := by
  have hE := fold_sh (addEntry w) (fun t : Array HTree => t.toList.map treeSh)
    (fun sh x => entryS sh (entSh x)) (fun b x b' h => (addEntry_law w b x).1 b' h)
    (fun b x h => (addEntry_law w b x).2 h)
  have hS := fold_sh (addSlot w G.ns) (fun a : Array E => a.size)
    (fun _ x => decide (x.1 < G.ns)) (fun b x b' h => (addSlot_law w G.ns b x).1 b' h)
    (fun b x h => (addSlot_law w G.ns b x).2 h)
  have hR := fold_sh (addRun w) (fun t : Array HTree => t.toList.map treeSh)
    (fun sh x => runS sh (runSh x)) (fun b x b' h => (addRun_law w b x).1 b' h)
    (fun b x h => (addRun_law w b x).2 h)
  have e1 : (claimSh cl).form.ents.all (entryS (G.trees.toList.map treeSh)) =
      cl.form.ents.toList.all fun x => entryS (G.trees.toList.map treeSh) (entSh x) := by
    show (cl.form.ents.toList.map entSh).all _ = _
    rw [List.all_map]
    rfl
  have e2 : (claimSh cl).form.slots.all (fun j => decide (j < G.ns)) =
      cl.form.slots.toList.all fun x => decide (x.1 < G.ns) := by
    show (cl.form.slots.toList.map (·.1)).all _ = _
    rw [List.all_map]
    rfl
  have e3 : (claimSh cl).runs.all (runS (G.trees.toList.map treeSh)) =
      cl.runs.toList.all fun x => runS (G.trees.toList.map treeSh) (runSh x) := by
    show (cl.runs.toList.map runSh).all _ = _
    rw [List.all_map]
    rfl
  rw [e1, e2, e3]
  unfold addForm addRuns
  simp only [← Array.foldlM_toList]
  constructor
  · intro H h
    simp only [ans_bind] at h
    obtain ⟨G', ⟨t1, ht1, LS', hLS, eG⟩, t2, ht2, eH⟩ := h
    obtain rfl := Except.ok.inj eG
    obtain rfl := Except.ok.inj eH
    obtain ⟨a1, a2⟩ := (hE cl.form.ents.toList G.trees).1 t1 ht1
    obtain ⟨b1, b2⟩ := (hS cl.form.slots.toList G.LS).1 LS' hLS
    obtain ⟨c1, c2⟩ := (hR cl.runs.toList t1).1 t2 ht2
    dsimp only at a2 b2 c1 c2
    rw [a2] at c1 c2
    exact ⟨⟨a1, b1, c1⟩, t2, LS', _, rfl, c2, b2⟩
  · intro a1 b1 c1
    obtain ⟨t1, ht1⟩ := (hE cl.form.ents.toList G.trees).2 a1
    obtain ⟨LS', hLS⟩ := (hS cl.form.slots.toList G.LS).2 b1
    have a2 := ((hE cl.form.ents.toList G.trees).1 t1 ht1).2
    dsimp only at a2
    obtain ⟨t2, ht2⟩ := (hR cl.runs.toList t1).2 (by dsimp only; rw [a2]; exact c1)
    simp only [ans_bind]
    exact ⟨_, _, ⟨t1, ht1, LS', hLS, rfl⟩, t2, ht2, rfl⟩

theorem addOne_carries (F G : Fork) (cl : Claim) (h : addOne F cl = .ok G) :
    addOneS (ledSh F) (claimSh cl) = some (ledSh G) := by
  unfold addOne at h
  simp only [ans_bind] at h
  obtain ⟨x, hx, G', hG', hG⟩ := h
  obtain ⟨n1, n2⟩ := (next_law F).1 x hx
  have hb : (addForm x.2 ((cl.eqFirst.map fun first =>
      powE F.theta (F.planClaimsF + first)).getD x.1) cl.form >>= fun G' =>
      addRuns G' ((cl.eqFirst.map fun first =>
        powE F.theta (F.planClaimsF + first)).getD x.1) cl.runs) = .ok G := by
    rw [hG']
    exact hG
  obtain ⟨⟨a1, a2, a3⟩, trees, LS, c0, rfl, t1, t2⟩ := (forms_law x.2 _ cl).1 G hb
  rw [n2] at a1 a2 a3 t1 t2 ⊢
  unfold addOneS
  rw [if_pos (by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨n1, a1⟩, a2⟩, a3⟩)]
  exact congrArg some (ledSh_next F trees LS c0 t1 t2).symm

theorem addOne_returns (F : Fork) (cl : Claim) (y : LedSh)
    (h : addOneS (ledSh F) (claimSh cl) = some y) : ∃ G, addOne F cl = .ok G := by
  unfold addOneS at h
  split at h
  · rename_i hb
    simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨n1, a1⟩, a2⟩, a3⟩ := hb
    obtain ⟨x, hx⟩ := (next_law F).2 n1
    have n2 := ((next_law F).1 x hx).2
    obtain ⟨H, hH⟩ := (forms_law x.2 ((cl.eqFirst.map fun first =>
      powE F.theta (F.planClaimsF + first)).getD x.1) cl).2
      (by rw [n2]; exact a1) (by rw [n2]; exact a2) (by rw [n2]; exact a3)
    refine ⟨H, ?_⟩
    unfold addOne
    simp only [ans_bind] at hH ⊢
    obtain ⟨G', h1, h2⟩ := hH
    exact ⟨x, hx, G', h1, h2⟩
  · exact nomatch h

/-! ## 4 A list of claims -/

/-- **THE ADDING OF A LIST OF CLAIMS ON SHAPES.** -/
def addListS (L : LedSh) : List ClaimSh → Option LedSh
  | [] => some L
  | c :: cs => (addOneS L c).bind fun L' => addListS L' cs

theorem addList_carries : ∀ (cls : List Claim) (F G : Fork), addList F cls = .ok G →
    addListS (ledSh F) (cls.map claimSh) = some (ledSh G)
  | [], F, G, h => by
    obtain rfl : F = G := Except.ok.inj h
    rfl
  | cl :: cls, F, G, h => by
    have h' : (addOne F cl >>= fun F' => addList F' cls) = .ok G := by
      unfold addList at h ⊢
      rw [List.foldlM_cons] at h
      exact h
    obtain ⟨F', h1, h2⟩ := (ans_bind _ _ _).1 h'
    show (addOneS (ledSh F) (claimSh cl)).bind (fun L' => addListS L' (cls.map claimSh)) = _
    rw [addOne_carries F F' cl h1]
    exact addList_carries cls F' G h2

theorem addList_returns : ∀ (cls : List Claim) (F : Fork) (y : LedSh),
    addListS (ledSh F) (cls.map claimSh) = some y → ∃ G, addList F cls = .ok G
  | [], F, _, _ => ⟨F, rfl⟩
  | cl :: cls, F, y, h => by
    obtain ⟨L', h1, h2⟩ := Option.bind_eq_some_iff.1
      (show (addOneS (ledSh F) (claimSh cl)).bind
        (fun L' => addListS L' (cls.map claimSh)) = some y from h)
    obtain ⟨F', hF'⟩ := addOne_returns F cl L' h1
    obtain rfl : ledSh F' = L' :=
      Option.some.inj ((addOne_carries F F' cl hF').symm.trans h1)
    obtain ⟨G, hG⟩ := addList_returns cls F' y h2
    refine ⟨G, ?_⟩
    unfold addList at hG ⊢
    rw [List.foldlM_cons, hF']
    exact hG

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.addOne_carries
#print axioms VerifiableInference.Desc.K9.Shape.addOne_returns
#print axioms VerifiableInference.Desc.K9.Shape.addList_carries
#print axioms VerifiableInference.Desc.K9.Shape.addList_returns
#print axioms VerifiableInference.Desc.K9.Shape.next_law
#print axioms VerifiableInference.Desc.K9.Shape.ledSh_next
#print axioms VerifiableInference.Desc.K9.Shape.fold_sh
#print axioms VerifiableInference.Desc.K9.Shape.addEntry_law
#print axioms VerifiableInference.Desc.K9.Shape.addSlot_law
#print axioms VerifiableInference.Desc.K9.Shape.addRun_law
#print axioms VerifiableInference.Desc.K9.Shape.map_same
#print axioms VerifiableInference.Desc.K9.Shape.entryS
#print axioms VerifiableInference.Desc.K9.Shape.entry_sh
#print axioms VerifiableInference.Desc.K9.Shape.trees_same
#print axioms VerifiableInference.Desc.K9.Shape.runS
#print axioms VerifiableInference.Desc.K9.Shape.run_sh
#print axioms VerifiableInference.Desc.K9.Shape.nextB
#print axioms VerifiableInference.Desc.K9.Shape.nextS
#print axioms VerifiableInference.Desc.K9.Shape.addOneS
#print axioms VerifiableInference.Desc.K9.Shape.forms_law
#print axioms VerifiableInference.Desc.K9.Shape.addListS
