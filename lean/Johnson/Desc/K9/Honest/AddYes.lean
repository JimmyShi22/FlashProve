-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K9/Honest/AddYes.lean (kind K9): WHEN K9's OWN ADDING RETURNS: from two Bools with code.
Statements and proofs ON THE VERIFIER's OWN TEXT (`K9.addList`, Johnson/Desc/First/Batch/Add.lean); no prover
is in this file, and no goal is stated.

  `claimFits trees ns cl`   the claim's entries, slots and runs are there: K9's own three tests
                    ("K9.entry-there", "K9.slot-there", "K9.run-fits"), asked AT THE ARRAYS IN FRONT OF THE
                    WHOLE ADDING
  `addReady F k`    the ledger can take k claims more: the equation is open; chi is drawn; the numbers stay
                    within the plan's; one mark for each number of the plan; the next k numbers are free
  `entryThere_congr`, `runFitsRow_congr`   the two tests on the arrays read their frame alone (all but the
                    weights' values)
  `fold_iff`, `addForm_iff`, `addRuns_iff`, `weightNext_iff`   the adding's parts, each both ways
  `Added F G`       what one adding leaves and turns, beside the sums: the frame, the number of slots, the
                    flags and the plan's number stay; one claim more is counted; its number is marked
  `addOne_yes`, `addOne_only`   one claim, both ways. `ready_succ`: the ledger can take k + 1 claims just if it
                    can take one and, behind that one's adding, k more
  `AddedAll F G k`  the like of k claims: k more are counted; the frame, the number of slots, the flags and the
                    plan's number stay
  `addList_yes`     **`addReady F cls.length` and every claim fits ⟹ the adding returns**, and `AddedAll`
  `addList_only`    and the other way round: where the adding returns, every claim fitted, and, IF THERE WAS A
                    CLAIM, the ledger could take them all (of no claim the adding returns whatever the ledger
                    is). SO THE ADDING's YES HANGS ON NO VALUE: on no weight, coefficient, constant or chi

WHAT IS NOT CLAIMED. That a real segment's claims fit. Nothing on any property.

-/
import Johnson.Desc.First.Batch.Law.AddAgrees
import OnBytes.Model.TreesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9H
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (addList addOne addForm addRuns addEntry addRun weightNext
  entryThere runFitsRow)
open VerifiableInference.Desc.K9L (toOption_some addEntry_older addRun_older)

/-- The claim's entries, slots and runs are there. -/
def claimFits (trees : Array HTree) (ns : Nat) (cl : Claim) : Bool :=
  cl.form.ents.toList.all (entryThere trees) && cl.form.slots.toList.all (fun x => decide (x.1 < ns)) &&
    cl.runs.toList.all (runFitsRow trees)

/-- The ledger can take k claims more. -/
def addReady (F : Fork) (k : Nat) : Bool :=
  !F.doorShutF && F.thetaDrawnF && decide (F.nClaim + k ≤ F.planClaimsF) &&
    F.kapMapF.size == F.planClaimsF && (List.range k).all fun i => !F.kapMapF.getD (F.nClaim + i) true

/-- A row's frame at an index, off the arrays' frame. -/
theorem row_frame (A B : Array HTree) (h : treesFrame A = treesFrame B) (t r : Nat) :
    ((A[t]?).bind fun X => (X.rows[r]?).map HRow.frame) =
      ((B[t]?).bind fun X => (X.rows[r]?).map HRow.frame) := by
  have e : ∀ T : Array HTree, ((T[t]?).bind fun X => (X.rows[r]?).map HRow.frame) =
      (((treesFrame T)[t]?).bind fun y => y.2[r]?) := by
    intro T
    simp only [treesFrame, Array.getElem?_map]
    cases T[t]? with
    | none => rfl
    | some X => simp [HTree.frame, Array.getElem?_map]
  rw [e A, e B, h]

/-- The test on an entry reads the row's frame alone. -/
theorem entryThere_eq (A : Array HTree) (x : Ent) :
    entryThere A x =
      match ((A[x.tree]?).bind fun X => (X.rows[x.row]?).map HRow.frame) with
      | none => false
      | some fr => decide (fr.1.L0 ≤ x.idx) && decide (x.idx - fr.1.L0 < fr.2) := by
  unfold entryThere
  cases A[x.tree]? with
  | none => rfl
  | some X =>
    show (match X.rows[x.row]? with
      | none => false
      | some r => decide (r.L0 ≤ x.idx) && decide (x.idx - r.L0 < r.L.size)) =
      match (X.rows[x.row]?).map HRow.frame with
      | none => false
      | some fr => decide (fr.1.L0 ≤ x.idx) && decide (x.idx - fr.1.L0 < fr.2)
    cases X.rows[x.row]? <;> rfl

theorem entryThere_congr (A B : Array HTree) (h : treesFrame A = treesFrame B) (x : Ent) :
    entryThere A x = entryThere B x := by
  rw [entryThere_eq, entryThere_eq, row_frame A B h]

/-- The test on a run reads the row's frame alone. -/
theorem runFitsRow_eq (A : Array HTree) (r : Run2) :
    runFitsRow A r =
      match ((A[r.tree]?).bind fun X => (X.rows[r.row]?).map HRow.frame) with
      | none => false
      | some fr =>
        decide (r.w0 ≤ r.w.size) && decide (r.n ≤ r.w.size - r.w0) && decide (fr.1.L0 ≤ r.first) &&
          decide (r.first - fr.1.L0 ≤ fr.2) && decide (r.n ≤ fr.2 - (r.first - fr.1.L0)) := by
  unfold runFitsRow
  cases A[r.tree]? with
  | none => rfl
  | some X =>
    show (match X.rows[r.row]? with
      | none => false
      | some R =>
        decide (r.w0 ≤ r.w.size) && decide (r.n ≤ r.w.size - r.w0) && decide (R.L0 ≤ r.first) &&
          decide (r.first - R.L0 ≤ R.L.size) && decide (r.n ≤ R.L.size - (r.first - R.L0))) =
      match (X.rows[r.row]?).map HRow.frame with
      | none => false
      | some fr =>
        decide (r.w0 ≤ r.w.size) && decide (r.n ≤ r.w.size - r.w0) && decide (fr.1.L0 ≤ r.first) &&
          decide (r.first - fr.1.L0 ≤ fr.2) && decide (r.n ≤ fr.2 - (r.first - fr.1.L0))
    cases X.rows[r.row]? <;> rfl

theorem runFitsRow_congr (A B : Array HTree) (h : treesFrame A = treesFrame B) (x : Run2) :
    runFitsRow A x = runFitsRow B x := by
  rw [runFitsRow_eq, runFitsRow_eq, row_frame A B h]

theorem addEntry_frame (w : E) (A B : Array HTree) (x : Ent) (h : addEntry w A x = .ok B) :
    treesFrame B = treesFrame A :=
  pushEnt_frame w A B x (by rw [← addEntry_older, h]; rfl)

theorem addRun_frame (w : E) (A B : Array HTree) (x : Run2) (h : addRun w A x = .ok B) :
    treesFrame B = treesFrame A :=
  pushRun_frame w A B x (by rw [← addRun_older, h]; rfl)

theorem addEntry_iff (w : E) (A : Array HTree) (x : Ent) :
    (∃ B, addEntry w A x = .ok B) ↔ entryThere A x = true := by
  unfold addEntry
  cases entryThere A x with
  | true => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
  | false => exact ⟨fun ⟨_, h⟩ => (nomatch h), fun h => (nomatch h)⟩

theorem addRun_iff (w : E) (A : Array HTree) (x : Run2) :
    (∃ B, addRun w A x = .ok B) ↔ runFitsRow A x = true := by
  unfold addRun
  cases runFitsRow A x with
  | true => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
  | false => exact ⟨fun ⟨_, h⟩ => (nomatch h), fun h => (nomatch h)⟩

theorem addSlot_iff (w : E) (ns : Nat) (LS : Array E) (x : Nat × E) :
    (∃ B, VerifiableInference.Desc.K9.addSlot w ns LS x = .ok B) ↔ decide (x.1 < ns) = true := by
  unfold VerifiableInference.Desc.K9.addSlot
  cases decide (x.1 < ns) with
  | true => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
  | false => exact ⟨fun ⟨_, h⟩ => (nomatch h), fun h => (nomatch h)⟩

/-- A fold of steps each of which returns just where a test on a kept frame says yes. -/
theorem fold_iff {α β γ : Type} (f : β → α → Except String β) (test : β → α → Bool) (fr : β → γ)
    (h1 : ∀ b a, (∃ c, f b a = .ok c) ↔ test b a = true)
    (h2 : ∀ b a c, f b a = .ok c → fr c = fr b)
    (h3 : ∀ b c a, fr b = fr c → test b a = test c a) :
    ∀ (l : List α) (b : β), (∃ c, l.foldlM f b = .ok c ∧ fr c = fr b) ↔ l.all (test b) = true
  | [], b => ⟨fun _ => rfl, fun _ => ⟨b, rfl, rfl⟩⟩
  | a :: l, b => by
    rw [List.all_cons, Bool.and_eq_true, List.foldlM_cons]
    constructor
    · rintro ⟨c, hc, _⟩
      cases hf : f b a with
      | error m => rw [hf] at hc; exact nomatch hc
      | ok d =>
        rw [hf] at hc
        have hd := h2 b a d hf
        have hrest : ∃ c, l.foldlM f d = .ok c := ⟨c, hc⟩
        have key : ∀ (l : List α) (d : β), (∃ c, l.foldlM f d = .ok c) →
            ∃ c, l.foldlM f d = .ok c ∧ fr c = fr d := by
          intro l
          induction l with
          | nil => intro d ⟨c, h⟩; exact ⟨c, h, by rw [← Except.ok.inj h]⟩
          | cons a' l' ih =>
            intro d ⟨c, h⟩
            rw [List.foldlM_cons] at h
            cases hf' : f d a' with
            | error m => rw [hf'] at h; exact nomatch h
            | ok d' =>
              rw [hf'] at h
              obtain ⟨c', hc', e'⟩ := ih d' ⟨c, h⟩
              exact ⟨c', by rw [List.foldlM_cons, hf']; exact hc', e'.trans (h2 d a' d' hf')⟩
        have h4 := (fold_iff f test fr h1 h2 h3 l d).1 (key l d hrest)
        refine ⟨(h1 b a).1 ⟨d, hf⟩, ?_⟩
        rw [List.all_eq_true] at h4 ⊢
        intro y hy
        rw [h3 b d y hd.symm]
        exact h4 y hy
    · rintro ⟨ha, hl⟩
      obtain ⟨d, hf⟩ := (h1 b a).2 ha
      have hd := h2 b a d hf
      have hl' : l.all (test d) = true := by
        rw [List.all_eq_true] at hl ⊢
        intro y hy
        rw [h3 d b y hd]
        exact hl y hy
      obtain ⟨c, hc, e⟩ := (fold_iff f test fr h1 h2 h3 l d).2 hl'
      exact ⟨c, by rw [hf]; exact hc, e.trans hd⟩

/-- The form's share: it is added just where its entries and slots are there; the frame stays. -/
theorem addForm_iff (F : Fork) (w : E) (a : Aff) :
    ((∃ G, addForm F w a = .ok G) →
      (a.ents.toList.all (entryThere F.trees) = true ∧
        a.slots.toList.all (fun x => decide (x.1 < F.ns)) = true)) ∧
    ((a.ents.toList.all (entryThere F.trees) = true ∧
        a.slots.toList.all (fun x => decide (x.1 < F.ns)) = true) →
      ∃ G, addForm F w a = .ok G ∧ treesFrame G.trees = treesFrame F.trees ∧
        G = { F with trees := G.trees, LS := G.LS, c0 := G.c0 }) := by
  have hE := fold_iff (addEntry w) entryThere treesFrame (addEntry_iff w)
    (fun b x c h => addEntry_frame w b c x h) (fun b c x h => entryThere_congr b c h x)
    a.ents.toList F.trees
  have hS := fold_iff (VerifiableInference.Desc.K9.addSlot w F.ns) (fun _ x => decide (x.1 < F.ns))
    (fun _ => ()) (addSlot_iff w F.ns) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    a.slots.toList F.LS
  unfold addForm
  simp only []
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  constructor
  · rintro ⟨G, hG⟩
    cases h1 : a.ents.toList.foldlM (addEntry w) F.trees with
    | error m => rw [h1] at hG; exact nomatch hG
    | ok T =>
      rw [h1] at hG
      cases h2 : a.slots.toList.foldlM (VerifiableInference.Desc.K9.addSlot w F.ns) F.LS with
      | error m => rw [h2] at hG; exact nomatch hG
      | ok L =>
        have fT : treesFrame T = treesFrame F.trees := by
          have key : ∀ (l : List Ent) (b c : Array HTree), l.foldlM (addEntry w) b = .ok c →
              treesFrame c = treesFrame b := by
            intro l
            induction l with
            | nil => intro b c h; rw [← Except.ok.inj h]
            | cons x l ih =>
              intro b c h
              rw [List.foldlM_cons] at h
              cases hx : addEntry w b x with
              | error m => rw [hx] at h; exact nomatch h
              | ok d => rw [hx] at h; exact (ih d c h).trans (addEntry_frame w b d x hx)
          exact key _ _ _ h1
        exact ⟨hE.1 ⟨T, h1, fT⟩, hS.1 ⟨L, h2, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨T, hT, fT⟩ := hE.2 h1
    obtain ⟨L, hL, _⟩ := hS.2 h2
    rw [hT, hL]
    exact ⟨_, rfl, fT, rfl⟩

/-- The runs' share. -/
theorem addRuns_iff (F : Fork) (w : E) (runs : Array Run2) :
    ((∃ G, addRuns F w runs = .ok G) → runs.toList.all (runFitsRow F.trees) = true) ∧
    (runs.toList.all (runFitsRow F.trees) = true →
      ∃ G, addRuns F w runs = .ok G ∧ treesFrame G.trees = treesFrame F.trees ∧
        G = { F with trees := G.trees }) := by
  have hR := fold_iff (addRun w) runFitsRow treesFrame (addRun_iff w)
    (fun b x c h => addRun_frame w b c x h) (fun b c x h => runFitsRow_congr b c h x)
    runs.toList F.trees
  unfold addRuns
  simp only []
  rw [← Array.foldlM_toList]
  constructor
  · rintro ⟨G, hG⟩
    cases h1 : runs.toList.foldlM (addRun w) F.trees with
    | error m => rw [h1] at hG; exact nomatch hG
    | ok T =>
      have fT : treesFrame T = treesFrame F.trees := by
        have key : ∀ (l : List Run2) (b c : Array HTree), l.foldlM (addRun w) b = .ok c →
            treesFrame c = treesFrame b := by
          intro l
          induction l with
          | nil => intro b c h; rw [← Except.ok.inj h]
          | cons x l ih =>
            intro b c h
            rw [List.foldlM_cons] at h
            cases hx : addRun w b x with
            | error m => rw [hx] at h; exact nomatch h
            | ok d => rw [hx] at h; exact (ih d c h).trans (addRun_frame w b d x hx)
        exact key _ _ _ h1
      exact hR.1 ⟨T, h1, fT⟩
  · intro h1
    obtain ⟨T, hT, fT⟩ := hR.2 h1
    rw [hT]
    exact ⟨_, rfl, fT, rfl⟩

/-- What one adding leaves and turns, beside the sums. -/
structure Added (F G : Fork) : Prop where
  frame : treesFrame G.trees = treesFrame F.trees
  ns : G.ns = F.ns
  door : G.doorShutF = F.doorShutF
  drawn : G.thetaDrawnF = F.thetaDrawnF
  plan : G.planClaimsF = F.planClaimsF
  count : G.nClaim = F.nClaim + 1
  marks : G.kapMapF = F.kapMapF.set! F.nClaim true

/-- The next number is handed out just where the ledger can take one claim more. -/
theorem weightNext_iff (F : Fork) :
    (∃ x, weightNext F = .ok x) ↔ addReady F 1 = true := by
  unfold weightNext addReady
  cases F.doorShutF <;> cases F.thetaDrawnF <;>
    cases h3 : decide (F.nClaim < F.planClaimsF) <;>
    cases h4 : (F.kapMapF.size == F.planClaimsF) <;>
    cases h5 : F.kapMapF.getD F.nClaim true <;>
    simp_all [VerifiableInference.Desc.K9.need, bind, Except.bind, pure, Except.pure, List.range_succ]

theorem weightNext_is (F : Fork) (x : E × Fork) (h : weightNext F = .ok x) :
    x.2 = { F with kapMapF := F.kapMapF.set! F.nClaim true, nClaim := F.nClaim + 1 } :=
  congrArg (·.2) (VerifiableInference.Desc.K9L.weightNext_ok F x h).2.2.2.2.2

theorem all_congr {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a, p a = q a) :
    l.all p = l.all q := by
  have : p = q := funext h
  rw [this]

/-- **One claim, the one way**: where the ledger can take one more and the claim fits, it is added. -/
theorem addOne_yes (F : Fork) (cl : Claim) (hr : addReady F 1 = true)
    (hf : claimFits F.trees F.ns cl = true) : ∃ G, addOne F cl = .ok G ∧ Added F G := by
  unfold claimFits at hf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hf
  obtain ⟨x, hx⟩ := (weightNext_iff F).2 hr
  have ex := weightNext_is F x hx
  have t1 : x.2.trees = F.trees := by rw [ex]
  have t2 : x.2.ns = F.ns := by rw [ex]
  obtain ⟨H, hH, fH, eH⟩ := (addForm_iff x.2 ((cl.eqFirst.map fun first =>
    powE F.theta (F.planClaimsF + first)).getD x.1) cl.form).2 (by rw [t1, t2]; exact hf.1)
  have hruns : cl.runs.toList.all (runFitsRow H.trees) = true := by
    rw [all_congr _ _ _ (runFitsRow_congr H.trees F.trees (by rw [fH, t1]))]
    exact hf.2
  obtain ⟨G, hG, fG, eG⟩ := (addRuns_iff H ((cl.eqFirst.map fun first =>
    powE F.theta (F.planClaimsF + first)).getD x.1) cl.runs).2 hruns
  refine ⟨G, ?_, ?_⟩
  · unfold addOne
    simp only []
    rw [hx]
    simp only [bind, Except.bind, hH]
    exact hG
  · exact ⟨by rw [fG, fH, t1], by rw [eG, eH, ex], by rw [eG, eH, ex], by rw [eG, eH, ex],
      by rw [eG, eH, ex], by rw [eG, eH, ex], by rw [eG, eH, ex]⟩

/-- **One claim, the other way.** -/
theorem addOne_only (F G : Fork) (cl : Claim) (h : addOne F cl = .ok G) :
    addReady F 1 = true ∧ claimFits F.trees F.ns cl = true ∧ Added F G := by
  have h0 := h
  unfold addOne at h
  simp only [] at h
  cases hx : weightNext F with
  | error m => rw [hx] at h; exact nomatch h
  | ok x =>
    rw [hx] at h
    have hr := (weightNext_iff F).1 ⟨x, hx⟩
    have ex := weightNext_is F x hx
    have t1 : x.2.trees = F.trees := by rw [ex]
    have t2 : x.2.ns = F.ns := by rw [ex]
    cases hf : addForm x.2 ((cl.eqFirst.map fun first =>
        powE F.theta (F.planClaimsF + first)).getD x.1) cl.form with
    | error m => simp only [bind, Except.bind, hf] at h; exact nomatch h
    | ok H =>
      simp only [bind, Except.bind, hf] at h
      have a1 := (addForm_iff x.2 _ cl.form).1 ⟨H, hf⟩
      obtain ⟨H', hH', fH, _⟩ := (addForm_iff x.2 ((cl.eqFirst.map fun first =>
        powE F.theta (F.planClaimsF + first)).getD x.1) cl.form).2 a1
      have eH : H' = H := Except.ok.inj (hH'.symm.trans hf)
      rw [eH] at fH
      have a2 := (addRuns_iff H _ cl.runs).1 ⟨G, h⟩
      have hfit : claimFits F.trees F.ns cl = true := by
        unfold claimFits
        rw [Bool.and_eq_true, Bool.and_eq_true]
        rw [t1, t2] at a1
        refine ⟨a1, ?_⟩
        rw [all_congr _ _ _ (runFitsRow_congr F.trees H.trees (by rw [fH, t1]))]
        exact a2
      obtain ⟨G', hG', hA⟩ := addOne_yes F cl hr hfit
      have eG : G' = G := Except.ok.inj (hG'.symm.trans h0)
      rw [eG] at hA
      exact ⟨hr, hfit, hA⟩

/-- Behind one adding the ledger can take k more just if it could take k + 1. -/
theorem ready_succ (F G : Fork) (hA : Added F G) (k : Nat) :
    addReady F (k + 1) = true ↔ (addReady F 1 = true ∧ addReady G k = true) := by
  have hm : ∀ i, G.kapMapF.getD (G.nClaim + i) true = F.kapMapF.getD (F.nClaim + (i + 1)) true := by
    intro i
    rw [hA.marks, hA.count]
    have hne : F.nClaim ≠ F.nClaim + 1 + i := by omega
    simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne hne]
    congr 2
    omega
  have hs : G.kapMapF.size = F.kapMapF.size := by
    rw [hA.marks]; simp
  unfold addReady
  simp only [hA.door, hA.drawn, hA.plan, hA.count, hs, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨⟨⟨⟨⟨h1, h2⟩, by omega⟩, h4⟩, fun i hi => h5 i (by omega)⟩,
      ⟨⟨⟨⟨h1, h2⟩, by omega⟩, h4⟩, fun i hi => ?_⟩⟩
    have := hm i
    rw [hA.count] at this
    rw [this]
    exact h5 (i + 1) (by omega)
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, _⟩, h4⟩, h5⟩, ⟨⟨_, h3⟩, _⟩, h6⟩
    refine ⟨⟨⟨⟨h1, h2⟩, by omega⟩, h4⟩, fun i hi => ?_⟩
    cases i with
    | zero => exact h5 0 (by omega)
    | succ j =>
      have := hm j
      rw [hA.count] at this
      rw [← this]
      exact h6 j (by omega)

theorem fits_congr (F G : Fork) (hA : Added F G) (cl : Claim) :
    claimFits G.trees G.ns cl = claimFits F.trees F.ns cl := by
  unfold claimFits
  rw [hA.ns, all_congr _ _ _ (entryThere_congr G.trees F.trees hA.frame),
    all_congr _ _ _ (runFitsRow_congr G.trees F.trees hA.frame)]

/-- What the adding of k claims leaves and turns, beside the sums and the marks. -/
structure AddedAll (F G : Fork) (k : Nat) : Prop where
  frame : treesFrame G.trees = treesFrame F.trees
  ns : G.ns = F.ns
  door : G.doorShutF = F.doorShutF
  drawn : G.thetaDrawnF = F.thetaDrawnF
  plan : G.planClaimsF = F.planClaimsF
  count : G.nClaim = F.nClaim + k

/-- **The adding returns**: where the ledger can take as many claims as there are, and each fits. -/
theorem addList_yes : ∀ (cls : List Claim) (F : Fork), addReady F cls.length = true →
    cls.all (claimFits F.trees F.ns) = true → ∃ G, addList F cls = .ok G ∧ AddedAll F G cls.length
  | [], F, _, _ => ⟨F, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cl :: l, F, hr, hf => by
    rw [List.all_cons, Bool.and_eq_true] at hf
    have h1 : addReady F 1 = true := by
      unfold addReady at hr ⊢
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
        List.length_cons] at hr ⊢
      obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := hr
      exact ⟨⟨⟨⟨a, b⟩, by omega⟩, d⟩, fun i hi => e i (by omega)⟩
    obtain ⟨H, hH, hA⟩ := addOne_yes F cl h1 hf.1
    have h2 := ((ready_succ F H hA l.length).1 hr).2
    have h3 : l.all (claimFits H.trees H.ns) = true := by
      rw [all_congr _ _ _ (fits_congr F H hA)]
      exact hf.2
    obtain ⟨G, hG, hB⟩ := addList_yes l H h2 h3
    refine ⟨G, ?_, ?_⟩
    · unfold addList
      rw [List.foldlM_cons, hH]
      exact hG
    · exact ⟨hB.frame.trans hA.frame, hB.ns.trans hA.ns, hB.door.trans hA.door,
        hB.drawn.trans hA.drawn, hB.plan.trans hA.plan, by
          rw [hB.count, hA.count, List.length_cons]; omega⟩

/-- **And the other way round**: where it returns, every claim fitted; and, if there was a claim, the
ledger could take them all. -/
theorem addList_only : ∀ (cls : List Claim) (F G : Fork), addList F cls = .ok G →
    cls.all (claimFits F.trees F.ns) = true ∧ (cls ≠ [] → addReady F cls.length = true)
  | [], _, _, _ => ⟨rfl, fun h => absurd rfl h⟩
  | cl :: l, F, G, h => by
    unfold addList at h
    rw [List.foldlM_cons] at h
    cases hH : addOne F cl with
    | error m => rw [hH] at h; exact nomatch h
    | ok H =>
      rw [hH] at h
      obtain ⟨h1, h2, hA⟩ := addOne_only F H cl hH
      obtain ⟨h3, h4⟩ := addList_only l H G h
      refine ⟨?_, fun _ => ?_⟩
      · rw [List.all_cons, Bool.and_eq_true]
        refine ⟨h2, ?_⟩
        rw [← all_congr _ _ _ (fits_congr F H hA)]
        exact h3
      · rw [List.length_cons]
        refine (ready_succ F H hA l.length).2 ⟨h1, ?_⟩
        cases l with
        | nil =>
          unfold addReady at h1 ⊢
          simp only [hA.door, hA.drawn, hA.plan, hA.count, Bool.and_eq_true, List.all_eq_true,
            List.mem_range, decide_eq_true_eq, List.length_nil] at h1 ⊢
          obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, _⟩ := h1
          have hs : H.kapMapF.size = F.kapMapF.size := by rw [hA.marks]; simp
          exact ⟨⟨⟨⟨a, b⟩, by omega⟩, by rw [hs]; exact d⟩, fun i hi => absurd hi (by omega)⟩
        | cons c l' => exact h4 (by simp)

end VerifiableInference.Desc.K9H

#print axioms VerifiableInference.Desc.K9H.entryThere_congr
#print axioms VerifiableInference.Desc.K9H.runFitsRow_congr
#print axioms VerifiableInference.Desc.K9H.fold_iff
#print axioms VerifiableInference.Desc.K9H.addForm_iff
#print axioms VerifiableInference.Desc.K9H.addRuns_iff
#print axioms VerifiableInference.Desc.K9H.weightNext_iff
#print axioms VerifiableInference.Desc.K9H.addOne_yes
#print axioms VerifiableInference.Desc.K9H.addOne_only
#print axioms VerifiableInference.Desc.K9H.ready_succ
#print axioms VerifiableInference.Desc.K9H.addList_yes
#print axioms VerifiableInference.Desc.K9H.addList_only
