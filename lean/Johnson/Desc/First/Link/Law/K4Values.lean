-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K4Values.lean: THE VALUES OF THE CLAIMS OF THE LAYERS' KIND (K4), RUNS
«front» AND «back», READ AT ANY LATER LEDGER, ARE NAMED BY WHAT WAS HEARD, THE LEDGER IN FRONT OF
THE BATCHING's DRAW AND THE PROVER's DATA. Theorems, at the ledger.

Why. The batching kind's law asks of every run of claims that its claims' values, read at any later
full state, are functions of what was fixed before the draw and of the data. K4's two runs are
called behind the draw, and they write: each lays the hiding coefficients of a sumcheck (shown 0,
factor −1) under a window of slots that were free, and marks claims as added
(OnBytes/Desc/First/K4/Plain.lean: `formsFrontWith`, `formsBack`). This file shows that the values
do not feel it.

What is said.
  `refWorld ρ U wins ent y`: the world that the ledger U in front of the draw names: under a slot of
    a window the mask row's entry; under another slot what U holds; the entries of virtual rows as
    given. `laid_of_run`: a run of hiding coefficients lays its window, and it stays laid.
    `value_ref`, `values_ref`: a form each of whose slots lies in a laid window or is filled in U
    has, at a later ledger, its value in that world.
  `backForms o`: the forms of «back»: a function of what was heard alone (`formsBack_some`,
    OnBytes/Desc/First/K4/ClaimsLaws.lean). `back_values`: **where `formsBack o F = some (fs, G)`, U
    earlier than F, B later than G: the values of fs as plain claims at B are those of `backForms o`
    in the world that U names.**
  `frontForms rows P g o U`: the forms of «front»: a function of what was heard and of what U shows
    under the slots of the row products' end values. `shown_later`, `front_forms`: the run's own
    forms are these, if these slots are filled in U. `front_values`: **the like for «front»**, with
    its two windows.

Limits. (1) AT THE LEDGER: the step to the carried record and to the batching kind's premise on a
run (its letters: the lens, «goes on from q», «full») is not here. (2) THREE PREMISES ARE LEFT TO
THE KIND's OWN FILES AND ARE SHOWN OF NOTHING HERE: hs: every slot that a form names lies in the
run's own window or is filled in front of the draw; hsh: the end values' slots are filled there; he:
at a full later state the entries of virtual rows that the forms name are a given function (of what
was heard and the data). (3) `Sized F` is asked. (4) No member; no tooth. Nothing on soundness.

-/
import OnBytes.Desc.First.K4.ClaimsLaws
import Johnson.Desc.First.Link.Law.ValueLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K4Values
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc
open OnBytes.Desc.First.K4
open OnBytes.PscRun (Later Filled Sized hideRun_ok hideRun_keeps paid_later)
open VerifiableInference.Desc.K9L (claimValue worldAt Bound)
open VerifiableInference.Desc.ValueLater

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## 1 A world named by the ledger in front of the draw -/

/-- The slot j lies in the window w = (first, length). -/
def InWin (w : ℕ × ℕ) (j : ℕ) : Prop := w.1 ≤ j ∧ j < w.1 + w.2

instance (w : ℕ × ℕ) (j : ℕ) : Decidable (InWin w j) := inferInstanceAs (Decidable (_ ∧ _))

/-- The window of a sumcheck's hiding coefficients. -/
def winOf (p : Psc) : ℕ × ℕ := (p.first, p.walk.1.length)

/-- **The world that the ledger U in front of the draw names**: under a slot of one of the windows
the mask row's entry (what stands there once the run has laid shown 0, factor -1); under another
slot what U holds; the entries of virtual rows as given. -/
def refWorld (U : Fork) (wins : List (ℕ × ℕ)) (ent : ℕ → ℕ → ℕ → K) (y : Bound K) : World K where
  slot := fun j => if ∃ w ∈ wins, InWin w j then y.mask j
    else ρ.val (U.vp.getD j zeroE) - ρ.val (U.mf.getD j zeroE) * y.mask j
  entry := ent

/-- The ledger B holds (shown 0, factor -1) under the slots of the window w. -/
def LaidAt (B : Fork) (w : ℕ × ℕ) : Prop :=
  ∀ j, InWin w j → B.vp.getD j zeroE = zeroE ∧ B.mf.getD j zeroE = subE zeroE oneE

/-- A run of hiding coefficients lays its window, and it stays laid. -/
theorem laid_of_run {F G B : Fork} {first n : ℕ} (hF : Sized F)
    (h : F.hideRun first (Array.replicate n zeroE) (subE zeroE oneE) = some G) (hB : Later G B) :
    LaidAt B (first, n) := by
  intro j hj
  obtain ⟨_, _, hin, _⟩ := hideRun_ok F G first _ _ hF h
  obtain ⟨i, rfl⟩ : ∃ i, j = first + i := ⟨j - first, by have := hj.1; simp only at this; omega⟩
  have hi : i < n := by have := hj.2; simp only at this; omega
  obtain ⟨_, _, hfill, h1, h2⟩ := hin i (by simpa using hi)
  obtain ⟨_, k1, k2⟩ := hB.keep _ hfill
  refine ⟨k1.trans (h1.trans ?_), k2.trans h2⟩
  simp [Array.getD_eq_getD_getElem?, hi]

/-- **A form's value at a later ledger is its value in the world that U names**, if each slot that
it names lies in a window that is laid in B, or is filled in U; and its entries are as given. -/
theorem value_ref (f : Aff) (L : LinkCtx) (U B : Fork) (wins : List (ℕ × ℕ))
    (ent : ℕ → ℕ → ℕ → K) (y : Bound K) (hU : Later U B) (hw : ∀ w ∈ wins, LaidAt B w)
    (hs : ∀ x ∈ f.slots.toList, (∃ w ∈ wins, InWin w x.1) ∨ Filled U x.1)
    (he : ∀ x ∈ f.ents.toList, (worldAt ρ L B y).entry x.tree x.row x.idx =
      ent x.tree x.row x.idx) :
    f.value ρ (worldAt ρ L B y) = f.value ρ (refWorld ρ U wins ent y) := by
  refine value_on ρ f _ _ (fun x hx => ?_) he
  show _ = if ∃ w ∈ wins, InWin w x.1 then y.mask x.1
    else ρ.val (U.vp.getD x.1 zeroE) - ρ.val (U.mf.getD x.1 zeroE) * y.mask x.1
  by_cases hin : ∃ w ∈ wins, InWin w x.1
  · rw [if_pos hin]
    obtain ⟨w, hw', hj⟩ := hin
    obtain ⟨h1, h2⟩ := hw w hw' x.1 hj
    exact slot_laid ρ L B y x.1 h1 h2
  · rw [if_neg hin]
    exact slot_later ρ L L U B y hU x.1 ((hs x hx).resolve_left hin)

/-- The like of a list of forms, as plain claims. -/
theorem values_ref (fs : List Aff) (L : LinkCtx) (U B : Fork) (wins : List (ℕ × ℕ))
    (ent : ℕ → ℕ → ℕ → K) (y : Bound K) (hU : Later U B) (hw : ∀ w ∈ wins, LaidAt B w)
    (hs : ∀ f ∈ fs, ∀ x ∈ f.slots.toList, (∃ w ∈ wins, InWin w x.1) ∨ Filled U x.1)
    (he : ∀ f ∈ fs, ∀ x ∈ f.ents.toList, (worldAt ρ L B y).entry x.tree x.row x.idx =
      ent x.tree x.row x.idx) :
    (fs.map fun f => ({ form := f } : Claim)).map (claimValue ρ (worldAt ρ L B y)) =
      fs.map fun f => f.value ρ (refWorld ρ U wins ent y) := by
  rw [List.map_map]
  refine List.map_congr_left fun f hf => ?_
  show claimValue ρ _ { form := f } = _
  rw [claim_plain, value_ref ρ f L U B wins ent y hU hw (hs f hf) (he f hf)]

/-! ## 2 What is shown under a filled slot stays -/

theorem shown_later {U F : Fork} (h : Later U F) (j : ℕ) (hj : Filled U j) :
    F.shown j = U.shown j := by
  obtain ⟨h1, h2, _⟩ := h.keep j hj
  have e1 : F.gotF.getD j false = true := h1
  have e2 : U.gotF.getD j false = true := hj
  unfold Fork.shown
  rw [h.ns, e1, e2, h2]

theorem mapM_congr_list {α β : Type} {f g : α → Option β} : ∀ (l : List α),
    (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a List.mem_cons_self,
      mapM_congr_list l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem mapM_congr_array {α β : Type} {f g : α → Option β} (xs : Array α)
    (h : ∀ a ∈ xs.toList, f a = g a) : xs.mapM f = xs.mapM g := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, mapM_congr_list _ h]

/-! ## 3 K4's run "back" -/

/-- The forms of the run "back": a function of what was heard alone. -/
def backForms (o : Own) : List Aff := back o (o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {})

/-- **THE VALUES OF THE RUN "back", READ AT ANY LATER LEDGER, ARE NAMED BY WHAT WAS HEARD, THE
LEDGER IN FRONT OF THE DRAW AND THE DATA.** U: the ledger in front of the draw. F: the ledger at
which the run is called. G: the one that it hands on. B: any later one. -/
theorem back_values {o : Own} {U F G B : Fork} {fs : Array Aff} (L : LinkCtx)
    (ent : ℕ → ℕ → ℕ → K) (y : Bound K) (h : formsBack o F = some (fs, G)) (hF : Sized F)
    (hU : Later U F) (hB : Later G B)
    (hs : ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
      InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled U x.1)
    (he : ∀ f ∈ backForms o, ∀ x ∈ f.ents.toList,
      (worldAt ρ L B y).entry x.tree x.row x.idx = ent x.tree x.row x.idx) :
    (fs.toList.map fun f => ({ form := f } : Claim)).map (claimValue ρ (worldAt ρ L B y)) =
      (backForms o).map fun f => f.value ρ (refWorld ρ U [winOf o.wo.toWsMerged.p] ent y) := by
  obtain ⟨F1, rfl, h1, rfl⟩ := formsBack_some h
  have hB1 : Later F1 B := (paid_later F1 _).trans hB
  rw [List.toList_toArray]
  exact values_ref ρ _ L U B _ ent y (hU.trans ((hideRun_keeps h1).trans hB1))
    (fun w hw => by
      obtain rfl := List.mem_singleton.1 hw
      exact laid_of_run hF h1 hB1)
    (fun f hf x hx => (hs f hf x hx).imp (fun k => ⟨_, List.mem_singleton.2 rfl, k⟩) id) he

/-! ## 4 K4's run "front" -/

/-- The forms of the run "front": a function of what was heard and of what the ledger U shows under
the slots of the row products' end values. -/
def frontForms (rows : Bool) (P : Pub) (g : ℕ) (o : Own) (U : Fork) : Option (List Aff) := do
  let sh ← (Array.range (4 * P.y.NI)).mapM fun i => U.shown (o.H.tV.sEnd + i)
  let pp ← planesParts o.v o.H.fo
  front rows P g o (o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {}) (o.H.fo.leaves.rowForm oneE pp.1)

/-- **The run's forms are those that the ledger in front of the draw names**, if the end values'
slots are filled there. -/
theorem front_forms {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {U F G : Fork} {fs : Array Aff}
    (h : formsFrontWith rows P g o F = some (fs, G)) (hU : Later U F)
    (hsh : ∀ i, i < 4 * P.y.NI → Filled U (o.H.tV.sEnd + i)) :
    frontForms rows P g o U = some fs.toList := by
  obtain ⟨sh, pp, l, F1, F2, a1, a2, a3, rfl, -, -, -⟩ := formsFrontWith_some h
  have e : ((Array.range (4 * P.y.NI)).mapM fun i => U.shown (o.H.tV.sEnd + i)) = some sh := by
    rw [← a1]
    refine mapM_congr_array _ fun i hi => (shown_later hU _ (hsh i ?_)).symm
    simpa using hi
  unfold frontForms
  rw [e, a2]
  exact a3

/-- The two windows of the run "front". -/
def frontWins (o : Own) : List (ℕ × ℕ) := [winOf o.H.tV.p, winOf o.H.fo.leaves]

/-- **THE VALUES OF THE RUN "front", READ AT ANY LATER LEDGER, ARE NAMED BY WHAT WAS HEARD, THE
LEDGER IN FRONT OF THE DRAW AND THE DATA.** -/
theorem front_values {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {U F G B : Fork} {fs : Array Aff}
    (L : LinkCtx) (ent : ℕ → ℕ → ℕ → K) (y : Bound K)
    (h : formsFrontWith rows P g o F = some (fs, G)) (hF : Sized F) (hU : Later U F)
    (hB : Later G B) (hsh : ∀ i, i < 4 * P.y.NI → Filled U (o.H.tV.sEnd + i))
    (hs : ∀ l, frontForms rows P g o U = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
      (∃ w ∈ frontWins o, InWin w x.1) ∨ Filled U x.1)
    (he : ∀ l, frontForms rows P g o U = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt ρ L B y).entry x.tree x.row x.idx = ent x.tree x.row x.idx) :
    ∃ l, frontForms rows P g o U = some l ∧
      (fs.toList.map fun f => ({ form := f } : Claim)).map (claimValue ρ (worldAt ρ L B y)) =
        l.map fun f => f.value ρ (refWorld ρ U (frontWins o) ent y) := by
  have hl := front_forms h hU hsh
  obtain ⟨sh, pp, l, F1, F2, -, -, -, -, h1, h2, rfl⟩ := formsFrontWith_some h
  have hF1 : Sized F1 := (hideRun_ok F F1 _ _ _ hF h1).2.1
  have hG : Later F2
      ((if rows then F2.paid o.H.fo.owedObjects else F2).paid o.H.fo.owedPlanes) := by
    cases rows
    · exact paid_later _ _
    · exact (paid_later _ _).trans (paid_later _ _)
  have hB2 : Later F2 B := hG.trans hB
  have hB1 : Later F1 B := (hideRun_keeps h2).trans hB2
  refine ⟨_, hl, values_ref ρ _ L U B _ ent y (hU.trans ((hideRun_keeps h1).trans hB1))
    (fun w hw => ?_) (hs _ hl) (he _ hl)⟩
  simp only [frontWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact laid_of_run hF h1 hB1
  · exact laid_of_run hF1 h2 hB2

end VerifiableInference.Desc.K4Values

#print axioms VerifiableInference.Desc.K4Values.laid_of_run
#print axioms VerifiableInference.Desc.K4Values.value_ref
#print axioms VerifiableInference.Desc.K4Values.values_ref
#print axioms VerifiableInference.Desc.K4Values.shown_later
#print axioms VerifiableInference.Desc.K4Values.mapM_congr_list
#print axioms VerifiableInference.Desc.K4Values.mapM_congr_array
#print axioms VerifiableInference.Desc.K4Values.back_values
#print axioms VerifiableInference.Desc.K4Values.front_forms
#print axioms VerifiableInference.Desc.K4Values.front_values
