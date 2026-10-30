-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/WalkShape.lean: kind K5: A SECOND RELATION THAT RIDES FROM THE KIND's HEARING TO THE SEGMENT's BATCHING, beside CarK5 (Claims/WalkK5.lean: the ledger only grows; what the
kind heard stands): WHAT THE LOOKUP ON THE CALLS RETURNED STAYS, AND EVERY ARRAY OF THE LEDGER KEEPS ITS SHAPE (R rows, K columns).

Why. That the kind's runs give ONE answer at every record between (Claims/InAtOne.lean; a reader that "is the run itself") also wants: the key points that the runs read (off what the lookup
returned), the width of the array of the reads, and "that array has one own row". CarK5 carries none of the three.

Main names:
  shapes? s: the list of the open ledger's arrays' (R, K). Kept5 s s' := s'.look? = s.look? ∧ shapes? s' = shapes? s (S.look?: Johnson/Desc/First/State.lean: at an attention segment: a.g).
  kept5_pre · kept5_same · kept5_putFork.
  WHO KEEPS (Block.Steps Kept5): commitAtS_keeps | laterAt_keeps (kind K1's later moment; over Johnson/Desc/K1/KeepsShapes.lean) · readsAtO_keeps · piece4_keeps · k8_keeps · quietDigits_keeps ·
    seated7_keeps · behind_k5_keep: the four seated blocks behind K5's, THE LOOKUP's OWN BLOCK ON THE DIGITS UNDER A NAMED PREMISE.
  WHAT IT GIVES: tree_of_shapes: at every array's number the two ledgers have one (R, K), or both have no array.
IS IT EMPTY HERE? Implications on yeses. The named premise on the lookup's block is shown of no block.
Limits. look_putFork's sentence also stands in another kind's law file (Johnson/Desc/Kinds/Law/RowPins.lean, under that kind's own namespace): a twin by content; that file's imports are a
  whole kind's law: not imported for five lines. Its home would be beside Johnson/Desc/First/StateLedger.lean's laws.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K1.KeepsShapes
import Johnson.Desc.First.Att.Claims.WalkSeat
import Johnson.Desc.First.Att.Claims.WalkDigits

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn Block Pre roundlessBlock stepsAndThen)
open VerifiableInference.Desc.First (K8.atS K8.approximateRangeProofDrawKind K8.Par)
open VerifiableInference.Desc.First.Att

/-- The open ledger's arrays' shapes. -/
def shapes? (s : First.S) : Option (Array (ℕ × ℕ)) := s.fork?.map fun F => F.trees.map fun T => (T.R, T.K)

/-- What the lookup on the calls returned stays; every array keeps its shape. -/
abbrev Kept5 (s s' : First.S) : Prop := s'.look? = s.look? ∧ shapes? s' = shapes? s

theorem kept5_pre : Pre Kept5 :=
  ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ _ h₁ h₂ => ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩⟩

theorem look_of_here (s s' : First.S) (h : s'.here = s.here) : s'.look? = s.look? := by
  unfold First.S.look?
  rw [h]

theorem look_putFork (s : First.S) (F : Fork) : (s.putFork F).look? = s.look? := by
  unfold First.S.look? First.S.putFork
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [ho, hh]
  | _ => simp [hh]

theorem look_putTl (s : First.S) (tl : HTailF2) : (s.putTl tl).look? = s.look? := by
  unfold First.S.look? First.S.putTl
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [ho, hh]
  | _ => simp [hh]

theorem look_putLink (s : First.S) (L : LinkCtx) : (s.putLink L).look? = s.look? := by
  unfold First.S.look? First.S.putLink
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [ho, hh]
  | _ => simp [hh]

theorem kept5_same (s s' : First.S) (hf : s'.fork? = s.fork?) (hl : s'.look? = s.look?) : Kept5 s s' :=
  ⟨hl, by unfold shapes?; rw [hf]⟩

/-- putFork G keeps where a ledger is open and G has its arrays' shapes. -/
theorem kept5_putFork (s : First.S) (F G : Fork) (hF : s.fork? = some F)
    (h : VerifiableInference.Desc.K1.ShapesSame F G) : Kept5 s (s.putFork G) :=
  ⟨look_putFork s G, by
    unfold shapes?
    rw [First.S.fork_putFork s F G hF, hF]
    exact congrArg some h⟩

/-! ### who keeps -/

theorem commitAtS_keeps {Cl : Type} (P₁ : VerifiableInference.Desc.K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) :
    (VerifiableInference.Desc.K1.commitAtS (Cl := Cl) P₁ link moment arrays).Steps Kept5 := by
  intro s rs gs s' h
  obtain ⟨L, F, tl, y, _, hF, _, rfl, hs⟩ := VerifiableInference.Desc.K1.commitAtS_shapes h
  have ef : ((VerifiableInference.Desc.K1.laid s y.w).putLink y.L).fork? = s.fork? :=
    (First.S.fork_putLink _ _).trans (First.S.fork_of_here _ _ rfl)
  have m : Kept5 s ((VerifiableInference.Desc.K1.laid s y.w).putLink y.L) :=
    kept5_same _ _ ef ((look_putLink _ _).trans (look_of_here _ _ rfl))
  exact kept5_pre.trans _ _ _ m (kept5_putFork _ F _ (ef.trans hF) hs)

theorem laterAt_keeps {Cl : Type} (q : Params.First) (gp : Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    (VerifiableInference.Desc.K1.laterAt (Cl := Cl) q gp link piece moment arrays).Steps Kept5 :=
  commitAtS_keeps _ _ _ _

theorem readsAtSO_keeps {A : Attention.Plan} {s s' : First.S} (h : readsAtSO A s = .ok s') : Kept5 s s' := by
  obtain ⟨a, _, _, _, _, _, he, _, _, _, _, _, rfl⟩ := reads_next_o A s s' h
  refine kept5_same _ _ ?_ ?_
  · unfold First.S.fork?
    rw [he]
  · unfold First.S.look?
    rw [he]

theorem readsAtO_keeps {Cl : Type} (W : Verify.Public) (l g : ℕ) (b : Block First.S Cl)
    (hb : readsAtO W l g = some b) : b.Steps Kept5 := by
  unfold readsAtO at hb
  obtain ⟨A, _, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact fun s _ _ s' h => readsAtSO_keeps h

theorem piece4_keeps {Cl : Type} (q : Params.First) (gp : Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) (name : String) (W : Verify.Public) (l g : ℕ) (z : Block First.S Cl)
    (hz : readsAtO W l g = some z) :
    ((VerifiableInference.Desc.K1.laterAt (Cl := Cl) q gp link piece moment arrays).andThen name z).Steps Kept5 :=
  stepsAndThen kept5_pre name _ _ (laterAt_keeps q gp link piece moment arrays) (readsAtO_keeps W l g z hz)

theorem k8_lay_keeps (s : First.S) (m : _) (first : _) (s' : First.S)
    (h : K8.atS.lay s m first = .ok s') : Kept5 s s' := by
  simp only [K8.atS] at h
  split at h
  · injection h with h
    subst h
    exact kept5_same _ _ (First.S.fork_putTl _ _) (look_putTl _ _)
  · cases h

theorem k8_keeps {Cl : Type} (p : K8.Par) : (K8.approximateRangeProofDrawKind (Cl := Cl) K8.atS p).Steps Kept5 :=
  (Meaning.K2.k8_whole Kept5 K8.atS k8_lay_keeps p).1

theorem quietDigits_keeps (used claims : ℕ) {s t : First.S}
    (h : VerifiableInference.Desc.K3.quietDigits used claims s = .ok t) : Kept5 s t := by
  obtain ⟨F, hF, _, rfl⟩ := VerifiableInference.Desc.K3.quietDigits_ok used claims s t h
  exact kept5_putFork s F _ hF rfl

theorem seated7_keeps {Cl : Type} (b : Block First.S Cl) (hb : b.Steps Kept5) (name name' : String) (link : Option ℕ)
    (piece used claims : ℕ) :
    (b.andThen name (roundlessBlock name' 1 link piece
      (VerifiableInference.Desc.K3.quietDigits used claims))).Steps Kept5 :=
  stepsAndThen kept5_pre name _ _ hb fun _ _ _ _ h => quietDigits_keeps used claims h

/-- **The four blocks behind K5's.** -/
theorem behind_k5_keep {Cl : Type} (q₄ q₆ : Params.First) (gp : Desc.Plain.GPar) (link : ℕ)
    (reads digits : Option (List ℕ)) (name : String) (W : Verify.Public) (g : ℕ) (z : Block First.S Cl)
    (hz : readsAtO W link g = some z) (p₈ : K8.Par) (b₇ : Block First.S Cl) (hK3 : b₇.Steps Kept5) :
    ∀ x ∈ [(VerifiableInference.Desc.K1.laterAt (Cl := Cl) q₄ gp link 4 1 reads).andThen name z,
        K8.approximateRangeProofDrawKind (Cl := Cl) K8.atS p₈, VerifiableInference.Desc.K1.laterAt (Cl := Cl) q₆ gp link 6 2 digits,
        b₇], x.Steps Kept5 := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact piece4_keeps _ _ _ _ _ _ _ _ _ _ _ hz
  · exact k8_keeps _
  · exact laterAt_keeps _ _ _ _ _ _
  · exact hK3

/-! ### what it gives -/

/-- At every array's number the two ledgers have one shape, or both have no array. -/
theorem tree_of_shapes {s s' : First.S} {F F' : Fork} (h : shapes? s' = shapes? s) (hF : s.fork? = some F)
    (hF' : s'.fork? = some F') (t : ℕ) :
    (F'.trees[t]?).map (fun T => (T.R, T.K)) = (F.trees[t]?).map fun T => (T.R, T.K) := by
  unfold shapes? at h
  rw [hF, hF'] at h
  have e := Option.some.inj h
  have := congrArg (fun a => a[t]?) e
  simpa [Array.getElem?_map] using this

end K5Law

#print axioms K5Law.kept5_pre
#print axioms K5Law.commitAtS_keeps
#print axioms K5Law.behind_k5_keep
#print axioms K5Law.tree_of_shapes
