-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/WholeLaws.lean: first laws of the reduction of a whole file
(OnBytes/Maker/Whole.lean), each by unfolding or by one law of the library.

  `chainsOf_laws`, `chainsOf_seams`: the rounds of the file meet Compile/Joined/Types.lean's two
    lists of conditions on rounds: the joining round is shared and its annotation's data fit
    together; the front, the joining round and the seam send a plain part alone.
  `length_uLT`, `chainsOf_nJ`, `chainsOf_n3`: the numbers of the joining round and of the seam in
    the whole, as functions of the chains' numbers of rounds.
  `wholeIOR_shape`: the reduction's shape is the shape of these rounds.
  `wholeIOR_tied`: the condition `IOR.Tied` (Ior/Batch.lean) holds, because the field `tie` is
    empty.
  `annOf_coherent`: the annotation's data fit together in every round (`RoundSplits.Coherent`).
  `wholeDesc`: the reduction's own fields, laid into the type of a file's verifier (`Desc`,
    Compile/Joined/Types.lean).
  `wholeIOR_toProto`, `wholeIOR_toBatch`: a fit of TYPES, by unfolding: the reduction's shape is
    `Chains.sh` and its annotation `Chains.ann`, so it has the type that the compiler's side over
    `Chains` takes. They are no agreement with another text: `wholeDesc` is made of the reduction.
  `wholeIOR_out_run`: where the verifier says yes, `run` has said yes at that instance on some three
    views (which views is not said in the statement).
  `wantsOf_noStored`, `wholeIOR_extReads₂`: if the first and the third chain open no stored table,
    the positions read of the stored table hang on the second chain's verifier's messages alone.
  `wholeIOR_out_silent`, `wholeDesc_answers`: a yes of the verifier is a yes of the test `silent`;
    so the verifier has the property `Desc.Answers` if that test compares the answers with the
    instance's.

What is not claimed here. That the verifier is local: OnBytes/Maker/WholeLocal.lean. Nothing on
soundness. OnBytes/Maker/SilentLaws.lean [not in this library] calls `wholeDesc_answers` at the test
`silentOf` (`wholeDesc_answers_silentOf`); nobody calls that law. Nobody calls `wholeIOR_extReads₂`.


-/
import OnBytes.Maker.Whole
import Ior.Batch
import Compile.Joined.Laws

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ Compile.Joined

variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

theorem chainsOf_laws : (chainsOf C D tF tJ t3).Laws := ⟨rfl, RAnn.ofShared_coherent _ _⟩

theorem chainsOf_seams : (chainsOf C D tF tJ t3).Seams :=
  ⟨plainRound_isSeam _ _, plainRound_isSeam _ _, plainRound_isSeam _ _⟩

/-- A chain has a typed round for each round of its data. -/
theorem length_uLT : ∀ ds : List RDT, (uLT C ds).length = ds.length
  | [] => rfl
  | _ :: ds => congrArg (· + 1) (length_uLT ds)

/-- The number of the joining round in the whole: behind the front and the first chain's rounds. -/
theorem chainsOf_nJ : (chainsOf C D tF tJ t3).nJ = D.ds₁.length + 1 :=
  congrArg (· + 1) (length_uLT C D.ds₁)

/-- The number of the seam in the whole. -/
theorem chainsOf_n3 : (chainsOf C D tF tJ t3).n3 = D.ds₁.length + D.ds₂.length + 2 := by
  show (uLT C D.ds₁).length + (uLT C D.ds₂).length + 2 = _
  rw [length_uLT, length_uLT]

variable {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

theorem wholeIOR_shape :
    (reductionOfWholeFile C D tF tJ t3 silent run).shape = (chainsOf C D tF tJ t3).sh := rfl

theorem wholeIOR_tied : (reductionOfWholeFile C D tF tJ t3 silent run).Tied :=
  fun _ _ _ => Finset.empty_subset _

/-- The annotation's data fit together in every round. -/
theorem annOf_coherent : (annOf C D tF tJ t3 silent run).Coherent :=
  (chainsOf C D tF tJ t3).ann_coherent (chainsOf_laws C D tF tJ t3)

/-- The reduction's own fields, in the type of a file's verifier. -/
@[reducible] def wholeDesc : Desc (chainsOf C D tF tJ t3) Xi (oneExternalString (2 ^ D.a) SgX) where
  blinded := (reductionOfWholeFile C D tF tJ t3 silent run).blinded
  extReads := fun _ ρ => (reductionOfWholeFile C D tF tJ t3 silent run).extReads ρ
  reads := fun _ ρ _ => (reductionOfWholeFile C D tF tJ t3 silent run).reads ρ
  accept := fun x y τ => ((reductionOfWholeFile C D tF tJ t3 silent run).out x y τ).isSome

theorem wholeIOR_toProto :
    (reductionOfWholeFile C D tF tJ t3 silent run).toInteractiveOracleProof = (wholeDesc C D tF tJ t3 silent run).proto := rfl

theorem wholeIOR_toBatch :
    (⟨reductionOfWholeFile C D tF tJ t3 silent run, annOf C D tF tJ t3 silent run⟩ :
      BIOP Xi (oneExternalString (2 ^ D.a) SgX)).toBatch =
      (wholeDesc C D tF tJ t3 silent run).batch := rfl

/-- Where the verifier says yes, the test of what the silent rounds send has said yes. -/
theorem wholeIOR_out_silent (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : Tr (chainsOf C D tF tJ t3).sh)
    (h : ((reductionOfWholeFile C D tF tJ t3 silent run).out x y τ).isSome = true) :
    silent x ((chainsOf C D tF tJ t3).msgF τ).2 ((chainsOf C D tF tJ t3).msgJ τ).2
      ((chainsOf C D tF tJ t3).msg3 τ).2 = true := by
  simp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact hc.1.2
  · cases h

/-- Where the verifier says yes, the run has said yes at that instance, on some three views. -/
theorem wholeIOR_out_run (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : Tr (chainsOf C D tF tJ t3).sh)
    (h : ((reductionOfWholeFile C D tF tJ t3 silent run).out x y τ).isSome = true) :
    ∃ v₁ v₂ v₃, run x v₁ v₂ v₃ = true := by
  simp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact ⟨_, _, _, hc.2⟩
  · cases h

/-- A chain that opens no stored table wants no position of the stored table. -/
theorem wantsOf_noStored (dep : ℕ → Option ℕ) : ∀ (ds : List RDT) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = []) → (wantsOf D.a dep ds Rs).filterMap (extPosOf D) = []
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | d :: ds, R :: Rs, h => by
      have hd : d.stored = [] := h d List.mem_cons_self
      have ih := wantsOf_noStored dep ds Rs fun e he => h e (List.mem_cons_of_mem _ he)
      unfold wantsOf
      rw [hd, List.flatMap_nil, List.nil_append, List.filterMap_append, ih, List.append_nil,
        List.filterMap_eq_nil_iff]
      intro w hw
      obtain ⟨j, _, hj⟩ := List.mem_flatMap.1 hw
      cases hb : dep j with
      | none => rw [hb] at hj; cases hj
      | some b =>
          rw [hb] at hj
          obtain ⟨_, _, rfl⟩ := List.mem_map.1 hj
          rfl

/-- **The stored table is read at positions that hang on the second chain's verifier's messages
alone**, if the first and the third chain open no stored table. -/
theorem wholeIOR_extReads₂ (h₁ : ∀ d ∈ D.ds₁, d.stored = []) (h₃ : ∀ d ∈ D.ds₃, d.stored = [])
    (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    (reductionOfWholeFile C D tF tJ t3 silent run).extReads ρ =
      ((wants₂ C D tF tJ t3 ρ).filterMap (extPosOf D)).toFinset := by
  show ((wants₁ C D tF tJ t3 ρ ++ (wants₂ C D tF tJ t3 ρ ++ wants₃ C D tF tJ t3 ρ)).filterMap
    (extPosOf D)).toFinset = _
  rw [List.filterMap_append, List.filterMap_append]
  unfold wants₁ wants₃
  rw [wantsOf_noStored D D.depth D.ds₁ _ h₁, wantsOf_noStored D D.depth D.ds₃ _ h₃, List.nil_append,
    List.append_nil]

/-- **The decision holds the prover to the record's answers** (`Desc.Answers`), if the test of what
the silent rounds send does. -/
theorem wholeDesc_answers {A : Type} (ans : Xi → A) (atF : TF → A) (atJ : TJ → A)
    (h : ∀ x f j t, silent x f j t = true → atF f = ans x ∧ atJ j = ans x) :
    (wholeDesc C D tF tJ t3 silent run).Answers ans atF atJ where
  front := fun x y τ ha => (h x _ _ _ (wholeIOR_out_silent C D tF tJ t3 silent run x y τ ha)).1
  join := fun x y τ ha => (h x _ _ _ (wholeIOR_out_silent C D tF tJ t3 silent run x y τ ha)).2

end OnBytes.Maker
