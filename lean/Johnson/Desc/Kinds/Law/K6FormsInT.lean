-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6FormsInT.lean: THE TABLE OF JOINTS' PUBLIC TEST formsInT
(Johnson/Desc/First/Batch/FormsIn.lean) AT THE OUTPUT HEAD's FOUR RUNS, AT THE BORDER RIGHT BEHIND
THE HEAD's OWN BLOCK, WHERE THE READER IS Law/K6Silent.lean's k6Silent: IT SAYS YES, under named
premises on the plan. And a test with code: that k6Silent answers. Definitions, statements and
proofs.

  Row0 iU3 K3 f    every entry that the form names stands in array iU3, row 0, at a column below K3.
  kept2_row0, kept_row0   it is kept by the forms' arithmetic.
  EntriesRow0      A NAMED PREMISE: below each read's length the seat's entry has Row0.
  claims_row0, keyVector_row0   so have the 35 forms and the six key vectors (by
                   Law/AlikeWorth.lean's walk, which carries the bounds on the indices).
  slotIn_filled    a filled slot of a well laid ledger passes the test on slots.
  k6_formsInT      MAIN: see its docstring.
  (k6SilentB, the test with code that k6Silent answers, lies in Law/K6SilentCode.lean.)

WHAT IT IS NOT. AN IMPLICATION. ASSUMED, BY NAME: EntriesRow0 (other files' to show: the places
lie below the array's width) · hEnt (the table's test on an entry says yes at array iU3, row 0,
below K3: ON THE PLAN AND THE LINK's CONTEXT) · hMask (the mask row's seat is there) · hFree (no
slot of the merge is
laid yet) · K6HeardAt, WellLaid, the lookup's last claim filled and bare (behind the head's yes) ·
K6States · hRd · the tests on the plan · AND THAT k6Silent ANSWERS (hR). k6SilentB has run nowhere.
Nothing on soundness.
LETTERS. No letter stands under "there is". K3: the width: read by EntriesRow0 and hEnt alone.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Silent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff Ent)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Readers readerOf segAt? RunOf)
open Norm (lt ls d lPd T S2)

/-- Every entry that the form names stands in array iU3, row 0, at a column below K3. -/
def Row0 (iU3 K3 : Nat) (f : Form) : Prop :=
  ∀ x ∈ f.ents.toList, x.tree = iU3 ∧ x.row = 0 ∧ x.idx < K3

theorem row0_addMul {iU3 K3 : Nat} {a b : Form} (ha : Row0 iU3 K3 a) (hb : Row0 iU3 K3 b) (k : E) :
    Row0 iU3 K3 (Aff.addMul a b k) := by
  intro x hx
  rw [addMul_ents] at hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
    exact hb z hz

theorem row0_bare {iU3 K3 : Nat} {f : Form} (h : f.ents = #[]) : Row0 iU3 K3 f := by
  intro x hx
  rw [h] at hx
  simp at hx

theorem kept2_row0 (iU3 K3 : Nat) : Kept2 fun _ f' => Row0 iU3 K3 f' :=
  { addMul := fun k ha hb => row0_addMul ha hb k
    bare := fun _ h => row0_bare h }

theorem kept_row0 (iU3 K3 : Nat) : Kept (Row0 iU3 K3) :=
  { addMul := fun k ha hb => row0_addMul ha hb k
    bare := fun _ h _ => row0_bare h }

section Walk

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard]

/-- **Below each read's length the filling's entry stands in row 0 of the reads' array.** -/
structure EntriesRow0 (iU3 K3 : Nat) (N : FinalNorm.Reads) (R : Reads) : Prop where
  norm : ∀ r i, i < readLenN r → Row0 iU3 K3 (N.entry r i)
  wide : ∀ i, i < wideLenN → Row0 iU3 K3 (N.wide i)
  head : ∀ r i, i < readLen r → Row0 iU3 K3 (R.entry r i)

variable {iU3 K3 : Nat} {N : FinalNorm.Reads} {R : Reads}

/-- The 35 forms. -/
theorem claims_row0 (A : EntriesRow0 iU3 K3 N R) (B : HeardBare) (hd : S2 ∣ d) :
    ∀ name fs, (claimsAt N R).lookup name = some fs → ∀ f, f ∈ fs → Row0 iU3 K3 f := by
  intro name fs hl f hf
  obtain ⟨_, _, _, _, h⟩ := alike_claims (kept2_row0 iU3 K3) N N R R A.norm A.head hd
    (heardAlike_of_bare (kept2_row0 iU3 K3) B) (fun S0 => row0_bare (B.lgLeft S0))
    (row0_bare B.lgEnd) name fs hl f hf
  exact h

/-- A call's key vector. -/
theorem keyVector_row0 (A : EntriesRow0 iU3 K3 N R) (B : HeardBare) (hd : S2 ∣ d) (hJ : JVa ≤ JV)
    (padding : E) (keys : List PlaceKey) :
    Row0 iU3 K3 (letI := N; letI := R; keyVector key padding keys) := by
  unfold keyVector
  have step : ∀ (l : List Form) (a : Form), Row0 iU3 K3 a → (∀ f ∈ l, Row0 iU3 K3 f) →
      Row0 iU3 K3 (l.foldl (· + ·) a) := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons x xs ih =>
      intro a ha hl
      exact ih _ (row0_addMul ha (hl x List.mem_cons_self) _)
        fun f hf => hl f (List.mem_cons_of_mem _ hf)
  refine step _ _ (row0_bare rfl) fun f hf => ?_
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hf
  cases k with
  | inl k =>
    exact alikeN_key (kept2_row0 iU3 K3) N N A.norm A.wide hd
      (heardAlike_of_bare (kept2_row0 iU3 K3) B) k
  | inr k => exact rel_key (kept2_row0 iU3 K3) R R A.head hJ (row0_bare B.lgClaimed) k

end Walk

/-- A filled slot of a well laid ledger passes the table's test on slots, where the mask row's seat
is there and the merge has laid no slot. -/
theorem slotIn_filled (own : List (Nat × Nat)) (late : List (Nat × E × E)) (a : K9.Part) (j : Nat)
    (hW : WellLaid a.F) (hM : (K9.maskSeat own a).isSome = true)
    (hj : OnBytes.PscRun.Filled a.F j) :
    K9.slotIn own none late a j = true := by
  have hlt : j < a.F.gotF.size := by
    by_contra hn
    unfold OnBytes.PscRun.Filled at hj
    simp [Array.getD, hn] at hj
  have hg : a.F.gotF.getD j false = true := hj
  unfold K9.slotIn
  simp [hM, hg, hW.2.1, hW.2.2, hW.1 ▸ hlt]

/-- **formsInT SAYS YES AT THE HEAD's FOUR RUNS, WHERE k6Silent ANSWERS.** s: the record behind the
head's own block. -/
theorem k6_formsInT (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH) (l piece b : Nat)
    (states : Nat → List (RunOf S))
    (K : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (Rd : Readers) (own : List (Nat × Nat)) (s : S) (a : K9.Part) (ha : segAt? s = some a)
    (hRd : ∀ name, K6Name name → Rd.forms b name s = k6Silent P states b name s)
    (hok : (parOf W.hS (workOf W)).ok = true)
    (hT : K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s)
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s))
    (hfill : ∀ gk, s.lookHeard? = some gk → CEndFilled gk ((seatAt W.hS (readsOf W)).ledger s))
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[])
    (K3 : Nat)
    (hRow : ∀ e v, withTables P s = some e →
      lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v →
      (letI := v.1
       letI := v.2.1
       EntriesRow0 (readsOf W) K3 v.2.2.final v.2.2.head))
    (hEnt : ∀ x : Ent, x.tree = readsOf W → x.row = 0 → x.idx < K3 → K9.entInT own a x = true)
    (hMask : (K9.maskSeat own a).isSome = true) (hFree : K9.mergeOf s = none)
    (name : String)
    (hn : K6Name name) (R : K9.Read)
    (hR : k6Silent P states b name s = some R) :
    K9.formsInT Rd own b name s = true := by
  obtain ⟨g, H, F0, G, rs, hg, hH, hW0, hh, hLt⟩ := hT
  have hB := heardBare_of_hear hW0 hh
  obtain ⟨e, he, hRe⟩ := Option.bind_eq_some_iff.mp hR
  have hF : (seatAt W.hS (readsOf W)).ledger s = a.F := by
    show s.fork?.getD {} = a.F
    rw [seg_fork ha]
    rfl
  rw [hF] at hWL hLt
  -- it is enough that each form has Row0 and names filled slots alone
  have enough : R.late = [] → (∀ f ∈ R.forms, Row0 (readsOf W) K3 f ∧
      ∀ x ∈ f.slots.toList, OnBytes.PscRun.Filled a.F x.1) →
      K9.formsInT Rd own b name s = true := by
    intro hl hall
    unfold K9.formsInT
    rw [ha, hRd name hn, hR]
    simp only [hl, Bool.and_eq_true, List.all_eq_true]
    refine ⟨by simp [K9.lateOk], fun f hf => ?_⟩
    unfold K9.affInT
    rw [hFree]
    simp only [Bool.and_eq_true, List.all_eq_true]
    exact ⟨fun x hx => hEnt x ((hall f hf).1 x hx).1 ((hall f hf).1 x hx).2.1
      ((hall f hf).1 x hx).2.2, fun x hx => slotIn_filled own [] a x.1 hWL hMask
      ((hall f hf).2 x hx)⟩
  -- the letters at e are the record's own
  have hse := front_withTables he
  have letters : ∀ v, lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v →
      v.1 = g ∧ (v.2.1.norm, v.2.1.final, v.2.1.head) = H ∧
      ((∀ r i, (v.2.2.final.entry r i).slots = #[]) ∧
        (∀ r i, (v.2.2.head.entry r i).slots = #[]) ∧ ∀ i, (v.2.2.final.wide i).slots = #[]) := by
    intro v hv
    obtain ⟨H', x, k1, k2, k3, k4⟩ := lettersAt_ok W.hS (readsOf W) (parOf W.hS (workOf W)) hv
    have e1 : (Except.ok v.1 : Except String Given) = .ok g := by
      rw [← k1, given_front W.hS (readsOf W) _ hse, hg]
    have e2 := heard_front W.hS (readsOf W) hse H hH
    rw [k2] at e2
    refine ⟨Except.ok.inj e1, ?_, ?_⟩
    · rw [k4]
      exact Option.some.inj e2
    · rw [k4]
      exact ⟨(reads_bare W.hS (readsOf W) k3).1, (reads_bare W.hS (readsOf W) k3).2,
        wide_bare W.hS (readsOf W) k3⟩
  by_cases hjn : name = "join"
  · subst hjn
    obtain ⟨v, gk, hv, hgke, ej, tj⟩ := reader_join K e R hRe
    obtain ⟨rfl, rfl, hb⟩ := letters v hv
    have hgk : s.lookHeard? = some gk := by rw [← (fork_withTables he).2]; exact hgke
    obtain ⟨_, _, k1, _⟩ := lettersAt_ok W.hS (readsOf W) (parOf W.hS (workOf W)) hv
    obtain ⟨hd, hJ⟩ := sizes_of_plan _ _ e v.1 hok k1
    refine enough tj fun f hf => ?_
    rw [ej] at hf
    obtain rfl := List.mem_singleton.mp hf
    refine ⟨?_, join_slots_filled v gk F0 G a.F rs hW0 hh hLt (hF ▸ hfill gk hgk) hb⟩
    refine joinForm_has (kept_row0 (readsOf W) K3) gk (keyVectorsAt v) (fun c hc => ?_)
      (row0_bare (hbare gk hgk))
    have hlen : c < v.1.calls.length := by
      simpa [keyVectorsAt] using hc
    letI := v.1
    letI := v.2.1
    letI := v.2.2
    unfold keyVectorsAt
    rw [Came.getD_map_toArray v.1.calls _ c hlen (Aff.ofConst zeroE) (0, [])]
    exact keyVector_row0 (hRow e v he hv) hB hd hJ _ _
  · have hn' : name = "norm" ∨ name = "policy" ∨ name = "logits" := by
      rcases hn with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd h hjn
    obtain ⟨v, fs, hv, lk, ef, tf⟩ := reader_own K name hn' e R hRe
    obtain ⟨rfl, rfl, hb⟩ := letters v hv
    obtain ⟨_, _, k1, _⟩ := lettersAt_ok W.hS (readsOf W) (parOf W.hS (workOf W)) hv
    obtain ⟨hd, _⟩ := sizes_of_plan _ _ e v.1 hok k1
    refine enough tf fun f hf => ?_
    rw [ef] at hf
    letI := v.1
    letI := v.2.1
    letI := v.2.2
    exact ⟨claims_row0 (hRow e v he hv) hB hd name fs lk f hf, fun x hx =>
      (forms_filled hW0 hh hb.1 hb.2.1 hLt name fs lk f hf x hx).2.1⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.claims_row0
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keyVector_row0
#print axioms VerifiableInference.Desc.Kinds.Head.Law.slotIn_filled
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_formsInT
