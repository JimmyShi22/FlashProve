-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmElsePaid.lean: THE OUTPUT HEAD's HALF OF THE BINDER hArm AT THE LOOKUP ARGUMENT's TWO
RUNS "objects" AND "guests" (the premise hElse of arm_at_reads_three, Johnson/Desc/K1/Law/ArmHead.lean):
NEITHER RUN's FORMS NAME AN ENTRY OF A VIRTUAL ROW, so the exchange has nothing to say at them: "guests"
answers the empty list; "objects" answers the rows that the lookup on the calls heard, and these are bare
UNDER ONE FACT ON THE STATE IN FRONT: RowsBareH: a clause for the letter J of ArmOk. A definition, and
statements with their proofs.

Main names:
  RowsBare s          the rows that the lookup on the calls heard name no entry.
  RowsBareH s         the same where the state stands in the output head's segment (idle elsewhere).
  BareRun ρ           at a state with RowsBare an accept of ρ claims forms without an entry.
                      bare_objects · bare_guests · bare_guard.
  reader_forms        where a run's reader answers, its forms are the run's own claims' forms.
  k3At_else_bare · states2_bare   what link 24's second hearing sub-protocol states under another name
                      than "planes".
  rowsBare_tables     laying the reads' tables leaves what the lookup heard.
  elseRunsB · elseRuns [kernel] · elseRuns_fails: in the fence a run that is none of K6's four and not
                      "planes" stands in block 2 and is not "K8.equations".
  hElse_of            **the premise hElse, from J alone** (hJb : J gives RowsBareH) and the scope.
What is not claimed. RowsBareH at a reached state (Johnson/Desc/AtSeats/RowsBareAtHead.lean is to say that).
Nothing on soundness, on an honest prover or on hiding.
THE RECURSION LIMIT IS RAISED IN THIS FILE (maxRecDepth 1000000): for the kernel's evaluations'
elaboration alone.

-/
import Johnson.Desc.K1.Law.ArmHeadJ

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place Strs named)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers flatPlacesOf standOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13 mgBase rowQ Mem
  seatTab dataQ ArmCellIn)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (Read Readers RunOf readerOf LinkHoles statesOfLink readersOfLink
  holesAt phAt)
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff k6Silent K6Name p8K6)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

/-! ## 1 Runs whose forms name no entry -/

/-- The rows that the lookup on the calls heard name no entry of a virtual row. -/
def RowsBare (s : S) : Prop := ∀ g, s.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[]

/-- The same where the state stands in the output head's segment. -/
def RowsBareH (s : S) : Prop := ∀ o, s.here = .head o → RowsBare s

def BareRun (ρ : ℕ → S → Except String (List Claim × S)) : Prop :=
  ∀ s z, RowsBare s → ρ 0 s = .ok z → ∀ cl ∈ z.1, cl.form.ents = #[]

theorem bare_objects : BareRun K9.objectsCalls := by
  intro s z hb e cl hcl
  unfold K9.objectsCalls K9.objectsBy at e
  obtain ⟨F, _, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨g, hg, e⟩ := (bind_ok _ _ _).1 e
  obtain rfl := Except.ok.inj e
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hcl
  exact hb g (some_of_named hg) a ha

theorem bare_guests : BareRun K9.guestsNone := by
  intro s z _ e cl hcl
  have e' : (Except.ok ([], s) : Except String (List Claim × S)) = .ok z := e
  obtain rfl := Except.ok.inj e'
  cases hcl

theorem bare_guard (same : S → S → Bool) (ρ : ℕ → S → Except String (List Claim × S))
    (h : BareRun ρ) : BareRun (IM.guardRun same ρ) := by
  intro s z hb e
  exact h s z hb ((IM.guardRun_yes ρ 0 s z).1 e).1

/-- Where a run's reader answers, its forms are the forms of the run's own claims. -/
theorem reader_forms (states : ℕ → List (RunOf S)) (b : ℕ) (name : String) {s : S} {X : Read}
    (h : readerOf states b name s = some X) :
    ∃ r z, (states b).find? (fun r => r.1 == name) = some r ∧ r.2 0 s = .ok z ∧
      X.forms = z.1.map (·.form) := by
  unfold readerOf at h
  obtain ⟨r, hr1, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · rename_i z F e1 e2
    obtain ⟨G, _, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · rw [← Option.some.inj h]
      exact ⟨r, z, hr1, e1, rfl⟩
    · cases h
  · cases h

/-- So, at a state with RowsBare, the reader of a bare run answers forms without an entry. -/
theorem reader_bare (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
    (hr : ∀ r, (states b).find? (fun r => r.1 == name) = some r → BareRun r.2) {s : S} {X : Read}
    (hb : RowsBare s) (h : readerOf states b name s = some X) : ∀ f ∈ X.forms, f.ents = #[] := by
  obtain ⟨r, z, f1, f2, f3⟩ := reader_forms states b name h
  intro f hf
  rw [f3] at hf
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.1 hf
  exact hr r f1 s z hb f2 cl hcl

/-- Laying the reads' tables leaves what the lookup heard. -/
theorem rowsBare_tables (P : K8.ReadsQuiet.PH) {s e : S} (he : withTables P s = some e)
    (hb : RowsBare s) : RowsBare e := by
  obtain ⟨a, cov, x, tt, ha, _, _, _, _, rfl⟩ := (withTables_iff P s e).1 he
  intro g hg
  refine hb g ?_
  unfold S.lookHeard? at hg ⊢
  rw [ha]
  exact hg

/-! ## 2 What link 24 states at its second hearing sub-protocol -/

/-- The lookup's lot's sub-protocol on the calls: every run but "planes". -/
theorem k3At_else_bare (W : Verify.Public) (Z : ProofFile.Pub) (a : Place) (ha : a.piece ≤ 3)
    (b' : Block S Cl) (h : IM.k3At W Z a = some b') :
    ∀ r ∈ b'.claims, r.1 ≠ "planes" → BareRun r.2 := by
  have h' : K3.theStated K3Lot.ofForm (K3Lot.readersAt W) W Z.first.codes Z.first.shape a =
      some b' := h
  unfold K3.theStated at h'
  obtain ⟨b₀, h₀, h'⟩ := Option.bind_eq_some_iff.1 h'
  have e0 : ∀ r ∈ b₀.claims, BareRun r.2 :=
    theWhole_calls_of (fun c => BareRun c.2) K3Lot.ofForm
      (fun piece laid sent p c hc => by
        have hc' : c ∈ [("objects", K9.objectsCalls), ("guests", K9.guestsNone)] := hc
        have : c = ("objects", K9.objectsCalls) ∨ c = ("guests", K9.guestsNone) := by
          simpa using hc'
        rcases this with e | e <;> rw [e]
        · exact bare_objects
        · exact bare_guests) W _ _ a ha b₀ h₀
  split at h'
  · obtain rfl : b₀ = b' := Option.some.inj h'
    exact fun r hr _ => e0 r hr
  · split at h'
    · obtain rfl : b₀ = b' := Option.some.inj h'
      exact fun r hr _ => e0 r hr
    · split at h'
      · obtain rfl : b₀ = b' := Option.some.inj h'
        exact fun r hr _ => e0 r hr
      · rename_i rd _
        obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h'
        intro r hm hn
        have hm' : r ∈ b₀.claims ++
            [("planes", K3.planesRun (K3.seatCalls K3Lot.ofForm) p.lm rd)] := hm
        rcases List.mem_append.1 hm' with h1 | h1
        · exact e0 r h1
        · rw [List.mem_singleton.1 h1] at hn
          exact absurd rfl hn

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem states2_bare (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (lk : Link S Cl)
    (eL : c.links[24]? = some lk) (name : String) (hn : name ≠ "planes") :
    ∀ r, (statesOfLink lk 2).find? (fun r => r.1 == name) = some r → BareRun r.2 := by
  obtain ⟨Lk, b, b', e1, e2, k3, la⟩ := IM.k3_of hS hR O 24 (by omega) false
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  have e2' : lk.hear[2]? = some b := e2
  intro r hr
  have hb := List.find?_some (p := fun r : RunOf S => r.1 == name) hr
  have hnm : r.1 = name := eq_of_beq hb
  have hm : r ∈ statesOfLink lk 2 := List.mem_of_find?_eq_some hr
  unfold statesOfLink at hm
  rw [e2'] at hm
  have hm' : r ∈ b.claims := hm
  rw [IM.claims_alone la] at hm'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm'
  exact bare_guard _ _ (k3At_else_bare Bs.G₀.W Z _ (by decide) b' k3 q hq (by
    intro e
    exact hn (hnm.symm.trans e)))

end

/-! ## 3 Where the other runs stand -/

def elseRunsB (b2 : ℕ) : Bool :=
  (rowQ linksFull (flatPlacesOf linksFull true) (noL 24 false)).ins.all fun it =>
    match it with
    | .formsT l j n => (runsAt linksFull l j n).all fun p =>
        (p.2 == "norm" || p.2 == "policy" || p.2 == "logits" || p.2 == "join" || p.2 == "planes") ||
          (p.1 == b2 && p.2 != "K8.equations")
    | _ => true

theorem elseRuns : elseRunsB 2 = true := by decide +kernel

/-- The test can fail. -/
theorem elseRuns_fails : elseRunsB 3 = false := by decide +kernel

theorem else_of_run {p : ℕ × String}
    (h : ∃ j n, Item.formsT 24 j n ∈
      (rowQ linksFull (flatPlacesOf linksFull true) (noL 24 false)).ins ∧
        p ∈ runsAt linksFull 24 j n) (h6 : ¬ K6Name p.2) (hp : p.2 ≠ "planes") :
    p.1 = 2 ∧ (p.2 == "K8.equations") = false := by
  obtain ⟨j, n, hi, hm⟩ := h
  have t := List.all_eq_true.1 (List.all_eq_true.1 elseRuns _ hi) p hm
  rcases Bool.or_eq_true_iff.1 t with t | t
  · exfalso
    simp only [Bool.or_eq_true, beq_iff_eq] at t
    rcases t with (((e | e) | e) | e) | e
    · exact h6 (Or.inl e)
    · exact h6 (Or.inr (Or.inl e))
    · exact h6 (Or.inr (Or.inr (Or.inl e)))
    · exact h6 (Or.inr (Or.inr (Or.inr e)))
    · exact hp e
  · obtain ⟨t1, t2⟩ := Bool.and_eq_true_iff.1 t
    exact ⟨eq_of_beq t1, by simpa using t2⟩

/-! ## 4 The premise -/

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

/-- **THE PREMISE hElse OF arm_at_reads_three, FROM J ALONE.** -/
theorem hElse_of (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJb : ∀ s, J s → RowsBareH s) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → ¬ K6Name p.2 →
      p.2 ≠ "planes" →
      ArmCellIn (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH 24) := by
  intro X arrs x x' y y' w p A B Fc h6 hp
  obtain ⟨lk, _, _, _, eL, -⟩ := IM.k6_of hS hR O
  have hX : headLink XV = 24 := hWX ▸ headLink_open hS hR O
  obtain ⟨hp1, hp8⟩ : p.1 = 2 ∧ (p.2 == "K8.equations") = false := by
    refine else_of_run ?_ h6 hp
    obtain ⟨j, n, h1, h2⟩ := Fc.run
    refine ⟨j, n, h1, ?_⟩
    have h2' : p ∈ runsAt Dm.links 24 j n := h2
    rw [hDlk] at h2'
    exact h2'
  obtain ⟨o, ho⟩ := here_head_of_stand (stand_of_promise 24 (by decide) x y Fc.inAt)
  have hb : RowsBare x.2 := hJb _ Fc.inv o ho
  have hr := states2_bare hS hR O lk eL p.2 hp
  intro R hR' f hf e he
  exfalso
  rw [rd24 Dm hX lk ((hlk 24 (by decide)).trans eL), hp1] at hR'
  have h1 : (if (p.2 == "K8.equations") = true then (holesAt XV 24 24 lk).small x.2
    else
      match readerOf (statesOfLink lk) 2 p.2 x.2 with
      | some R => some R
      | Option.none => (holesAt XV 24 24 lk).silent 2 p.2 x.2) = some R := hR'
  rw [hp8, silent24] at h1
  have hbare : ∀ f ∈ R.forms, f.ents = #[] := by
    cases hq : readerOf (statesOfLink lk) 2 p.2 x.2 with
    | some R₁ =>
      rw [hq] at h1
      obtain rfl : R₁ = R := Option.some.inj h1
      exact reader_bare _ 2 p.2 hr hb hq
    | none =>
      rw [hq] at h1
      have h2 : (withTables (p8K6 XV 24) x.2).bind (readerOf (statesOfLink lk) 2 p.2) = some R := h1
      obtain ⟨e', he', h3⟩ := Option.bind_eq_some_iff.1 h2
      exact reader_bare _ 2 p.2 hr (rowsBare_tables _ he' hb) h3
  rw [hbare f hf] at he
  cases he

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.bare_objects
#print axioms VerifiableInference.Desc.K1.bare_guests
#print axioms VerifiableInference.Desc.K1.bare_guard
#print axioms VerifiableInference.Desc.K1.reader_forms
#print axioms VerifiableInference.Desc.K1.reader_bare
#print axioms VerifiableInference.Desc.K1.rowsBare_tables
#print axioms VerifiableInference.Desc.K1.k3At_else_bare
#print axioms VerifiableInference.Desc.K1.states2_bare
#print axioms VerifiableInference.Desc.K1.elseRuns
#print axioms VerifiableInference.Desc.K1.elseRuns_fails
#print axioms VerifiableInference.Desc.K1.else_of_run
#print axioms VerifiableInference.Desc.K1.hElse_of
