-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ChainEndExact.lean: the chains' end's law, both ways at the block, for every clause at
the fold, and for all three chains at a file's decision. Theorems. THE LAW IS OF untestedL, refuse
AND chainEnd AS THEY STAND IN Johnson/Desc/ChainEnd.lean.

  chainEnd_decide_iff   the end says yes just where every one of its clauses holds, and hands the
                        record on as it is.
  untested_iff          the two clauses of untestedL hold just where NothingLeft does.
  Exact ask e           the first of these, as a property of a block e.
  Core st e             "a chain's fold with e as last block says yes only with NothingLeft at the
                        record that it returns", as a property of a block e.
  Law st ask e          both: Exact ask e and Core st e.
  core_of_exact         Exact ask e and Asks st ask give Core st e.
  chainEnd_law          the end meets the law, wherever its clauses hold untestedL's among them.
  chainAt_end_clauses   a chain's fold with the end as last block says yes only where every clause
                        of the end holds at the record that it returns.
  EndsWith c ask        the chain c, as it is typed, has the end with the clauses ask in its field
                        "last".
  endsWith_mk           a chain that is typed so ends so: whatever stands in its other fields.
  flat_of_endsWith      then the chain's flat list has that very block as its last.
  runEnd_ends           a file's decision, at a description whose three chains end so: every clause
                        of each end holds at that chain's last record.
  run_nothing_left3     **ALL THREE CHAINS AT ONCE**, from FileDescription.run = true: the first chain's
                        own clauses; NothingLeft at the shared and at the second chain's last
                        record.
WHAT OF `verify-on-bytes` IS USED: its plain record Statement. No routine in a
context is reached from a statement or a proof here.
What is not claimed. "Its test has begun" is the mark inRun: nothing on whether the test was carried
through. Nothing of a claim that was never laid on a group. THE READING st IS FREE: the law is worth
what the reading is: it is to be spent at the very field into which the chain's blocks lay groups
and messages and write the mark; at a reading that forgets the record it says nothing. Core alone is
met by a block that refuses all: it is Exact beside it that such a block fails
(Johnson/Desc/ChainEndControls.lean [not in this library]). That the first chain's open groups
arrive in the second chain's statement is the second chain's start's matter. "No round and no column
is left" and "no count of claims is owed" are stated elsewhere. Nothing on soundness as such, on an
honest prover or on hiding.

-/
import Johnson.Desc.ChainEndFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.ChainEnd
open OnBytes VerifiableInference.Desc

variable {S Cl : Type}

/-- The end says yes just where every clause holds, and hands the record on as it is. -/
theorem chainEnd_decide_iff (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (ask : S → Clauses) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (chainEnd (Cl := Cl) chain piece sealed inFront ask).decide s rs gs = .ok s' ↔
      s' = s ∧ ∀ c ∈ ask s, c.2 = true := by
  have hd : (chainEnd (Cl := Cl) chain piece sealed inFront ask).decide s rs gs =
      (refuse (ask s)).map fun _ => s := rfl
  rw [hd, ← refuse_ok_iff]
  cases refuse (ask s) with
  | error e => simp [Except.map]
  | ok u => cases u; simp [Except.map, eq_comm]

/-- The two clauses of untestedL hold just where nothing is left untested. -/
theorem untested_iff (T : Statement) : refuse (untestedL T) = .ok () ↔ NothingLeft T := by
  refine ⟨untested_spec T, fun h => ?_⟩
  rw [refuse_ok_iff]
  intro c hc
  simp only [untestedL, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact Array.all_eq_true.2 h.1
  · show (T.oracles.all fun x =>
      !x.sampled || x.groups.any fun g => (T.groups[g]?).any (·.inRun)) = true
    rw [Array.all_eq_true]
    intro i hi
    cases hs : (T.oracles[i]).sampled with
    | false => simp
    | true =>
      obtain ⟨g, hg, G, hG, hr⟩ := h.2 i hi hs
      simp only [Bool.not_true, Bool.false_or, List.any_eq_true]
      exact ⟨g, hg, by simp [hG, hr]⟩

/-- A block says yes just where every clause of ask holds, and hands the record on as it is. -/
def Exact (ask : S → Clauses) (e : Block S Cl) : Prop :=
  ∀ s rs gs s', e.decide s rs gs = .ok s' ↔ s' = s ∧ ∀ c ∈ ask s, c.2 = true

/-- A chain's fold with e as last block says yes only with nothing left untested. -/
def Core (st : S → Statement) (e : Block S Cl) : Prop :=
  ∀ (name : String) (ft : Nat) (bs : List (Block S Cl)) (s s' : S) (v : Fmt.View),
    chainAt name ft (bs ++ [e]) s v = .ok s' → NothingLeft (st s')

/-- **The law, as a property of a last block**: both halves. -/
def Law (st : S → Statement) (ask : S → Clauses) (e : Block S Cl) : Prop :=
  Exact ask e ∧ Core st e

/-- The end is exact at its clauses. -/
theorem chainEnd_exact (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (ask : S → Clauses) : Exact ask (chainEnd (Cl := Cl) chain piece sealed inFront ask) :=
  fun s rs gs s' => chainEnd_decide_iff chain piece sealed inFront ask s s' rs gs

/-- An exact block whose clauses hold untestedL's among them has the core. -/
theorem core_of_exact (st : S → Statement) (ask : S → Clauses) (e : Block S Cl)
    (he : Exact ask e) (ha : Asks st ask) : Core st e := by
  intro name ft bs s s' v h
  refine chainAt_last name ft e (fun t => NothingLeft (st t)) ?_ bs s s' v h
  intro t rs gs t' hd
  obtain ⟨ht, hc⟩ := (he t rs gs t').1 hd
  subst ht
  exact (untested_iff _).1 ((refuse_ok_iff _).2 fun c hx => hc c (ha _ c hx))

/-- **The end meets the law**, wherever its clauses hold untestedL's among them. -/
theorem chainEnd_law (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (st : S → Statement) (ask : S → Clauses) (ha : Asks st ask) :
    Law st ask (chainEnd (Cl := Cl) chain piece sealed inFront ask) :=
  ⟨chainEnd_exact chain piece sealed inFront ask,
    core_of_exact st ask _ (chainEnd_exact chain piece sealed inFront ask) ha⟩

/-- Every clause of the end holds at the record that the chain's fold returns. -/
theorem chainAt_end_clauses (name : String) (ft chain piece : Nat) (sealed : Bool)
    (inFront : List Fmt.DeclaredRound) (ask : S → Clauses) (bs : List (Block S Cl)) (s s' : S)
    (v : Fmt.View)
    (h : chainAt name ft (bs ++ [chainEnd chain piece sealed inFront ask]) s v = .ok s') :
    ∀ c ∈ ask s', c.2 = true := by
  refine chainAt_last name ft _ (fun t => ∀ c ∈ ask t, c.2 = true) ?_ bs s s' v h
  intro t rs gs t' hd
  obtain ⟨ht, hc⟩ := (chainEnd_decide_iff chain piece sealed inFront ask t t' rs gs).1 hd
  subst ht
  exact hc

/-- The chain, as it is typed, has the end with the clauses ask in its field "last". -/
def EndsWith (c : Chain S Cl) (ask : S → Clauses) : Prop :=
  ∃ (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound),
    c.last = chainEnd chain piece sealed inFront ask

/-- A chain that is typed with the end in its field "last" ends so. -/
theorem endsWith_mk (first : Block S Cl) (front : List (Block S Cl)) (links : List (Link S Cl))
    (back : List (Block S Cl)) (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (ask : S → Clauses) :
    EndsWith { first := first, front := front, links := links, back := back,
               last := chainEnd chain piece sealed inFront ask } ask :=
  ⟨chain, piece, sealed, inFront, rfl⟩

/-- A block without claims and without runs behind a batching is laid into the flat list as it
is. -/
theorem bare_eq (b : Block S Cl) (h : b.hasNoClaimsAndNothingAfter = true) :
    { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } = b := by
  rw [h, Bool.and_true]

/-- The flat list of a chain that ends so has that very block as its last. -/
theorem flat_of_endsWith (c : Chain S Cl) (ask : S → Clauses) (h : EndsWith c ask) :
    ∃ (l : List (Block S Cl)) (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound),
      c.blocksInOrder = l ++ [chainEnd chain piece sealed inFront ask] := by
  obtain ⟨chain, piece, sealed, inFront, hb⟩ := h
  refine ⟨{ c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } ::
    c.front.map (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) ++
    c.links.flatMap Link.blocksInOrder ++ c.back.map (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }),
    chain, piece, sealed, inFront, ?_⟩
  unfold Chain.blocksInOrder
  simp only [hb, bare_eq (chainEnd chain piece sealed inFront ask) rfl]

/-- Every clause of each chain's end holds at that chain's last record. -/
theorem runEnd_ends {Xi : Type} (F : FileDescription Xi) (a₁ : F.S₁ → Clauses) (a₂ : F.S₂ → Clauses)
    (a₃ : F.S₃ → Clauses) (h₁ : EndsWith F.first a₁) (h₂ : EndsWith F.shared a₂)
    (h₃ : EndsWith F.second a₃) (x : Xi) (v₁ v₂ v₃ : Fmt.View) (e₁ : F.S₁) (e₂ : F.S₂) (e₃ : F.S₃)
    (h : F.runEnd x v₁ v₂ v₃ = .ok (e₁, e₂, e₃)) :
    (∀ c ∈ a₁ e₁, c.2 = true) ∧ (∀ c ∈ a₂ e₂, c.2 = true) ∧ ∀ c ∈ a₃ e₃, c.2 = true := by
  unfold FileDescription.runEnd at h
  obtain ⟨j₁, j₂, ⟨s₃, _, j₃⟩, _⟩ := runCore_chains _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨l₁, _, _, _, _, k₁⟩ := flat_of_endsWith _ _ h₁
  obtain ⟨l₂, _, _, _, _, k₂⟩ := flat_of_endsWith _ _ h₂
  obtain ⟨l₃, _, _, _, _, k₃⟩ := flat_of_endsWith _ _ h₃
  rw [k₁] at j₁
  rw [k₂] at j₂
  rw [k₃] at j₃
  exact ⟨chainAt_end_clauses _ _ _ _ _ _ _ _ _ _ _ j₁, chainAt_end_clauses _ _ _ _ _ _ _ _ _ _ _ j₂,
    chainAt_end_clauses _ _ _ _ _ _ _ _ _ _ _ j₃⟩

/-- Clauses that hold untestedL's among them, all true, give that nothing is left untested. -/
theorem nothingLeft_of_clauses (st : S → Statement) (ask : S → Clauses) (ha : Asks st ask) (s : S)
    (h : ∀ c ∈ ask s, c.2 = true) : NothingLeft (st s) :=
  (untested_iff _).1 ((refuse_ok_iff _).2 fun c hx => h c (ha _ c hx))

/-- **All three chains at once**, from the decision's Boolean. -/
theorem run_nothing_left3 {Xi : Type} (F : FileDescription Xi) (a₁ : F.S₁ → Clauses)
    (a₂ : F.S₂ → Clauses) (a₃ : F.S₃ → Clauses) (st₂ : F.S₂ → Statement) (st₃ : F.S₃ → Statement)
    (h₁ : EndsWith F.first a₁) (h₂ : EndsWith F.shared a₂) (h₃ : EndsWith F.second a₃)
    (k₂ : Asks st₂ a₂) (k₃ : Asks st₃ a₃) (x : Xi) (v₁ v₂ v₃ : Fmt.View)
    (h : F.run x v₁ v₂ v₃ = true) :
    ∃ e₁ e₂ e₃, F.runEnd x v₁ v₂ v₃ = .ok (e₁, e₂, e₃) ∧ (∀ c ∈ a₁ e₁, c.2 = true) ∧
      NothingLeft (st₂ e₂) ∧ NothingLeft (st₃ e₃) := by
  unfold FileDescription.run at h
  cases hr : F.runEnd x v₁ v₂ v₃ with
  | error e => simp [hr, Except.isOk, Except.toBool] at h
  | ok r =>
    obtain ⟨e₁, e₂, e₃⟩ := r
    obtain ⟨c₁, c₂, c₃⟩ := runEnd_ends F a₁ a₂ a₃ h₁ h₂ h₃ x v₁ v₂ v₃ e₁ e₂ e₃ hr
    exact ⟨e₁, e₂, e₃, rfl, c₁, nothingLeft_of_clauses st₂ a₂ k₂ e₂ c₂,
      nothingLeft_of_clauses st₃ a₃ k₃ e₃ c₃⟩

end VerifiableInference.Desc.ChainEnd
