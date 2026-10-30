-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Member.lean: pieces for the model of one chain: what
`chainSteps` prepares at a chain's first sub-protocol; the stretches of a list of parts after a
rejection; and the place of one chain's verifier's state in a session's `Stand`.

  1  `bareStepsR`, `chainSteps_cons_ok`   a chain's `Step`s, cut after its first sub-protocol
  2  `subs_tables`, `sub_model`, `row_sub`   after a rejection the fold at coins over the stretches
     of a list of parts produces the substitutes
  3  `VerAt`, `ver₁`, `ver₂`, `ver₃`   one chain's state in `Stand`: how it is read and set, and the
     chain's step `judge`

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Real
import Johnson.Desc.ProofFile.Honest.Law.Rule.SubSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi S Cl V W Y : Type}

/-! ## 1 A chain's `Step`s, cut after its first sub-protocol -/

/-- The rounds of a sub-protocol at whose place no prover's side is defined, as `chainSteps`
prepares them. -/
def bareStepsR (b : Block S Cl) : List (Step W Y) :=
  (b.rounds.zip b.oracles).map fun r => (⟨b.name, ⟨b.place, 0⟩, r.1, r.2, fun _ _ => none,
    fun _ _ => none, 0, false, none⟩ : Step W Y)

theorem chainSteps_cons_ok {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {b : Block S Cl} {bs : List (Block S Cl)} {hs : List (Placed V W Y)}
    {ss : List (Step W Y)} (h : chainSteps B rows look v (b :: bs) hs = .ok ss) :
    b.oracles.length = b.rounds.length ∧ ∃ l, chainSteps B rows look v bs hs = .ok l ∧
      (((hs.find? fun g => g.place == b.place) = none ∧ ss = bareStepsR b ++ l) ∨
        ∃ g c, (hs.find? fun g => g.place == b.place) = some g ∧
          g.rounds = b.rounds.length ∧ B.cuts.lookup b.place = some (g.parts.map (·.moves.length)) ∧
          lendRow B rows look b.place g.parts 0 = .ok c ∧ ss = g.steps b v c ++ l) := by
  simp only [chainSteps] at h
  split at h
  · cases h
  rename_i hlen
  refine ⟨by simpa using hlen, ?_⟩
  split at h
  · rename_i hnone
    cases hrec : chainSteps B rows look v bs hs with
    | error e => simp [hrec, Except.map] at h
    | ok l =>
      simp only [hrec, Except.map] at h
      cases h
      exact ⟨l, rfl, Or.inl ⟨hnone, rfl⟩⟩
  · rename_i g hg
    split at h
    · cases h
    rename_i hr
    split at h
    · cases h
    rename_i hcut
    split at h
    · cases h
    split at h
    · cases h
    cases hc : lendRow B rows look b.place g.parts 0 with
    | error e => simp [hc, Except.mapError, Except.bind] at h
    | ok c =>
      cases hrec : chainSteps B rows look v bs hs with
      | error e => simp [hc, hrec, Except.mapError, Except.bind, Except.map] at h
      | ok l =>
        simp only [hc, hrec, Except.mapError, Except.bind, Except.map] at h
        cases h
        exact ⟨l, rfl, Or.inr ⟨g, c, hg, by simpa using hr, by simpa using hcut, hc, rfl⟩⟩

/-! ## 2 After a rejection -/

theorem subs_tables : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn), ds.length = ss.length →
    (subsOf ss ds).map (·.tables.length) = ss.map (·.oracles.length)
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | s :: ss, d :: ds, h => by
    have ih := subs_tables ss ds (by simpa using h)
    show ((s.oracles.map substituteZeroTable).map some).length :: (subsOf ss ds).map (·.tables.length) =
      s.oracles.length :: ss.map (·.oracles.length)
    rw [ih, List.length_map, List.length_map]

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (x : Xi) (st : List (Nat × Nat × List UInt64))
  (R : RealAt Bk) (k : Coins Bk) (ch : Nat) (tree : Nat → List Nat)

/-- One stretch after a rejection. In the statement: the chain is not live; for chain number 2 that
is so before its start is reached, too. -/
theorem sub_model (Z : Stand F) (hlive : Z.live ch = false) (a : Addr) (ss : List (Step W Y))
    (ds : List Fmt.Drawn) (n : Nat) (t : Option Teller) :
    (Act.stage x st R (.lay ⟨ch, a, ss.map fun s => (s.decl, s.oracles), ds,
      asksFrom tree ((ss.map fun s => (s.decl, s.oracles)).map (·.2.length)) n, t⟩ :
        Act F)).shows k Z = pairsBy tree (subsOf ss ds) n := by
  show (if Z.live ch = true then _ else Stretch.sub _) = _
  rw [if_neg (by rw [hlive]; exact Bool.false_ne_true), sub_pairs, List.map_map]
  rfl

/-- **The stretches of a list of parts after a rejection.** -/
theorem row_sub (tl : Addr → Option Teller) (a : Place) :
    ∀ (cuts : List Nat) (j : Nat) (ss : List (Step W Y)) (ds : List Fmt.Drawn) (n : Nat)
      (Z : Stand F), Z.live ch = false → cuts.sum = ss.length → ds.length = ss.length →
    Kit.real ((cutRow ch tree tl a j cuts (ss.map fun s => (s.decl, s.oracles)) n ds).map
        fun s => Act.stage x st R (.lay s : Act F)) k Z =
      { Z with laid := Z.laid.add ch (pairsBy tree (subsOf ss ds) n) }
  | [], j, ss, ds, n, Z, _, hs, _ => by
    have e : ss = [] := List.eq_nil_of_length_eq_zero (by simpa using hs.symm)
    subst e
    show Z = { Z with laid := Z.laid.add ch [] }
    rw [Laid.add_nil]
  | c :: cuts, j, ss, ds, n, Z, hlive, hs, hd => by
    simp only [List.sum_cons] at hs
    have e1 : (ss.map fun s => (s.decl, s.oracles)).take c =
        (ss.take c).map fun s => (s.decl, s.oracles) := by rw [List.map_take]
    have e2 : (ss.map fun s => (s.decl, s.oracles)).drop c =
        (ss.drop c).map fun s => (s.decl, s.oracles) := by rw [List.map_drop]
    have hl1 : (ds.take c).length = (ss.take c).length := by
      rw [List.length_take, List.length_take, hd]
    have ih := row_sub tl a cuts (j + 1) (ss.drop c) (ds.drop c)
      (n + (((ss.take c).map fun s => (s.decl, s.oracles)).map (·.2.length)).sum)
      { Z with laid := Z.laid.add ch (pairsBy tree (subsOf (ss.take c) (ds.take c)) n) } hlive
      (by rw [List.length_drop]; omega) (by rw [List.length_drop, List.length_drop, hd])
    show Kit.real ((cutRow ch tree tl a (j + 1) cuts
        ((ss.map fun s => (s.decl, s.oracles)).drop c)
        (n + (((ss.map fun s => (s.decl, s.oracles)).take c).map (·.2.length)).sum)
        (ds.drop c)).map fun s => Act.stage x st R (.lay s : Act F)) k
      { Z with laid := Z.laid.add ch ((Act.stage x st R (.lay ⟨ch, ⟨a, j⟩,
        (ss.map fun s => (s.decl, s.oracles)).take c, ds.take c,
        asksFrom tree (((ss.map fun s => (s.decl, s.oracles)).take c).map (·.2.length)) n,
        tl ⟨a, j⟩⟩ : Act F)).shows k Z) } = _
    rw [e1, e2, sub_model x st R k ch tree Z hlive ⟨a, j⟩ (ss.take c) (ds.take c) n, ih]
    show ({ Z with laid := ((Z.laid.add ch (pairsBy tree (subsOf (ss.take c) (ds.take c)) n)).add
        ch (pairsBy tree (subsOf (ss.drop c) (ds.drop c))
          (n + (((ss.take c).map fun s => (s.decl, s.oracles)).map (·.2.length)).sum))) } :
        Stand F) = { Z with laid := Z.laid.add ch (pairsBy tree (subsOf ss ds) n) }
    have e3 : subsOf ss ds = subsOf (ss.take c) (ds.take c) ++ subsOf (ss.drop c) (ds.drop c) := by
      rw [← subsOf_append _ _ _ _ hl1.symm, List.take_append_drop, List.take_append_drop]
    rw [Laid.add_add, e3, pairsBy_append, subs_tables _ _ hl1, List.map_map]
    rfl

end

/-! ## 3 One chain's state in a `Stand` -/

/-- **Which field of a `Stand` holds one chain's verifier's state.** `ch`, `ft`: the chain's number,
from 0, and the number in the label of its first own tree. `x`: the instance. `st`: the stored
tables' columns. `get`, `set`: how the state is read and set. `J`: the chain's step `judge`. `live`:
the verifier has not rejected in the chain just where `get` is `some`. `add`: the step's stage
ignores what is shown and sets the state to `judgeOff` of it. `get_set`, `set_get`, `set_set`: the
three lens laws. `get_laid`, `laid_set`, `set_laid`: the state and `laid` do not touch. -/
structure VerAt (F : FileDescription Xi) (S Cl : Type) (x : Xi) (st : List (Nat × Nat × List UInt64))
    (ch ft : Nat) where
  get : Stand F → Option S
  set : Stand F → Option S → Stand F
  J : Block S Cl → List Fmt.Drawn → Act F
  live : ∀ Z : Stand F, Z.live ch = (get Z).isSome
  add : ∀ b own Z new,
    (J b own).add x st Z new = set Z ((get Z).bind (judgeOff ch ft st b own Z.laid))
  get_laid : ∀ (Z : Stand F) (l : Laid), get { Z with laid := l } = get Z
  get_set : ∀ Z v, get (set Z v) = v
  set_get : ∀ Z, set Z (get Z) = Z
  laid_set : ∀ Z v, (set Z v).laid = Z.laid
  set_set : ∀ Z v v', set (set Z v) v' = set Z v'
  set_laid : ∀ (Z : Stand F) (v : Option S) (l : Laid),
    ({ set Z v with laid := l } : Stand F) = set { Z with laid := l } v

/- The first chain's: the field `v₁`, `Act.judge₁`, the numbers 0 and 0. -/
def ver₁ (F : FileDescription Xi) (x : Xi) (st : List (Nat × Nat × List UInt64)) :
    VerAt F F.S₁ F.Cl x st 0 0 where
  get := (·.v₁)
  set := fun Z v => { Z with v₁ := v }
  J := Act.judge₁
  live := fun _ => rfl
  add := fun _ _ _ _ => rfl
  get_laid := fun _ _ => rfl
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  laid_set := fun _ _ => rfl
  set_set := fun _ _ _ => rfl
  set_laid := fun _ _ _ => rfl

/- The shared chain's: `v₂`, `Act.judge₂`, 1 and 0. -/
def ver₂ (F : FileDescription Xi) (x : Xi) (st : List (Nat × Nat × List UInt64)) :
    VerAt F F.S₂ F.Cl x st 1 0 where
  get := (·.v₂)
  set := fun Z v => { Z with v₂ := v }
  J := Act.judge₂
  live := fun _ => rfl
  add := fun _ _ _ _ => rfl
  get_laid := fun _ _ => rfl
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  laid_set := fun _ _ => rfl
  set_set := fun _ _ _ => rfl
  set_laid := fun _ _ _ => rfl

/- The second chain's: `v₃`, `Act.judge₃`, 2 and `F.lastChainFirstTreeNumber`. -/
def ver₃ (F : FileDescription Xi) (x : Xi) (st : List (Nat × Nat × List UInt64)) :
    VerAt F F.S₃ F.Cl x st 2 F.lastChainFirstTreeNumber where
  get := (·.v₃)
  set := fun Z v => { Z with v₃ := v }
  J := Act.judge₃
  live := fun _ => rfl
  add := fun _ _ _ _ => rfl
  get_laid := fun _ _ => rfl
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  laid_set := fun _ _ => rfl
  set_set := fun _ _ _ => rfl
  set_laid := fun _ _ _ => rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.chainSteps_cons_ok
#print axioms ProofFile.Honest.subs_tables
#print axioms ProofFile.Honest.sub_model
#print axioms ProofFile.Honest.row_sub
