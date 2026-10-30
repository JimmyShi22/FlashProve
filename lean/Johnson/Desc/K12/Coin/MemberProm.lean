-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/MemberProm.lean: **A MEMBER OF THE WHOLE PROMISE OF THE PROXIMITY TEST's LAW's
SECOND ARM (`k12_lawRecFreeO`, FreeOff.lean), AT ONE RECORD OF A STORED PROOF.** Statements and
proofs, over the literals and the member of `PayRec` of the kind's own law's side
(Johnson/Desc/K12/Law/LitO.lean, MemberO.lean; Coin/MemberOTrue.lean).

The record tO and the place's numbers piO are those in front of "BAT" at the opened rows' test on
the shared chain (the place whose first fold sends its own mask) of the smaller stored proof, as a
run printed them. The promise has three clauses on the record:

  `roots_O`: the record's count of roots is 5 (and the place's first free own number is 5).
  `dO`, `dO_facts`: the plain data that the record fixes: the first switch opens the book's places
    1, 2, 5, under the declared sources own 1, own 2, own 5; the members' trees stand at 1 and 2,
    the mask's at 5. By Lean's kernel, on the literals.
  `firstOpensOwn_O`: **`FirstOpensOwn` at tO, WHATEVER THE NUMBERS t₁, t₂ OF TREES THAT THE EARLIER
    CHAINS SEND**: at num := numAt t₁ t₂ 1, no := fun z => t₁ + z, base := t₁ + 5.
  `promise_O`: the three clauses together, at whatever oracles.
  `firstOpensOwn_O_moved`: the clause can fail: at base := t₁ + 4 it is false of the same record.
Limits. NO SOUNDNESS IS CLAIMED. A MEMBER OF THE PROMISE, NOT OF THE LAW's PREMISES: `AtPlaceOwn` is
not shown here. THAT tO IS THE RECORD WHICH THE VERIFIER REACHES ON THE STORED FILE IS A RUN's WORD.
That the letter no := fun z => t₁ + z is the one under which the blocks in front speak of these
trees is not shown: it is the table's letter. One place of the smaller proof; nothing at the full
size. That 5 is the number of roots that a written description's shared chain declares in front is
not shown.
-/
import Johnson.Desc.K12.Coin.MemberOTrue
import Johnson.Desc.K12.Coin.FreeOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (gpOf Plain)
open H2K.Member (piO tO)
open H2K.Pin (PayRec)

theorem roots_O : tO.roots = 5 ∧ piO.nums.free = 5 := ⟨rfl, rfl⟩

/-- The plain data that the record fixes. -/
def dO : Option Plain :=
  match piO.nums.stages, tO.st.groups[tO.g]?, tO.st.layout tO.g with
  | a :: _, some G0, some Ly =>
    gpOf piO { tO with st := begun tO.st tO.g G0, pass := .nothing } a Ly
  | _, _, _ => none

theorem dO_facts :
    (dO.map fun D => (D.ts, D.opens.map (·.2), D.mems.map (·.t), D.fresh.t)) =
      some ([1, 2, 5], [.own 1, .own 2, .own 5], [1, 2], 5) := by
  decide +kernel

theorem dO_of {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout}
    {D : Plain} (hf : Fixes piO tO a rest G0 Ly D) :
    D.ts = [1, 2, 5] ∧ D.opens.map (·.2) = [.own 1, .own 2, .own 5] ∧
      D.mems.map (·.t) = [1, 2] ∧ D.fresh.t = 5 := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  have f5 : gpOf piO { tO with st := begun tO.st tO.g G0, pass := .nothing } a Ly = some D :=
    f4 default
  have hD : dO = some D := by
    unfold dO
    rw [f1, f2, f3]
    exact f5
  have h := dO_facts
  rw [hD] at h
  have h' := Option.some.inj h
  exact ⟨congrArg (·.1) h', congrArg (·.2.1) h', congrArg (·.2.2.1) h', congrArg (·.2.2.2) h'⟩

/-- **`FirstOpensOwn` at the record, whatever the earlier chains' numbers of trees.** -/
theorem firstOpensOwn_O (t₁ t₂ : ℕ) :
    FirstOpensOwn piO (numAt t₁ t₂ 1) (fun z => t₁ + z) (t₁ + 5) tO := by
  intro a rest G0 Ly D hf
  obtain ⟨e1, e2, e3, e4⟩ := dO_of hf
  refine ⟨?_, fun i => ?_, ?_⟩
  · have h : D.opens.map (fun o => numAt t₁ t₂ 1 o.2) =
        (D.opens.map (·.2)).map (numAt t₁ t₂ 1) := by
      rw [List.map_map]
      rfl
    rw [h, e2, e1]
    simp [numAt]
  · have h : (D.mems.get i).t ∈ D.mems.map (·.t) :=
      List.mem_map.2 ⟨_, List.get_mem _ i, rfl⟩
    rw [e3] at h
    show t₁ + (D.mems.get i).t < t₁ + 5
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    omega
  · show t₁ + D.fresh.t = t₁ + 5
    rw [e4]

/-- **The whole promise of `k12_lawRecFreeO`, at the record and whatever oracles.** -/
theorem promise_O (t₁ t₂ : ℕ) :
    tO.roots = 5 ∧ (FirstOpensOwn piO (numAt t₁ t₂ 1) (fun z => t₁ + z) (t₁ + 5) tO ∧
      PayRec piO tO) :=
  ⟨rfl, firstOpensOwn_O t₁ t₂, member_O_true.2.2.2.1⟩

/-- The clause can fail: at a base one lower it is false of the same record. -/
theorem firstOpensOwn_O_moved (t₁ t₂ : ℕ) :
    ¬ FirstOpensOwn piO (numAt t₁ t₂ 1) (fun z => t₁ + z) (t₁ + 4) tO := by
  intro h
  obtain ⟨a, rest, G0, Ly, D, hf⟩ := member_O_true.1
  obtain ⟨_, _, _, e4⟩ := dO_of hf
  have h3 : t₁ + D.fresh.t = t₁ + 4 := (h a rest G0 Ly D hf).2.2
  rw [e4] at h3
  omega

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.dO_facts
#print axioms VerifiableInference.Desc.K12.Coin.firstOpensOwn_O
#print axioms VerifiableInference.Desc.K12.Coin.promise_O
#print axioms VerifiableInference.Desc.K12.Coin.firstOpensOwn_O_moved
