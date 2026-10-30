-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- (Where this and lean/THEOREM.md differ,
-- the page holds.)
-- AFTER Coin/MemberProm.lean (promise_O at the smaller example): its text with the place, the record and four numbers turned.
/-
Johnson/Desc/K12/Coin/MemberPromFull.lean: AT THE FULL SIZE: A MEMBER OF PayK ITSELF AND OF THE WHOLE PROMISE OF K12's LAW's SECOND ARM, at the record tOFull of the proximity test O of the full-size stored example. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  member_OFull_true: Fixes is inhabited · PayK · PayY at 474 · PayRec · PayNum, OVER THE TRUE NAMES (each twin is its original by rfl: Coin/MemberOTrue.lean).
  dOFull · dOFull_facts (by the kernel on the literals): the first switch opens the book's places 1, 2, 7 under the declared sources own 1, own 2, own 7; the members' trees at 1 | 2, the mask's at 7.
  firstOpensOwn_OFull · promise_OFull (t₁ t₂): tOFull.roots = 7 ∧ (FirstOpensOwn piOFull (numAt t₁ t₂ 1) (fun z => t₁ + z) (t₁ + 7) tOFull ∧ PayRec piOFull tOFull): the three clauses of k12_lawRecFreeO's promise, whatever t₁, t₂.
  firstOpensOwn_OFull_moved: at base := t₁ + 6 it is false of the same record.
WHAT STAYS: that tOFull is the record which the verifier reaches on the stored file is nobody's word; THE LITERALS AT THE FULL SIZE HAVE NO WAY BACK (Law/LitOFull.lean's head) · «no := fun z => t₁ + z» is a choice of the table's letter, tied to no block in front · 7 = rootsOf pre at a written description: shown by nobody · no member of AtPlaceOwn here.

-/
import Johnson.Desc.K12.Coin.MemberOTrue
import Johnson.Desc.K12.Coin.FreeOff
import Johnson.Desc.K12.Law.MemberOFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (gpOf Plain)
open H2K.Member (piOFull tOFull rOFull member_OFull oF_v0 payY_of payRec_of payNum_of)
open H2K.Pin (PayRec)

theorem member_OFull_true :
    (∃ a rest G0 Ly D, Fixes piOFull tOFull a rest G0 Ly D) ∧
    H2K.Pin.PayK piOFull (fun s => rOFull s.st) 474 tOFull ∧
    PayY piOFull (fun s => rOFull s.st) 474 tOFull ∧
    H2K.Pin.PayRec piOFull tOFull ∧ H2K.Pin.PayNum piOFull tOFull := by
  have h := member_OFull.2.1
  have hY := payY_of member_OFull.2.1
  rw [oF_v0] at h hY
  exact ⟨member_OFull.1, h, hY, payRec_of member_OFull.2.1, payNum_of member_OFull.2.1⟩

theorem roots_OFull : tOFull.roots = 7 ∧ piOFull.nums.free = 7 := ⟨rfl, rfl⟩

/-- The plain data that the record fixes. -/
def dOFull : Option Plain :=
  match piOFull.nums.stages, tOFull.st.groups[tOFull.g]?, tOFull.st.layout tOFull.g with
  | a :: _, some G0, some Ly =>
    gpOf piOFull { tOFull with st := begun tOFull.st tOFull.g G0, pass := .nothing } a Ly
  | _, _, _ => none

theorem dOFull_facts :
    (dOFull.map fun D => (D.ts, D.opens.map (·.2), D.mems.map (·.t), D.fresh.t)) =
      some ([1, 2, 7], [.own 1, .own 2, .own 7], [1, 2], 7) := by
  decide +kernel

theorem dOFull_of {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout}
    {D : Plain} (hf : Fixes piOFull tOFull a rest G0 Ly D) :
    D.ts = [1, 2, 7] ∧ D.opens.map (·.2) = [.own 1, .own 2, .own 7] ∧
      D.mems.map (·.t) = [1, 2] ∧ D.fresh.t = 7 := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  have f5 : gpOf piOFull { tOFull with st := begun tOFull.st tOFull.g G0, pass := .nothing } a Ly =
      some D := f4 default
  have hD : dOFull = some D := by
    unfold dOFull
    rw [f1, f2, f3]
    exact f5
  have h := dOFull_facts
  rw [hD] at h
  have h' := Option.some.inj h
  exact ⟨congrArg (·.1) h', congrArg (·.2.1) h', congrArg (·.2.2.1) h', congrArg (·.2.2.2) h'⟩

/-- **`FirstOpensOwn` at the record, whatever the earlier chains' numbers of trees.** -/
theorem firstOpensOwn_OFull (t₁ t₂ : ℕ) :
    FirstOpensOwn piOFull (numAt t₁ t₂ 1) (fun z => t₁ + z) (t₁ + 7) tOFull := by
  intro a rest G0 Ly D hf
  obtain ⟨e1, e2, e3, e4⟩ := dOFull_of hf
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
    show t₁ + (D.mems.get i).t < t₁ + 7
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    omega
  · show t₁ + D.fresh.t = t₁ + 7
    rw [e4]

/-- **The whole promise of `k12_lawRecFreeO`, at the full-size record and whatever oracles.** -/
theorem promise_OFull (t₁ t₂ : ℕ) :
    tOFull.roots = 7 ∧ (FirstOpensOwn piOFull (numAt t₁ t₂ 1) (fun z => t₁ + z) (t₁ + 7) tOFull ∧
      PayRec piOFull tOFull) :=
  ⟨rfl, firstOpensOwn_OFull t₁ t₂, member_OFull_true.2.2.2.1⟩

/-- The clause can fail: at a base one lower it is false of the same record. -/
theorem firstOpensOwn_OFull_moved (t₁ t₂ : ℕ) :
    ¬ FirstOpensOwn piOFull (numAt t₁ t₂ 1) (fun z => t₁ + z) (t₁ + 6) tOFull := by
  intro h
  obtain ⟨a, rest, G0, Ly, D, hf⟩ := member_OFull_true.1
  obtain ⟨_, _, _, e4⟩ := dOFull_of hf
  have h3 : t₁ + D.fresh.t = t₁ + 6 := (h a rest G0 Ly D hf).2.2
  rw [e4] at h3
  omega

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.member_OFull_true
#print axioms VerifiableInference.Desc.K12.Coin.dOFull_facts
#print axioms VerifiableInference.Desc.K12.Coin.firstOpensOwn_OFull
#print axioms VerifiableInference.Desc.K12.Coin.promise_OFull
#print axioms VerifiableInference.Desc.K12.Coin.firstOpensOwn_OFull_moved
