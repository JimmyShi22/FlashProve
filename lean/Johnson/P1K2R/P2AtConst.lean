-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/P2AtConst.lean: code switching (K2): THE FIELD hp OF THE KIND's CONDITION
(Johnson/Top/H0/K2Ties/Assembly.lean: P2At r (pAt m)) AT THE SENTENCE's OWN NUMBERS pAt :=
ProofFile.pAtK2 Zp: entry m of the made table and the sentence's numbers at m declare the same two
entries. A join of Johnson/P1K2R/P2AtTable.lean with seated_is_pAt
(Johnson/Top/H0/K2Caller/PAtSeated.lean). NO BLOCK IMPORTS THIS FILE.
  nums_grp     the lot's numbers bear the group's number: numsAt P link = some n ⟹ n.grp =
               link.getD ‹the number of links›. By numsAt's text
  hp_at        tableOf pol lay KL = .ok t · pubPlain secondHashFunction pol lay KL = .ok Zp · blankBy
               pureRoad.links Zp = some G₀ · spotsFitB Zp = true · x a sub-protocol of the kind's
               bare table that passes its test on the plan · t[m]? = some r · (hm) at every P: x's
               place's link stands for group m + 1 ⟹ P2At r (ProofFile.pAtK2 Zp m)
  hp_written   the same at t := tableFullLit, from tableWrittenB's accept
WHAT STAYS, BY NAME: tableWrittenB pol lay KL = true (EVALUATED ONCE AT THE STORED FULL-SIZE
FILES; NO THEOREM)
(Where this and lean/THEOREM.md differ, the page
holds.) · spotsFitB Zp = true (by report a theorem at the
constant under the pin on the cut; not read here) · x, its
membership and its test on the plan · hm. No example. No soundness is claimed.
-/
import Johnson.P1K2R.P2AtTable
import Johnson.Top.H0.K2Caller.PAtSeated
import Johnson.Top.H0.K2Caller.TableWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Params OnBytes.Plan
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2Caller (SwRow P2At tableOf spotsFitB seated_is_pAt
  tableWrittenB tableWritten_is tableFullLit)

theorem nums_grp {P : Prep} {link : Option Nat} {n : Nums} (h : numsAt P link = some n) :
    n.grp = link.getD P.z.request.link.length := by
  unfold numsAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨f, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨lay, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨rd, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    rfl

theorem hp_at {pol lay KL : ByteArray} {t : List SwRow} (hT : tableOf pol lay KL = .ok t)
    {Zp : ProofFile.Pub} (hpub : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Zp) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (hSp : spotsFitB Zp = true)
    {x : Block S Unit} (hx : x ∈ pureTable (fun _ _ => some none) Zp G₀)
    (hxp : x.planOk = true) {m : Nat} {r : SwRow} (hr : t[m]? = some r)
    (hm : ∀ P, prepOf Zp G₀ = some P → x.place.link.getD P.z.request.link.length = m + 1) :
    P2At r (ProofFile.pAtK2 Zp m) := by
  obtain ⟨P, n, hP, hn, e, _⟩ := seated_is_pAt hG hSp hx hxp
  have hg : n.grp - 1 = m := by
    rw [nums_grp hn, hm P hP]
    rfl
  rw [hg] at e
  rw [e]
  exact p2At_table hT hpub hG hP hr (hm P hP) hn

theorem hp_written {pol lay KL : ByteArray} (hT : tableWrittenB pol lay KL = true)
    {Zp : ProofFile.Pub} (hpub : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Zp) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (hSp : spotsFitB Zp = true)
    {x : Block S Unit} (hx : x ∈ pureTable (fun _ _ => some none) Zp G₀)
    (hxp : x.planOk = true) {m : Nat} {r : SwRow} (hr : tableFullLit[m]? = some r)
    (hm : ∀ P, prepOf Zp G₀ = some P → x.place.link.getD P.z.request.link.length = m + 1) :
    P2At r (ProofFile.pAtK2 Zp m) :=
  hp_at (tableWritten_is hT) hpub hG hSp hx hxp hr hm

end P1K2

#print axioms P1K2.nums_grp
#print axioms P1K2.hp_at
#print axioms P1K2.hp_written
