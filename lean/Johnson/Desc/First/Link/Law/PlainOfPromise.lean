-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlainOfPromise.lean: THE TEST `plainThereB` (K5's files' item
"K5.plain") AT A STATE IN FRONT OF AN ATTENTION SEGMENT's BATCHING, DRAWN OUT OF THE TABLE's OWN
PROMISE THERE; AND SO THE TWO CLAUSES "entsFirst" AND "entsSecond" WITH ONE PREMISE FEWER.
No walk: a join of what lies, after another file's make (OkK5Paid.lean: `okThere_of_onQ`,
`okAtt_k5_at`). Statements and proofs.

The road. The promise at a state without a mark holds every public item that is open at the border
(`pub_of_onQ`, OkK5Paid.lean). At an attention segment m the item "more (some m) K5.plain" says, at
the composed meaning (`mgAll_pub`; `pubAll_more_plain`, Johnson/Desc/First/PubAllAt.lean): the test
plainThereB at the m / 2-th attention plan's iU3 and nW accepts the state.

  `plain_of_onQ`: there is the plan p at m / 2, and plainThereB p.iU3 p.nW accepts the state.
  `entsFirst_at`, `entsSecond_at`: **the two clauses at fixed9 φ (get a.1).2.**
PREMISES of the join. On the state: the promise (hon) and "no mark" (hu); the static clause at what
is fixed (hs). Closed: hatt (m is an attention segment); hq (the item is open at border k); hc (c's
iU3 and nW are those of the plan at m / 2); h0 (the third vector is planned with at least one
entry). On the fixed structure: hU (it names c.iU3 for the third vector). On the letters φ and rd:
hrd.
Limits. The closed premises are evaluated by nobody here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.EntsAtt
import Johnson.Desc.First.Link.Law.OkK5Paid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Pub Meaning pubSets pubAll_more_plain)
open VerifiableInference.Desc.First.Att.P (ParC)
open H2K5.Door (plainThereB)
open K5Law

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)

/-- At an attention segment at whose border the item is open the test accepts. -/
theorem plain_of_onQ {A : Type} {Fr : Frame} (get : A → P × S) (k m : ℕ) (a : A × Fr.E.Str)
    (hon : onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl get k a) (hu : (get a.1).2.failed = none)
    (hatt : 𝔇.pubD.d5.isAtt m = true)
    (hq : Pub.more (some m) "K5.plain" ∈ (pubSets (mgAll 𝔇 Mg₀).more links pl)[k]?.getD []) :
    ∃ p, 𝔇.pubD.d5.W.A[m / 2]? = some p ∧ plainThereB p.iU3 p.nW (get a.1).2 = true := by
  have h := pub_of_onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl get k a hon hu _ hq
  rw [mgAll_pub, pubAll_more_plain 𝔇.pubD Mg₀.pub m hatt] at h
  cases hp : 𝔇.pubD.d5.W.A[m / 2]? with
  | none =>
    rw [hp] at h
    exact absurd (show false = true from h) Bool.false_ne_true
  | some p =>
    rw [hp] at h
    exact ⟨p, rfl, h⟩

/-- **THE CLAUSE entsFirst, AT WHAT IS FIXED IN FRONT OF THE BATCHING.** -/
theorem entsFirst_at {A α : Type} {Fr : Frame} (get : A → P × S) (k m : ℕ) (a : A × Fr.E.Str)
    (hon : onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl get k a) (hu : (get a.1).2.failed = none)
    (hatt : 𝔇.pubD.d5.isAtt m = true)
    (hq : Pub.more (some m) "K5.plain" ∈ (pubSets (mgAll 𝔇 Mg₀).more links pl)[k]?.getD [])
    (c : ParC) (hc : ∀ p, 𝔇.pubD.d5.W.A[m / 2]? = some p → c.iU3 = p.iU3 ∧ c.nW = p.nW)
    (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α)
    (rd : α → Option (Forest.Heard × First.Att.P.Heard))
    (hrd : ∀ g h, rd (φ (get a.1).2) = some (g, h) → (get a.1).2.heard5? = some h)
    {nU : Array ℕ}
    (hs : ∀ tlb v, (π (fixed9 φ (get a.1).2).1).1 = some tlb →
      (fixed9 φ (get a.1).2).2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (π (fixed9 φ (get a.1).2).1).1 = some tlb →
      tlb.ix.U.getD 2 none = some c.iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ l, fsFirst rd c (fixed9 φ (get a.1).2) = some l →
      EntsAt π nU (fixed9 φ (get a.1).2) l := by
  obtain ⟨p, hp, hok⟩ := plain_of_onQ 𝔇 Mg₀ links pl get k m a hon hu hatt hq
  exact entsFirst_of_plain π φ rd c (by rw [(hc p hp).1, (hc p hp).2]; exact hok) hrd hs hU h0

/-- **THE CLAUSE entsSecond, AT WHAT IS FIXED IN FRONT OF THE BATCHING.** -/
theorem entsSecond_at {A α : Type} {Fr : Frame} (get : A → P × S) (k m : ℕ) (a : A × Fr.E.Str)
    (hon : onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl get k a) (hu : (get a.1).2.failed = none)
    (hatt : 𝔇.pubD.d5.isAtt m = true)
    (hq : Pub.more (some m) "K5.plain" ∈ (pubSets (mgAll 𝔇 Mg₀).more links pl)[k]?.getD [])
    (c : ParC) (hc : ∀ p, 𝔇.pubD.d5.W.A[m / 2]? = some p → c.iU3 = p.iU3 ∧ c.nW = p.nW)
    (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α)
    (rd : α → Option (Forest.Heard × First.Att.P.Heard))
    (hrd : ∀ g h, rd (φ (get a.1).2) = some (g, h) → (get a.1).2.heard5? = some h)
    {nU : Array ℕ}
    (hs : ∀ tlb v, (π (fixed9 φ (get a.1).2).1).1 = some tlb →
      (fixed9 φ (get a.1).2).2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (π (fixed9 φ (get a.1).2).1).1 = some tlb →
      tlb.ix.U.getD 2 none = some c.iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ l, fsSecond rd c (fixed9 φ (get a.1).2) = some l →
      EntsAt π nU (fixed9 φ (get a.1).2) l := by
  obtain ⟨p, hp, hok⟩ := plain_of_onQ 𝔇 Mg₀ links pl get k m a hon hu hatt hq
  exact entsSecond_of_plain π φ rd c (by rw [(hc p hp).1, (hc p hp).2]; exact hok) hrd hs hU h0

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.plain_of_onQ
#print axioms VerifiableInference.Desc.LinkJoin.entsFirst_at
#print axioms VerifiableInference.Desc.LinkJoin.entsSecond_at
