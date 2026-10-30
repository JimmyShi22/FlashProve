-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OkK5Paid.lean: THE CLAUSE k5 OF "Ok AT AN ATTENTION LINK" (`OkAtt`,
OkOne.lean: for what is fixed before the batching's draw: the attention kind's
promise on filled slots, `K5OkAt`) AT WHAT IS FIXED AT A STATE IN FRONT OF THE BATCHING, FROM THE
TABLE's OWN PROMISE THERE. No walk: a join of what lies. Statements and proofs.

The road. The promise at a state without a mark holds every public item that is open at the border
(`pubHeld`). At an attention segment m the item "more (some m) K5.okAt" says, at the composed
meaning (mgAll_pub; pubAll_more_okAt, Johnson/Desc/First/PubAllAt.lean): the test okThereB at the
geometry of the m / 2-th attention plan accepts the state. Another file's law (H2K5.Door.ok_spent,
Johnson/Desc/First/Att/Door/Law/OkThereTie.lean) spends that test: the state's ledger U and what
the segment's own rounds handed on, hh, are there, and K5OkAt c zk hh U at every zk.

What is said.
  `pubHeld_of_onQ`: the promise at a state without a mark holds pubHeld, AT ANY BORDER AND MEANING
    (another file has the like at one border: pubHeld_of_on,
    Johnson/Top/H0/MergeLaw/TiedFull.lean). `pub_of_onQ`: so every public item that is open there.
  `okThere_of_onQ`: at the composed meaning, at an attention segment m at whose border the item is
    open: there is the plan p at m / 2, and okThereB (geoOf p.S) accepts the state.
  `k5_of_okThere`: **the clause's text at fixed9 φ s**, from the test's yes at c's geometry and
    hrd: "what rd reads off φ s as the kind's own hearing is the state's".
  `okAtt_k5_at`: **the join: OkAtt's field k5, to the letter, at q := fixed9 φ (get a.1).2.**

PREMISES of the join. On the state: the promise (hon) and "no mark" (hu). Closed: hatt (m is an
attention segment) · hq (the item is open at border k) · hc (c's geometry is that of the plan at m
/ 2). On the letters φ and rd: hrd.

Limits. The closed premises are evaluated by nobody here. hrd is a debt of whoever chooses φ and
rd. OF OkAtt's OTHER CLAUSES NOTHING IS SAID. Nothing on soundness.

-/
import Johnson.Desc.First.Att.Door.Law.OkThereTie
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Batch.BlindK3
import Johnson.Desc.First.Batch.Law.FitsAtS
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.BordersQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers start openSets pubSets pubHeld
  pubAll_more_okAt)
open VerifiableInference.Desc.First.Att.P (ParC)
open H2K5.Door (okThereB ok_spent)
open K5Law

/-- The promise at a state without a mark holds the public items' test. -/
theorem pubHeld_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × S) (k : ℕ) (a : A × Fr.E.Str)
    (h : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) :
    pubHeld Mg ((openSets links ps (start links))[k]?.getD [])
      ((pubSets Mg.more links ps)[k]?.getD []) (get a.1) = true := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · have e := h'.1
    simp only [Bool.and_eq_true] at e
    exact e.1.2

/-- So every public item that is open there. -/
theorem pub_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × S) (k : ℕ) (a : A × Fr.E.Str)
    (h : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) (q : Pub)
    (hq : q ∈ (pubSets Mg.more links ps)[k]?.getD []) : Mg.pub q (get a.1) = true :=
  List.all_eq_true.1 (pubHeld_of_onQ N Mg links ps get k a h hm) q (List.mem_append_left _ hq)

/-- **The clause's text, from the test's yes.** -/
theorem k5_of_okThere {α : Type} (c : ParC) (s : S) (hok : okThereB c.geo s = true) (φ : S → α)
    (rd : α → Option (Forest.Heard × First.Att.P.Heard))
    (hrd : ∀ g h, rd (φ s) = some (g, h) → s.heard5? = some h) :
    ∀ v g h, (fixed9 φ s).2 = some v → rd (fixed9 φ s).1 = some (g, h) →
      K5OkAt c g.zk h v.F := by
  obtain ⟨U, hh, hU, hH, H⟩ := ok_spent hok
  intro v g h hv hr
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hv
  obtain rfl : b.F = U := Option.some.inj ((K9.get_fork s b hb).symm.trans hU)
  obtain rfl : h = hh := Option.some.inj ((hrd g h hr).symm.trans hH)
  exact H g.zk

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)

/-- At an attention segment at whose border the item is open the test accepts. -/
theorem okThere_of_onQ {A : Type} {Fr : Frame} (get : A → P × S) (k m : ℕ) (a : A × Fr.E.Str)
    (hon : onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl get k a) (hu : (get a.1).2.failed = none)
    (hatt : 𝔇.pubD.d5.isAtt m = true)
    (hq : Pub.more (some m) "K5.okAt" ∈ (pubSets (mgAll 𝔇 Mg₀).more links pl)[k]?.getD []) :
    ∃ p, 𝔇.pubD.d5.W.A[m / 2]? = some p ∧
      okThereB (First.Att.P.geoOf p.S) (get a.1).2 = true := by
  have h := pub_of_onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl get k a hon hu _ hq
  rw [mgAll_pub, pubAll_more_okAt 𝔇.pubD Mg₀.pub m hatt] at h
  cases hp : 𝔇.pubD.d5.W.A[m / 2]? with
  | none =>
    rw [hp] at h
    exact absurd (show false = true from h) Bool.false_ne_true
  | some p =>
    rw [hp] at h
    exact ⟨p, rfl, h⟩

/-- **OkAtt's FIELD k5, TO THE LETTER, AT WHAT IS FIXED IN FRONT OF THE BATCHING.** -/
theorem okAtt_k5_at {A α : Type} {Fr : Frame} (get : A → P × S) (k m : ℕ) (a : A × Fr.E.Str)
    (hon : onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl get k a) (hu : (get a.1).2.failed = none)
    (hatt : 𝔇.pubD.d5.isAtt m = true)
    (hq : Pub.more (some m) "K5.okAt" ∈ (pubSets (mgAll 𝔇 Mg₀).more links pl)[k]?.getD [])
    (c : ParC) (hc : ∀ p, 𝔇.pubD.d5.W.A[m / 2]? = some p → c.geo = First.Att.P.geoOf p.S)
    (φ : S → α) (rd : α → Option (Forest.Heard × First.Att.P.Heard))
    (hrd : ∀ g h, rd (φ (get a.1).2) = some (g, h) → (get a.1).2.heard5? = some h) :
    ∀ v g h, (fixed9 φ (get a.1).2).2 = some v → rd (fixed9 φ (get a.1).2).1 = some (g, h) →
      K5OkAt c g.zk h v.F := by
  obtain ⟨p, hp, hok⟩ := okThere_of_onQ 𝔇 Mg₀ links pl get k m a hon hu hatt hq
  exact k5_of_okThere c _ (by rw [hc p hp]; exact hok) φ rd hrd

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pubHeld_of_onQ
#print axioms VerifiableInference.Desc.LinkJoin.pub_of_onQ
#print axioms VerifiableInference.Desc.LinkJoin.k5_of_okThere
#print axioms VerifiableInference.Desc.LinkJoin.okThere_of_onQ
#print axioms VerifiableInference.Desc.LinkJoin.okAtt_k5_at
