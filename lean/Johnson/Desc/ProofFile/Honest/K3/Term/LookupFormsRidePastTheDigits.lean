-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupFormsRidePastTheDigits.lean: the kind "lookup" (K3): an item
"forms" that is open on both sides of a lookup on the digits rides past it: `RidesPastAtS`
(Honest/Thread/SharesS.lean) at that item, at the first chain's thread of `lettersHead`
(Honest/Thread/FirstHead.lean) with "keeps" by the place's kind (`kpBy f`).

What is shown.
  `partsStayOverTheDigits`, `partsStayOverTheHeadsDigits`: under the lookups' own clause of "keeps"
    at the digits, the open link's part is there behind, with the same link, statement and book and
    a later ledger.
  `keepsAreTheKindsClauseAtTheBorder`: the thread's "keeps" at a lookup's border is f at the kind K3
    at the lookup's place.
  `formsItemRidesPastTheDigits`: the statement above.

Hypotheses that remain, at `formsItemRidesPastTheDigits`.
  `h`: the library's hypothesis `P5J.AtMgA` at the hash function `secondHashFunction`. H, Q, test, carryX, item,
    n₁, n₂, b₀, Vd, Rd, f, w, `Said` are variables. l < 25.
  On the letter f, at the kind K3 and the place of the lookup on the digits, three arrows:
    `keepsGivesTheLookupClause`: to the lookups' own clause `k3KeepsAt`;
    `keepsGivesTheFormsTestsBehind`: to "the public tests of the items forms open behind hold behind";
    `keepsGivesThatTheReadersStay`: to "the readers' answers at the runs of an item forms open on both
      sides stay".
  `openInFront`, `openBehind`: the item stands in the table's two lists of open items.
  `weightsGoOn`: at the name "weights" alone: the sentence on the weights passes.

Limits. An implication. Nothing here shows that the invariant holds at any run, or that f has the
three arrows at the value that the thread's authors give it. At the full size alone.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupFormsGoOn
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBehindAndRidesPast
import Johnson.Desc.First.Batch.FormsPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Chain Place Strs KindName)
open VerifiableInference.Desc.First (Item Pub pubOfItems)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (segAt_cut segAt_make)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script head_keeps_kind)
open ProofFile.Honest.K3.Law.AtThr

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 On states alone -/

theorem partsStayOverTheDigits {sh : OnBytes.Model.Forest.Shape} {claims : Nat} {s s' : FS}
    (hK : K3KeepsDigits sh claims s s') :
    ∀ a, segAt? s = some a → ∃ b, segAt? s' = some b ∧ b.L = a.L ∧ b.d.st = a.d.st ∧
      b.d.book = a.d.book ∧ _root_.Fo.Later a.F b.F := by
  intro a ha
  have hSame := keepsDigits_sameBut hK
  obtain ⟨_, tl, F, Hd, G, _, hF, hA, hL⟩ := hK
  obtain ⟨h1, h2, _, h4, h5⟩ := segAt_cut ha
  have eF : a.F = F := Option.some.inj (h2.symm.trans hF)
  have hG : s'.fork? = some { G with planClaimsF := claims } ∧ s'.tl?.isSome = true := by
    rcases hA with ⟨a₁, _, e⟩ | ⟨a₁, _, e⟩ | ⟨a₁, _, ho, e⟩
    · rw [e]
      exact ⟨rfl, rfl⟩
    · rw [e]
      exact ⟨rfl, rfl⟩
    · rw [e]
      exact ⟨by simp [VerifiableInference.Desc.First.S.fork?, ho],
        by simp [VerifiableInference.Desc.First.S.tl?, ho]⟩
  obtain ⟨b, hb, e1, e2, e3, e4⟩ := segAt_make (hSame.link.trans h1) hG.1 hG.2
  refine ⟨b, hb, e1, by rw [e3, hSame.st, h4], by rw [e4, hSame.book, h5], ?_⟩
  rw [eF, e2]
  exact ⟨hL.1.next, hL.1.ns, hL.1.keep⟩

theorem partsStayOverTheHeadsDigits {sh : OnBytes.Model.Forest.Shape} {s s' : FS}
    (hK : K3KeepsHead sh s s') :
    ∀ a, segAt? s = some a → ∃ b, segAt? s' = some b ∧ b.L = a.L ∧ b.d.st = a.d.st ∧
      b.d.book = a.d.book ∧ _root_.Fo.Later a.F b.F := by
  intro a ha
  have hSame := keepsHead_sameBut hK
  obtain ⟨_, tl, F, Hd, G, a₀, claim, _, hF, _, ho, e, hL⟩ := hK
  obtain ⟨h1, h2, _, h4, h5⟩ := segAt_cut ha
  have eF : a.F = F := Option.some.inj (h2.symm.trans hF)
  have hG : s'.fork? = some G ∧ s'.tl?.isSome = true := by
    rw [e]
    exact ⟨by simp [VerifiableInference.Desc.First.S.fork?, ho],
      by simp [VerifiableInference.Desc.First.S.tl?, ho]⟩
  obtain ⟨b, hb, e1, e2, e3, e4⟩ := segAt_make (hSame.link.trans h1) hG.1 hG.2
  refine ⟨b, hb, e1, by rw [e3, hSame.st, h4], by rw [e4, hSame.book, h5], ?_⟩
  rw [eF, e2]
  exact ⟨hL.1.next, hL.1.ns, hL.1.keep⟩

/-- The public test that is tied to an open item "forms" stands in the list of tied tests. -/
theorem formsTestIsTiedToTheOpenItem {O : List Item} {mm kk : Nat} {ρ : String}
    (itemIsOpen : Item.forms mm kk ρ ∈ O) : Pub.formsIn mm kk ρ ∈ pubOfItems O := by
  unfold pubOfItems
  exact List.mem_flatMap.2 ⟨_, itemIsOpen, (List.mem_singleton.2 rfl : _ ∈ [Pub.formsIn mm kk ρ])⟩

-- from here on the closed lists are not unfolded
attribute [local irreducible] IM.openAt VerifiableInference.Desc.First.flatPlacesOf

/-! ## 2 At the thread -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LK" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w

/-- The thread's "keeps" at a lookup's border is f at the kind K3 at the lookup's place. -/
theorem keepsAreTheKindsClauseAtTheBorder {l : Nat} (linkBelow : l < 25) (d : Bool) {t t' : TS}
    (hk : (LK).thread.keeps (borderOf l d) t t') : f .K3 (IM.k3Place l d) t t' := by
  obtain ⟨blk, hblk, hp⟩ := member_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w l linkBelow d
  have hkind : blk.place.kind = KindName.K3 := by rw [hp]
  have h1 := (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hblk hkind t t').1 hk
  rw [hp] at h1
  exact h1

/-- **An item "forms" that is open on both sides of a lookup on the digits rides past it.**
Conditional on what this file's head lists. -/
theorem formsItemRidesPastTheDigits
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat} (linkBelow : l < 25)
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t')
    (keepsGivesTheFormsTestsBehind : ∀ t t', f .K3 (IM.k3Place l true) t t' →
      ∀ q ∈ pubOfItems (IM.openAt P5J.At.links P5J.At.ps
          (VerifiableInference.Desc.First.borderOf P5J.At.ps (some (IM.k3Place l true)) + 1)),
        VerifiableInference.Desc.K9.pubForms h.𝔇.pubD.Rd h.𝔇.pubD.runs h.𝔇.pubD.ah h.𝔇.pubD.N
          (fun _ (_ : Unit × TS) => true) q ((), t') = true)
    (keepsGivesThatTheReadersStay : ∀ t t', f .K3 (IM.k3Place l true) t t' → ∀ mm kk ρ,
      Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps
        (VerifiableInference.Desc.First.borderOf P5J.At.ps (some (IM.k3Place l true))) →
      Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps
        (VerifiableInference.Desc.First.borderOf P5J.At.ps (some (IM.k3Place l true)) + 1) →
      ∀ q ∈ h.𝔇.pubD.runs mm kk ρ,
        VerifiableInference.Reads.Pass.Fwd (h.𝔇.pubD.Rd mm) q.1 q.2 t t')
    {mm kk : Nat} {ρ : String}
    (openInFront : Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps
      (VerifiableInference.Desc.First.borderOf P5J.At.ps (some (IM.k3Place l true))))
    (openBehind : Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps
      (VerifiableInference.Desc.First.borderOf P5J.At.ps (some (IM.k3Place l true)) + 1))
    (weightsGoOn : ρ = "weights" → ∀ (k : Coins Bk) (s : TS)
      (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (s' : TS) (y y' : Strs) (v : WtF),
      ThrS (LK).thread Said (borderOf l true) k s m E → (LK).thread.keeps (borderOf l true) s s' →
      h.𝔇.wt mm (m.st.input.x.pub, s) y v → h.𝔇.wt mm (m.st.input.x.pub, s') y' v) :
    RidesPastAtS (LK).thread Said (borderOf l true) (Item.forms mm kk ρ) := by
  intro k s m E s' ps v hA hK h0
  have hfK := keepsAreTheKindsClauseAtTheBorder h H Q test carryX item n₁ n₂ b₀ Vd Rd f w linkBelow
    true hK
  have hk := keepsGivesTheLookupClause _ _ _ hfK
  have hParts : ∀ a, segAt? s = some a → ∃ b, segAt? s' = some b ∧ b.L = a.L ∧
      b.d.st = a.d.st ∧ b.d.book = a.d.book ∧ _root_.Fo.Later a.F b.F := by
    by_cases e : l = 24
    · subst e
      obtain ⟨sh, hD⟩ := lookupClauseAtTheHeadsDigits h hk
      exact partsStayOverTheHeadsDigits hD
    · obtain ⟨sh, c, hD⟩ := lookupClauseAtTheDigits h (by omega) hk
      exact partsStayOverTheDigits hD
  exact lookupFormsItemGoesOn
    { h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX } mgBase
    m.st.input.x.pub ((LK).thread.strs E) ((LK).thread.strs (E.add ps)) v hParts
    (keepsGivesThatTheReadersStay s s' hfK mm kk ρ openInFront openBehind)
    (keepsGivesTheFormsTestsBehind s s' hfK _ (formsTestIsTiedToTheOpenItem openBehind))
    (fun e => weightsGoOn e k s m E s' ((LK).thread.strs E) ((LK).thread.strs (E.add ps)) v hA hK) h0

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.partsStayOverTheDigits
#print axioms ProofFile.Honest.K3.Term.partsStayOverTheHeadsDigits
#print axioms ProofFile.Honest.K3.Term.formsTestIsTiedToTheOpenItem
#print axioms ProofFile.Honest.K3.Term.keepsAreTheKindsClauseAtTheBorder
#print axioms ProofFile.Honest.K3.Term.formsItemRidesPastTheDigits
