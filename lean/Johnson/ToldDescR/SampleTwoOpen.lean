-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/SampleTwoOpen.lean: no soundness is claimed.
h₄ (sampleTwoB cs V at the first chain's reached ends; the premise of five_at_end_in (declared nowhere in this library) at B₄ := sampleTwoB cs V), at the proof file's IOP as written in Lean, in the letters of the opening IM.Open (Johnson/IMR/SeatOpen.lean).
The family hands back the wrapped step (HandsBackB), and the earning is called: P2Law.sampleAtB_behind_ok (Johnson/P2LawR/SampleBehindOk.lean).
  **sampleTwoB_h4_open**   the walk, the join and the two carryings in one call; hFirst | hSend in the form that fits the earning
  **sampleTwoB_h4_paid**   in the place of hFirst | hSend: closed facts on the two sendings' parameters (PlanAtSend: condPort · the place k is sampled · its shape · the codes) and SampleStep at the two numbers (sampleL_at_index | sampleL_at_W, Johnson/IMR/SampleAtW.lean, pay it under madeRow)
What stays in _paid, by name: hEnd (four facts at the last state, fenced) · hCount (356, fenced) · hCount₂ (2) · the two PlanAtSend · the two SampleStep · hE.
Does not show. Any of these. No member. Nothing on soundness.
-/
import Johnson.ToldDescR.SampleTwoEnd
import Johnson.ToldDescR.SmpWalkOpen
import Johnson.ToldDescR.SampleAtW
import Johnson.ToldDescR.SampleAtFirst
import Johnson.P2LawR.SampleBehindOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ToldDesc
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (S)

/-- **Closed facts on a sending's parameters**: K1's own test on them passes at some radii; the
place k of the sending is sampled, has the shape sh, and the codes are cs. -/
def PlanAtSend (P : K1.Par) (cs : Codes) (sh : OracleShape) (k : ℕ) : Prop :=
  (∃ rad, K1.condPort P rad = true) ∧ P.codes = cs ∧
    ∃ i : Fin (K1.shapesOf P).length, i.val = k ∧ K1.sampledAt P i ∧ K1.shapeAt P i = sh

/-- The earning, at such parameters. -/
theorem sampleAtB_at_send {L : Type} {P : K1.Par} {cs : Codes} {sh : OracleShape} {k : ℕ}
    (H : PlanAtSend P cs sh k) (owed : Option Nat) (d d' : _root_.Desc.Plain.DState L)
    (r₁ r₂ : Fmt.RoundView) (ids : Array Nat) (hfit : roundsFit (K1.rounds P) [r₁, r₂] = true)
    (hok : ∀ x ∈ K1.seedsOf P r₁, okE x.2 = true)
    (hyes : K1.decideSend P owed d [r₁, r₂] = .ok (ids, d'))
    (hL : P2Law.SampleStep cs sh (d.st.oracles.size + k)) :
    sampleAtB cs sh d'.st (d.st.oracles.size + k) = true := by
  obtain ⟨⟨rad, hC⟩, rfl, i, rfl, hk, rfl⟩ := H
  exact P2Law.sampleAtB_behind_ok P rad owed d d' r₁ r₂ ids hC hfit hyes hok i hk hL

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **h₄ at the opening.** -/
theorem sampleTwoB_h4_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true)
    {Pp : Type} {Rch : ℕ → Pp × S → Prop} (hb : HandsBackB c.blocksInOrder Rch) {cs : Codes}
    {V : OwnSeats} {n₀ kI nW : ℕ}
    (hEnd : ∀ z s, Rch 358 (z, s) → s.failed = none → ownSitsB V s = true ∧
      bookFitsB s.book = true ∧ s.book.place[n₀ + kI]? = some V.index ∧
      s.book.place[nW]? = some V.w)
    (hCount : ∀ z s₁, Rch 356 (z, s₁) → s₁.failed = none → s₁.st.oracles.size = nW)
    (hCount₂ : ∀ z s b ft rs cols s' n, Rch 2 (z, s) → c.blocksInOrder[2]? = some b →
      b.step ft s rs cols = .ok (s', n) → s'.failed = none → s.st.oracles.size = n₀)
    (hFirst : ∀ owed (d₁ : _root_.Desc.Plain.DState Unit) (r₁ r₂ : Fmt.RoundView) ids d₂,
      roundsFit (K1.rounds (K1.firstPar Bs.G₀.first (K1.gpOf Z))) [r₁, r₂] = true →
      (∀ x ∈ K1.seedsOf (K1.firstPar Bs.G₀.first (K1.gpOf Z)) r₁, okE x.2 = true) →
      K1.decideSend (K1.firstPar Bs.G₀.first (K1.gpOf Z)) owed d₁ [r₁, r₂] = .ok (ids, d₂) →
      sampleAtB cs V.indexShape d₂.st (d₁.st.oracles.size + kI) = true)
    (hSend : ∀ msg (s : S) (r₁ r₂ : Fmt.RoundView) ids d', linMessageW Z.first.lin = some msg →
      roundsFit (K1.rounds
        (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg))
        [r₁, r₂] = true →
      (∀ x ∈ K1.seedsOf
        (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg) r₁,
        okE x.2 = true) →
      K1.decideSend (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg)
        (K1.owedOf s) (K1.stateOf s (#[] : Array Nat)) [r₁, r₂] = .ok (ids, d') →
      sampleAtB cs V.wShape d'.st s.st.oracles.size = true)
    {Q P₀ : Type} (get : Q → P₀ × S) (Oc : Q → Strs → Prop) (Rc : Q → Prop)
    (hE : ∀ q y, Oc q y → Rc q → ∃ z, Rch 358 (z, (get q).2)) :
    ∀ q y, Oc q y → Rc q → (get q).2.failed = none → sampleTwoB cs V (get q).2 = true :=
  sampleTwoB_h4 hb.plain (open_smpStay hF O) (open_planOk O hp) hEnd 2 (by decide)
    (e1_of_first hS hR O hb hCount₂ hFirst) (e2_of_send hS hR O hb hCount hSend) get Oc Rc hE

/-- **h₄ at the opening, the earning called.** -/
theorem sampleTwoB_h4_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true)
    {Pp : Type} {Rch : ℕ → Pp × S → Prop} (hb : HandsBackB c.blocksInOrder Rch) {cs : Codes}
    {V : OwnSeats} {n₀ kI nW : ℕ}
    (hEnd : ∀ z s, Rch 358 (z, s) → s.failed = none → ownSitsB V s = true ∧
      bookFitsB s.book = true ∧ s.book.place[n₀ + kI]? = some V.index ∧
      s.book.place[nW]? = some V.w)
    (hCount : ∀ z s₁, Rch 356 (z, s₁) → s₁.failed = none → s₁.st.oracles.size = nW)
    (hCount₂ : ∀ z s b ft rs cols s' n, Rch 2 (z, s) → c.blocksInOrder[2]? = some b →
      b.step ft s rs cols = .ok (s', n) → s'.failed = none → s.st.oracles.size = n₀)
    (hP₁ : PlanAtSend (K1.firstPar Bs.G₀.first (K1.gpOf Z)) cs V.indexShape kI)
    (hP₂ : ∀ msg, linMessageW Z.first.lin = some msg → PlanAtSend
      (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg) cs V.wShape 0)
    (hL₁ : ∀ o, P2Law.SampleStep cs V.indexShape o) (hL₂ : ∀ o, P2Law.SampleStep cs V.wShape o)
    {Q P₀ : Type} (get : Q → P₀ × S) (Oc : Q → Strs → Prop) (Rc : Q → Prop)
    (hE : ∀ q y, Oc q y → Rc q → ∃ z, Rch 358 (z, (get q).2)) :
    ∀ q y, Oc q y → Rc q → (get q).2.failed = none → sampleTwoB cs V (get q).2 = true :=
  sampleTwoB_h4_open hS hR hF O hp hb hEnd hCount hCount₂
    (fun owed d₁ r₁ r₂ ids d₂ hfit hok hyes =>
      sampleAtB_at_send hP₁ owed d₁ d₂ r₁ r₂ ids hfit hok hyes (hL₁ _))
    (fun msg s r₁ r₂ ids d' hm hfit hok hyes =>
      sampleAtB_at_send (hP₂ msg hm) _ _ d' r₁ r₂ ids hfit hok hyes (hL₂ _))
    get Oc Rc hE

end

end ToldDesc

#print axioms ToldDesc.sampleAtB_at_send
#print axioms ToldDesc.sampleTwoB_h4_open
#print axioms ToldDesc.sampleTwoB_h4_paid
