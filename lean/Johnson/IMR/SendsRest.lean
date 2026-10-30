-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsRest.lean: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre»
(Johnson/Desc/Sound/SmpPlaces.lean): THE DEBT SendsOn (Johnson/IMR/SendsFold.lean) AT THE BATCHING
AND AT THE SUB-PROTOCOL BEHIND IT, AT THE LINKS l < 24: 48 NUMBERS: THEY SEND NOTHING.
BY A TOOL, CALLED (Johnson/IMR/LinkRest.lean · Johnson/Goal/Meaning/RunsKeep.lean): hear_runs: every hearing sub-protocol's RUNS (of claims; behind the batching) keep R, for every reflexive, transitive R that Quiet implies: the senders' makers have no run · rest_by · link_behind_runs; its one premise «the link's first sub-protocol accepts
somewhere» is drawn from «reached» (reached_accepts). AT R := CalmG: «the number of oracle messages, the book and the count of roots stay, and the statement grows» (batch_three | batch_grows · closeOf_three | closeOf_grows).
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
  CalmG · calmG_refl | _trans | _of_quiet   the relation.
  first_accepts     at a state reached behind a link's first place, that place's sub-protocol's decision has accepted somewhere.
  sends_batch · sends_behind   the two debts at l < 24.
What is not claimed. The head's link (l = 24): two numbers. No soundness.
-/
import Johnson.IMR.SendsArms
import Johnson.IMR.LinkRest

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (Core ByC)
open VerifiableInference.Desc.K1.RelCore (coreS)
open Meaning.K2 (Quiet GR)
open ProofFile (Cl)

/-- The number of oracle messages, the book and the count of roots stay, and the statement grows. -/
def CalmG (s t : S) : Prop := ByC ThreeC coreS s t ∧ GR s t

theorem calmG_refl (s : S) : CalmG s s := ⟨⟨rfl, rfl, rfl⟩, Meaning.K2.gr_refl s⟩

theorem calmG_trans (a b c : S) (h : CalmG a b) (k : CalmG b c) : CalmG a c :=
  ⟨⟨k.1.1.trans h.1.1, k.1.2.1.trans h.1.2.1, k.1.2.2.trans h.1.2.2⟩,
    Meaning.K2.gr_trans a b c h.2 k.2⟩

theorem calmG_of_quiet (s t : S) (q : Quiet s t) : CalmG s t := by
  have e : t.st = s.st := q.1.1
  refine ⟨⟨by show t.st.oracles.size = s.st.oracles.size; rw [e], q.1.2.2.1, q.1.2.2.2⟩, ?_⟩
  have := Meaning.K2.gr_refl s
  show VerifiableInference.Desc.Grows s.st t.st
  rw [e]
  exact this

theorem calmG_batch (p : VerifiableInference.Desc.K9.Where)
    {claims : S → Except String (List Cl × S)}
    (h : FnCl CalmG claims) :
    Decides CalmG (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p claims) :=
  fun s rs gs t hy =>
    ⟨(Meaning.K2.batch_three three_h3
        (fun h k => ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.trans h.2.2⟩) p
        (fun s y e => (h s y e).1)).1 s rs gs t hy,
      (Meaning.K2.batch_grows p (fun s y e => (h s y e).2)).1 s rs gs t hy⟩

theorem calmG_close (p : VerifiableInference.Desc.K9.Where)
    (Q : VerifiableInference.Desc.First.Close.Par) :
    ∀ x ∈ VerifiableInference.Desc.K9.closeOf (Cl := Unit) p Q, Decides CalmG x :=
  fun x hx s rs gs t hy =>
    ⟨(Meaning.K2.closeOf_three (Cl := Unit) three_h3 p Q x hx).1 s rs gs t hy,
      (Meaning.K2.closeOf_grows (Cl := Unit) p Q x hx).1 s rs gs t hy⟩

theorem sends_of_calmG {ft : ℕ} {codes : Codes} {b : Block S Cl} (h : Decides CalmG b) :
    SendsAt ft codes [] b :=
  sends_of_calm fun s rs gs t hy => calm_of (h s rs gs t hy).1 (h s rs gs t hy).2

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- At a state reached behind a link's first place, that place's sub-protocol's decision has accepted somewhere. -/
theorem first_accepts (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {s₀ s : S} {l j : ℕ}
    (hl : l < 25) (hj : 14 * l + 2 < j) (hg : ReachedAt ft c.blocksInOrder s₀ j s) {Lk : Link S Cl}
    (e1 : c.links[l]? = some Lk) :
    ∀ b₀, Lk.hear[0]? = some b₀ → ∃ s rs gs t, b₀.decide s rs gs = .ok t := by
  intro b₀ e0
  have hix := hear_at_flat e1 e0
  rw [flatIx_scope hS hR O (by omega) 0] at hix
  obtain ⟨u, rs, cols, u', n, hy⟩ := reached_accepts hg (i := 14 * l + 0 + 2) (by omega) hix
  exact ⟨u, _, _, u', (VerifiableInference.Desc.step_inv ft b₀ u u' rs cols n hy).2.2.2⟩

/-- **THE BATCHING, l < 24.** -/
theorem sends_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {codes : Codes} {s₀ : S}
    {l : ℕ} (hl : l < 24) {Lk : Link S Cl} (e1 : c.links[l]? = some Lk) :
    SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + nAt l + 2)) []
      (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)) := by
  intro s s' rs cols n hg hy hc
  have hy0 := first_accepts hS hR O (by omega) (by unfold nAt; split <;> omega) hg e1
  obtain ⟨Lk', p, w, T, eL', -, -, -, -, -, hal, -, -⟩ := (k9_of hS hR O).2 l (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans eL')
  have hruns := Meaning.K2.hear_runs calmG_refl calmG_trans calmG_of_quiet hS hR O hl e1 hy0
  exact ((sends_of_calmG (calmG_batch p
    (Meaning.K2.link_claims_runs calmG_refl calmG_trans Lk hruns))).under (alone_underR (hal _)))
    s s' rs cols n hy hc

/-- **THE SUB-PROTOCOL BEHIND THE BATCHING, l < 24.** -/
theorem sends_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {codes : Codes} {s₀ : S}
    {l : ℕ} (hl : l < 24) {Lk : Link S Cl} {b : Block S Cl} (e1 : c.links[l]? = some Lk)
    (hd : ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) :
    SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + nAt l + 3)) [] b := by
  intro s s' rs cols n hg hy hc
  have hy0 := first_accepts hS hR O (by omega) (by unfold nAt; split <;> omega) hg e1
  have hruns := Meaning.K2.hear_runs calmG_refl calmG_trans calmG_of_quiet hS hR O hl e1 hy0
  exact (sends_of_calmG (b := b) fun u rs' gs' t h =>
    Meaning.K2.link_behind_runs calmG_refl calmG_trans Lk hruns u t (by rw [← hd u rs' gs']; exact h))
    s s' rs cols n hy hc

end

end IM

#print axioms IM.first_accepts
#print axioms IM.sends_batch
#print axioms IM.sends_behind
