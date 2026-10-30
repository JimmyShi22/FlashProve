-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/SampleAtFirst.lean: no soundness is claimed.
The premise E₁ of sampleTwoB_last_end | sampleTwoB_h4 (SampleTwoEnd.lean) at j := 2 (behind the sub-protocol number 2 of the first chain's flat list, the request's first sending, the test accepts the index masks' message), carried from the seated sub-protocol's wrapped step down to kind K1's own decision decideSend, where the earning (P2Law.sampleAtB_behind_ok, Johnson/P2LawR/SampleBehindOk.lean) speaks.
hFirst is bound at two rounds that fit, with every factor's words below the prime, and at decideSend itself: K1.firstOwn's text is opened. At every list of rounds at which K1.firstOwn accepts it would ask more than the earning can give.
  firstOwn_mid    an accept of K1.firstOwn: a group is opened (the messages stay as many), then decideSend accepts, then the joining, which keeps SmpStay
  **e1_of_first**  HandsBackB c.blocksInOrder Rc · hCount₂ (in front of the first sending the statement has n₀ messages: asked only of a state from which that sub-protocol's step accepts, with no mark behind) · hFirst (at decideSend) ⇒ ∀ z s', Rc 3 (z, s') → sampleAtB cs sh s'.st (n₀ + kI) = true
Does not show. hFirst · hCount₂. No member. Nothing on soundness.
-/
import Johnson.ToldDescR.SmpWalk
import Johnson.ToldDescR.HandsBackB
import Johnson.IMR.FirstUnder
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Desc.K1.Law.OkView
import Johnson.Desc.K1.KeepsAtS
import Johnson.Desc.CoreKeepsSize
import Johnson.Desc.StepKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ToldDesc
open Meaning.K2
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (SmpStay groundKeeps_smpStay)

/-- An accept of the first sending's own text, opened. -/
theorem firstOwn_mid (P : K1.Par) (owed : Option Nat) (c : OnBytes.Model.ChainCheck)
    (d : _root_.Desc.Plain.DState Unit) (rs : List Fmt.RoundView)
    (y : OnBytes.Model.ChainCheck × _root_.Desc.Plain.DState Unit)
    (h : K1.firstOwn P owed c d rs = .ok y) :
    ∃ (d₁ : _root_.Desc.Plain.DState Unit) (ids : Array Nat)
      (d₂ : _root_.Desc.Plain.DState Unit), d₁.st.oracles.size = d.st.oracles.size ∧
      K1.decideSend P owed d₁ rs = .ok (ids, d₂) ∧ SmpStay d₂.st y.2.st := by
  unfold K1.firstOwn at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (K1.bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (K1.bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, h⟩ := (K1.bind_ok _ _ _).1 h
  cases h
  exact ⟨d₁, ids, d₂, Ground.newGroupP_size d d₁ _ _ g ((K1.named_ok _ _ _).1 h1), h2,
    K1.Rel.joinOwnP_keeps groundKeeps_smpStay _ _ _ _ _ _ ((K1.named_ok _ _ _).1 h3)⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **E₁ at j := 2, from kind K1's own decision at the first sending.** -/
theorem e1_of_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pp : Type}
    {Rc : ℕ → Pp × S → Prop} (hb : HandsBackB c.blocksInOrder Rc) {cs : Codes} {sh : OracleShape}
    {n₀ kI : ℕ}
    (hCount₂ : ∀ z s b ft rs cols s' n, Rc 2 (z, s) → c.blocksInOrder[2]? = some b →
      b.step ft s rs cols = .ok (s', n) → s'.failed = none → s.st.oracles.size = n₀)
    (hFirst : ∀ owed (d₁ : _root_.Desc.Plain.DState Unit) (r₁ r₂ : Fmt.RoundView) ids d₂,
      roundsFit (K1.rounds (K1.firstPar Bs.G₀.first (K1.gpOf Z))) [r₁, r₂] = true →
      (∀ x ∈ K1.seedsOf (K1.firstPar Bs.G₀.first (K1.gpOf Z)) r₁, okE x.2 = true) →
      K1.decideSend (K1.firstPar Bs.G₀.first (K1.gpOf Z)) owed d₁ [r₁, r₂] = .ok (ids, d₂) →
      sampleAtB cs sh d₂.st (d₁.st.oracles.size + kI) = true) :
    ∀ z s', Rc 3 (z, s') → sampleAtB cs sh s'.st (n₀ + kI) = true := by
  intro z s' h
  obtain ⟨s₁, b, ft, rs, cols, n, r1, hk, hyB⟩ := hb 2 z s' h
  obtain ⟨hy, cv, hv⟩ := below_step hyB
  obtain ⟨Lk, b0, e1, e2, hj⟩ := IM.k1_first_sits hS hR O
  have hix : IM.flatIx c 0 0 = 2 := IM.flatIx_scope hS hR O (l := 0) (by decide) 0
  have hfl : c.blocksInOrder[2]? = some b0 := by
    have k := IM.hear_at_flat e1 e2
    rwa [hix] at k
  obtain rfl : b0 = b := Option.some.inj (hfl.symm.trans hk)
  obtain ⟨fs, f, m, hfs, hf, hst, -, hop, hmk, -⟩ := hj.step hy
  obtain ⟨hfit, gs, hd⟩ := Keeps.step_fit ft _ s₁ m rs cols n hst
  have hl := Keeps.fit_length _ _ hfit
  obtain ⟨q₁, q₂, rfl⟩ : ∃ q₁ q₂, rs = [q₁, q₂] := by
    match rs, hl with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨x, d', hO, est, -⟩ := K1.firstAtS_ok (Cl := Unit) _ _ s₁ m _ gs hd
  obtain ⟨d₁, ids, d₂, hsz, hdS, hst2⟩ := firstOwn_mid _ _ _ _ _ _ hO
  have a := hFirst _ d₁ (noDigest q₁) (noDigest q₂) ids d₂ hfit
    (K1.okView_factors _ _ _ (by simp) hv) hdS
  have e0 : d₁.st.oracles.size = n₀ := hsz.trans (hCount₂ z s₁ _ _ _ _ _ _ r1 hk hy hmk)
  rw [e0] at a
  have a' : sampleAtB cs sh m.st (n₀ + kI) = true := by
    rw [est]
    exact sampleAtB_stay a hst2
  have k : SmpStay m.st s'.st :=
    (framesOf_byQ stQuiet_smpStay hfs f (List.mem_of_getElem? hf)).2.1 m s' hop
  exact sampleAtB_stay a' k

end

end ToldDesc

#print axioms ToldDesc.firstOwn_mid
#print axioms ToldDesc.e1_of_first
