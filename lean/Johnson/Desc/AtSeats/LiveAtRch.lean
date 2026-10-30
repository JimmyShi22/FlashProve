-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/LiveAtRch.lean: "THE COPY IN USE HAS THE PUBLIC SHAPE AND LAYOUT", ALONG
REACHED STATES, AT THE CLOSED CONSTANT (P5J.mgAtAll, Johnson/P5J/MgAtAll.lean), ONCE, IN THE THREE
FORMS THAT KIND K1's CLAUSES ASK.
By calls: liveShape_field and liveLayout_field (Johnson/IMR/AtReach.lean).
  liveIs_at_rch     LiveIs hA.𝔇.shape hA.𝔇.layout a.1.2 (Johnson/Desc/K1/Law/ArmAttEntry.lean) at
                    EVERY border, at every reached state without a mark: neither the promise nor
                    the place in front of the reads is spent
  liveLayout_at_rch its second half alone: a.1.2.live.rows.layout = hA.𝔇.layout (the form of
                    jHead_of_live's premise hl)
  partLive_at_rch   at the open part A (K9.segAt? a.1.2 = some A): A.L.check.frame.shape and
                    A.L.check.rows.layout are the public ones (the form of the field hlay on the
                    part in front)
  jLive_atAll       hJl's own type at J := JReach ‹reached, with a typed public part› …:
                    ∀ s, J s → LiveIs hA.𝔇.shape hA.𝔇.layout s (by jReach_elim)
hA.𝔇.shape is P5J.At.shape Zp and hA.𝔇.layout is P5J.At.layout Zp, by unfolding.
PREMISES: the shared head hA alone, "reached" (the wider RchAt), no mark.
What is not claimed. That hA can be met: NO MEMBER. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K01FactsOf
import Johnson.Desc.K1.Law.ArmAttEntry
import Johnson.Desc.K1.Law.JReach
import Johnson.Desc.K1.Law.PubAtLaterIndex

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Slice OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.Sound
open Johnson.Desc.First.Walk.Tied (RchAt RchPub rchAt_raw)
open ProofFile (Cl)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
include hA

/-- **The copy in use has the public shape and layout, at every reached state without a mark.** -/
theorem liveIs_at_rch {Str : Type} (j : ℕ) (a : (ProofFile.InstPub × S) × Str)
    (hr : RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) j a) (hm : a.1.2.failed = none) :
    LiveIs hA.𝔇.shape hA.𝔇.layout a.1.2 := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  have hpl : ∀ b ∈ cF.blocksInOrder, b.planOk = true := _root_.Meaning.K2.flat_planOk O.desc hA.laid.planOk
  exact ⟨_root_.Meaning.K2.liveShape_field hA.scope hA.reads O hpl _ id (fun _ _ q => q) j a.1
      (rchAt_raw hr) hm,
    _root_.Meaning.K2.liveLayout_field hA.scope hA.reads O hpl _ id (fun _ _ q => q) j a.1
      (rchAt_raw hr) hm⟩

/-- Its second half alone. -/
theorem liveLayout_at_rch {Str : Type} (j : ℕ) (a : (ProofFile.InstPub × S) × Str)
    (hr : RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) j a) (hm : a.1.2.failed = none) :
    a.1.2.live.rows.layout = hA.𝔇.layout := (liveIs_at_rch hA j a hr hm).2

/-- **At the open part.** -/
theorem partLive_at_rch {Str : Type} (j : ℕ) (a : (ProofFile.InstPub × S) × Str)
    (hr : RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) j a) (hm : a.1.2.failed = none) (A : K9.Part)
    (hseg : K9.segAt? a.1.2 = some A) :
    A.L.check.frame.shape = hA.𝔇.shape ∧ A.L.check.rows.layout = hA.𝔇.layout := by
  obtain ⟨_, hL, -, -, -⟩ := segAt_some hseg
  have hlive : a.1.2.live = A.L.check := by
    unfold S.live
    rw [hL]
  have h := liveIs_at_rch hA j a hr hm
  unfold LiveIs at h
  rw [hlive] at h
  exact h

/-- **hJl's own type**, at the invariant "reached in front of some segment's reads, inside the
promise, without a mark". -/
theorem jLive_atAll : ∀ s,
    JReach (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0).E.Str)
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) K13.Law.typedPub) hA.𝔇.N (mgAll hA.𝔇 mgBase) s →
    LiveIs hA.𝔇.shape hA.𝔇.layout s :=
  jReach_elim _ _ _ (LiveIs _ _) fun _ _ a hr _ hm => liveIs_at_rch hA _ a hr.1 hm

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.liveIs_at_rch
#print axioms VerifiableInference.Desc.K1.liveLayout_at_rch
#print axioms VerifiableInference.Desc.K1.partLive_at_rch
#print axioms VerifiableInference.Desc.K1.jLive_atAll
