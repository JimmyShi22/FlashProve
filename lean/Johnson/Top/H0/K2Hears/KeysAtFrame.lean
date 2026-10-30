-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/KeysAtFrame.lean: the code switch: the four facts of KeysInScope.lean in the
letters of the structure that spends them (`KeysFit`, Johnson/Top/H0/K2Caller/AfterMade.lean): at
the frame F := frameAt (D.at a) (allOf (D.at a)) (D.at a).key₁ 0 and the stage
⟨F.a, q.base, F.all, [d₁, d₂], F.key, F.all⟩, which is the stage of the switch's piece at that frame
and base. One statement and its proof; no definition.

  `keys_at_frame`  ft ∧ first ∧ low ∧ old, field for field
Premises: those of `keys_in_scope`, and p.firstTree = 0 (FtAtPub.lean's `P1K2.ft_of_pub` has that of
the numbers that `P1K2.p2With` makes).
Limits. Those of KeysInScope.lean. This file does not import AfterMade.lean: that the four are
`KeysFit`'s fields is seen where its term is laid. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hears.KeysInScope
import Johnson.Desc.Sound.FileRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (numAt)
open VerifiableInference.Desc.Sound (Frame Piece Tiled rowData allOf Along RoundIs)
open _root_.Run.PQ (CK)
open LPFD.Full (proofDataAndDecisionOfPublicFiles RunPF)

/-- **The four facts, in the letters of the structure that spends them.** -/
theorem keys_at_frame {C : CK} {S Cl W : Type} {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
    {r : RunPF} (hZ : VerifierAndGoals.InScope Z = true) (h : proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r))
    (a : Nat) {F : Frame} (hF : F = Sound.frameAt (D.at a) (allOf (D.at a)) (D.at a).key₁ 0)
    (p₀ : Piece C F S Cl W) (l : List (Piece C F S Cl W)) (ht : Tiled p₀ l) (hb : p₀.base = 0)
    (hd : rowData p₀ l = D.ds₁) {k : Nat} {q : Piece C F S Cl W} (hq : (p₀ :: l)[k]? = some q)
    (p : P2) (hft : p.firstTree = 0) {t₁ t₂ : Nat} {d₁ d₂ : RDT} (hds : q.ds = [d₁, d₂])
    (hA : Along (RoundIs (numAt t₁ t₂ 0)) (rounds p) [d₁, d₂]) :
    F.ft = p.firstTree ∧
    (∀ j, j < (⟨F.a, q.base, F.all, [d₁, d₂], F.key, F.all⟩ : StageD).base →
      ((⟨F.a, q.base, F.all, [d₁, d₂], F.key, F.all⟩ : StageD).Lin.find? fun L =>
        (⟨F.a, q.base, F.all, [d₁, d₂], F.key, F.all⟩ : StageD).key L.no ==
          (⟨F.a, q.base, F.all, [d₁, d₂], F.key, F.all⟩ : StageD).key j).map (·.no) = some j) ∧
    (∀ x ∈ p.read, x.1 < 2 ^ 16) ∧
    ∀ d ∈ (⟨F.a, q.base, F.all, [d₁, d₂], F.key, F.all⟩ : StageD).ds, ∀ j ∈ d.opens,
      j < (⟨F.a, q.base, F.all, [d₁, d₂], F.key, F.all⟩ : StageD).base := by
  subst hF
  obtain ⟨k1, k2, k3, -⟩ := keys_in_scope hZ h p₀ l ht hb hd hq p hds hA a a
  exact ⟨hft.symm, k1, k2, hds ▸ k3⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.keys_at_frame
