-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeysScope.lean: the code switch: THE STRUCTURE `KeysFit` (AfterMade.lean) IN
THE GOALS' SCOPE: so `cols_shownP` and `lawAfter_light` are called with no premise on the trees'
keys left. One theorem: four facts that another file proves, laid as the structure's fields.

Main names:
  `keysFit_in_scope`: under the scope's test, the yes of the laying of the public values, and the
    rule of composition's own facts on the first chain's row of pieces (it tiles; it starts at base
    0; its data are the file's; the piece at k has two written rounds that go along the switch's
    declared rounds) and p.firstTree = 0: `KeysFit` at the frame of the whole file, at the piece's
    own base. By `K2.keys_at_frame` (Johnson/Top/H0/K2Hears/KeysAtFrame.lean).
Limits. Those of KeysAtFrame.lean and KeysInScope.lean: the full size alone; two of the four facts
rest on closed facts on the written lists, checked by Lean's kernel. Nothing on soundness. On hiding
nothing.

-/
import Johnson.Top.H0.K2Caller.AfterMade
import Johnson.Top.H0.K2Hears.KeysAtFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (numAt)
open VerifiableInference.Desc.Sound (Frame Piece Tiled rowData allOf Along RoundIs)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open LPFD.Full (proofDataAndDecisionOfPublicFiles RunPF)

/-- **`KeysFit` IN THE GOALS' SCOPE**, at every piece of the first chain's row that holds a code
switch: the four facts of `K2.keys_at_frame` (Johnson/Top/H0/K2Hears/KeysAtFrame.lean) laid as the
structure's fields. General in the law's letters: the structure reads of them the piece's stage, the
trees that the switch reads and its first tree alone. -/
theorem keysFit_in_scope {C : CK} {S Cl W W₁ : Type} {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles}
    {D : WholeD} {rn : RunPF} (hZ : VerifierAndGoals.InScope Z = true)
    (h : proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, rn)) (a : ℕ) {F : Frame}
    (hF : F = VerifiableInference.Desc.Sound.frameAt (D.at a) (allOf (D.at a)) (D.at a).key₁ 0)
    (p₀ : Piece C F S Cl W) (l : List (Piece C F S Cl W)) (ht : Tiled p₀ l) (hb : p₀.base = 0)
    (hd : rowData p₀ l = D.ds₁) {k : ℕ} {q : Piece C F S Cl W} (hq : (p₀ :: l)[k]? = some q)
    (p : K2.P2) (hft : p.firstTree = 0) {t₁ t₂ : ℕ} {d₁ d₂ : RDT} (hds : q.ds = [d₁, d₂])
    (hA : Along (RoundIs (numAt t₁ t₂ 0)) (K2.rounds p) [d₁, d₂])
    {r : SwRow} {H : r.OK} (X : Letters r H)
    (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (ρ : WordsOf (selZ X iJ iQ) d₁)
    (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W₁ → W₁) :
    KeysFit (F := F) (W := W₁) X iJ iQ d₁ d₂ ρ p q.base ext := by
  obtain ⟨k1, k2, k3, k4⟩ := K2.keys_at_frame hZ h a hF p₀ l ht hb hd hq p hft hds hA
  exact ⟨k1, k2, k3, k4⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.keysFit_in_scope
