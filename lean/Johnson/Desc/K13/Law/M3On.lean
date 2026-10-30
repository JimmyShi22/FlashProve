-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/M3On.lean: what the batching's joined block promises of the record behind it:
the claim is made of a row. Statements with their proofs.
Main names:
  `ClaimMade`: the first half of `FrontOk` (Johnson/Desc/K13/Law/M4Law.lean).
  `atM3_claim`: where `atM3 P` says yes, the claim behind it is made of a row.
  `piece_ok`: where a piece says yes, its block's own decision has said yes. General in the piece.
  `atM3_goodIn_on`: the law of Johnson/Desc/K13/Law/Tries.lean (`atM3_goodIn_dec`) with that promise
    behind.
Used of `verify-on-bytes`: `memberClaim`, as a pure function.

What is not claimed. The second half of `FrontOk`, that W's vector fits its table. That the blocks
between the two places keep the promise. `Declared` is a test on a plan's written rounds: an
evaluation at two stored sets' public files, a small and a full-size one, said yes, and five
controls said no; no theorem says it of a plan. `Local` asks only that the decoder reads the stored
table and the earlier trees: every such function meets it. A decoder that reads the oracles alone
singles out one member of a list whatever the samples in the record say: so the laws at such a
decoder are idle for the witness that the samples pin. The form to carry on is that of
Johnson/Desc/K13/Law/PinA.lean.

-/
import Johnson.Desc.K13.Law.M4Proof
import Johnson.Desc.K13.Law.Tries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type} {nR : ℕ}

/-- The claim at the chain's end, if there is one, is made of a row. -/
def ClaimMade {F : Frame} (b : S × F.E.Str) : Prop :=
  ∀ l, linAt b.1 = some l → ∃ row, l.claim = memberClaim row

/-- Where the joined block says yes, the claim behind it is made of a row. -/
theorem atM3_claim {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    ∀ l, linAt s' = some l → ∃ row, l.claim = memberClaim row := by
  have h' : (((frontB (Cl := Cl) atS P).decide s _ _).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ _ _).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ _ _) = .ok s' := h
  obtain ⟨s₂, h12, h3⟩ := ebind_ok.1 h'
  obtain ⟨s₁, _, h2⟩ := ebind_ok.1 h12
  obtain ⟨p, out, hp, _, rfl⟩ := battB_ok atS P h2
  obtain ⟨p', msg, hp', rfl⟩ := quietB_ok atS P h3
  obtain ⟨m₁, hs1, _, _, _⟩ := get_mem hp
  simp only [atS, hs1] at hp'
  obtain rfl := Option.some.inj hp'
  intro l hl
  simp only [atS, hs1, linAt] at hl
  exact ⟨out.1, by rw [← Option.some.inj hl]⟩

/-- **Where a piece says yes, its block's own decision has said yes.** General in the piece. -/
theorem piece_ok {T : Type} {C : PQ.CK} {F : Frame} (p : Piece C F T Cl W) {a b : T × F.E.Str}
    {τ : Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some b) :
    ∃ rs gs, p.b.decide a.1 rs gs = .ok b.1 := by
  have hb' : (if sTests C p.stage a.2 τ then p.run a.1 (sView C p.stage a.2 τ) else none).map
      (fun xo => (xo, p.ior.imp a.2 τ)) = some b := h
  split at hb'
  · cases hrun : p.run a.1 (sView C p.stage a.2 τ) with
    | none =>
      rw [hrun] at hb'
      cases hb'
    | some s' =>
      rw [hrun] at hb'
      obtain rfl := Option.some.inj hb'
      obtain ⟨gs, _, hdec⟩ := single_ok hrun
      exact ⟨_, gs, hdec⟩
  · cases hb'

/-- **The law of the batching's joined block, with the promise behind it.** -/
theorem atM3_goodIn_on (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (rw : W → Wit GE nR ds.length)
    (dec : F.E.Str → Wit GE nR ds.length) (hloc : Local base dec) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn (fun _ => True) ClaimMade
      (RowsHold rw (pinOf rw dec)) (RowsHold rw (pinOf rw dec)) := by
  intro a ha
  refine Doomed.mono _ _ ?_ (atM3_goodIn_dec (Cl := Cl) F P base dZ d0 ds hD rw dec hloc a ha)
  intro τ hτ b hb
  obtain ⟨rs, gs, hdec⟩ := piece_ok _ hb
  exact ⟨atM3_claim hdec, (hτ b hb).2⟩

end VerifiableInference.Desc.K13.Law
