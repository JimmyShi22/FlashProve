-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ShapeJV.lean: THE VALUES WITH J IN HAND. The shape's authors'
wish on Honest/Thread/ShapeJ.lean: its two lemmas at the cut take `Values`
(Honest/Thread/Shape.lean): the member's named tests on values pass, from the thread in front
alone. Whoever pays that at a member may want to know the state's shape: and where these lemmas
call it, J is in hand. `ValuesJ` asks the same from the pair (`ThrS`) and with "J b s": two premises
more: the weaker premise. The two lemmas again, over it; their proofs are ShapeJ.lean's own, with hJ
handed on. One
definition: a premise's form. Three conditional lemmas.

  `ValuesJ`, `valuesJ_of`   the values with J in hand; `Values` gives it
  `nextJ_of_shapeV`, `acceptedJ_of_shapeV`   the two debts at the cut's J, from `ValuesJ`

Limits. Nothing shows that a premise is met at any member. None is one of the library's goals. This
file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **THE VALUES, WITH J IN HAND**: `Values`, from the pair, with J at the state in front as one
premise more. It is a definition: a premise's form. -/
def ValuesJ (J : Nat → S → Prop) (Z : Shape S)
    (fall : Nat → S → List Fmt.Drawn → Option String) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, ThrS T Said b k s m E → J b s →
    drawsFit blk.rounds ds = true →
    chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none → fall b s ds = none →
    T.Moved blk k m E ds y cols →
    Z.vals b s ((roundsOf y.1).map noDigest) (blk.shown T.ft (roundsOf y.1) cols) = true

theorem valuesJ_of {J : Nat → S → Prop} {Z : Shape S}
    {fall : Nat → S → List Fmt.Drawn → Option String} {b : Nat} (h : Values T Z fall b) :
    ValuesJ T Said J Z fall b :=
  fun blk hblk k s m E ds y cols hA _ => h blk hblk k s m E ds y cols hA.1

/-- **ONE MEMBER ON, AT THE CUT**, from (B1) with the values in hand and the values with J in
hand, under the named premise `Z.yes a₀ n` at some n above b. -/
theorem nextJ_of_shapeV (Z : Shape S) {a₀ : Z.Sh} {n b : Nat}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hb : b < n) (hyes : Z.yes a₀ n = true)
    (hC : CarriesU T.bs T.ft Z b) (hV : ValuesJ T Said (shapeJ Z a₀) Z fall b) :
    NextJ T Said (shapeJ Z a₀) fall b := by
  intro blk hblk k s m E ds y cols s' hA hJ hd hst hf hS
  obtain ⟨t, ht⟩ := run_front Z a₀ n (b + 1) hb hyes
  have hg : Z.g b (Z.sh s) = .ok t := by
    have ht' : (Z.run b a₀).bind (Z.g b) = .ok t := ht
    rw [show Z.run b a₀ = .ok (Z.sh s) from hJ] at ht'
    exact ht'
  have hv := hV blk hblk k s m E ds y cols hA hJ hd hst hf hS.1
  have e := hC blk hblk s (roundsOf y.1) cols s' cols.length t hS.2 hg hv
  show Z.run (b + 1) a₀ = .ok (Z.sh s')
  rw [ht, e]

/-- **THE RULE OF THE CUT**, from (B2) and `FitsAt` at this member and the values with J in hand,
under the named premise `Z.yes a₀ n` at some n above b. -/
theorem acceptedJ_of_shapeV (Z : Shape S) {a₀ : Z.Sh} {n b : Nat}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hb : b < n) (hyes : Z.yes a₀ n = true)
    (hR : Returns T.bs T.ft Z b) (hF : FitsAt T b)
    (hV : ValuesJ T Said (shapeJ Z a₀) Z fall b) :
    AcceptedJ T Said (shapeJ Z a₀) fall b := by
  intro blk hblk k s m E ds y cols hA hJ hd hst hf hMv
  obtain ⟨t, ht⟩ := run_front Z a₀ n (b + 1) hb hyes
  have hg : Z.g b (Z.sh s) = .ok t := by
    have ht' : (Z.run b a₀).bind (Z.g b) = .ok t := ht
    rw [show Z.run b a₀ = .ok (Z.sh s) from hJ] at ht'
    exact ht'
  have hfit := hF blk hblk k m E ds y cols hd hMv
  obtain ⟨s', hdec⟩ := hR blk hblk s (roundsOf y.1) cols t hg hfit
    (hV blk hblk k s m E ds y cols hA hJ hd hst hf hMv)
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := blk) (rs := roundsOf y.1)
    (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', ?_⟩
  unfold Thread.Stepped
  refine ⟨hMv, ?_⟩
  rw [← hw]
  exact (step_iff T.ft blk s s' (roundsOf y.1) cols _).2 ⟨hfit, hdec, rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.valuesJ_of
#print axioms ProofFile.Honest.nextJ_of_shapeV
#print axioms ProofFile.Honest.acceptedJ_of_shapeV
