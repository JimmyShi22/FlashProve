-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ShapeJ.lean: A THIRD FAMILY BESIDE THE THREAD AND WHAT IS
SAID, FOR ACCEPTANCE ALONE: WHAT HOLDS OF THE VERIFIER's STATE ALONG A RUN AT WHICH NOTHING HAS
STOPPED AND NO FALL HAS SPOKEN; and the cut "structure | values" (Honest/Thread/Shape.lean) over
it. WHY. The question of the shape's authors: at a member whose shape behind hangs on a value's not
being 0 (the batching), no law "the shape's step returns the shape behind" can hold from a bare yes:
(B1) `Carries` cannot be met; under the member's named tests on values it can. But `shape_reach`
walks what is reached by bare yeses, and the thread at a border does not remember that no fall spoke
earlier: what it owes behind a member it owes at all draws. So the sentence "the state has the
run's shape" is carried here by a family J of its own, one member on UNDER "no stop, no fall", and
acceptance is asked with J in hand. The rule that carries J along a run is row 12's
(Honest/Law/AcceptJ.lean). Four definitions: premises' forms; three conditional lemmas.

  `CarriesU`           (B1) with the member's named tests on values in hand; `carriesU_of`
  `NextJ`, `AcceptedJ`  the two debts at a member: J one member on; the member's yes with J in hand
  `acceptedJ_of`       a member that is accepted without J is accepted with it
  `shapeJ`             J at the cut: the shape's run returns the state's shape
  `nextJ_of_shape`, `acceptedJ_of_shape`   the two debts at that J

Limits. Nothing shows that a premise is met at any member. None is one of the library's goals. This
file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Shape
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **(B1) WITH THE VALUES IN HAND**: where the member's own step says yes, the shape's own step
returns AND THE MEMBER's NAMED TESTS ON VALUES PASS, it returns the shape behind that yes. It is a
definition: a premise's form. -/
def CarriesU (bs : List (Block S Cl)) (ft : Nat) (Z : Shape S) (b : Nat) : Prop :=
  ∀ blk, bs[b]? = some blk → ∀ s rs cols s' n t, blk.step ft s rs cols = .ok (s', n) →
    Z.g b (Z.sh s) = .ok t → Z.vals b s (rs.map noDigest) (blk.shown ft rs cols) = true →
    t = Z.sh s'

theorem carriesU_of {bs : List (Block S Cl)} {ft : Nat} {Z : Shape S} {b : Nat}
    (h : Carries bs ft Z b) : CarriesU bs ft Z b :=
  fun blk hblk s rs cols s' n t hs hg _ => h blk hblk s rs cols s' n t hs hg

variable (T : Thread Bk S Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
  (J : Nat → S → Prop)

/-- **J ONE MEMBER ON**: from the pair in front and J there, where nothing of the member stops and
the letter fall says nothing, behind the member's step J holds at the next border. It is a
definition: a premise's form. -/
def NextJ (fall : Nat → S → List Fmt.Drawn → Option String) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E → J b s →
    drawsFit blk.rounds ds = true →
    chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none → fall b s ds = none →
    T.Stepped blk k s m E ds y cols s' → J (b + 1) s'

/-- `AcceptedS`, asked with J in hand. It is a definition: a premise's form. -/
def AcceptedJ (fall : Nat → S → List Fmt.Drawn → Option String) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, ThrS T Said b k s m E → J b s →
    drawsFit blk.rounds ds = true →
    chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none → fall b s ds = none →
    T.Moved blk k m E ds y cols → ∃ s', T.Stepped blk k s m E ds y cols s'

theorem acceptedJ_of {fall : Nat → S → List Fmt.Drawn → Option String} {b : Nat}
    (h : AcceptedS T Said fall b) : AcceptedJ T Said J fall b :=
  fun blk hblk k s m E ds y cols hA _ => h blk hblk k s m E ds y cols hA

/-- **J AT THE CUT**: the shape's run over the members in front returns the state's shape. -/
def shapeJ (Z : Shape S) (a₀ : Z.Sh) : Nat → S → Prop := fun b s => Z.run b a₀ = .ok (Z.sh s)

/-- **ONE MEMBER ON, AT THE CUT**: from (B1) with the values in hand and the values, under the named
premise `Z.yes a₀ n` at some n above b. -/
theorem nextJ_of_shape (Z : Shape S) {a₀ : Z.Sh} {n b : Nat}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hb : b < n) (hyes : Z.yes a₀ n = true)
    (hC : CarriesU T.bs T.ft Z b) (hV : Values T Z fall b) :
    NextJ T Said (shapeJ Z a₀) fall b := by
  intro blk hblk k s m E ds y cols s' hA hJ hd hst hf hS
  obtain ⟨t, ht⟩ := run_front Z a₀ n (b + 1) hb hyes
  have hg : Z.g b (Z.sh s) = .ok t := by
    have ht' : (Z.run b a₀).bind (Z.g b) = .ok t := ht
    rw [show Z.run b a₀ = .ok (Z.sh s) from hJ] at ht'
    exact ht'
  have hv := hV blk hblk k s m E ds y cols hA.1 hd hst hf hS.1
  have e := hC blk hblk s (roundsOf y.1) cols s' cols.length t hS.2 hg hv
  show Z.run (b + 1) a₀ = .ok (Z.sh s')
  rw [ht, e]

/-- **THE RULE OF THE CUT, WITH J IN `shape_at`'s STEAD**: (B2) and `FitsAt` at this member, and the
values, under the named premise `Z.yes a₀ n` at some n above b. -/
theorem acceptedJ_of_shape (Z : Shape S) {a₀ : Z.Sh} {n b : Nat}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hb : b < n) (hyes : Z.yes a₀ n = true)
    (hR : Returns T.bs T.ft Z b) (hF : FitsAt T b) (hV : Values T Z fall b) :
    AcceptedJ T Said (shapeJ Z a₀) fall b := by
  intro blk hblk k s m E ds y cols hA hJ hd hst hf hMv
  obtain ⟨t, ht⟩ := run_front Z a₀ n (b + 1) hb hyes
  have hg : Z.g b (Z.sh s) = .ok t := by
    have ht' : (Z.run b a₀).bind (Z.g b) = .ok t := ht
    rw [show Z.run b a₀ = .ok (Z.sh s) from hJ] at ht'
    exact ht'
  have hfit := hF blk hblk k m E ds y cols hd hMv
  obtain ⟨s', hdec⟩ := hR blk hblk s (roundsOf y.1) cols t hg hfit
    (hV blk hblk k s m E ds y cols hA.1 hd hst hf hMv)
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

#print axioms ProofFile.Honest.carriesU_of
#print axioms ProofFile.Honest.acceptedJ_of
#print axioms ProofFile.Honest.nextJ_of_shape
#print axioms ProofFile.Honest.acceptedJ_of_shape
