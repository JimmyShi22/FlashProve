--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
GrownRch.lean: e₁ AT THE PROOF FILE: THE JOIN ALONG THE FOLD AT THE NARROW FENCE:
"reached by the steps of the WRAPPED sub-protocols" (below b: b behind the test that every word
shown is below the prime): the family that a piece's accept makes (RchAt,
Johnson/Top/H0/Walk/ReachAt.lean, at the state's side). A FENCE WITH A SPENDER, AT WHICH TWO SORTS
OF SHARE MEET: one at that family, one at the wide "reached". Two definitions and theorems, proved.



WHY. SharesRF and x_reach_scope stand at the WIDE fence: reached by the
sub-protocols' own steps. A part that knows its step only at states that the wrapped steps reach
could not hand its share in there: HandsR.weaker goes from the wide fence to the narrow alone.

  below_under (below b).UnderR b: below_narrows.
  RB c Z p   the narrow fence: RF 0 (c.blocksInOrder.map below) (ProofFile.startS Z) p. rb_wide: it lies inside the
    wide one (reach_raw).
  SharesRB   SharesRF's sentence at RB. sharesRB_of_RF: WHOEVER HAS THE WIDE FENCE HAS THE NARROW.
  x_rch_scope   **in scope: SharesRB, the plan's two counts at the front = 0, E 0 at the first
    state: then X k at every state without a mark that the wrapped steps reach.** By x_at_reach
    at the list c.blocksInOrder.map below; each row is carried from b to below b by
    HandsR.under.

OBJECT: c.blocksInOrder.map below. USER: RowsAtRch.lean. LETTERS: N, E, p: free.

What is not claimed. HandsR at any sub-protocol. A place for a proof whose fence is narrower still
(one that asks the table's whole promise in front, say): it hands in nowhere here. That X k holds at
a state which only the sub-protocols' own steps reach (x_reach_scope's end is wider; its premise
too). No soundness.
-/
import Johnson.IMR.GrownReach
import Johnson.Desc.Sound.MergeNarrow

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (below below_narrows)
open VerifiableInference.Desc.First (S Numbers frontPlace)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open ProofFile (Cl)

/-- The wrapped sub-protocol stands under its own. -/
theorem below_under (b : Block S Cl) : (below b).UnderR b :=
  ⟨(below_narrows b).1, (below_narrows b).2⟩

/-- **The narrow fence**: reached by the wrapped sub-protocols' steps. -/
def RB (c : Chain S Cl) (Z : ProofFile.Pub) (p : ProofFile.InstPub) : ℕ → S → Prop :=
  RF 0 (c.blocksInOrder.map below) (ProofFile.startS Z) p

/-- It lies inside the wide one. -/
theorem rb_wide {c : Chain S Cl} {Z : ProofFile.Pub} {p : ProofFile.InstPub} {k : ℕ} (s : S)
    (h : RB c Z p k s) : RF 0 c.blocksInOrder (ProofFile.startS Z) p k s :=
  reach_raw h

/-- **The shares at the narrow fence.** -/
def SharesRB (p : ProofFile.InstPub) (N : Numbers) (E : ℕ → S → Bool) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : Chain S Cl) : Prop :=
  ∀ k b, c.blocksInOrder[k]? = some b → FlatCase Z G₀ c k b → HandsR (RB c Z p) N linksW placesW E 0 k b

/-- **Whoever has the wide fence has the narrow.** -/
theorem sharesRB_of_RF {p : ProofFile.InstPub} {N : Numbers} {E : ℕ → S → Bool} {Z : ProofFile.Pub}
    {G₀ : ProofFile.Ground} {c : Chain S Cl} (h : SharesRF p N E Z G₀ c) : SharesRB p N E Z G₀ c :=
  fun k b hb hc => (h k b hb hc).weaker rb_wide

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **X AT EVERY STATE WITHOUT A MARK THAT THE WRAPPED STEPS REACH.** -/
theorem x_rch_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {N : Numbers} {E : ℕ → S → Bool}
    {p : ProofFile.InstPub} (Sh : SharesRB p N E Z Bs.G₀ c)
    (hT : N.treesAt (some frontPlace) = 0) (hM : N.msgsAt (some frontPlace) = 0)
    (hE : (ProofFile.startS Z p).failed = none → E 0 (ProofFile.startS Z p) = true) {k : ℕ} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (p, s)) (hu : s.failed = none) :
    XK N linksW placesW E k s = true := by
  have h0 := s0_of_open (links := linksW) O p hT hM hE
  rw [places_scope hS hR O] at h0
  refine x_at_reach (bs := c.blocksInOrder.map below) (fun j b' hb' => ?_) h0 hr hu
  rw [List.getElem?_map] at hb'
  cases hB : c.blocksInOrder[j]? with
  | none =>
    rw [hB] at hb'
    cases hb'
  | some b =>
    rw [hB] at hb'
    obtain rfl : below b = b' := Option.some.inj hb'
    exact (Sh j b hB (flat_cases hS hR O j b hB)).under (below_under b)

end IM

#print axioms IM.below_under
#print axioms IM.sharesRB_of_RF
#print axioms IM.x_rch_scope
