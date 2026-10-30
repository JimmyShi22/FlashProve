-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/ReplyNatField.lean: THE FIELD «replyNat» OF THE STRUCTURE
FoldFacts (Johnson/Desc/First/FoldFacts.lean), WHOLE, ending in the field's own type:
a reply that the verifier's state holds is a number: its first coordinate alone bears it.
Statements and proofs.

HOW. Entry 338 of the first chain's flat list is the one sub-protocol of kind K7: it hears the
reply (Johnson/IMR/TokAtReach.lean's hearer_at). BEHIND IT (borders 339 to 358): tokSmallAt_border:
what is held is an entry of the public part's vocabulary; replyNat_of_tokSmall
(Johnson/Desc/Kinds/Law/ReplyNat.lean) turns that into the field's sentence, where the vocabulary's
size is at most the field's characteristic: in scope it is the reference's (sizes_in_scope), and
the closed comparison is by the kernel. IN FRONT OF IT (borders 0 to 338): every entry in front of
338 leaves the held reply (ProofFile.chainBy_leaves and cut_pins, as in later_leaves), and the start
holds none: so none is held, and the field's sentence is free there.

  earlier_leaves     every entry of the flat list in front of 338 leaves the held reply
  start_unheard      the start holds no reply, whether z's request passes its test or not
  unheard_reach      at a border up to 338 a reached state holds no reply
  vocab_small        in scope the public part's vocabulary's size is at most the characteristic
  replyNat_reach     the field's sentence at every reached state
  replyNat_field     **the field, general in Rch and at_**

THE PREMISES IN FRONT, BY NAME: hS · hR (the goals' scope; the public files are read) · O (the
opening: free by seat_open) · hRch: what is reached in Rch's sense is reached in
Johnson/IMR/AtReach.lean's
(Reach over the chain's own sub-protocols from the start at the statement's own public
part). THE FENCE «no mark» IS NOT SPENT. No test on the plan is asked.
What is not claimed. The structure is not imported here: Lean's check of the fit is in
Johnson/IMR/AtReachFits.lean. That a reply is held anywhere; that hS, hR, O, hRch can be met
together.
Nothing on whose reply it is. No soundness.

-/
import Johnson.IMR.TokAtReach
import Johnson.IMR.RecRun
import Johnson.Desc.Kinds.Law.ReplyNat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Every entry of the flat list in front of 338 leaves the held reply.** -/
theorem earlier_leaves (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (h : k < 338)
    {b : Block S Cl} (hb : c.blocksInOrder[k]? = some b) : b.Leaves fun s : S => s.out.reply := by
  obtain ⟨b₀, e₀, J⟩ := hearer_at hS hR O
  obtain ⟨h₀, g₀⟩ := List.getElem?_eq_some_iff.1 e₀
  have cut : c.blocksInOrder = c.blocksInOrder.take 338 ++ b₀ :: c.blocksInOrder.drop 339 := by
    rw [← g₀, ← List.drop_eq_getElem_cons h₀, List.take_append_drop]
  have hk : b₀.place.kind = .K7 := by rw [joined_place J]
  have hn := (cut_pins c.blocksInOrder _ _ b₀ cut hk (ProofFile.chainBy_count Z base _ _ c O.chain)).1
  have hm : b ∈ c.blocksInOrder.take 338 := by
    refine List.mem_of_getElem? (i := k) ?_
    rw [List.getElem?_take_of_lt h]
    exact hb
  exact ((ProofFile.chainBy_leaves (fun s : S => s.out.reply) Z base _ _ c O.chain
    fun t s e => ProofFile.sameReply_eq t s e) b (List.mem_of_getElem? hb)).resolve_left (hn b hm)

/-- The start holds no reply. At every o. -/
theorem start_unheard {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (z : ProofFile.InstPub) :
    (ProofFile.startS Z z).out.reply = none := by
  unfold ProofFile.startS
  dsimp only
  split
  · have hs := Meaning.K2.pub_start h
    unfold S.startP at hs
    split at hs
    · have e := Option.some.inj hs
      rw [← e]
      rfl
    · cases hs
  · rfl

/-- **At a border up to 338 a reached state holds no reply.** -/
theorem unheard_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft k : ℕ} (h : k ≤ 338)
    {p : ProofFile.InstPub} {s : S} (R : Reach ft c.blocksInOrder (ProofFile.startS Z) k (p, s)) :
    s.out.reply = none := by
  induction k generalizing s with
  | zero =>
    cases R
    exact start_unheard O.pub p
  | succ k ih =>
    cases R with
    | @succ _ _ s₀ _ b R₀ hb hy =>
      obtain ⟨rs, gs, d⟩ := step_accepts hy
      have e : s.out.reply = s₀.out.reply := earlier_leaves hS hR O (by omega) hb s₀ rs gs s d
      rw [e]
      exact ih (by omega) R₀

/-- In scope the public part's vocabulary's size is at most the field's characteristic. -/
theorem vocab_small (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    Z.p.X.hS.V ≤ OnBytes.pW.toNat := by
  have e := (Meaning.HeadS.sizes_in_scope hS hR O.public).2.2.1
  rw [← O.W, e]
  decide

/-- **The field's sentence at every reached state.** -/
theorem replyNat_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft k : ℕ}
    {a : ProofFile.InstPub × S} (R : Reach ft c.blocksInOrder (ProofFile.startS Z) k a) :
    ∀ g, a.2.out.reply = some g → OnBytes.Model.ofNat g.c0.toNat = g := by
  rcases Nat.lt_or_ge k 339 with h | h
  · intro g hg
    rw [unheard_reach hS hR O (by omega) (p := a.1) (s := a.2) R] at hg
    cases hg
  · exact Kinds.Head.Law.replyNat_of_tokSmall _ (vocab_small hS hR O) a.2
      (tokSmallAt_border hS hR O h R)

/-- **Field replyNat, whole.** The fence is not spent. -/
theorem replyNat_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) :
    ∀ k a, Rch k a → (at_ a).2.failed = none → ∀ g, (at_ a).2.out.reply = some g →
      OnBytes.Model.ofNat g.c0.toNat = g :=
  fun k a h _ => replyNat_reach hS hR O (hRch k a h)

end IM

#print axioms IM.earlier_leaves
#print axioms IM.start_unheard
#print axioms IM.unheard_reach
#print axioms IM.vocab_small
#print axioms IM.replyNat_reach
#print axioms IM.replyNat_field
