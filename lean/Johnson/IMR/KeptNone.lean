-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/KeptNone.lean: A LIGHT FILE: NOTHING IS KEPT AT THE FIRST THREE
CUTS: at the cuts 0, 1 and 2 of the first chain's flat list the walk's own copy of the request's
frame (s.check.frame, not an open link's) has an empty list keptBefore. "The state": the verifier's
state, the value that the fold of the IOP as written in Lean carries from sub-protocol to
sub-protocol. "The cut k": the state behind the flat list's first k entries.
  first_keeps_none: the first state's frame keeps nothing. (Johnson/IMR/ListsEnds.lean's start_kept,
    said
    again: that file draws files that this one shall not.)
  cut_is_first: the state at the cuts 0, 1 and 2 IS the first state: the front hands the state back;
    "link 0: laid" hands it back. (At the cut 2: Johnson/IMR/GroupAt.lean's laid_is_start, said
      again for the
    same reason.)
  kept_none_front: THE TOP, in the letters of a sentence by position
    (HashBuild.Queue.KeptNoneAtFrontOwed [not in this library]). Its premise on the tests on the
    list of rounds is not spent.
  kept0_at: the same, general in "reached" and at_, with one premise: what is reached is the return
    of a fold from ProofFile.startS Z. The fence "no mark" is not spent.
NOT HERE: the sentence «link = 0 → nothing kept» along the whole fold.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K1's files (its law at the
first sending).
Every theorem on states starts from the premise that a fold returns; no proof file is exhibited for
which one does. No soundness.
-/
import Johnson.IMR.SizeSeat
import Johnson.IMR.FlatScope
import Johnson.IMR.FrontSeat
import Johnson.IMR.FrameSeat
import Johnson.IMR.FoldTools
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- The first state's frame keeps nothing. -/
theorem first_keeps_none {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).check.frame.keptBefore = #[] := by
  have e : Z.s₀.check.frame.keptBefore = #[] := by
    have k := pub_start hZ
    unfold VerifiableInference.Desc.First.S.startP at k
    split at k
    · rw [← Option.some.inj k]
      rfl
    · cases k
  unfold ProofFile.startS
  dsimp only
  split
  · exact e
  · rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The state at the cuts 0, 1 and 2 is the first state.** -/
theorem cut_is_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List OpenedColumn} :
    ∀ k ≤ 2, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C') → t = ProofFile.startS Z p
  | 0, _, t, R', C', f => by
    have fz : foldBlocks 0 (c.blocksInOrder.take 0) (ProofFile.startS Z p) R C = .ok (ProofFile.startS Z p, R, C) := rfl
    rw [fz] at f
    cases f
    rfl
  | 1, _, t, R', C', f => by
    have fz : foldBlocks 0 (c.blocksInOrder.take 0) (ProofFile.startS Z p) R C = .ok (ProofFile.startS Z p, R, C) := rfl
    obtain ⟨b, hb, -, -, -, -, hd⟩ := IM.front_of O
    obtain ⟨rs, gs, d⟩ := fold_next hb fz f
    exact (hd _ rs gs _).1 d
  | 2, _, t, R', C', f => by
    obtain ⟨t', R₁, C₁, f1⟩ := fold_back (k := 1) f
    have e1 := cut_is_first hS hR O 1 (by omega) t' R₁ C₁ f1
    obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
    obtain ⟨LkF, fr, bL, bB, bC, -, -, -, -, efl, hlay, -, iL, -, dL, -⟩ := hfr 0 (by decide)
    have iL' : c.blocksInOrder[1]? = some bL := iL
    obtain ⟨rsL, gsL, dl⟩ := fold_next iL' f1 f
    rw [dL] at dl
    have hlf := ((hlay t' t).1 dl).1
    rw [efl] at hlf
    rw [(Johnson.Desc.First.Walk.Law.layFront_ok hlf).1, e1]
  | n + 3, hn, _, _, _, _ => absurd hn (by omega)

end

/-- **NOTHING IS KEPT BEHIND AT MOST TWO SUB-PROTOCOLS FROM THE START.** -/
theorem kept_none_front :
  ∀ (P : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : ByteArray) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat), VerifierAndGoals.InScope P = true → VerifierAndGoals.readFiles P = .ok pp →
    IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B →
    (∀ b ∈ c.blocksInOrder, b.planOk = true) →
    ∀ (p : ProofFile.InstPub) (l₁ l₂ : List (Block S Cl)), c.blocksInOrder = l₁ ++ l₂ → l₁.length ≤ 2 →
      ∀ (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn),
        foldBlocks 0 l₁ (ProofFile.startS Z p) rs cols = .ok r → r.1.check.frame.keptBefore = #[] := by
  intro P pp lay F Z Bs base c A B hS hR O _ p l₁ l₂ hc hl rs cols r f
  have e : c.blocksInOrder.take l₁.length = l₁ := by
    rw [hc]
    simp
  rw [← e] at f
  obtain ⟨t, R', C'⟩ := r
  rw [cut_is_first hS hR O l₁.length hl t R' C' f]
  exact first_keeps_none O.pub p

/-- **The same at "reached"**, general in Rch and at_. -/
theorem kept0_at {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type}
    (Rch : Nat → X → Prop) (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q)) :
    ∀ k a, Rch k a → k ≤ 2 → (at_ a).2.failed = none →
      (at_ a).2.check.frame.keptBefore = #[] := by
  intro k a hr hk _
  obtain ⟨rs, cols, r, q, f⟩ := hRch k a hr
  rw [cut_is_first hS hR O k hk _ r q f]
  exact first_keeps_none O.pub _

#print axioms first_keeps_none
#print axioms cut_is_first
#print axioms kept_none_front
#print axioms kept0_at

end Meaning.K2
