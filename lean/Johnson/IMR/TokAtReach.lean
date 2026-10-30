-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/TokAtReach.lean: THE REPLY's NEXT TOKEN ALONG THE FOLD: in the goals' scope, at the
second hash function: wherever the verifier's state is reached at a border behind entry
338 of the flat list of the first chain of the IOP as written in Lean (the sub-protocol that hears
the reply), a token's number below the reference's vocabulary's size stands heard in it.



Compiled with the whole library.
HOW. "Reached" is inductive: the proof goes along it, border by border, from 339 on; it takes no
fold and speaks of no list of rounds. At each border the step's yes holds the sub-protocol's own
accepting decision (step_ok_iff).
  (1) Border 339 is reached through entry 338, which is hearing sub-protocol number 0 of link 24
  (k7_sits, hear_at_flat, flatIx_scope); its accepting decision is that of "a front, and then the
  next token's sub-protocol", with the same state behind it (k7_sits_yes); behind that a token below
  the vocabulary's size is heard (joined_hearsTok); in scope that size is the reference's
  (sizes_in_scope).
  (2) Every entry of the flat list stands at a place of the kind K7 or leaves the reply
  (chainBy_leaves, by the guard under which the driver lays the chain); just one entry stands at
  that kind (chainBy_count), and entry 338 does: so none behind it does (cut_pins).

  step_accepts     a step's yes holds an accepting decision, from the same state to the same state.
  hearer_at        entry 338 is in the joined form, at K7's place.
  joined_place     the joined form stands at the place that it names: so entry 338's kind is K7.
  later_leaves     every entry from 339 on leaves the held reply.
  reply_reach      THE ONE INDUCTION: a sentence Q on the held reply that holds behind every
                   accepting decision of K7's place's own sub-protocol holds at every border k,
                   339 ≤ k.
  heardToken_reach some x is heard and isToken Z.p.X.hS.V x = true: at the public part's own
                   vocabulary.
  tokSmall_reach   THE TOP: the heard reply, read as a token's number, is some y < ppref.V: at the
                   reference's vocabulary, which in scope is the public part's (sizes_in_scope).
  tokSmallAt_reach | tokSmallAt_border   the form that the next token's files spend: TokSmall
                   Z.p.X.hS.V s (Johnson/Desc/Kinds/Law/TokenSmall.lean), off heardToken_reach; the
                   second at a pair a, of a.2.
  tokSmall_below | heardToken_below | tokSmallAt_below   the three at THE NARROWER "REACHED" of
                   Johnson/Top/H0/Walk/Reach.lean:
                   reached by the steps of the wrapped sub-protocols (Sound.below: the sub-protocol
                   behind the test that every word shown is below the prime): each by reach_raw.
  descOf | desc_is | tokSmallAt_desc | heardToken_desc   AT THE DESCRIPTION's OWN NAMES: descOf Z A
                   B c: the value that Open names (desc_is: F = descOf Z A B c, by O.desc); the
                   two forms from Reach 0 ((descOf Z A B c).first.blocksInOrder.map below) (descOf Z A B
                   c).start₁ k a.1, of a.1.2. That premise is the right side of RchAt F k a
                   (ReachAt.lean) by our reading of that file: RchAt is written out,
                   not imported (that file stands over two files not at hand here): that the
                   written text is RchAt's is held by no run here.

OBJECT: the first chain of ProofFile.onlineDescription's value at the second hash function. USER: none in Lean yet;
meant: the next token's files' bill at border 341. LETTERS: the files in scope; k, p, s: free; y, x:
under "there is", pinned by the equation beside each. Border k: the verifier's state in front of
entry k of the flat list (Reach … k). ft: the number in the label of the chain's first own tree,
which a step hands to its reading of the columns: free but in the top, in tokSmall_below and in the
two at the description's names, whose 0 is the number at which the run lays the first chain
(Johnson/Desc/Block.lean: runCore: chainAt "the first chain" 0).

WHAT IS NOT SAID. WHICH token is heard: that one is, and its range, not its identity: nothing ties y
to the request, to the reply file or to the model. That any state is reached at a border from 339
on: no member of "reached" there is shown, and the driver's guard can refuse an honest file: so that
an honest proof comes to border 339 is not shown either. Nothing in front of border 339. Nothing at
an o other than `OnBytes.secondHashFunction`. The guard on the reply is scaffolding of the driver: where it is
struck, (2) is owed anew. No soundness.

-/
import Johnson.IMR.FirstSeats
import Johnson.IMR.FlatScope
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.Plain.Leaves.PureHears
import Johnson.Desc.Kinds.Law.ReplyHears
import Johnson.Desc.Kinds.Law.TokenSmall
import Johnson.Goal.Meaning.HeadShapeScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach StepYes reach_raw)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- A step's yes holds an accepting decision, from the same state to the same state. -/
theorem step_accepts {ft : ℕ} {b : Block S Cl} {s t : S} (h : StepYes ft b s t) :
    ∃ rs gs, b.decide s rs gs = .ok t := by
  obtain ⟨R, C, -, hs⟩ := h
  exact ⟨_, _, ((Sound.step_ok_iff ft b s t R C C.length).1 hs).2.2.2⟩

/-- **Entry 338 of the flat list is the sub-protocol that hears the reply**, in the joined form. -/
theorem hearer_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ b, c.blocksInOrder[338]? = some b ∧ Joined Z 24 b (k7Block Bs.G₀.W 24).retype k7Place := by
  obtain ⟨Lk, b, eL, e0, J, -⟩ := k7_sits hS hR O
  have q := hear_at_flat eL e0
  rw [flatIx_scope hS hR O (Nat.le_refl 24) 0] at q
  exact ⟨b, q, J⟩

/-- The joined form stands at the place that it names. -/
theorem joined_place {l : ℕ} {b b' : Block S Cl} {a : Place} (h : Joined Z l b b' a) :
    b.place = a := by
  obtain ⟨fs, f, -, -, e⟩ := h
  rw [e]
  rfl

/-- **Every entry of the flat list from 339 on leaves the held reply.** -/
theorem later_leaves (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (h : 339 ≤ k)
    {b : Block S Cl} (hb : c.blocksInOrder[k]? = some b) : b.Leaves fun s : S => s.out.reply := by
  obtain ⟨b₀, e₀, J⟩ := hearer_at hS hR O
  obtain ⟨h₀, g₀⟩ := List.getElem?_eq_some_iff.1 e₀
  have cut : c.blocksInOrder = c.blocksInOrder.take 338 ++ b₀ :: c.blocksInOrder.drop 339 := by
    rw [← g₀, ← List.drop_eq_getElem_cons h₀, List.take_append_drop]
  have hk : b₀.place.kind = .K7 := by rw [joined_place J]
  have hn := (cut_pins c.blocksInOrder _ _ b₀ cut hk (ProofFile.chainBy_count Z base _ _ c O.chain)).2
  have hm : b ∈ c.blocksInOrder.drop 339 := by
    refine List.mem_of_getElem? (i := k - 339) ?_
    rw [List.getElem?_drop, show 339 + (k - 339) = k by omega]
    exact hb
  exact ((ProofFile.chainBy_leaves (fun s : S => s.out.reply) Z base _ _ c O.chain
    fun t s e => ProofFile.sameReply_eq t s e) b (List.mem_of_getElem? hb)).resolve_left (hn b hm)

/-- **ALONG "REACHED", ONCE FOR EVERY SENTENCE ON THE HELD REPLY**: a sentence that holds of the
reply behind every accepting decision of K7's place's own sub-protocol holds of the reply wherever
the verifier's state is reached at a border from 339 on. -/
theorem reply_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (Q : Option E → Prop)
    (hQ : ∀ s rs gs t, (k7Block Bs.G₀.W 24).decide s rs gs = .ok t → Q t.out.reply)
    {ft k : ℕ} (h : 339 ≤ k) {p : ProofFile.InstPub} {s : S}
    (R : Reach ft c.blocksInOrder (ProofFile.startS Z) k (p, s)) : Q s.out.reply := by
  induction k, h using Nat.le_induction generalizing s with
  | base =>
    obtain ⟨b₀, e₀, J⟩ := hearer_at hS hR O
    cases R with
    | @succ _ _ s₀ _ b _ hb hy =>
      obtain rfl : b₀ = b := Option.some.inj (e₀.symm.trans hb)
      obtain ⟨rs, gs, d⟩ := step_accepts hy
      exact hQ _ _ _ _ (k7_sits_yes hS hR O J d).1
  | succ k hk ih =>
    cases R with
    | @succ _ _ s₀ _ b R₀ hb hy =>
      obtain ⟨rs, gs, d⟩ := step_accepts hy
      have e : s.out.reply = s₀.out.reply := later_leaves hS hR O hk hb s₀ rs gs s d
      rw [e]
      exact ih R₀

/-- **A token of the public part's own vocabulary stands heard.** -/
theorem heardToken_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft k : ℕ} (h : 339 ≤ k)
    {p : ProofFile.InstPub} {s : S} (R : Reach ft c.blocksInOrder (ProofFile.startS Z) k (p, s)) :
    ∃ x, s.heard = some x ∧ OnBytes.Desc.Reply.isToken Z.p.X.hS.V x = true := by
  rw [← O.W]
  exact reply_reach hS hR O
    (fun r => ∃ x, r = some x ∧ OnBytes.Desc.Reply.isToken Bs.G₀.W.hS.V x = true)
    (Kinds.Head.Law.behind_andThen "H:1" _ (Kinds.Reply.blockOf Bs.G₀.W 24) _
      fun _ _ _ _ hd => Kinds.Head.Law.heard_behind_some 24 Bs.G₀.W.hS.V hd) h R

/-- **THE REPLY's NEXT TOKEN ALONG THE FOLD**: in scope, at `secondHashFunction`: wherever the verifier's
state is reached at a border behind entry 338 of the first chain's flat list, a token's number below
the reference's vocabulary's size (ppref.V; in scope the public part's) stands heard in it. -/
theorem tokSmall_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (h : 339 ≤ k)
    {p : ProofFile.InstPub} {s : S}
    (R : Johnson.Desc.First.Walk.Tied.Reach 0 c.blocksInOrder (ProofFile.startS Z) k (p, s)) :
    ∃ y, (s.heard.bind fun g => if ofNat g.c0.toNat == g then some g.c0.toNat else none) = some y ∧
      y < Inst.Model.ppref.V :=
  reply_reach hS hR O
    (fun r => ∃ y, (r.bind fun g => if ofNat g.c0.toNat == g then some g.c0.toNat else none) =
      some y ∧ y < Inst.Model.ppref.V)
    (Kinds.Head.Law.joined_hearsTok Bs.G₀.W 24 "H:1" _
      (Nat.le_of_eq (Meaning.HeadS.sizes_in_scope hS hR O.public).2.2.1)) h R

/-- **The form that the next token's files spend**: every element in the reply's seat is an entry
of the public part's own vocabulary. TokSmall, as it is defined, is true also where nothing is
heard; here something is heard (heardToken_reach). -/
theorem tokSmallAt_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft k : ℕ} (h : 339 ≤ k)
    {p : ProofFile.InstPub} {s : S} (R : Reach ft c.blocksInOrder (ProofFile.startS Z) k (p, s)) :
    Kinds.Head.Law.TokSmall Z.p.X.hS.V s := by
  obtain ⟨x, hx, ht⟩ := heardToken_reach hS hR O h R
  intro x' hx'
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  exact ht

/-- The same at a pair, as a bill at a border states it. -/
theorem tokSmallAt_border (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft k : ℕ} (h : 339 ≤ k)
    {a : ProofFile.InstPub × S} (R : Reach ft c.blocksInOrder (ProofFile.startS Z) k a) :
    Kinds.Head.Law.TokSmall Z.p.X.hS.V a.2 :=
  tokSmallAt_reach hS hR O h (p := a.1) (s := a.2) R

/-! ## At the narrower "reached": by the steps of the wrapped sub-protocols -/

/-- The top at the narrower family, at a pair. -/
theorem tokSmall_below (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (h : 339 ≤ k)
    {a : ProofFile.InstPub × S} (R : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k a) :
    ∃ y, (a.2.heard.bind fun g => if ofNat g.c0.toNat == g then some g.c0.toNat else none) =
      some y ∧ y < Inst.Model.ppref.V :=
  tokSmall_reach hS hR O h (p := a.1) (s := a.2) (reach_raw R)

/-- A token of the public part's own vocabulary stands heard, at the narrower family. -/
theorem heardToken_below (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft k : ℕ} (h : 339 ≤ k)
    {a : ProofFile.InstPub × S} (R : Reach ft (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k a) :
    ∃ x, a.2.heard = some x ∧ OnBytes.Desc.Reply.isToken Z.p.X.hS.V x = true :=
  heardToken_reach hS hR O h (p := a.1) (s := a.2) (reach_raw R)

/-- The form that the next token's files spend, at the narrower family. -/
theorem tokSmallAt_below (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft k : ℕ} (h : 339 ≤ k)
    {a : ProofFile.InstPub × S} (R : Reach ft (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k a) :
    Kinds.Head.Law.TokSmall Z.p.X.hS.V a.2 :=
  tokSmallAt_border hS hR O h (reach_raw R)

/-! ## At the description's own names -/

/-- The value that Open names. -/
abbrev descOf (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S Cl) :
    FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c

/-- It is the description that was opened. -/
theorem desc_is (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : F = descOf Z A B c :=
  O.desc

/-- A token of the public part's own vocabulary stands heard: from the narrower "reached" in the
description's own names. Str: whatever stands beside the pair: it is not read. -/
theorem heardToken_desc (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (h : 339 ≤ k) {Str : Type}
    {a : ((descOf Z A B c).XiPub × (descOf Z A B c).S₁) × Str}
    (R : Reach 0 ((descOf Z A B c).first.blocksInOrder.map Sound.below) (descOf Z A B c).start₁ k a.1) :
    ∃ x, S.heard a.1.2 = some x ∧ OnBytes.Desc.Reply.isToken Z.p.X.hS.V x = true :=
  heardToken_below hS hR O h R

/-- The form that the next token's files spend, from the same. -/
theorem tokSmallAt_desc (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (h : 339 ≤ k) {Str : Type}
    {a : ((descOf Z A B c).XiPub × (descOf Z A B c).S₁) × Str}
    (R : Reach 0 ((descOf Z A B c).first.blocksInOrder.map Sound.below) (descOf Z A B c).start₁ k a.1) :
    Kinds.Head.Law.TokSmall Z.p.X.hS.V a.1.2 :=
  tokSmallAt_below hS hR O h R

#print axioms step_accepts
#print axioms hearer_at
#print axioms joined_place
#print axioms later_leaves
#print axioms reply_reach
#print axioms heardToken_reach
#print axioms tokSmall_reach
#print axioms tokSmallAt_reach
#print axioms tokSmallAt_border
#print axioms tokSmall_below
#print axioms heardToken_below
#print axioms tokSmallAt_below
#print axioms desc_is
#print axioms heardToken_desc
#print axioms tokSmallAt_desc

end IM
