-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LTPileR/AtGate.lean (over three files:
Johnson/IMR/MemberPath.lean, MemberOfGate.lean and OpenFlat.lean): THE EXAMPLES FOR TWO
FACTS ALONG THE FOLD: THEIR CONDITIONS ARE MET, AND THE FACTS HOLD AT A REACHED STATE AT EVERY
BORDER, WHEREVER TWO TESTS ON verify()'S OWN ROAD ACCEPT.



Three of the theorems (`fact_each`, `fact_on_path`, `req_at_gate`) rest on `member_each` and
`member_path` (Johnson/IMR/MemberPath.lean).


Main names (namespace `Meaning.K2`).
  `weights_at_open`, `req_at_open`: the two facts (`weightsB a.2 = true`; under "no mark": `a.2.req
    = Verify.words32 a.1.request`) at every `Reach ft c.blocksInOrder (ProofFile.startS Z) k a`, AT THE CHAIN c OF
    A GIVEN OPENING `IM.Open … c …`, under `Block.planOk` at every sub-protocol of `c.blocksInOrder`: by
    `open_fold_all` (OpenFlat.lean) at `seatKeeps_rides` | `seatBack_rides weights_pileLaw` and
    `seatKeeps_req` | `seatBack_req`. (WeightsReached.lean's and ReqSeat.lean's forms
    bind a chain of their own behind "there is".)
  **`fact_at_gate`**: ONCE, GENERAL IN THE FACT: from
    `VerifierAndGoals.InScope P = true` and `FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true`:
    for every Fact that holds at every reached state of every opening's own chain: the IOP as
    written in Lean is made, it opens, every sub-protocol passes its test on the list of rounds,
    there are 358, and AT EVERY BORDER k ≤ 358 THERE IS A STATE, REACHED IN THE NARROWER SENSE
    (`c.blocksInOrder.map Sound.below`), AT WHICH THE FACT HOLDS.
  **`fact_each`**: THE SAME FOR A FACT UNDER THE FENCE "NO MARK": at every border there is a state,
    reached in the narrower sense, WITHOUT A MARK, at which the fact holds. **`fact_on_path`**: the
    same along ONE LIST OF STATES st, each stepping to the next by `StepYes 0 (Sound.below b)`, from
    the chain's own start. A field's example is one of these three with the field applied.
  **`weights_at_gate`**: so for `weightsB`. **`req_at_gate`**: for the request's words, AT EVERY
    BORDER. `req_at_gate_last`: the form at the last border alone.

Every "there is", walked. F, Z, Bs, base, c, A, B: tied by the opening. s, e, st: tied by `Reach`
(st also by its start and its steps).
WHO PAYS THE TWO PREMISES. No theorem. By a text of this project that is not in this repository, on
`member_of_gate`, they are two tests that the run which counts over the stored full-size files
printed as accepted; that tie is BY READING, with four gaps which that text names.
Limits. AT o := `OnBytes.secondHashFunction` (the two forms at an opening: at every o). Which state is not said.
`fact_on_path`'s steps bind their rounds and columns under "there are", each step apart: that they
are one transcript's is not said. "No mark" is shown of SOME reached state at each border, not of
every one. Nothing on a cheating prover's reached states beyond what the two facts themselves say.
Nothing on soundness or on hiding.

-/
import Johnson.IMR.MemberPath
import Johnson.IMR.OpenFlat
import Johnson.LTPileR.WeightsReached
import Johnson.LTPileR.ReqSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Pub Cl)
open Johnson.Desc.First.Walk.Tied (Reach StepYes reach_raw)

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The pending rows' weights, at an opening's own chain.** -/
theorem weights_at_open (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (ft k : Nat) (a : ProofFile.InstPub × S)
    (h : Reach ft c.blocksInOrder (ProofFile.startS Z) k a) : weightsB a.2 = true := by
  obtain ⟨-, rs, cols, hf⟩ := h.fold
  exact open_fold_all (seatKeeps_rides weights_pileLaw) (seatBack_rides weights_pileLaw) O trivial
    (fun _ _ _ => trivial) hp k hf (weights_start O.pub a.1)

/-- **The request's words, at an opening's own chain.** -/
theorem req_at_open (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (ft k : Nat) (a : ProofFile.InstPub × S)
    (h : Reach ft c.blocksInOrder (ProofFile.startS Z) k a) (hm : a.2.failed = none) :
    a.2.req = Verify.words32 a.1.request := by
  obtain ⟨-, rs, cols, hf⟩ := h.fold
  have q : ReqStays (ProofFile.startS Z a.1) a.2 :=
    open_fold_all seatKeeps_req seatBack_req O trivial (fun _ _ _ => trivial) hp k hf
  rw [q.1]
  exact req_start Z a.1 (q.2 hm)

end

/-- **ONCE, GENERAL IN THE FACT**: a fact that holds at every reached state of every opening's own
chain is met, at every border, wherever the two tests on verify()'s own road accept. -/
theorem fact_at_gate {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true)
    (Fact : Pub → ProofFile.InstPub × S → Prop)
    (H : ∀ (F : FileDescription ProofFile.Inst) (Z : Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B →
      (∀ b ∈ c.blocksInOrder, b.planOk = true) →
      ∀ k a, Reach 0 c.blocksInOrder (ProofFile.startS Z) k a → Fact Z a) :
    ∃ (F : FileDescription ProofFile.Inst) (Z : Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F ∧
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      (∀ b ∈ c.blocksInOrder, b.planOk = true) ∧ c.blocksInOrder.length = 358 ∧
      ∀ k ≤ 358, ∃ s,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, s) ∧
        Fact Z ((LPFD.Full.instanceAsPlainRecord z).pub, s) := by
  obtain ⟨-, F, Z, Bs, base, c, A, B, -, hF, O, -, hp, hl, hr, -, -⟩ := IM.member_of_gate hS hg
  refine ⟨F, Z, Bs, base, c, A, B, hF, O, hp, hl, fun k hk => ?_⟩
  obtain ⟨s, h1, h2⟩ := hr k hk
  exact ⟨s, h1, H F Z Bs base c A B O hp k _ h2⟩

/-- **THE EXAMPLE FOR "weightsOk".** -/
theorem weights_at_gate {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (F : FileDescription ProofFile.Inst) (Z : Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F ∧
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      (∀ b ∈ c.blocksInOrder, b.planOk = true) ∧ c.blocksInOrder.length = 358 ∧
      ∀ k ≤ 358, ∃ s,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, s) ∧
        weightsB s = true :=
  fact_at_gate hS hg (fun _ a => weightsB a.2 = true)
    fun _ _ _ _ _ _ _ O hp k a h => weights_at_open O hp 0 k a h

/-- **THE EXAMPLE FOR "reqIs", AT THE LAST BORDER**: the one border at which the gate's accept gives
"no mark" so far. -/
theorem req_at_gate_last {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (F : FileDescription ProofFile.Inst) (Z : Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F ∧
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      (∀ b ∈ c.blocksInOrder, b.planOk = true) ∧
      ∃ e : S,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 358 ((LPFD.Full.instanceAsPlainRecord z).pub, e) ∧
        e.failed = none ∧ e.req = Verify.words32 (LPFD.Full.instanceAsPlainRecord z).pub.request := by
  obtain ⟨-, F, Z, Bs, base, c, A, B, -, hF, O, -, hp, -, -, -, e, he, -, hm, -⟩ :=
    IM.member_of_gate hS hg
  exact ⟨F, Z, Bs, base, c, A, B, hF, O, hp, e, he, hm,
    req_at_open O hp 0 358 _ (reach_raw he) hm⟩

/-- **ONCE, GENERAL IN THE FACT, UNDER THE FENCE "NO MARK"**: a fact that holds at every reached
state without a mark of every opening's own chain is met, at every border, at a reached state
without a mark, wherever the two tests accept. -/
theorem fact_each {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true)
    (Fact : Pub → ProofFile.InstPub × S → Prop)
    (H : ∀ (F : FileDescription ProofFile.Inst) (Z : Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B →
      (∀ b ∈ c.blocksInOrder, b.planOk = true) →
      ∀ k a, Reach 0 c.blocksInOrder (ProofFile.startS Z) k a → a.2.failed = none → Fact Z a) :
    ∃ (F : FileDescription ProofFile.Inst) (Z : Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      (∀ b ∈ c.blocksInOrder, b.planOk = true) ∧
      ∀ k ≤ 358, ∃ s : S,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, s) ∧
        s.failed = none ∧ Fact Z ((LPFD.Full.instanceAsPlainRecord z).pub, s) := by
  obtain ⟨-, F, Z, Bs, base, c, A, B, -, O, hp, hr, -, -⟩ := IM.member_each hS hg
  refine ⟨F, Z, Bs, base, c, A, B, O, hp, fun k hk => ?_⟩
  obtain ⟨s, h1, h2, h3⟩ := hr k hk
  exact ⟨s, h1, h3, H F Z Bs base c A B O hp k _ h2 h3⟩

/-- **THE SAME ALONG ONE LIST OF STATES, EACH STEPPING TO THE NEXT.** -/
theorem fact_on_path {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true)
    (Fact : Pub → ProofFile.InstPub × S → Prop)
    (H : ∀ (F : FileDescription ProofFile.Inst) (Z : Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B →
      (∀ b ∈ c.blocksInOrder, b.planOk = true) →
      ∀ k a, Reach 0 c.blocksInOrder (ProofFile.startS Z) k a → a.2.failed = none → Fact Z a) :
    ∃ (F : FileDescription ProofFile.Inst) (Z : Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (st : ℕ → S),
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      (∀ b ∈ c.blocksInOrder, b.planOk = true) ∧
      st 0 = ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub ∧
      (∀ k < 358, ∃ b, c.blocksInOrder[k]? = some b ∧ StepYes 0 (Sound.below b) (st k) (st (k + 1))) ∧
      ∀ k ≤ 358,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, st k) ∧
        (st k).failed = none ∧ Fact Z ((LPFD.Full.instanceAsPlainRecord z).pub, st k) := by
  obtain ⟨-, F, Z, Bs, base, c, A, B, st, -, -, O, -, hp, -, -, h0, hs, hr, -⟩ :=
    IM.member_path hS hg
  exact ⟨F, Z, Bs, base, c, A, B, st, O, hp, h0, hs, fun k hk =>
    ⟨(hr k hk).1, (hr k hk).2.2, H F Z Bs base c A B O hp k _ (hr k hk).2.1 (hr k hk).2.2⟩⟩

/-- **THE EXAMPLE FOR "reqIs", AT EVERY BORDER.** -/
theorem req_at_gate {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (F : FileDescription ProofFile.Inst) (Z : Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      (∀ b ∈ c.blocksInOrder, b.planOk = true) ∧
      ∀ k ≤ 358, ∃ s : S,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, s) ∧
        s.failed = none ∧ s.req = Verify.words32 (LPFD.Full.instanceAsPlainRecord z).pub.request :=
  fact_each hS hg (fun _ a => a.2.req = Verify.words32 a.1.request)
    fun _ _ _ _ _ _ _ O hp k a h hm => req_at_open O hp 0 k a h hm

#print axioms fact_each
#print axioms fact_on_path
#print axioms req_at_gate
#print axioms weights_at_open
#print axioms req_at_open
#print axioms fact_at_gate
#print axioms weights_at_gate
#print axioms req_at_gate_last

end Meaning.K2
