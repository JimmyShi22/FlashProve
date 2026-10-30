-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MemberOfGate.lean: PREMISES THAT THIS FOLDER's FACTS AT "REACHED" SHARE CAN BE
MET WHEREVER TWO TESTS ON verify()'s OWN ROAD SAY YES: the goals' scope test at the public files
(VerifierAndGoals.InScope) and the proof file's decision behind its gate (FlashProve.theProofGate). From these
two alone: the goals' reader returns; ProofFile.onlineDescription returns at the second hash function; its value
can be opened (Johnson/IMR/SeatOpen.lean: Open); it accepts at the instance written of z; ProofFile.okBy
passes (the test
on the instance, but for the shared chain's part); every sub-protocol of the flat list of the first
chain of the IOP as written in Lean passes its own test on the plan; that list has 358 entries; at
every border k ≤ 358 the verifier's state is reached, at some state, from the first state at the
instance's own public part: in the narrower sense (by the steps of the wrapped sub-protocols,
Sound.below) and so in the wider; and at the last border at a state without a mark, which passes the
fold's last test and in which the reply that was heard is the reply that is asked about; the live
test passes; and the proof file's seat is laid (LPFD.Full.proofDataAndDecisionOfPublicFiles returns F's data and F's run).


laid_of_gate and member_of_gate_laid carry the last two clauses;
member_of_gate is a projection of member_of_gate_laid.

WHAT IT IS FOR. An example for a row whose premises are hS, hR, Open, "every entry of the first
chain's flat list passes its own test on the plan", ProofFile.okBy, "live", "laid", and "reached": whoever
holds a run in which the two tests were evaluated to yes calls member_of_gate and has these premises
met at that run's P, z, v₁, v₂, v₃. It evaluates nothing itself. ROWS THAT ASK "NO MARK AT THE
STATE" AT A BORDER OTHER THAN THE LAST ARE NOT SERVED BY IT: SEE Johnson/IMR/MemberPath.lean.
THE TIE TO A RUN IS BY READING, NOT BY A THEOREM: that the run's printed yes is the value of these
two terms at some P, z, v₁, v₂, v₃ (the harness's text); that compiled code computes what the terms
mean (the compiler, and whatever is natively loaded beneath); that the compiled files which ran are
those of the sources over which this file is compiled.

BUILT ON: this folder's seats and
Johnson/Top/H0/Walk/Reach.lean.
Compiled with the whole library.
HOW. The gate is "live and run" (gatedFileDecision); the run is the second part of LPFD.Full.proofDataAndDecisionOfPublicFiles at the
three files, which is (F.pull instanceAsPlainRecord).run at onlineDescription's F (laidPOf_ok). Where F.run accepts,
runCore returns (runCore_ok): the test on the instance and the test on the words of the first view
pass, the first chain's fold over the whole flat list returns with nothing left over (chainAt_fold),
the second chain's start returns and the last test passes. THE WAY UP TO THE NARROWER FAMILY: the
fold of the wrapped sub-protocols is the fold of the sub-protocols with the test on all words in
front (endOk_below, Johnson/Desc/Sound/FoldBelowProof.lean, a theorem): that test is the run's own.
A fold that returns is "reached" at its last border (reach_of_fold); the earlier borders by going
down. The last border's state: ProofFile.fileDescBy's start₃ refuses unless S.fin passes, which asks "no
mark"; its fin asks S.finAsked at the asked reply, which holds "what was heard is what is asked"
(S.heard_of_finAsked, Johnson/Desc/First/StateHeard.lean: e.heard = some asked).

  reads_of_scope   in scope the goals' reader returns.
  gate_yes         where the gate accepts: the live test passes and the run accepts.
  laid_of_gate     so onlineDescription returns some F, proofDataAndDecisionOfPublicFiles returns (D, (F.pull instanceAsPlainRecord).run), and F.run
                   accepts at instanceAsPlainRecord z. (With laidPOf_ok: F.planOk, F's data, the tests
                   of LPFD.lawsAsk.)
  run_of_gate      the same without proofDataAndDecisionOfPublicFiles's return.
  parts_of_run     where F.run accepts: the test on the instance and the first view's words pass;
                   the first chain's fold returns; the second chain's start returns; the last test
                   passes.
  okViewW_seal     the test on the words passes at the view with the seal's empty round behind.
  fold_below_of    a fold that returns with nothing left over, at a list of rounds and opened
                   columns whose words pass, returns the same over the wrapped sub-protocols.
  reach_down       what is reached at border k is reached, from the same public part, at each j ≤ k.
  end_of_run       at an opening, at every o: where F.run accepts: ProofFile.okBy passes; the last border
                   is reached in the narrower sense at a state e with S.fin e, no mark, S.finAsked e
                   at the asked reply.
  reach_of_run     so every border of the flat list is reached, narrower and wider, at one state.
  flat_len_scope   in scope the flat list has 358 entries.
  member_of_gate_laid   THE TOP, with "live" and "laid" behind.
  member_of_gate   THE TOP WITHOUT THOSE TWO: nine clauses.

OBJECT: FlashProve.theProofGate at VerifierAndGoals.asDescriptionFiles P; the first chain of ProofFile.onlineDescription's value at the
second hash. USER: rows at "reached" whose premises are those named under WHAT IT IS FOR; meant:
all files whose rows share them. LETTERS: P, z, v₁, v₂, v₃: free; all else under "there is": pp, F
by the equations beside them; Z, Bs, base, c, A, B by Open, which pins them (Open.unique); s, e: NOT
PINNED. The wider clause follows from the narrower (reach_raw): it stands for the caller's ease.

WHAT IS NOT SAID. THAT THE TWO TESTS SAY YES ANYWHERE: that is a run's to show, and no run is part
of this file. THAT verify() ACCEPTS: only the proof file's decision is spoken of: nothing of the key
file's or the entry file's decision, of the other rows in front, of hashes, paths or the commitment
ID. That a state reached at a border other than the last bears no mark. Which state is reached:
"there is", at each border apart; that the states at two borders are one run's is not stated.
Nothing of the shared or the second chain but that the second's start returns. Nothing at an o other
than `OnBytes.secondHashFunction`, but for end_of_run and reach_of_run. Nothing on a cheating prover's reached
states: premises that are met once. Sound.below is a device of the proof and runs nowhere. That the
narrower clause is RchAt (ReachAt.lean) at this description is by unfolding, by reading alone: that
file is not imported. No soundness.

-/
import Johnson.IMR.PlacesScope
import Johnson.Top.H0.Walk.Reach
import Johnson.Goal.Description.Gates
import Johnson.Goal.Tie.ReadThruHead
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Desc.RunLaws
import Johnson.Desc.FoldKeeps
import Johnson.Desc.Sound.FoldBelowProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw reach_of_fold)

/-- In scope the goals' reader returns. -/
theorem reads_of_scope {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true) :
    ∃ pp, VerifierAndGoals.readFiles P = .ok pp := by
  cases h : VerifierAndGoals.readFiles P with
  | ok pp => exact ⟨pp, rfl⟩
  | error e =>
    unfold VerifierAndGoals.InScope at hS
    rw [h] at hS
    simp at hS

/-- Where the gate accepts, the live test passes and the run accepts. -/
theorem gate_yes {Zk : OnBytes.K.Pub} {z : LPFD.Full.XF × OnBytes.Flat.RecFull}
    {v₁ v₂ v₃ : Fmt.View} (h : FlashProve.theProofGate Zk z v₁ v₂ v₃ = true) :
    FlashProve.protocolDataWellFormed Zk = true ∧ FlashProve.theProofRun Zk z v₁ v₂ v₃ = true := by
  have h' : (FlashProve.protocolDataWellFormed Zk && FlashProve.theProofRun Zk z v₁ v₂ v₃) = true := h
  exact Bool.and_eq_true_iff.1 h'

/-- **So the proof file's seat is laid: onlineDescription returns some F, LPFD.Full.proofDataAndDecisionOfPublicFiles returns F's data
and F's run, and F accepts at the instance written of z.** -/
theorem laid_of_gate {Zk : OnBytes.K.Pub} {z : LPFD.Full.XF × OnBytes.Flat.RecFull}
    {v₁ v₂ v₃ : Fmt.View} (h : FlashProve.theProofGate Zk z v₁ v₂ v₃ = true) :
    ∃ F D, ProofFile.onlineDescription OnBytes.secondHashFunction Zk.pol Zk.lay Zk.KL = .ok F ∧
      LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction Zk.pol Zk.lay Zk.KL =
        .ok (D, (F.pull LPFD.Full.instanceAsPlainRecord).run) ∧
      F.run (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ = true := by
  have hr := (gate_yes h).2
  cases hl : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction Zk.pol Zk.lay Zk.KL with
  | error e =>
    unfold FlashProve.theProofRun FlashProve.theProofRunAt at hr
    have hl'' : FlashProve.proofDataAndDecisionOrRefusalAt OnBytes.secondHashFunction Zk = .error e := hl
    rw [hl''] at hr
    cases hr
  | ok p =>
    obtain ⟨D, r⟩ := p
    have hl' : FlashProve.theProofLaid Zk = .ok (D, r) := hl
    rw [FlashProve.theProofRun_ok hl'] at hr
    obtain ⟨F, hd, -, -, -, er⟩ := LPFD.Full.laidPOf_ok hl
    subst er
    exact ⟨F, D, hd, rfl, hr⟩

/-- **So onlineDescription returns, and its value accepts at the instance written of z.** -/
theorem run_of_gate {Zk : OnBytes.K.Pub} {z : LPFD.Full.XF × OnBytes.Flat.RecFull}
    {v₁ v₂ v₃ : Fmt.View} (h : FlashProve.theProofGate Zk z v₁ v₂ v₃ = true) :
    ∃ F, ProofFile.onlineDescription OnBytes.secondHashFunction Zk.pol Zk.lay Zk.KL = .ok F ∧
      F.run (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ = true := by
  obtain ⟨F, -, hd, -, hr⟩ := laid_of_gate h
  exact ⟨F, hd, hr⟩

/-- **Where a description's run accepts**: the test on the instance and the test on the first view's
words pass; the first chain's fold over the whole flat list returns with nothing left over; the
second chain's start returns; the last test passes. -/
theorem parts_of_run {Xi : Type} {F : FileDescription Xi} {x : Xi} {v₁ v₂ v₃ : Fmt.View}
    (h : F.run x v₁ v₂ v₃ = true) :
    F.okStart x = true ∧ viewWordsBelowPrime v₁ = true ∧ ∃ e₁ e₂ e₃ s₃,
      foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound v₁).rounds
        (withEmptySealRound v₁).opened = .ok (e₁, [], []) ∧
      F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧ F.fin x e₁ e₂ e₃ = true := by
  unfold FileDescription.run at h
  cases hq : F.runEnd x v₁ v₂ v₃ with
  | error e => simp [hq, Except.isOk, Except.toBool] at h
  | ok r =>
    obtain ⟨e₁, e₂, e₃⟩ := r
    unfold FileDescription.runEnd at hq
    obtain ⟨-, k₀, w₁, -, -, j₁, -, ⟨s₃, j₃, -⟩, jf⟩ := VerifiableInference.Desc.runCore_ok.1 hq
    exact ⟨k₀, w₁, e₁, e₂, e₃, s₃, Keeps.chainAt_fold _ _ _ _ _ _ j₁, j₃, jf⟩

/-- The test on the words passes at the view with the seal's empty round behind. -/
theorem okViewW_seal (v : Fmt.View) (h : viewWordsBelowPrime v = true) :
    viewWordsBelowPrime ⟨(withEmptySealRound v).rounds, (withEmptySealRound v).opened⟩ = true := by
  have t := Sound.okViewW_app v.rounds [⟨[], ⟨[], [], [], none⟩⟩] v.opened []
  rw [List.append_nil] at t
  have h' : viewWordsBelowPrime ⟨v.rounds, v.opened⟩ = true := h
  show viewWordsBelowPrime ⟨v.rounds ++ [⟨[], ⟨[], [], [], none⟩⟩], v.opened⟩ = true
  rw [t, h']
  rfl

section
variable {T C Q : Type}

/-- **THE WAY UP**: a fold that returns with nothing left over, at a list of rounds and opened
columns whose words pass the test, returns the same over the wrapped sub-protocols. -/
theorem fold_below_of {ft : ℕ} {bs : List (Block T C)} {s e : T} {rs : List Fmt.RoundView}
    {cs : List OpenedColumn} (hw : viewWordsBelowPrime ⟨rs, cs⟩ = true)
    (h : foldBlocks ft bs s rs cs = .ok (e, [], [])) :
    foldBlocks ft (bs.map Sound.below) s rs cs = .ok (e, [], []) := by
  have q := Sound.endOk_below ft bs s rs cs
  rw [if_pos hw, h] at q
  have q' : endOk (foldBlocks ft (bs.map Sound.below) s rs cs) = some e := q
  generalize foldBlocks ft (bs.map Sound.below) s rs cs = X at q'
  match X, q' with
  | .ok (s', [], []), q' =>
    obtain rfl : s' = e := Option.some.inj q'
    rfl

/-- What is reached at a border is reached, from the same public part, at each border in front. -/
theorem reach_down {ft : ℕ} {bs : List (Block T C)} {start : Q → T} {k : ℕ} {a : Q × T}
    (h : Reach ft bs start k a) : ∀ j ≤ k, ∃ s, Reach ft bs start j (a.1, s) := by
  induction h with
  | zero z =>
    intro j hj
    obtain rfl : j = 0 := Nat.le_zero.1 hj
    exact ⟨start z, Reach.zero z⟩
  | @succ k z s s' b R hb hy ih =>
    intro j hj
    by_cases e : j = k + 1
    · subst e
      exact ⟨s', Reach.succ R hb hy⟩
    · exact ih j (by omega)

end

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **Where the run accepts, at an opening, at every o**: ProofFile.okBy passes (the test on the instance,
but for the shared chain's part), and the last border of the first chain's flat list is reached, in
the narrower sense, from the first state at the instance's own public part, at a state that passes
the fold's last test, bears no mark, and in which the reply that was heard is the reply that is
asked about. -/
theorem end_of_run (O : Open o pol lay KL F Z Bs base c A B) {x : ProofFile.Inst}
    {v₁ v₂ v₃ : Fmt.View} (hr : F.run x v₁ v₂ v₃ = true) :
    ProofFile.okBy o ProofFile.pureRoad.links Z x = true ∧
      ∃ e : S, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length (x.pub, e) ∧
        e.fin = true ∧ e.failed = none ∧ e.finAsked x.asked = true := by
  obtain ⟨k₀, w₁, e₁, e₂, e₃, s₃, hf, h₃, hfin⟩ := parts_of_run hr
  have eF := O.desc
  subst eF
  have k₀' : (ProofFile.okBy o ProofFile.pureRoad.links Z x && A.okInst x.pub) = true := k₀
  have hf' : foldBlocks 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
      (withEmptySealRound v₁).opened = .ok (e₁, [], []) := hf
  have hb := fold_below_of (okViewW_seal v₁ w₁) hf'
  have R : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) (c.blocksInOrder.map Sound.below).length
      (x.pub, e₁) :=
    reach_of_fold _ (Nat.le_refl _) e₁ _ [] _ [] (by rw [List.take_length]; exact hb)
  rw [List.length_map] at R
  have hE : S.fin e₁ = true := by
    have h₃' : (if !(S.fin e₁) then (.error "the first chain does not stand at its end" :
        Except String B.σ) else
      match A.ended e₂ with
      | none => .error "the shared chain has not ended"
      | some e => B.start x.pub e₁ e) = .ok s₃ := h₃
    cases hq : S.fin e₁ with
    | true => rfl
    | false => rw [hq] at h₃'; cases h₃'
  have hM : S.failed e₁ = none := by
    have q := hE
    unfold S.fin at q
    rw [Bool.and_eq_true, Bool.and_eq_true] at q
    exact Option.isNone_iff_eq_none.1 q.1.1
  have hA : S.finAsked x.asked e₁ = true := by
    have q : (S.finAsked x.asked e₁ && S.req e₁ == OnBytes.Model.Verify.words32 x.pub.request &&
      (A.ended e₂).isSome && B.done e₃) = true := hfin
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at q
    exact q.1.1.1
  exact ⟨(Bool.and_eq_true_iff.1 k₀').1, e₁, R, hE, hM, hA⟩

/-- **So every border of the first chain's flat list is reached from the first state at the
instance's own public part**, in the narrower sense and in the wider, at one state. -/
theorem reach_of_run (O : Open o pol lay KL F Z Bs base c A B) {x : ProofFile.Inst}
    {v₁ v₂ v₃ : Fmt.View} (hr : F.run x v₁ v₂ v₃ = true) :
    ∀ k ≤ c.blocksInOrder.length, ∃ s, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (x.pub, s) ∧
      Reach 0 c.blocksInOrder (ProofFile.startS Z) k (x.pub, s) := by
  obtain ⟨-, e, R, -⟩ := end_of_run O hr
  intro k hk
  obtain ⟨s, hs⟩ := reach_down R k hk
  exact ⟨s, hs, reach_raw hs⟩

end

/-- In scope the first chain's flat list has 358 entries. -/
theorem flat_len_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : c.blocksInOrder.length = 358 := by
  rw [← List.length_map (f := (·.place)), places_scope hS hR O, places_len]

/-- **THE SAME WITH "LIVE" AND "LAID" BEHIND**: member_of_gate's nine clauses; the live test passes;
the proof file's seat is laid. -/
theorem member_of_gate_laid {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
      (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      VerifierAndGoals.readFiles P = .ok pp ∧
      ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F ∧
      Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      F.run (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ = true ∧
      (∀ b ∈ c.blocksInOrder, b.planOk = true) ∧
      c.blocksInOrder.length = 358 ∧
      (∀ k ≤ 358, ∃ s,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, s) ∧
        Reach 0 c.blocksInOrder (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, s)) ∧
      ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z (LPFD.Full.instanceAsPlainRecord z) = true ∧
      (∃ e : S,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 358 ((LPFD.Full.instanceAsPlainRecord z).pub, e) ∧
        e.fin = true ∧ e.failed = none ∧ e.finAsked (LPFD.Full.instanceAsPlainRecord z).asked = true) ∧
      FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true ∧
      ∃ D, LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL =
        .ok (D, (F.pull LPFD.Full.instanceAsPlainRecord).run) := by
  obtain ⟨pp, hR⟩ := reads_of_scope hS
  obtain ⟨F, D, hd, hlaid, hr⟩ := laid_of_gate hg
  have hd' : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F := hd
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := seat_open hd'
  have hlen := flat_len_scope hS hR O
  have hp : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
    have PP := FileDescription.planOk_parts_of_run hr
    have eF := O.desc
    subst eF
    exact fun b hb => (PP.blocks₁ b hb).1
  have q := reach_of_run O hr
  have q' := end_of_run O hr
  rw [hlen] at q q'
  exact ⟨pp, F, Z, Bs, base, c, A, B, hR, hd', O, hr, hp, hlen, q, q'.1, q'.2, (gate_yes hg).1, D,
    hlaid⟩

/-- **PREMISES THAT FACTS AT "REACHED" SHARE, FROM TWO TESTS ON verify()'s OWN ROAD**: the scope
test at the public files and the proof file's decision behind its gate. -/
theorem member_of_gate {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
      (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      VerifierAndGoals.readFiles P = .ok pp ∧
      ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F ∧
      Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      F.run (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ = true ∧
      (∀ b ∈ c.blocksInOrder, b.planOk = true) ∧
      c.blocksInOrder.length = 358 ∧
      (∀ k ≤ 358, ∃ s,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, s) ∧
        Reach 0 c.blocksInOrder (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, s)) ∧
      ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z (LPFD.Full.instanceAsPlainRecord z) = true ∧
      ∃ e : S,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 358 ((LPFD.Full.instanceAsPlainRecord z).pub, e) ∧
        e.fin = true ∧ e.failed = none ∧ e.finAsked (LPFD.Full.instanceAsPlainRecord z).asked = true := by
  obtain ⟨pp, F, Z, Bs, base, c, A, B, hR, hF, O, hr, hp, hlen, hk, hx, he, -, -⟩ :=
    member_of_gate_laid hS hg
  exact ⟨pp, F, Z, Bs, base, c, A, B, hR, hF, O, hr, hp, hlen, hk, hx, he⟩

#print axioms reads_of_scope
#print axioms gate_yes
#print axioms laid_of_gate
#print axioms run_of_gate
#print axioms parts_of_run
#print axioms okViewW_seal
#print axioms fold_below_of
#print axioms reach_down
#print axioms end_of_run
#print axioms reach_of_run
#print axioms flat_len_scope
#print axioms member_of_gate_laid
#print axioms member_of_gate

end IM
