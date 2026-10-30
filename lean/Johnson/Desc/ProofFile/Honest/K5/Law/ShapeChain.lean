-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ShapeChain.lean: CONDITIONAL: THE CUT "STRUCTURE | VALUES" AT
THE MEMBER OF THE KIND "AN ATTENTION SEGMENT's OWN ROUNDS" (K5), AT THE FIRST CHAIN's OWN SHAPE
(ChainSh, chainSh: Johnson/Desc/First/Shape/Chain.lean; firstShape: Honest/Thread/ShapeFirst.lean).
Definitions, and statements with their proofs.

Why. Honest/K5/Law/ShapeMember.lean has Carries and Returns at the kind's member for the kind's own
shape of five readers. The rule of Honest/Thread/Shape.lean takes one shape for a whole chain. Three
links lie between: the kind's shape is read off the chain's; the kind's Bool and update act through
that reading; the kind's step leaves every other component.

Main names:
  k5Of, k5Of_chainSh   the kind's five readers off the chain's shape; at a state's shape they are
    the kind's own
  k5GC, k5StepC   **the kind's one Bool and one update on the chain's shape**
  chainSh_behind   **every other component of the chain's shape is left by the kind's step**
  k5_chain_carries   Carries for the kind's own decision, at the chain's shape
  first_ok, k5_carries_first, k5_returns_first   **Carries and Returns at the member, at
    firstShape guard upd vals**
  k5_first_at_head   both at the kind's member of a group of the proof file's own flat list
  k5GC_at_thr   the Bool says yes wherever the first chain's thread stands in front of the kind's
    member

Conditional on: chainSh_behind: an attention link stands open. k5_chain_carries: the decision's yes
and the Bool's yes. The two at the member: blk is the member number b and decides as the kind's
decision with the two tests more (DecidesAs, Honest/K5/Law/Member.lean); AT THE BORDER b the letters
guard and upd are k5GC and k5StepC at the place's numbers. k5_first_at_head: also the hypothesis on
the public input (P5J.AtMgA, Johnson/P5J/MgAtAll.lean), which is proved of nothing here.
k5GC_at_thr: that, the plan's facts, and the thread's sentence at the border.
Whose. By the authors of the attention sub-protocol's (K5's) own rounds.
Limits. ONE MEMBER's SHARE: the rule wants Carries at every member in front and the run's yes: of
other members' letters nothing is said, and that the shape's run returns is not proved here. The
Bool is sufficient, not necessary. Of the kind's runs of claims nothing is said. The chain's shape
sees of the tables of an attention link their list alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ShapeMember
import Johnson.Desc.ProofFile.Honest.Thread.ShapeFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Strs Chain Claim First.S First.AttOwn noDigest step_iff)
open VerifiableInference.Desc.Part.MaskedSum (Fits)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ledSh attOwnSh attOf)
open H2K5.Honest (K5Sh k5Sh k5G k5Step k5_shape_carries k5_shape_returns k5_yes_is readyO_of_G
  k5_returns_whole)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-! ## 1 The kind's five readers, off the chain's shape -/

/-- The kind's shape (`K5Sh`, Johnson/Desc/K5/Honest/Law/ShapeK5.lean) read off the first chain's
shape (`ChainSh`, Johnson/Desc/First/Shape/Chain.lean): five of its components, of look that it is
laid. -/
def k5Of (a : ChainSh) : K5Sh :=
  { marked := a.marked, rowsOwed := a.rowsOwed, look := a.look.isSome, led := a.led, att := a.att }

/-- **At a state's shape it is the kind's own reader of the state.** -/
theorem k5Of_chainSh (s : First.S) : k5Of (chainSh s) = k5Sh s := by
  show K5Sh.mk s.failed.isSome s.rowsOwed (s.look?.map _).isSome (s.fork?.map ledSh)
    (attOf s.here) = K5Sh.mk s.failed.isSome s.rowsOwed s.look?.isSome (s.fork?.map ledSh)
    (attOf s.here)
  rw [Option.isSome_map]

/-- **The kind's guards as one Bool on the chain's shape.** -/
def k5GC (x : Params.AttentionRounds) (a : ChainSh) : Bool := k5G x (k5Of a)

/-- **The kind's step as one update of the chain's shape**: three components are laid; all the
others stand as they were. -/
def k5StepC (x : Params.AttentionRounds) (a : ChainSh) : ChainSh :=
  ((a.setRowsOwed none).layLed (k5Step x (k5Of a)).led).layAtt (k5Step x (k5Of a)).att

/-! ## 2 The kind's own decision, at the chain's shape -/

/-- **EVERY OTHER COMPONENT OF THE CHAIN's SHAPE IS LEFT BY THE KIND's STEP**: the shape of the
state behind the lay is the shape in front with three components laid. CONDITIONAL: an attention
link stands open. -/
theorem chainSh_behind {s : First.S} {a : First.AttOwn} (ha : s.here = .att a) (hd : Heard)
    (G : Fork) :
    chainSh (behind s a hd G) =
      (((chainSh s).setRowsOwed none).layLed (some (ledSh G))).layAtt
        (some (attOwnSh { a with F := G, heard5 := some hd })) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  simp only at ha
  subst ha
  rfl

/-- **Carries, for the kind's own decision, at the chain's shape.** CONDITIONAL on the decision's
yes and the Bool's yes. -/
theorem k5_chain_carries (p : Par) {s s' : First.S} {rs : List Fmt.RoundView}
    (h : decide seatSO p s rs = .ok s') (hG : k5GC p.own (chainSh s) = true) :
    chainSh s' = k5StepC p.own (chainSh s) := by
  have hG' : k5G p.own (k5Sh s) = true := by
    rw [← k5Of_chainSh]
    exact hG
  have e := k5_shape_carries p h hG'
  obtain ⟨a, hd, G, ha, _, rfl⟩ := k5_yes_is p h
  rw [chainSh_behind ha]
  unfold k5StepC
  rw [k5Of_chainSh, ← e]
  rfl

/-! ## 3 At the member, at the first chain's letters of the cut -/

section
variable {bs : List (Block First.S Claim)} {ft b : Nat} {p : Par} {blk : Block First.S Claim}
  {guard : Nat → ChainSh → Bool} {upd : Nat → ChainSh → ChainSh}
  {vals : Nat → First.S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}

/-- The guards' return at the form "one Bool and one update a member". -/
theorem first_ok {a t : ChainSh} (h : (firstShape guard upd vals).g b a = .ok t) :
    guard b a = true ∧ t = upd b a := by
  have h' : (if guard b a then Except.ok (upd b a)
      else Except.error "a guard on the shape") = .ok t := h
  cases e : guard b a with
  | true =>
    rw [e] at h'
    exact ⟨rfl, (Except.ok.inj h').symm⟩
  | false =>
    rw [e] at h'
    cases h'

/-- **CARRIES AT THE KIND's MEMBER, AT THE FIRST CHAIN's OWN SHAPE** (`firstShape`,
Honest/Thread/ShapeFirst.lean). CONDITIONAL on: blk is the member number b and decides as the kind's
decision with the two tests more; AT THE BORDER b the letters guard and upd are the kind's Bool and
update. Of the letters at other borders, and of vals, nothing is asked. -/
theorem k5_carries_first (hb : bs[b]? = some blk) (Dc : DecidesAs p blk)
    (hg : guard b = k5GC p.own) (hu : upd b = k5StepC p.own) :
    Carries bs ft (firstShape guard upd vals) b := by
  intro blk' hb' s rs cols s' n t hs h
  obtain rfl : blk = blk' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨hG, rfl⟩ := first_ok h
  obtain ⟨_, hd, _⟩ := (step_iff ft blk s s' rs cols n).1 hs
  rw [hg] at hG
  rw [hu]
  exact (k5_chain_carries p ((Dc.decides _ _ _ _).1 hd).1 hG).symm

/-- **RETURNS AT THE KIND's MEMBER, AT THE FIRST CHAIN's OWN SHAPE.** CONDITIONAL as
`k5_carries_first`, without upd. The premise on the tests on values is not spent: the kind's member
has none. -/
theorem k5_returns_first (hb : bs[b]? = some blk) (Dc : DecidesAs p blk)
    (hg : guard b = k5GC p.own) : Returns bs ft (firstShape guard upd vals) b := by
  intro blk' hb' s rs cols t h hF _
  obtain rfl : blk = blk' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨hG, _⟩ := first_ok h
  rw [hg] at hG
  have hG' : k5G p.own (k5Sh s) = true := by
    rw [← k5Of_chainSh]
    exact hG
  have R := readyO_of_G p hG'
  have h1 : VerifiableInference.Desc.roundsFit (rounds p) rs = true := by
    rw [← Dc.rounds]
    exact hF.1
  obtain ⟨a, hd, G, _, _, hdec, B⟩ :=
    k5_returns_whole p Dc.plan R (fits_of_roundsFit _ _ h1 (rounds_plain p))
  exact ⟨_, (Dc.decides _ _ _ _).2 ⟨hdec, B.failed.trans R.clean, same_of_out s _ B.out⟩⟩

end

/-! ## 4 At the library's own letters -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **BOTH AT THE KIND's MEMBER OF GROUP g OF THE PROOF FILE's OWN FLAT LIST, AT THE FIRST CHAIN's
OWN SHAPE.** CONDITIONAL: under the hypothesis h, which is proved of nothing here; g is below 12; a
is the plan of group g; at the kind's border the letters guard and upd are the kind's. -/
theorem k5_first_at_head {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) (ft : Nat) {guard : Nat → ChainSh → Bool}
    {upd : Nat → ChainSh → ChainSh}
    (vals : Nat → First.S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hG : guard (borderOf g) = k5GC (parAt Zp g a).own)
    (hU : upd (borderOf g) = k5StepC (parAt Zp g a).own) :
    Carries cF.blocksInOrder ft (firstShape guard upd vals) (borderOf g) ∧
      Returns cF.blocksInOrder ft (firstShape guard upd vals) (borderOf g) := by
  obtain ⟨blk, a', hfl, Pl, Dc⟩ := k5_member h hg
  obtain rfl : a' = a := Option.some.inj (Pl.plan.symm.trans ha)
  exact ⟨k5_carries_first hfl Dc hG hU, k5_returns_first hfl Dc hG⟩

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **The Bool on the chain's shape says yes wherever the first chain's thread stands in front of
the kind's member.** CONDITIONAL: under the hypothesis h, the plan's facts, and `Thr` at the border:
none is proved here. -/
theorem k5GC_at_thr {g : Nat} (hg : g < 12) {a : Attention.Plan} (Pl : PlanAt Zp g a)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) : k5GC (parAt Zp g a).own (chainSh s) = true := by
  show k5G _ (k5Of (chainSh s)) = true
  rw [k5Of_chainSh]
  exact k5G_at_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg Pl hT

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5Of_chainSh
#print axioms ProofFile.Honest.K5.chainSh_behind
#print axioms ProofFile.Honest.K5.k5_chain_carries
#print axioms ProofFile.Honest.K5.first_ok
#print axioms ProofFile.Honest.K5.k5_carries_first
#print axioms ProofFile.Honest.K5.k5_returns_first
#print axioms ProofFile.Honest.K5.k5_first_at_head
#print axioms ProofFile.Honest.K5.k5GC_at_thr
#print axioms ProofFile.Honest.K5.k5Of
#print axioms ProofFile.Honest.K5.k5GC
#print axioms ProofFile.Honest.K5.k5StepC
