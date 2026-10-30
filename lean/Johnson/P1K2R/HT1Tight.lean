-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/HT1Tight.lean: code switching (K2): THE BINDER hT1 OF K2AllOwes
(Johnson/Top/H0/K2Ties/Assembly.lean; the same binder of K2Caller/TieOneR.lean | TieFourR.lean) AT
EACH OF THE 25 PLACES, IN THE TIGHT FORM: from the head, one named test's accept, one named equation
on the chain, and ONE FIELD OF FoldFacts at «reached».
  hT1_link     the switch into group m + 1, m < 23 (number 14 (m + 1) + 2): over foldSideR_one
               (m = 0) and foldSideR_link (1 ≤ m)
  hT1_head     the output head's switch, into group 24 (number 339): over foldSideR_head
  hT1_fin      the finish's switch, into group 25 (number 353): over foldSideR_fin
  written3     the public part's codes, shape and listed shapes are the written ones
  msgCount_link · msgCount_head · msgCount_fin  at a state reached in front of a switch the
               statement holds the closed number of oracle messages
  noMark_link · noMark_closing  a state reached at 14 g + 2 (g ≤ 24), or at 14 l + 12 (l < 24),
               bears no mark
  shapes_reached · olds_reached  the field msgShapes, read as foldSideR_*'s He | He0 ask it
EACH ARM ENDS IN hT1's END, TO THE LETTER, at f₀ := fxAt r · W := the written front's frame · grp :=
g · rows := 0 · n0 := K2.n0At g · olds := K2.oldsAt g · r := the written table's entry g - 1: the
test frontB2 accepts · the typed list of new members is tied to the notices · the invariant on
stored sample rows holds at the front's statement · the test storedB accepts · the state's and the
front's statements hold the same oracle messages.
WHAT STANDS IN FRONT, BY NAME.
  THE HEAD: hS: in scope · hR: the files read · O: the opening, at the public files' own layout
      file · hF: onlineDescription returns F · hpl: F.planOk.
  ONE NAMED TEST: hy: madePinnedAt accepts: so the public part's codes, shape and listed shapes are
      the written ones (written3: the first three clauses of written_in_scope,
      Johnson/Top/H0/K2Hands/WrittenInScope.lean, by first_written_in_scope | sends_in_scope; its
      fourth clause wants K2Caller/ClosedAt25.lean, which is not beneath this file). The Lean
      verifier asks it as its entry test 9, madeRow (Johnson/Desc/Laid/ProofAsks.lean).
  ONE EQUATION ON THE CHAIN: hcut: its sub-protocols have the written cut (cut_of_row): for
      the counts (Johnson/IMR/ToldPaid.lean's n0_at_link_paid | _head_paid | _finish_paid ·
      counts_at_cut_paid) and for «the kept old messages lie below the count in front of the
      closing» (olds_of_test, Johnson/Top/H0/K2Hands/FoldSideOf.lean).
  ONE FIELD OF FoldFacts: msgShapes, in the field's own letters at at_ := (·.1), d.M := the shapes
      listed off the public part's first chain's sendings.
  hRch: Rch IS «reached»: Rch k x ↔ Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1: Tied.RchAt
      unfolds to the right side. Both directions are spent: the field is also read at the states
      reached earlier (in front of the last closing), with x.2 carried over.
  THE WAY IN: hent: at a link and at the head what the way in lets in is the state itself; at the
      finish it is what K2.finishFrontQ lets in.
NOT SPENT OF hT1's OWN BINDER: the promise in front (onQ …) and «the state bears no mark»: at these
numbers every reached state is without a mark (noMark_reach_below, Johnson/IMR/NoMarkReach.lean). A
caller drops the two.
LIMITS. A join: every step is a call. No premise is shown met at a real value: no example. The ends
say nothing at a state of which the switch's text makes no front. The full size alone. No
probability; no soundness is claimed.
-/
import Johnson.P1K2R.FoldSideR
import Johnson.P1K2R.FoldSidePaid
import Johnson.IMR.NoMarkReach
import Johnson.Goal.Numbers.MadeInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.First.K2Hands (frontB2 placeFrame Tied csW MW shapes_of_test
  olds_of_test)
open VerifiableInference.PlanWritten.Joined (sends_in_scope first_written_in_scope)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.G (fxAt storedB)
open _root_.Tw.K2 (switchNotices)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The public part's codes, shape and listed shapes are the written ones: the first three clauses
of written_in_scope (K2Hands/WrittenInScope.lean), by the two calls of its own proof. -/
theorem written3 {o : ProofFile.SecondHashFunctionArgument} (hS : VerifierAndGoals.InScope P = true)
    (h : ProofFile.pureRoad.pub o P.pol P.lay P.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.first.codes = csW ∧ Z.first.shape = K2Hands.shW ∧
      K12.Door.msgsOfChain Z.made.proof.1 = MW := by
  have f := first_written_in_scope hS h hy
  exact ⟨f.1, f.2.2.1, by rw [sends_in_scope hS h hy]; rfl⟩

/-! ## The counts and «no mark», at reached states -/

theorem msgCount_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull) {g : ℕ} (h1 : 1 ≤ g)
    (h2 : g ≤ 23) {z : ProofFile.InstPub} {t : S}
    (ht : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * g + 2) (z, t)) :
    t.st.oracles.size = K2.n0At g := by
  obtain ⟨-, R, C, f⟩ := (reach_raw ht).fold
  exact Meaning.Carry.n0_at_link_paid hS hR O hcut h1 h2
    (fun b hb => plan_of O hpl b (List.mem_of_mem_take hb)) z R C (t, [], []) f

theorem msgCount_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull) {z : ProofFile.InstPub} {t : S}
    (ht : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, t)) :
    t.st.oracles.size = K2.n0At 24 := by
  obtain ⟨-, R, C, f⟩ := (reach_raw ht).fold
  exact Meaning.Carry.n0_at_head_paid hS hR O hcut
    (fun b hb => plan_of O hpl b (List.mem_of_mem_take hb)) z R C (t, [], []) f

theorem msgCount_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull) {z : ProofFile.InstPub} {t : S}
    (ht : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, t)) :
    t.st.oracles.size = K2.n0At 25 := by
  obtain ⟨-, R, C, f⟩ := (reach_raw ht).fold
  exact Meaning.Carry.n0_at_finish_paid hS hR O hcut
    (fun b hb => plan_of O hpl b (List.mem_of_mem_take hb)) z R C (t, [], []) f

/-- A state reached at 14 g + 2, g ≤ 24, bears no mark. -/
theorem noMark_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} {z : ProofFile.InstPub} {t : S}
    (ht : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * g + 2) (z, t)) : t.failed = none :=
  IM.noMark_reach_below hS hR O ht (by omega) fun l _ => by unfold IM.nAt; split <;> omega

/-- A state reached at 14 l + 12 bears no mark. -/
theorem noMark_closing (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} {z : ProofFile.InstPub} {t : S}
    (ht : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 12) (z, t)) : t.failed = none :=
  IM.noMark_reach_below hS hR O ht (by omega) fun l' _ => by unfold IM.nAt; split <;> omega

/-! ## The field msgShapes, read as foldSideR_* ask it -/

section
variable {Str : Type} {Rch : ℕ → (ProofFile.InstPub × S) × Str → Prop}

/-- He: at a reached state without a mark each oracle message has the listed shape. σ: any value of
the second component, carried over. -/
theorem shapes_reached
    (hRch : ∀ k x, Rch k x ↔ Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (msgShapes : ∀ k x, Rch k x → x.1.2.failed = none →
      K12.Door.atFirstShapes (K12.Door.msgsOfChain Z.made.proof.1) x.1.2 = true)
    (hM : K12.Door.msgsOfChain Z.made.proof.1 = MW) (σ : Str) {k : ℕ} {z : ProofFile.InstPub} {t : S}
    (ht : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, t)) (hu : t.failed = none) :
    ∀ o, o < t.st.oracles.size → (t.st.oracles[o]?).map (·.shape) = MW[o]? :=
  shapes_of_test (msgShapes k ((z, t), σ) ((hRch k ((z, t), σ)).2 ht) hu) hM

/-- He0: at a state reached in front of link l's last closing, at the kept old numbers. -/
theorem olds_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hRch : ∀ k x, Rch k x ↔ Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (msgShapes : ∀ k x, Rch k x → x.1.2.failed = none →
      K12.Door.atFirstShapes (K12.Door.msgsOfChain Z.made.proof.1) x.1.2 = true)
    (hM : K12.Door.msgsOfChain Z.made.proof.1 = MW) (σ : Str) {l : ℕ} (hl : l < 24)
    {z : ProofFile.InstPub} {t : S}
    (ht : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 12) (z, t)) :
    ∀ o ∈ K2.oldsAt (l + 1), (t.st.oracles[o]?).map (·.shape) = MW[o]? := by
  obtain ⟨-, R, C, f⟩ := (reach_raw ht).fold
  exact olds_of_test hl hcut
    ((Meaning.Carry.counts_at_cut_paid hS hR O z R C (14 * l + 12) (by omega)
      (fun b hb => plan_of O hpl b (List.mem_of_mem_take hb)) (t, [], []) f).1.trans
        (Meaning.Carry.toldBefore_eq c.blocksInOrder (14 * l + 12)).symm)
    (msgShapes _ ((z, t), σ) ((hRch _ ((z, t), σ)).2 ht) (noMark_closing hS hR O ht)) hM

/-! ## hT1, three statements over foldSideR_*'s four -/

/-- **hT1 AT THE SWITCH INTO GROUP m + 1, m < 23.** -/
theorem hT1_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hRch : ∀ k x, Rch k x ↔ Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (msgShapes : ∀ k x, Rch k x → x.1.2.failed = none →
      K12.Door.atFirstShapes (K12.Door.msgsOfChain Z.made.proof.1) x.1.2 = true)
    {m : ℕ} (h23 : m < 23)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → t = s) {q : K2.P2}
    (hq : q.stands = .link) {r : SwRow} (hrw : tableFullLit[m]? = some r) {W : SwitchFrame}
    (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Str, Rch (14 * (m + 1) + 2) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt q t = some fx →
      frontB2 (fxAt r) W (m + 1) 0 (K2.n0At (m + 1)) (K2.oldsAt (m + 1)) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W (K2.n0At (m + 1)) (K2.oldsAt (m + 1))) fx = true ∧
        a.1.st.oracles = fx.st.oracles := by
  intro z a ha t he fx hfx
  obtain rfl := hent _ _ he
  obtain ⟨hcs, hsh, hM⟩ := written3 hS O.pub hy
  have hr := (hRch _ _).1 ha
  have hu := noMark_link hS hR O (g := m + 1) hr
  have Hn2 := msgCount_link hS hR O hpl hcut (g := m + 1) (by omega) (by omega) hr
  have He := shapes_reached hRch msgShapes hM a.2 hr hu
  have He0 := fun t ht => olds_reached hS hR O hpl hcut hRch msgShapes hM a.2 (l := m) (z := z)
    (t := t) (by omega) ht
  obtain ⟨W₀, hW, K⟩ : ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ (m + 1) 0 (K2.n0At (m + 1)) (K2.oldsAt (m + 1)) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At (m + 1)) (K2.oldsAt (m + 1))) fx = true ∧
        a.1.st.oracles = fx.st.oracles) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact foldSideR_one hS hR O hF hpl hcs hsh hr Hn2 He He0 hq hfx hrw
    · exact foldSideR_link hS hR O hF hpl hcs hsh hm h23 hr
        (fun t ht => msgCount_link hS hR O hpl hcut hm (by omega) ht) Hn2 He He0 hq hfx hrw
  obtain rfl : W₀ = W := Option.some.inj (hW.symm.trans h0f)
  exact K

/-- **hT1 AT THE OUTPUT HEAD's SWITCH, INTO GROUP 24.** -/
theorem hT1_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hRch : ∀ k x, Rch k x ↔ Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (msgShapes : ∀ k x, Rch k x → x.1.2.failed = none →
      K12.Door.atFirstShapes (K12.Door.msgsOfChain Z.made.proof.1) x.1.2 = true)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → t = s) {q : K2.P2}
    (hq : q.stands = .head) {r : SwRow} (hrw : tableFullLit[23]? = some r) {W : SwitchFrame}
    (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Str, Rch 339 ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt q t = some fx →
      frontB2 (fxAt r) W 24 0 (K2.n0At 24) (K2.oldsAt 24) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W (K2.n0At 24) (K2.oldsAt 24)) fx = true ∧
        a.1.st.oracles = fx.st.oracles := by
  intro z a ha t he fx hfx
  obtain rfl := hent _ _ he
  obtain ⟨hcs, hsh, hM⟩ := written3 hS O.pub hy
  have hr := (hRch _ _).1 ha
  have hu : a.1.failed = none :=
    IM.noMark_reach_below hS hR O hr (by omega) fun l _ => by unfold IM.nAt; split <;> omega
  obtain ⟨W₀, hW, K⟩ := foldSideR_head hS hR O hF hpl hcs hsh hr
    (fun t ht => msgCount_link hS hR O hpl hcut (g := 23) (by omega) (by omega) ht)
    (msgCount_head hS hR O hpl hcut hr) (shapes_reached hRch msgShapes hM a.2 hr hu)
    (fun t ht => olds_reached hS hR O hpl hcut hRch msgShapes hM a.2 (l := 23) (by omega) ht)
    hq hfx hrw
  obtain rfl : W₀ = W := Option.some.inj (hW.symm.trans h0f)
  exact K

/-- **hT1 AT THE FINISH's SWITCH, INTO GROUP 25.** The way in is K2.finishFrontQ. -/
theorem hT1_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hRch : ∀ k x, Rch k x ↔ Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (msgShapes : ∀ k x, Rch k x → x.1.2.failed = none →
      K12.Door.atFirstShapes (K12.Door.msgsOfChain Z.made.proof.1) x.1.2 = true)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → K2.finishFrontQ s = .ok t)
    {q : K2.P2} (hq : q.stands = .finish) {r : SwRow} (hrw : tableFullLit[24]? = some r)
    {W : SwitchFrame} (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Str, Rch 353 ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt q t = some fx →
      frontB2 (fxAt r) W 25 0 (K2.n0At 25) (K2.oldsAt 25) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W (K2.n0At 25) (K2.oldsAt 25)) fx = true ∧
        a.1.st.oracles = fx.st.oracles := by
  intro z a ha t he fx hfx
  obtain ⟨hcs, hsh, hM⟩ := written3 hS O.pub hy
  have hr := (hRch _ _).1 ha
  have hu : a.1.failed = none :=
    IM.noMark_reach_below hS hR O hr (by omega) fun l _ => by unfold IM.nAt; split <;> omega
  obtain ⟨W₀, hW, K⟩ := foldSideR_fin hS hR O hF hpl hcs hsh hr (msgCount_fin hS hR O hpl hcut hr)
    (shapes_reached hRch msgShapes hM a.2 hr hu) (hent _ _ he) hq hfx hrw
  obtain rfl : W₀ = W := Option.some.inj (hW.symm.trans h0f)
  exact K

end

end

end P1K2

#print axioms P1K2.written3
#print axioms P1K2.msgCount_link
#print axioms P1K2.msgCount_head
#print axioms P1K2.msgCount_fin
#print axioms P1K2.noMark_link
#print axioms P1K2.noMark_closing
#print axioms P1K2.shapes_reached
#print axioms P1K2.olds_reached
#print axioms P1K2.hT1_link
#print axioms P1K2.hT1_head
#print axioms P1K2.hT1_fin
