-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MemberPath.lean: "NO MARK AT EVERY BORDER", ALONG ONE LIST OF
STATES: from the same two tests as Johnson/IMR/MemberOfGate.lean (the goals' scope test at the
public files;
the proof file's decision behind its gate): there is ONE LIST st 0, …, st 358 of values of the
verifier's state: st 0 is the first state at the instance's own public part; each entry k of the
flat list of the first chain of the IOP as written in Lean steps, wrapped (Sound.below), from st k
to st (k + 1); so st k is reached at border k, in the narrower sense and in the wider; AND NO st k
BEARS A MARK.

WHY "NO MARK" IS NOT FREE. Of the ten forms of a flat entry (Johnson/IMR/FlatCases.lean) eight end
in "no mark at the state behind". Two do not: the front (entry 0: it hands the state on) and "behind
the batching" (25 entries: Link.runBehind, with no clause on a mark). THERE IT FOLLOWS FROM THE
LIST's GOING ON: the state behind entry 0 is the state in front of entry 1 (link 0's "laid"), which
hands its state on and accepts only without a mark; the state behind "behind the batching" is the
state in front of the link's first closing sub-protocol (the one equation), which leaves the mark as
it is (oneEquation_failed) and accepts, under the seat's guard, only without a mark. SO AT 27
BORDERS (0, 1, and the 25 at 14 l + nAt l + 4) IT IS A FACT OF A LIST THAT GOES ON, NOT OF EVERY
REACHED STATE. At the borders 0 and 1 a reached state does bear a mark where ProofFile.startS falls to the
blank state (the front hands on any state). At the 25, "no mark" is shown only of a state from which
a step goes one entry on; of a reached state in general it is not shown, either way.

NEAREST RELATIVE: Johnson/Desc/ProofFile/Law/MarkGuard.lean:
flat_no_mark, descPure_no_mark: every entry of the flat list hands on no mark by its
decision, but for the chain's first and, in each link, the one behind the batching: THE SAME TWO
EXCEPTIONS, found apart; said of the entries themselves, at every o, with no scope. case_noMark says
them by their numbers, in scope, off our own ten forms: the numbers are what noMark_path needs. That
file is not imported (one of its imports is not in this library). What it does not have: the two
exceptions closed along a list that goes on.

Compiled with the whole library.



  failed_putLink | failed_putFork | failed_atS_set   these writers leave the mark.
  oneEquation_failed   an accepting decision of the one equation leaves the mark as it is.
  alone_noMark     a sub-protocol that is laid alone accepts only without a mark behind.
  case_noMark      the ten forms: no mark behind · or entry 0, which hands the state on · or k is
                   the number of a link's "behind the batching".
  path_of_reach    general: what is reached at border k is the end of a list of states, from the
                   first state, each stepping to the next.
  reach_of_path    general: each state of such a list is reached at its border.
  noMark_path      in scope: along a list of 359 states that step through all 358 entries: no mark.
  member_path      THE TOP.
  member_each      the same without the list, border by border, for a field's example in one line:
                   at every k ≤ 358 there is a state that is reached at k, narrower and wider,
                   without a mark.
                   Both tops carry "live" and "laid" behind, as in Johnson/IMR/MemberOfGate.lean.

OBJECT, USER, LETTERS: as in Johnson/IMR/MemberOfGate.lean; st: under "there is", NOT PINNED.

WHAT IS NOT SAID. All that Johnson/IMR/MemberOfGate.lean does not say, but for the mark and that the
states
step one into the next. THAT EACH STEP IS TAKEN AT THE PROOF FILE's OWN ROUNDS AND COLUMNS, or that
the steps' lists of rounds follow one another in one transcript: a step binds its rounds and columns
under "there are", each step apart (it is so inside the proof; no statement says it). That every
reached state is without a mark: see above. No soundness.

-/
import Johnson.IMR.MemberOfGate
import Johnson.IMR.FlatCases
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S closeKinds)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach StepYes reach_raw stepYes_raw)

/-! ## 1 The one equation leaves the mark -/

theorem failed_putLink (s : S) (L : OnBytes.Model.LinkCtx) : (s.putLink L).failed = s.failed := by
  unfold S.putLink
  split <;> (try split) <;> rfl

theorem failed_putFork (s : S) (G : OnBytes.Model.Fork) : (s.putFork G).failed = s.failed := by
  unfold S.putFork
  split <;> (try split) <;> rfl

theorem failed_atS_set (s : S) (p : K9.Part) : (K9.atS.set s p).failed = s.failed := by
  show ((s.putLink p.L).putFork p.F).failed = s.failed
  rw [failed_putFork, failed_putLink]

/-- **An accepting decision of the one equation leaves the mark as it is.** -/
theorem oneEquation_failed {C : Type} (p : K9.Where) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (K9.oneEquation (Cl := C) K9.atS p).decide s rs gs = .ok t) : t.failed = s.failed := by
  simp only [K9.oneEquation] at h
  obtain ⟨q, -, h⟩ := Keeps.ebind_ok h
  obtain ⟨o, -, h⟩ := Keeps.ebind_ok h
  cases h
  exact failed_atS_set s _

/-! ## 2 The ten forms -/

/-- A sub-protocol that is laid alone accepts only without a mark behind. -/
theorem alone_noMark {same : S → S → Bool} {b b' : Block S Cl} {name : String} {a : Place}
    (h : LaidAlone same b b' name a) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (d : b.decide s rs gs = .ok t) :
    b'.decide s rs gs = .ok t ∧ t.failed = none := by
  by_cases hk : a.kind = KindName.K7
  · exact (yes_alone_K7 h hk s t rs gs).1 d
  · exact ⟨((yes_alone h hk s t rs gs).1 d).1, ((yes_alone h hk s t rs gs).1 d).2.1⟩

/-- **The ten forms**: behind an accepting decision no mark; or the entry is number 0 and hands the
state on; or k is the number of a link's "behind the batching". -/
theorem case_noMark {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {c : Chain S Cl} {k : ℕ} {b : Block S Cl}
    (fc : FlatCase Z G₀ c k b) {s t : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (d : b.decide s rs gs = .ok t) :
    t.failed = none ∨ (k = 0 ∧ t = s) ∨ ∃ l, l < 25 ∧ k = 14 * l + nAt l + 3 := by
  cases fc with
  | front b hr hd => exact Or.inr (Or.inl ⟨rfl, (hd s rs gs t).1 d⟩)
  | laid l hl b hr hd => exact Or.inl ((hd s rs gs t).1 d).2.1
  | first l hl k b b' hk lot hp hj =>
    obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ := hj.yes d
    exact Or.inl h
  | hear l hl i hi k b b' name hk lot hp hla => exact Or.inl (alone_noMark hla d).2
  | batch l hl Lk p e1 hp hal => exact Or.inl (alone_noMark (hal _) d).2
  | behind l hl Lk b e1 hr hd => exact Or.inr (Or.inr ⟨l, hl, rfl⟩)
  | close l hl p Q j k b x hp hQ hk ex hla => exact Or.inl (alone_noMark hla d).2
  | cleared l hl fs f b hfs hf hr hd => exact Or.inl ((hd s rs gs t).1 d).2.1
  | back j k b b' name hk lot hp hla => exact Or.inl (alone_noMark hla d).2
  | last lot hla => exact Or.inl (alone_noMark hla d).2

/-! ## 3 A list of states -/

section
variable {T C Q : Type}

/-- **What is reached at border k is the end of a list of states**, from the first state, each
stepping to the next by the entry of its number. -/
theorem path_of_reach {ft : ℕ} {bs : List (Block T C)} {start : Q → T} {k : ℕ} {a : Q × T}
    (h : Reach ft bs start k a) :
    ∃ st : ℕ → T, st 0 = start a.1 ∧ st k = a.2 ∧
      ∀ j < k, ∃ b, bs[j]? = some b ∧ StepYes ft b (st j) (st (j + 1)) := by
  induction h with
  | zero z => exact ⟨fun _ => start z, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | @succ k z s s' b R hb hy ih =>
    obtain ⟨st, h0, hk, hs⟩ := ih
    have hk' : st k = s := hk
    have h0' : st 0 = start z := h0
    refine ⟨fun j => if j ≤ k then st j else s', ?_, ?_, ?_⟩
    · show (if 0 ≤ k then st 0 else s') = start z
      rw [if_pos (Nat.zero_le k), h0']
    · show (if k + 1 ≤ k then st (k + 1) else s') = s'
      rw [if_neg (by omega)]
    · intro j hj
      show ∃ b, bs[j]? = some b ∧
        StepYes ft b (if j ≤ k then st j else s') (if j + 1 ≤ k then st (j + 1) else s')
      by_cases e : j = k
      · subst e
        rw [if_pos (Nat.le_refl j), if_neg (by omega), hk']
        exact ⟨b, hb, hy⟩
      · rw [if_pos (by omega), if_pos (by omega)]
        exact hs j (by omega)

/-- Each state of such a list is reached at its border. -/
theorem reach_of_path {ft : ℕ} {bs : List (Block T C)} {start : Q → T} {k : ℕ} {z : Q}
    {st : ℕ → T} (h0 : st 0 = start z)
    (hs : ∀ j < k, ∃ b, bs[j]? = some b ∧ StepYes ft b (st j) (st (j + 1))) :
    ∀ j ≤ k, Reach ft bs start j (z, st j)
  | 0, _ => by rw [h0]; exact Reach.zero z
  | j + 1, hj => by
    obtain ⟨b, hb, hy⟩ := hs j (by omega)
    exact Reach.succ (reach_of_path h0 hs j (by omega)) hb hy

end

/-! ## 4 No mark along a list that goes on -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In scope: along a list of 359 states that step through all 358 entries of the first chain's
flat list, no state bears a mark.** -/
theorem noMark_path (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {st : ℕ → S}
    (hs : ∀ j < 358, ∃ b, c.blocksInOrder[j]? = some b ∧ StepYes ft b (st j) (st (j + 1))) :
    ∀ j ≤ 358, (st j).failed = none := by
  have dec : ∀ j < 358, ∃ b rs gs, c.blocksInOrder[j]? = some b ∧
      b.decide (st j) rs gs = .ok (st (j + 1)) := by
    intro j hj
    obtain ⟨b, hb, R, C, -, hy⟩ := hs j hj
    exact ⟨b, _, _, hb, ((Sound.step_ok_iff ft b _ _ R C C.length).1 hy).2.2.2⟩
  obtain ⟨-, fs, -, hfr⟩ := frame_of hS hR O
  -- the state behind entry 0 is the state in front of it
  have e01 : st 1 = st 0 := by
    obtain ⟨b, rs, gs, hb, d⟩ := dec 0 (by omega)
    obtain ⟨b₀, hb₀, -, -, -, -, hd⟩ := front_of O
    obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
    exact (hd _ rs gs _).1 d
  -- link 0's "laid" hands its state on and accepts only without a mark
  have h1 : (st 1).failed = none := by
    obtain ⟨b, rs, gs, hb, d⟩ := dec 1 (by omega)
    obtain ⟨Lk, f, bL, bB, bC, -, -, -, -, hlay, hL, -, hbL, -, hdL, -⟩ := hfr 0 (by omega)
    obtain rfl : bL = b := Option.some.inj (hbL.symm.trans hb)
    rw [hdL] at d
    obtain ⟨d1, d2, -⟩ := (hL _ _).1 d
    rw [hlay] at d1
    rw [← (Johnson.Desc.First.Walk.Law.layFront_ok d1).1]
    exact d2
  -- the state behind "behind the batching" is in front of the one equation
  have hB : ∀ l, l < 25 → (st (14 * l + nAt l + 3 + 1)).failed = none := by
    intro l hl
    have hlt : 14 * l + nAt l + 3 + 1 < 358 := by unfold nAt; split <;> omega
    obtain ⟨b, rs, gs, hb, d⟩ := dec _ hlt
    obtain ⟨Lk, p, Q, e1, -, -, hcl⟩ := close_of hS hR O l hl
    obtain ⟨Lk', -, -, -, -, e1', hlen, -⟩ := hfr l hl
    obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
    obtain ⟨b', x, hb', ex, hla⟩ := hcl 0 _ rfl
    have hn := close_numbers hS hR O hl e1 hb'
    have ei : 14 * l + Lk.hear.length + 4 + 0 = 14 * l + nAt l + 3 + 1 := by
      rw [hlen]; unfold nAt; omega
    rw [ei] at hn
    obtain rfl : b' = b := Option.some.inj (hn.symm.trans hb)
    obtain ⟨dx, hm⟩ := alone_noMark hla d
    unfold K9.closeOf at ex
    rw [List.getElem?_cons_zero] at ex
    obtain rfl := Option.some.inj ex
    have dx' : (K9.oneEquation (Cl := Unit) K9.atS p).decide (st (14 * l + nAt l + 3 + 1)) rs gs =
      .ok (st (14 * l + nAt l + 3 + 1 + 1)) := dx
    rw [← oneEquation_failed p dx']
    exact hm
  intro j hj
  cases j with
  | zero => rw [← e01]; exact h1
  | succ k =>
    obtain ⟨b, rs, gs, hb, d⟩ := dec k (by omega)
    rcases case_noMark (flat_cases hS hR O k b hb) d with h | ⟨rfl, -⟩ | ⟨l, hl, rfl⟩
    · exact h
    · exact h1
    · exact hB l hl

end

/-- **ONE LIST OF STATES, EACH STEPPING TO THE NEXT, NONE WITH A MARK, FROM THE TWO TESTS ON
verify()'s OWN ROAD.** -/
theorem member_path {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
      (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
      (st : ℕ → S),
      VerifierAndGoals.readFiles P = .ok pp ∧
      ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F ∧
      Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      F.run (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ = true ∧
      (∀ b ∈ c.blocksInOrder, b.planOk = true) ∧
      c.blocksInOrder.length = 358 ∧
      ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z (LPFD.Full.instanceAsPlainRecord z) = true ∧
      st 0 = ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub ∧
      (∀ k < 358, ∃ b, c.blocksInOrder[k]? = some b ∧ StepYes 0 (Sound.below b) (st k) (st (k + 1))) ∧
      (∀ k ≤ 358,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, st k) ∧
        Reach 0 c.blocksInOrder (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, st k) ∧
        (st k).failed = none) ∧
      (st 358).fin = true ∧ (st 358).finAsked (LPFD.Full.instanceAsPlainRecord z).asked = true ∧
      FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true ∧
      ∃ D, LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL =
        .ok (D, (F.pull LPFD.Full.instanceAsPlainRecord).run) := by
  obtain ⟨pp, F, Z, Bs, base, c, A, B, hR, hF, O, hr, hp, hlen, -, hx, ⟨e, hE, hfin, -, hask⟩,
    hlive, hlaid⟩ := member_of_gate_laid hS hg
  obtain ⟨st, h0, hk, hs⟩ := path_of_reach hE
  have hk' : st 358 = e := hk
  have hs' : ∀ k < 358, ∃ b, c.blocksInOrder[k]? = some b ∧
      StepYes 0 (Sound.below b) (st k) (st (k + 1)) := by
    intro k hk
    obtain ⟨b', hb', hy⟩ := hs k hk
    rw [List.getElem?_map] at hb'
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb'
    exact ⟨b, hb, hy⟩
  have hm := noMark_path hS hR O (ft := 0) (st := st) fun j hj => by
    obtain ⟨b, hb, hy⟩ := hs' j hj
    exact ⟨b, hb, stepYes_raw hy⟩
  refine ⟨pp, F, Z, Bs, base, c, A, B, st, hR, hF, O, hr, hp, hlen, hx, h0, hs', ?_, ?_, ?_, hlive,
    hlaid⟩
  · intro k hk
    have R := reach_of_path (z := (LPFD.Full.instanceAsPlainRecord z).pub) h0 hs k hk
    exact ⟨R, reach_raw R, hm k hk⟩
  · rw [hk']; exact hfin
  · rw [hk']; exact hask

/-- **Border by border**: from the two tests: the shared premises, and at every border k ≤ 358 a
state that is reached there, in the narrower sense and in the wider, without a mark. -/
theorem member_each {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
      (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      VerifierAndGoals.readFiles P = .ok pp ∧
      Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      (∀ b ∈ c.blocksInOrder, b.planOk = true) ∧
      (∀ k ≤ 358, ∃ s : S,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, s) ∧
        Reach 0 c.blocksInOrder (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, s) ∧ s.failed = none) ∧
      FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true ∧
      ∃ D, LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL =
        .ok (D, (F.pull LPFD.Full.instanceAsPlainRecord).run) := by
  obtain ⟨pp, F, Z, Bs, base, c, A, B, st, hR, -, O, -, hp, -, -, -, -, hall, -, -, hlive, hlaid⟩ :=
    member_path hS hg
  exact ⟨pp, F, Z, Bs, base, c, A, B, hR, O, hp, fun k hk => ⟨st k, hall k hk⟩, hlive, hlaid⟩

#print axioms oneEquation_failed
#print axioms alone_noMark
#print axioms case_noMark
#print axioms path_of_reach
#print axioms reach_of_path
#print axioms noMark_path
#print axioms member_path
#print axioms member_each

end IM
