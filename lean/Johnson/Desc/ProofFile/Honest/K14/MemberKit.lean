-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/MemberKit.lean: kind K14: WHAT IS NEEDED, BUT FOR THE PREMISE ON
opened, TO SHOW THAT THE FIELD exact OF THE FRAME's RECORD Good (Honest/Side.lean) IS NOT MET FOR
NOTHING AT THE TWO SENDINGS OF THE SHARED CHAIN: written challenges and written positions, and the
laws by which all six premises of ExactMember (Honest/Small/Field.lean) hold at them. Two
definitions with code; statements with their proofs.

ON THE FIELD's OWN FORM. ExactMember is the condition asked at EVERY value of the stand's field
opened at which On holds; this kind's On reads what the stand has heard alone. Good's own field at
one member (ExactMemberAt pre, the same file) has ExactMember's six premises and a SEVENTH: the
stand's opened is what the front holds for the reads of pre. No premise of a statement here speaks
of opened: where a stand is bound (sendingMember_at, exactSix_at) it is bound by "every", under
premises on what it has heard and seen alone: so the statement holds, among others, at the stands
that meet the seventh premise; at a stand that does not meet it nothing is shown of the field's own
form. That a stand with a front meets all seven is the caller's to show. Where this file says the
field's test, premise or equation, the two forms have it in common.

NO EVALUATION IN THIS FILE TOUCHES A WEIGHT, A COIN OR A TABLE. Five of the six premises are general
in the plan. The sixth, the bound on positions, rests on two evaluations in Lean's kernel of public
numbers at the written sizes (written_u, written_omega): how many messages a sending has, which tree
holds which, which have main or mask rows, and the r and logN of three codes.

  onesAt          the written challenges of a sending's two rounds: every drawn element is 1; the
                  second round draws nothing
  fullAsks        the written positions: at "send o_u" 0 to 100 of its one tree; at "send o_omega" 0
                  to 3,570 of o_omega's tree and 0 to 151 of o_sp's
  onesAt_map      onesAt is drawnOnes (Honest/Law/DrawsOfDecl.lean) at the sending's declared rounds
  onesAt_fits     **drawsFit at the sending's declared rounds**, at every plan
  sendingMember_rounds   the member's declared rounds are the sending's
  holds_send      **a sending's rounds read nothing**: the field's test on what stands in front
                  accepts at every front
  stop_send       **a sending's part does not stop by its second stop**. (The proof sees no stop of
                  either sort. A part of the shared chain is shown nothing of the input, so this
                  premise of the field holds of every such part)
  budAt_of_lengths   where no list of positions is longer than a count that passes countsWithinB
                  (Honest/K14/BudTest.lean): budAt (Johnson/SendSim/At/Sim.lean)
  asked_zero, asked_one, card_range_mod   small steps: the first n numbers have n residues modulo a
                  power of two that is not smaller
  written_u, written_omega   the public numbers at the written sizes
  full_u, full_omega   **budAt at fullAsks; every tree of the sending has its list in fullAsks; AND
                  EACH LIST FILLS THE COUNT**: it has just as many distinct residues as the r of the
                  code of a message in its tree, and that r is the list's length. THE STATEMENT
                  NAMES NEITHER THE MESSAGE NOR THE ARM: it says: at some message of the tree, at
                  its main rows or at its mask rows. (The proofs lay: 101 at o_u's main rows; 3,571
                  at o_omega's; 152 at o_sp's mask row.) (By budAt's text one residue more at that
                  row's code breaks it: no statement here says so)
  full_u_at_files, full_omega_at_files   the same at the public part that the library lays off
                  public files in the goals' scope
  ofDecl_slice    **the written due list's slice at a sending is onesAt**: general in the
                  description
  sendingMember_at   at a sending's member, at onesAt: drawsFit, the test on the front, no second
                  stop; and what the part shows is "some ..." at all coins (shows_tie,
                  Honest/K14/TieShown.lean)
  exactSix_at     **ExactMember's SIX PREMISES, "some ..." AT ALL COINS, ITS EQUATION**: at every
                  stand that has heard a challenge and every front that shows what the stand has
                  seen; general in the job and the positions

What is assumed. In sendingMember_at: the test on the job's shapes (sendShapeFits); the side's
declared rounds (hr, hd); SameData at what the stand has heard. In exactSix_at: the first two of
these; that SameData follows from pointApart (hsd); that the row is a sending's part; that the
sentence at entry is pointApart with "LIN point" as round number 0; the bound at the positions, AT
EVERY NUMBER AND ALL CHALLENGES (hbud); ExactMember at the side's members (hE). The caller pays all
of them: AtFullSide/K14/MemberAtNamed.lean.

What is not claimed. STANDS THAT NO RUN REACHES ARE AMONG THEM: that a run's stand in front of the
part has heard a challenge, with a front true to it, is the frame's sentence's matter. The positions
are written here: they are not positions that a run asks. A datum that is not 0 is not shown: the
index is free. Nothing on what the proximity tests behind the sendings show. One request. Nothing on
what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.Law.DrawsOfDecl
import Johnson.Desc.ProofFile.Honest.K14.BudBoth
import Johnson.Desc.ProofFile.Honest.K14.TieShown
import Johnson.Desc.ProofFile.Honest.K14.ExactOfRows
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.K1 (Par)
open OnBytes.SendSim.At (budAt asked)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.PlanWritten (proofSizedFull)
open ProofFile.Honest.Small (ExactMember)

-- An instance of the library (Cb/Obj/LdObjectReqStd.lean) is offered to every search for
-- Nonempty and sends it after a field that nothing determines; it is struck inside this
-- namespace, in this file.
attribute [-instance] Cb.instNonemptyPGD

variable {S Cl W X Pb : Type}

/-- The written challenges of a sending's two rounds: every drawn element is 1. -/
def onesAt (P : Par) : List Fmt.Drawn :=
  [⟨List.replicate (VerifiableInference.Desc.K1.seedEntry P).drawE (1, 0, 0), [], [], none⟩,
    ⟨[], [], [], none⟩]

/-- The written positions: at "send o_u" 0 to 100 of its one tree; at "send o_omega" 0 to 3,570 of
o_omega's tree and 0 to 151 of o_sp's. (At every other place than "send o_u"'s it yields the second
list.) -/
def fullAsks (a : Place) : List (List (List Nat)) :=
  if a = sendPlace 2 then [[List.range 101]] else [[List.range 3571, List.range 152]]

/-- They are drawnOnes at the sending's declared rounds. -/
theorem onesAt_map (P : Par) : (VerifiableInference.Desc.K1.rounds P).map drawnOnes = onesAt P :=
  rfl

/-- **The written challenges fit the sending's declared rounds**, at every plan. -/
theorem onesAt_fits (P : Par) : drawsFit (VerifiableInference.Desc.K1.rounds P) (onesAt P) = true :=
  by
  rw [← onesAt_map]
  show (drawFit _ (drawnOnes _) && (drawFit _ (drawnOnes _) && true)) = true
  rw [drawnOnes_fits _ _ (by rfl), drawnOnes_fits _ _ (by rfl)]
  rfl

/-- The member's declared rounds are the sending's. -/
theorem sendingMember_rounds (σ : Side S Cl Empty W X Pb) (J : SendJob) (wit : W → Ask) (sim : Sim
  Pb)
    (hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds J.Q) (hd : SendDeclared σ.block J) :
    (sendingMember σ J wit sim).rounds.map (·.1) = VerifiableInference.Desc.K1.rounds J.Q := by
  obtain ⟨d₀, d₁, os, h1, h2, -⟩ := hd.rounds
  show ((σ.block.rounds.zip σ.block.oracles).take 2).map (·.1) = _
  rw [← hr, h1, h2]
  rfl

/-- **A sending's rounds read nothing**: the field's test on what stands in front accepts at every
front. -/
theorem holds_send (f : Before) (chain ft : Nat) (P : Par) (ds : List Fmt.Drawn) :
    f.holds chain ft (VerifiableInference.Desc.K1.rounds P) ds = true := by
  unfold Before.holds
  have e : readsOf chain ft (fun _ _ => none) (fun _ => none)
      (VerifiableInference.Desc.K1.rounds P) ds = [] := by
    match ds with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | _ :: _ :: _ :: _ => rfl
  rw [e]
  rfl

/-- **A sending's part does not stop by its second stop.** -/
theorem stop_send (J : SendJob) (wit : W → Ask) (v : Option Empty) (loc ds : List Fmt.Drawn) :
    (liftSend wit (sendingPart J) : Part Empty W X).stopAt v loc ds ≠ some .hid := by
  cases v with
  | some e => exact e.elim
  | none =>
    show ((List.range 3).findSome? fun _ => (none : Option Why)) ≠ some .hid
    decide

/-- **Where no list of positions is longer than a count that passes the test: budAt.** -/
theorem budAt_of_lengths (P : Par) (cnt : Nat → Nat) (asks : List (List (List Nat)))
    (hl : ∀ τ, (asked asks τ).length ≤ cnt τ)
    (hB : countsWithinB cnt 0 P.codes P.sent = true) : budAt P asks := by
  intro k τ hk hτ
  have h1 := List.all_eq_true.1 hB k (List.mem_range.2 hk)
  rw [hτ] at h1
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Nat.zero_add] at h1
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · exact le_trans (List.toFinset_card_le _) (by
      rw [List.length_map]
      exact le_trans (hl τ) (h1.1.resolve_left hm))
  · exact le_trans (List.toFinset_card_le _) (by
      rw [List.length_map]
      exact le_trans (hl τ) (h1.2.resolve_left hm))

/-- What is asked of the first tree. -/
theorem asked_zero (a : List Nat) (l : List (List Nat)) : asked [a :: l] 0 = a := rfl

/-- What is asked of the second tree. -/
theorem asked_one (a b : List Nat) (l : List (List Nat)) : asked [a :: b :: l] 1 = b := rfl

/-- The first n numbers have n residues modulo a power of two that is not smaller. -/
theorem card_range_mod (n l : Nat) (h : n ≤ 2 ^ l) :
    ((List.range n).map (· % 2 ^ l)).toFinset.card = n := by
  have e : (List.range n).map (· % 2 ^ l) = List.range n := by
    conv_rhs => rw [← List.map_id (List.range n)]
    exact List.map_congr_left fun x hx =>
      Nat.mod_eq_of_lt (lt_of_lt_of_le (List.mem_range.1 hx) h)
  rw [e, List.toFinset_card_of_nodup List.nodup_range, List.length_range]

/-- The numbers at the written sizes, "send o_u": two messages, both in tree 0; the first has main
rows; their code's r is 101, and it has at least 101 positions; the count 101 passes the test. -/
theorem written_u :
    ((Desc.K14.withU proofSizedFull.batch.shape).getD #[]).size = 2 ∧
    ((VerifiableInference.Desc.Own.treesMade proofSizedFull.codes
      ((Desc.K14.withU proofSizedFull.batch.shape).getD #[])).getD {}).tree[0]? = some 0 ∧
    ((VerifiableInference.Desc.Own.treesMade proofSizedFull.codes
      ((Desc.K14.withU proofSizedFull.batch.shape).getD #[])).getD {}).tree[1]? = some 0 ∧
    (((Desc.K14.withU proofSizedFull.batch.shape).getD #[]).getD 0 default).shape.mainRows ≠ 0 ∧
    (proofSizedFull.codes.base.getD
      (((Desc.K14.withU proofSizedFull.batch.shape).getD #[]).getD 0 default).shape.code
      default).r = 101 ∧
    101 ≤ 2 ^ (proofSizedFull.codes.base.getD
      (((Desc.K14.withU proofSizedFull.batch.shape).getD #[]).getD 0 default).shape.code
      default).logN ∧
    countsWithinB (fun _ => 101) 0 proofSizedFull.codes
      ((Desc.K14.withU proofSizedFull.batch.shape).getD #[]) = true := by decide +kernel

/-- The like at "send o_omega": two messages: o_omega in tree 0, main rows, r = 3,571; o_sp in tree
1, mask rows, r = 152. -/
theorem written_omega :
    (Desc.K14.withOmega proofSizedFull.batch.shape).size = 2 ∧
    ((VerifiableInference.Desc.Own.treesMade proofSizedFull.codes
      (Desc.K14.withOmega proofSizedFull.batch.shape)).getD {}).tree[0]? = some 0 ∧
    ((VerifiableInference.Desc.Own.treesMade proofSizedFull.codes
      (Desc.K14.withOmega proofSizedFull.batch.shape)).getD {}).tree[1]? = some 1 ∧
    ((Desc.K14.withOmega proofSizedFull.batch.shape).getD 0 default).shape.mainRows ≠ 0 ∧
    ((Desc.K14.withOmega proofSizedFull.batch.shape).getD 1 default).shape.maskRows ≠ 0 ∧
    (proofSizedFull.codes.base.getD
      ((Desc.K14.withOmega proofSizedFull.batch.shape).getD 0 default).shape.code default).r =
      3571 ∧
    3571 ≤ 2 ^ (proofSizedFull.codes.base.getD
      ((Desc.K14.withOmega proofSizedFull.batch.shape).getD 0 default).shape.code default).logN ∧
    (proofSizedFull.codes.mask.getD
      ((Desc.K14.withOmega proofSizedFull.batch.shape).getD 1 default).shape.maskCode default).r =
      152 ∧
    152 ≤ 2 ^ (proofSizedFull.codes.mask.getD
      ((Desc.K14.withOmega proofSizedFull.batch.shape).getD 1 default).shape.maskCode
      default).logN ∧
    countsWithinB (fun τ => if τ = 0 then 3571 else 152) 0 proofSizedFull.codes
      (Desc.K14.withOmega proofSizedFull.batch.shape) = true := by decide +kernel

/-- **budAt at the written positions of "send o_u"; every tree of the sending has its list; and each
list fills the count**: it has just as many distinct residues as the r of the code of a message in
its tree, and that r is the list's length: at a plan with the written sizes' codes and messages. -/
theorem full_u (P : Par) (hc : P.codes = proofSizedFull.codes)
    (hs : P.sent = (Desc.K14.withU proofSizedFull.batch.shape).getD #[]) :
    budAt P (fullAsks (sendPlace 2)) ∧
      (∀ k τ, k < P.sent.size →
        ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? = some τ →
        τ < ((fullAsks (sendPlace 2))[0]?.getD []).length) ∧
      ∀ τ, τ < ((fullAsks (sendPlace 2))[0]?.getD []).length → ∃ k, k < P.sent.size ∧
        ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? = some τ ∧
        (((shapeAt P k).mainRows ≠ 0 ∧
            ((asked (fullAsks (sendPlace 2)) τ).map
                (· % 2 ^ (P.codes.base.getD (shapeAt P k).code default).logN)).toFinset.card =
              (P.codes.base.getD (shapeAt P k).code default).r ∧
            (P.codes.base.getD (shapeAt P k).code default).r = (asked (fullAsks (sendPlace 2))
              τ).length) ∨
          ((shapeAt P k).maskRows ≠ 0 ∧
            ((asked (fullAsks (sendPlace 2)) τ).map
                (· % 2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logN)).toFinset.card =
              (P.codes.mask.getD (shapeAt P k).maskCode default).r ∧
            (P.codes.mask.getD (shapeAt P k).maskCode default).r =
              (asked (fullAsks (sendPlace 2)) τ).length)) := by
  obtain ⟨wz, w1, w1', w2, w3, w4, w5⟩ := written_u
  have ea : fullAsks (sendPlace 2) = [[List.range 101]] := rfl
  rw [ea]
  refine ⟨budAt_of_lengths P (fun _ => 101) _ (fun τ => ?_) (by rw [hc, hs]; exact w5),
    fun k τ hk hτ => ?_, fun τ hτ => ?_⟩
  · match τ with
    | 0 =>
      rw [asked_zero, List.length_range]
    | _ + 1 => exact Nat.zero_le _
  · rw [hs, wz] at hk
    rw [hc, hs] at hτ
    show τ < 1
    match k, hk with
    | 0, _ =>
      obtain rfl : 0 = τ := Option.some.inj (w1.symm.trans hτ)
      exact Nat.zero_lt_one
    | 1, _ =>
      obtain rfl : 0 = τ := Option.some.inj (w1'.symm.trans hτ)
      exact Nat.zero_lt_one
  · obtain rfl : τ = 0 := Nat.lt_one_iff.1 hτ
    refine ⟨0, by rw [hs, wz]; exact Nat.zero_lt_two, by rw [hc, hs]; exact w1,
      Or.inl ⟨?_, ?_, ?_⟩⟩
    · unfold shapeAt
      rw [hs]
      exact w2
    · unfold shapeAt
      rw [hc, hs, w3, asked_zero]
      exact card_range_mod 101 _ w4
    · unfold shapeAt
      rw [hc, hs, w3, asked_zero, List.length_range]

/-- **The like at "send o_omega".** -/
theorem full_omega (P : Par) (hc : P.codes = proofSizedFull.codes)
    (hs : P.sent = Desc.K14.withOmega proofSizedFull.batch.shape) :
    budAt P (fullAsks (sendPlace 5)) ∧
      (∀ k τ, k < P.sent.size →
        ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? = some τ →
        τ < ((fullAsks (sendPlace 5))[0]?.getD []).length) ∧
      ∀ τ, τ < ((fullAsks (sendPlace 5))[0]?.getD []).length → ∃ k, k < P.sent.size ∧
        ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? = some τ ∧
        (((shapeAt P k).mainRows ≠ 0 ∧
            ((asked (fullAsks (sendPlace 5)) τ).map
                (· % 2 ^ (P.codes.base.getD (shapeAt P k).code default).logN)).toFinset.card =
              (P.codes.base.getD (shapeAt P k).code default).r ∧
            (P.codes.base.getD (shapeAt P k).code default).r = (asked (fullAsks (sendPlace 5))
              τ).length) ∨
          ((shapeAt P k).maskRows ≠ 0 ∧
            ((asked (fullAsks (sendPlace 5)) τ).map
                (· % 2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logN)).toFinset.card =
              (P.codes.mask.getD (shapeAt P k).maskCode default).r ∧
            (P.codes.mask.getD (shapeAt P k).maskCode default).r =
              (asked (fullAsks (sendPlace 5)) τ).length)) := by
  obtain ⟨wz, t0, t1, m0, m1, r0, l0, r1, l1, w5⟩ := written_omega
  have ea : fullAsks (sendPlace 5) = [[List.range 3571, List.range 152]] := rfl
  rw [ea]
  refine ⟨budAt_of_lengths P (fun τ => if τ = 0 then 3571 else 152) _ (fun τ => ?_)
    (by rw [hc, hs]; exact w5), fun k τ hk hτ => ?_, fun τ hτ => ?_⟩
  · match τ with
    | 0 =>
      rw [asked_zero, List.length_range]
      exact Nat.le_refl _
    | 1 =>
      rw [asked_one, List.length_range]
      exact Nat.le_refl _
    | _ + 2 => exact Nat.zero_le _
  · rw [hs, wz] at hk
    rw [hc, hs] at hτ
    show τ < 2
    match k, hk with
    | 0, _ =>
      obtain rfl : 0 = τ := Option.some.inj (t0.symm.trans hτ)
      exact Nat.zero_lt_two
    | 1, _ =>
      obtain rfl : 1 = τ := Option.some.inj (t1.symm.trans hτ)
      exact Nat.one_lt_two
  · have hτ' : τ < 2 := hτ
    match τ, hτ' with
    | 0, _ =>
      refine ⟨0, by rw [hs, wz]; exact Nat.zero_lt_two, by rw [hc, hs]; exact t0,
        Or.inl ⟨?_, ?_, ?_⟩⟩
      · unfold shapeAt
        rw [hs]
        exact m0
      · unfold shapeAt
        rw [hc, hs, r0, asked_zero]
        exact card_range_mod 3571 _ l0
      · unfold shapeAt
        rw [hc, hs, r0, asked_zero, List.length_range]
    | 1, _ =>
      refine ⟨1, by rw [hs, wz]; exact Nat.one_lt_two, by rw [hc, hs]; exact t1,
        Or.inr ⟨?_, ?_, ?_⟩⟩
      · unfold shapeAt
        rw [hs]
        exact m1
      · unfold shapeAt
        rw [hc, hs, r1, asked_one]
        exact card_range_mod 152 _ l1
      · unfold shapeAt
        rw [hc, hs, r1, asked_one, List.length_range]

/-- **The written due list's slice at a sending is the sending's written challenges**: general in
the description. -/
theorem ofDecl_slice {Xi : Type} (F : VerifiableInference.Desc.FileDescription Xi)
    (pre t : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (hx : F.shared.blocksInOrder = pre ++ b :: t)
    (P : Par) (hr : b.rounds = VerifiableInference.Desc.K1.rounds P) :
    ((Draws.ofDecl F).shared.drop (pre.flatMap (·.rounds)).length).take 2 = onesAt P := by
  show (((F.shared.blocksInOrder.flatMap (·.rounds)).map drawnOnes).drop _).take 2 = _
  rw [hx, List.flatMap_append, List.flatMap_cons, List.map_append, List.map_append,
    List.drop_left' (by rw [List.length_map]), hr, onesAt_map]
  rfl

/-- **At a sending's member, at the written challenges: three of ExactMember's premises (drawsFit,
the test on the front, no second stop), and what the part shows is "some ..."**: under the test on
the job's shapes, the side's declared rounds, and SameData at what the stand has heard. General in
the job. -/
theorem sendingMember_at (J : SendJob) (hfit : sendShapeFits J = true) (wit : W → Ask)
    (φ : Face Empty W Pb) (σ : Side S Cl Empty W X Pb) (sim : Sim Pb)
    (hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds J.Q) (hd : SendDeclared σ.block J)
    (chain ft : Nat) (m : Mid W X) (front : Before) (asks : List (List (List Nat)))
    (hs : SameData J m.st.heard) :
    drawsFit ((sendingMember σ J wit sim).rounds.map (·.1)) (onesAt J.Q) = true ∧
      front.holds chain ft ((sendingMember σ J wit sim).rounds.map (·.1)) (onesAt J.Q) = true ∧
      (sendingMember σ J wit sim).part.stopAt (φ.sees m.st.input) m.loc (onesAt J.Q) ≠
        some .hid ∧
      ∀ c : Cs (sendingPart J).takes,
        ∃ y, σ.shows φ (sendingMember σ J wit sim) (c, (), ()) m (onesAt J.Q) asks = some y := by
  rw [sendingMember_rounds σ J wit sim hr hd]
  exact ⟨onesAt_fits J.Q, holds_send front chain ft J.Q _, stop_send J wit _ _ _,
    fun c => ⟨_, shows_tie J hfit wit φ σ sim hd m hs _ _ asks c⟩⟩

/-- **ALL SIX PREMISES OF ExactMember, "some ..." AT ALL COINS, AND ITS EQUATION**, at a side whose
row is a sending's part, at the written challenges, at every stand that has heard a challenge and
every front that shows what the stand has seen; under the test on the job's shapes and the side's
declared rounds; where SameData follows from pointApart, the sentence at entry is pointApart with
"LIN point" as round number 0, the bound holds at the positions asks at every number and all
challenges, and ExactMember holds at the side's members. General in the job and the positions. The
stand's field opened is free: Good's own field asks, as a seventh premise, that it be what the front
holds (the head). -/
theorem exactSix_at {W₀ Rc Ky : Type} (A : SendPub) (hA : A.atPoint = 0) (J : SendJob)
    (hfit : sendShapeFits J = true) (hsd : ∀ h, pointApart A h → SameData J h)
    (wit : Common W₀ Rc Ky → Ask) (σ : Side S Cl Empty (Common W₀ Rc Ky) X Ky) (sim : Sim Ky)
    (hrow : σ.row = [(liftSend wit (sendingPart J), sim)])
    (hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds J.Q) (hd : SendDeclared σ.block J)
    (On : (u : Member Empty (Common W₀ Rc Ky) X Ky) → CsAll u.part.carries →
      Mid (Common W₀ Rc Ky) X → Before → Prop)
    (hOn : On = fun _ _ m _ => pointApart A m.st.heard)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (asks : List (List (List Nat)))
    (hbud : ∀ j ds, bud j ds asks)
    (hE : ∀ u ∈ σ.members, ExactMember .shared σ 1 0 On bud u) :
    ∀ u ∈ σ.members, ∀ (ca : CsAll u.part.carries) (m : Mid (Common W₀ Rc Ky) X) (front : Before),
      m.st.heard ≠ [] → m.seen = front.seen →
      On u ca m front ∧ m.seen = front.seen ∧
      drawsFit (u.rounds.map (·.1)) (onesAt J.Q) = true ∧
      bud u.number (onesAt J.Q) (asks) ∧
      front.holds 1 0 (u.rounds.map (·.1)) (onesAt J.Q) = true ∧
      u.part.stopAt (Face.shared.sees m.st.input) m.loc (onesAt J.Q) ≠ some .hid ∧
      (∀ c : Cs u.part.takes × CsAll u.part.spends,
        ∃ y, σ.shows .shared u (c.1, c.2, ca) m (onesAt J.Q) (asks) = some y) ∧
      (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
          (fun c => σ.shows .shared u (c.1, c.2, ca) m (onesAt J.Q) (asks)) =
        (Prob.unif (Cs u.sim.takes)).map
          fun c => u.tells .shared c m.st.input front (onesAt J.Q) (asks) := by
  intro u hu ca m front hh hsn
  have hE' := hE u hu
  have hu' : u = sendingMember σ J wit sim := by
    rw [members_send σ _ sim hrow] at hu
    exact List.mem_singleton.1 hu
  subst hu'
  have hap : pointApart A m.st.heard := by
    unfold pointApart
    rw [hA]
    exact fun e => hh (List.eq_nil_of_length_eq_zero e.symm)
  obtain ⟨k1, k2, k3, k4⟩ := sendingMember_at J hfit wit .shared σ sim hr hd 1 0 m front asks (hsd _
    hap)
  have o : On (sendingMember σ J wit sim) ca m front := by
    rw [hOn]
    exact hap
  have hb : bud (sendingMember σ J wit sim).number (onesAt J.Q) asks := hbud _ _
  refine ⟨o, hsn, k1, hb, k2, k3, ?_, ?_⟩
  · intro c
    exact k4 c.1
  · exact hE' ca m front (onesAt J.Q) asks o hsn k1 hb k2 k3

section files
open VerifierAndGoals (InScope asDescriptionFiles)
open P5J (LaidAt TS)
open AtPublicFiles.TreeReads (sized_at written_proof)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **budAt at the written positions of "send o_u", and they fill the count**, at the public part
that the library lays off public files in the goals' scope. -/
theorem full_u_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r₀ Zp Np cF) (a : Nat) :
    budAt (jobU ⟨qAt Zp Np, a⟩).Q (fullAsks (sendPlace 2)) ∧
      (∀ k τ, k < (jobU ⟨qAt Zp Np, a⟩).Q.sent.size →
        ((VerifiableInference.Desc.Own.treesMade (jobU ⟨qAt Zp Np, a⟩).Q.codes (jobU ⟨qAt Zp Np,
          a⟩).Q.sent).getD {}).tree[k]? = some τ →
        τ < ((fullAsks (sendPlace 2))[0]?.getD []).length) ∧
      ∀ τ, τ < ((fullAsks (sendPlace 2))[0]?.getD []).length → ∃ k, k < (jobU ⟨qAt Zp Np,
        a⟩).Q.sent.size ∧
        ((VerifiableInference.Desc.Own.treesMade (jobU ⟨qAt Zp Np, a⟩).Q.codes (jobU ⟨qAt Zp Np,
          a⟩).Q.sent).getD {}).tree[k]? = some τ ∧
        (((shapeAt (jobU ⟨qAt Zp Np, a⟩).Q k).mainRows ≠ 0 ∧
            ((asked (fullAsks (sendPlace 2)) τ).map
                (· % 2 ^ ((jobU ⟨qAt Zp Np, a⟩).Q.codes.base.getD (shapeAt (jobU ⟨qAt Zp Np, a⟩).Q
                  k).code default).logN)).toFinset.card =
              ((jobU ⟨qAt Zp Np, a⟩).Q.codes.base.getD (shapeAt (jobU ⟨qAt Zp Np, a⟩).Q k).code
                default).r ∧
            ((jobU ⟨qAt Zp Np, a⟩).Q.codes.base.getD (shapeAt (jobU ⟨qAt Zp Np, a⟩).Q k).code
              default).r = (asked (fullAsks (sendPlace 2)) τ).length) ∨
          ((shapeAt (jobU ⟨qAt Zp Np, a⟩).Q k).maskRows ≠ 0 ∧
            ((asked (fullAsks (sendPlace 2)) τ).map
                (· % 2 ^ ((jobU ⟨qAt Zp Np, a⟩).Q.codes.mask.getD (shapeAt (jobU ⟨qAt Zp Np, a⟩).Q
                  k).maskCode default).logN)).toFinset.card =
              ((jobU ⟨qAt Zp Np, a⟩).Q.codes.mask.getD (shapeAt (jobU ⟨qAt Zp Np, a⟩).Q k).maskCode
                default).r ∧
            ((jobU ⟨qAt Zp Np, a⟩).Q.codes.mask.getD (shapeAt (jobU ⟨qAt Zp Np, a⟩).Q k).maskCode
              default).r =
              (asked (fullAsks (sendPlace 2)) τ).length)) := by
  refine full_u _ ?_ ?_
  · show Zp.p.chains.made.sized.proof.codes = _
    rw [sized_at scope L, written_proof]
  · have e : (jobU ⟨qAt Zp Np, a⟩).Q.sent = (Desc.K14.withU (qAt Zp Np).S).getD #[] :=
      Desc.K14.Law.parK1_sent (qAt Zp Np) 2 _ _
    rw [e]
    show (Desc.K14.withU Zp.p.chains.made.sized.proof.batch.shape).getD #[] = _
    rw [sized_at scope L, written_proof]

/-- **The like at "send o_omega".** -/
theorem full_omega_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r₀ Zp Np cF) (a : Nat) :
    budAt (jobOmega ⟨qAt Zp Np, a⟩).Q (fullAsks (sendPlace 5)) ∧
      (∀ k τ, k < (jobOmega ⟨qAt Zp Np, a⟩).Q.sent.size →
        ((VerifiableInference.Desc.Own.treesMade (jobOmega ⟨qAt Zp Np, a⟩).Q.codes (jobOmega ⟨qAt Zp
          Np, a⟩).Q.sent).getD {}).tree[k]? = some τ →
        τ < ((fullAsks (sendPlace 5))[0]?.getD []).length) ∧
      ∀ τ, τ < ((fullAsks (sendPlace 5))[0]?.getD []).length → ∃ k, k < (jobOmega ⟨qAt Zp Np,
        a⟩).Q.sent.size ∧
        ((VerifiableInference.Desc.Own.treesMade (jobOmega ⟨qAt Zp Np, a⟩).Q.codes (jobOmega ⟨qAt Zp
          Np, a⟩).Q.sent).getD {}).tree[k]? = some τ ∧
        (((shapeAt (jobOmega ⟨qAt Zp Np, a⟩).Q k).mainRows ≠ 0 ∧
            ((asked (fullAsks (sendPlace 5)) τ).map
                (· % 2 ^ ((jobOmega ⟨qAt Zp Np, a⟩).Q.codes.base.getD (shapeAt (jobOmega ⟨qAt Zp Np,
                  a⟩).Q k).code default).logN)).toFinset.card =
              ((jobOmega ⟨qAt Zp Np, a⟩).Q.codes.base.getD (shapeAt (jobOmega ⟨qAt Zp Np, a⟩).Q
                k).code default).r ∧
            ((jobOmega ⟨qAt Zp Np, a⟩).Q.codes.base.getD (shapeAt (jobOmega ⟨qAt Zp Np, a⟩).Q
              k).code default).r = (asked (fullAsks (sendPlace 5)) τ).length) ∨
          ((shapeAt (jobOmega ⟨qAt Zp Np, a⟩).Q k).maskRows ≠ 0 ∧
            ((asked (fullAsks (sendPlace 5)) τ).map
                (· % 2 ^ ((jobOmega ⟨qAt Zp Np, a⟩).Q.codes.mask.getD (shapeAt (jobOmega ⟨qAt Zp Np,
                  a⟩).Q k).maskCode default).logN)).toFinset.card =
              ((jobOmega ⟨qAt Zp Np, a⟩).Q.codes.mask.getD (shapeAt (jobOmega ⟨qAt Zp Np, a⟩).Q
                k).maskCode default).r ∧
            ((jobOmega ⟨qAt Zp Np, a⟩).Q.codes.mask.getD (shapeAt (jobOmega ⟨qAt Zp Np, a⟩).Q
              k).maskCode default).r =
              (asked (fullAsks (sendPlace 5)) τ).length)) := by
  refine full_omega _ ?_ ?_
  · show Zp.p.chains.made.sized.proof.codes = _
    rw [sized_at scope L, written_proof]
  · have e : (jobOmega ⟨qAt Zp Np, a⟩).Q.sent = Desc.K14.withOmega (qAt Zp Np).S :=
      Desc.K14.Law.parK1_sent (qAt Zp Np) 5 _ _
    rw [e]
    show Desc.K14.withOmega Zp.p.chains.made.sized.proof.batch.shape = _
    rw [sized_at scope L, written_proof]

end files

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.ofDecl_slice
#print axioms ProofFile.Honest.K14.sendingMember_at
#print axioms ProofFile.Honest.K14.exactSix_at
#print axioms ProofFile.Honest.K14.full_u_at_files
#print axioms ProofFile.Honest.K14.full_omega_at_files
#print axioms ProofFile.Honest.K14.onesAt_map
#print axioms ProofFile.Honest.K14.onesAt_fits
#print axioms ProofFile.Honest.K14.sendingMember_rounds
#print axioms ProofFile.Honest.K14.holds_send
#print axioms ProofFile.Honest.K14.stop_send
#print axioms ProofFile.Honest.K14.budAt_of_lengths
#print axioms ProofFile.Honest.K14.asked_zero
#print axioms ProofFile.Honest.K14.asked_one
#print axioms ProofFile.Honest.K14.card_range_mod
#print axioms ProofFile.Honest.K14.written_u
#print axioms ProofFile.Honest.K14.written_omega
#print axioms ProofFile.Honest.K14.full_u
#print axioms ProofFile.Honest.K14.full_omega
#print axioms ProofFile.Honest.K14.onesAt
#print axioms ProofFile.Honest.K14.fullAsks
