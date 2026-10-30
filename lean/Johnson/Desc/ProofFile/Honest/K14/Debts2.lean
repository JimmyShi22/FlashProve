-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Debts2.lean: kind K14: UNDER THE PUBLIC PREMISES Plan2 (and, at
the member 1, where a valid input's key has sizes that fit), FROM THE THREAD IN FRONT AND THE
MEMBER's STEP: THE FORM BEHIND AND keeps AT THE MEMBERS 1 TO 8 OF THE SHARED CHAIN's THREAD, at this
kind's letters (Honest/K14/Thread2.lean: letters2): «Behind» (Honest/Thread/Pays.lean) without its
clause on the letter rides. Three definitions, and statements with their proofs.

Behind a member's own step, with the thread in front in hand: the form behind (the kind's
book-keeping shapeK at the next number; the state's codes are the plan's; the statement is in
order), and what the step has left (keeps2). How: the thread's clause on how the state was made,
with the member's step, is a run of steps up to the member (Johnson/Desc/K14/Honest/FlatSteps.lean:
FlatAt.member1, …, member8); the rest is StepsTwins.lean's and ItemsOwn.lean's. The form in front is
spent at one member: the sending of o_u. SO THESE LAWS STAND ON THE THREAD IN FRONT, NOT ON THE
MEMBER's ACCEPTING STEP ALONE. Of keeps2 the last clause (laid2) and QuietStep come from the
member's step and public premises, without the thread; the clauses at the two sendings that read o_u
as the message to come (uRK) spend what the run in front has laid.

THE LETTER rides. This kind leaves it free at every border, and NO MEMBER OF THE EIGHT LAYS A CLAUSE
OF IT. Where the letter is a list of clauses (Honest/Thread/Riders.lean: ridersOf), «Behind» at a
member comes down to the form, the member's clause of keeps and the clauses that the member lays: so
from FormKeeps, with «each clause stays by keeps» (StaysBy: whoever lays the thread shows it),
«Behind» follows: behind_of_formKeeps. A CLAUSE GOES PAST A MEMBER BY keeps ALONE, not by the
member's step: so it can stay only as far as keeps2 speaks. At "LIN point" and "LIN zeta" keeps2
says LESS THAN ALL THAT THE MEMBER HAS LAID (laid2: the library's own relations): every field of the
state behind but the noted point; WHICH POINT IS NOTED, which is what the member lays, IS UNSAID:
only that it is some round's drawn elements: any list. At the two sendings, at this kind's own
public parameters: what the kind notes; the codes, the groups and the elder messages; how many
messages are new; the book and the count of roots behind; of a new message its shape, that it is in
no group and not spent, whether it is sampled, the number of its sample constraints, and its ledger
where it has answers; UNSAID OF IT: the entries of its sample constraints, its pad, its ledger where
it has no answer. At "(rec_gamma)", "LOC", the joinings and "SPLIT" it says QuietStep
(Johnson/Desc/K14/Law/LedgerOne.lean: a step onward that leaves what the kind notes, the messages
and the book): LESS THAN ALL THAT THE MEMBER HAS LAID.

Main names:
  Plan2, Plan2.pub, Plan2.eight   the public premises: PlanFacts; the two sendings pass their kind's
                      test on the plan. Under them the kind's text makes its eight sub-protocols
  FormKeeps, FormKeepsS, formKeepsS_of   **the form behind and keeps**: definitions: premises'
                      forms, general in the thread: to the letter the premise hFK of Riders.lean's
                      behind_of_keeps and behindS_of_keeps (and of RidersAnd.lean's two)
  behind_of_formKeeps, behindS_of_formKeeps   «Behind» of a member that lays no such clause: calls
                      of these two laws. Their premises are met together at a term in
                      Honest/K14/Thread2Member.lean (behind_at_key: the list of no clause)
  laid2_step          **keeps2's last clause FROM THE MEMBER's ACCEPTING STEP**, at every state in
                      front, without the thread: what "LIN point", the two sendings and "LIN zeta"
                      have laid. Beside the step: five public premises, which follow from Plan2
                      (what goes out with o_u; the shape splits; masks ahead; the two sendings' test
                      on the plan). It stands at the kind's own eight; formKeeps1, 2, 5 and 7 carry
                      it to the list's members
  formKeeps1, …, formKeeps8   **under Plan2: FormKeeps (letters2 Q sentU O Cl).thread b**: NO
                      PREMISE ON rides
Who calls them: behindS_of_formKeeps is called by no other file.

What is assumed, as premises: Plan2. AT formKeeps1 ALONE: a valid input's key has sizes that fit
(hkey): the form behind "LIN point" holds the key's fit. At every key that the library's own maker
of keys returns the sizes fit, in the library's own form (tableKey_fits,
OnBytes/Params/EntryRoundsRecord.lean); hkey's own sentence stands, as the field key of FiveFields
(Honest/K14/FiveFields.lean), at every input whose key the committer makes of its index and coins
(validAt), at every public part that the maker (pubPlain) returns of public files in the goals'
scope: fiveFieldsK14_inScope (Johnson/Bind/ForProver/FiveFieldsAt.lean): NOT IN FRONT OF A LAW OVER
COINS (the rule: that file's head); at the offline plan's index shape: keyFits_of_relation
(E2E/OfflineOwnKeyFits.lean).

What is not claimed. That a clause of rides stays past one of the eight (StaysBy): no clause is
named here. That the thread holds at any run: at a thread that is false everywhere these are met for
nothing. The thread's other premises on a member. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Thread2
import Johnson.Desc.ProofFile.Honest.Thread.Riders
import Johnson.Desc.Key.Laid.Draws
import Johnson.Desc.Key.Laid.Laid2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Slice (rdE)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.K1 (planOkOwn decideSend_iff)
open VerifiableInference.Desc.Key (laid_point)
open VerifiableInference.Desc.Key.LaidW (inFrontOf laid22_of_yes laid25_of_yes)
open Johnson.Prover.Send (behind_rest)
open VerifiableInference.Desc.Sound (step_ok_iff)
open Desc.K14 (P14 first)
open Desc.K14.Honest
open Desc.K14.Law (parU parO parK1_sent linZeta_inv uRK uRK_seated seatedUB_iff shapeK)

/-- **The public premises.** -/
structure Plan2 (Q : P14) (sentU : Array OracleNotice) (layO : TreeLay) : Prop where
  facts : PlanFacts Q.par Q.codes sentU layO
  planU : planOkOwn (parU Q sentU) = true
  planO : planOkOwn (parO Q) = true

/-- They give Public8 at the shared chain's first state, at every key. -/
theorem Plan2.pub {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}
    (h : Plan2 Q sentU layO) (key : TableKey) : Public8 Q sentU layO (first Q.codes key) :=
  ⟨h.facts, h.planU, h.planO, rfl, rfl⟩

/-- Under them the kind's text makes its eight: it fails only where what goes out with o_u cannot be
said. -/
theorem Plan2.eight {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}
    (h : Plan2 Q sentU layO) : Nonempty (Eight Q) := by
  have hU : Desc.K14.withU Q.S = some sentU := h.facts.goes
  exact ⟨⟨_, _, _, _, _, _, _, _, by
    unfold Desc.K14.blocks
    rw [hU]
    rfl⟩⟩

/-! ## The form behind and keeps: general in the thread -/

section general
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **THE FORM BEHIND AND keeps**, at the member number b: from the thread in front and the member's
step: behind it the form holds, and the step has left what keeps names: «Behind» (Honest/Thread/
Pays.lean) WITHOUT ITS CLAUSE ON rides. To the letter the premise hFK of behind_of_keeps and
behind_of_keeps_and (Honest/Thread/Riders.lean, RidersAnd.lean). It is a definition: a premise's
form. -/
def FormKeeps (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Form (b + 1) k s' y.2 ∧ T.keeps b s s'

/-- The like, asked from the pair of the thread and a further sentence Said on the run (ThrS,
Honest/Thread/Said.lean; BehindS, Honest/Thread/PaysS.lean): behindS_of_keeps' premise hFK. -/
def FormKeepsS (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Form (b + 1) k s' y.2 ∧ T.keeps b s s'

variable {T}

/-- From the one form to the other. -/
theorem formKeepsS_of (Said : Nat → Coins Bk → Mid W X → Prop) {b : Nat} (h : FormKeeps T b) :
    FormKeepsS T Said b :=
  fun blk hblk k s m E ds y cols s' hA => h blk hblk k s m E ds y cols s' hA.1

/-- **«Behind» of a member that lays no clause of the letter rides**, where that letter is a list of
clauses: from FormKeeps, and: each clause that speaks on both sides of the member stays by the
member's clause of keeps. A call of behind_of_keeps. -/
theorem behind_of_formKeeps {cs : List (RiderCl W S)} {b : Nat}
    (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s) (h : FormKeeps T b)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c) (hno : ∀ c ∈ cs, c.lo ≠ b + 1) :
    Behind T b :=
  behind_of_keeps T hr h hst fun c hc e => absurd e (hno c hc)

/-- The like from the pair of the thread and Said. A call of behindS_of_keeps. -/
theorem behindS_of_formKeeps (Said : Nat → Coins Bk → Mid W X → Prop) {cs : List (RiderCl W S)}
    {b : Nat} (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s) (h : FormKeepsS T Said b)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c) (hno : ∀ c ∈ cs, c.lo ≠ b + 1) :
    BehindS T Said b :=
  behindS_of_keeps T Said hr h hst fun c hc e => absurd e (hno c hc)

end general

/-! ## At this kind's letters, at the members 1 to 8 -/

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OracleNotice}
  {layO : TreeLay}

/-- **WHAT "LIN point", THE TWO SENDINGS AND "LIN zeta" HAVE LAID, FROM THE MEMBER's ACCEPTING
STEP**, under five public premises: no thread, at every state in front: by the library's laid_point,
laid22_of_yes, laid25_of_yes (Johnson/Desc/Key/Laid/Draws.lean, Laid2.lean) and linZeta_inv. At 1
and 7 the library's laws name the round (rs = [r]); THE FORM laid2 CANNOT HOLD IT, AND IT IS LET GO
HERE. -/
theorem laid2_step {P : P14} (hU : Desc.K14.withU P.S = some sentU)
    (hS : P.S.sharedSplitNeeded = true) (hM : P.par.S.masksAhead = true)
    (hBU : planOkOwn (parU P sentU) = true) (hBO : planOkOwn (parO P) = true) (B : Eight P)
    (ft : Nat) (d d' : Desc.K14.St) (rs : List Fmt.RoundView) (c : List VerifiableInference.Desc.OpenedColumn)
    (n : Nat) :
    (B.b1.step ft d rs c = .ok (d', n) → laid2 P sentU 1 d d') ∧
    (B.b2.step ft d rs c = .ok (d', n) → laid2 P sentU 2 d d') ∧
    (B.b5.step ft d rs c = .ok (d', n) → laid2 P sentU 5 d d') ∧
    (B.b7.step ft d rs c = .ok (d', n) → laid2 P sentU 7 d d') := by
  obtain ⟨-, ⟨n2, f2, g2, e2⟩, n5, f5, g5, e5⟩ := B.fronts hU
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨R, -, -, k, -⟩ := B.back1 hU ft d d' rs c n h
    obtain ⟨r, -, hp⟩ := laid_point P.par _ _ _ hS k
    exact ⟨fun _ => ⟨r, hp⟩, fun h => by omega, fun h => by omega, fun h => by omega⟩
  · obtain ⟨Ra, Rb, -, -, hf, k⟩ := B.back2 hU ft d d' rs c n h
    rw [e2] at k
    exact ⟨fun h => by omega, fun _ => laid22_of_yes P n2 _ f2 g2 _ _ _ _ _ hBU hf hM k,
      fun h => by omega, fun h => by omega⟩
  · obtain ⟨Ra, Rb, -, -, hf, k⟩ := B.back5 hU ft d d' rs c n h
    rw [e5] at k
    exact ⟨fun h => by omega, fun h => by omega,
      fun _ => laid25_of_yes P n5 _ f5 g5 _ _ _ _ _ hBO hf hS k, fun h => by omega⟩
  · obtain ⟨R, -, -, k, -⟩ := B.back7 hU ft d d' rs c n h
    exact ⟨fun h => by omega, fun h => by omega, fun h => by omega,
      fun _ => ⟨_, ⟨linZeta_inv _ _ _ k⟩⟩⟩

/-- **Under Plan2, and where a valid input's key has sizes that fit (hkey): the form behind and
keeps at "LIN point".** -/
theorem formKeeps1 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hkey : ∀ w, O.valid w → keyFits w.key Q.par.S.fold.index = true) :
    FormKeeps (letters2 Q sentU O Cl).thread 1 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA _ hS
  obtain ⟨-, -, -, -, hM, -, hV⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hs : blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) := hS.2
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, -, -, -, e1, e2, u⟩ := FlatAt.member1 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  have S := hQ.pub m.st.input.key
  refine ⟨⟨?_, Steps.order1 S u (first_kept rdE Q.codes _ fun _ _ _ => 0).1⟩, ?_⟩
  · show (form2 Q O.shape 2 D.d1 && _) = true
    rw [form2_eq Q O.shape 2 _ (by omega), Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨Steps.shape1 S u (hkey _ hV), Steps.codes1 S u _⟩, rfl⟩
  · refine (keepsAll_eq Q sentU O.keeps 1 s D.d1 (by omega)).mpr ?_
    have hl := F.at1 hblk
    rw [hl.step] at hs
    exact ⟨fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega,
      (laid2_step hQ.facts.goes hQ.facts.two hQ.facts.ahead hQ.planU hQ.planO B 0 _ _ _ _ _).1 hs⟩

/-- **Under Plan2: the form behind and keeps at the sending of o_u.** The book-keeping behind comes
from the form in front. -/
theorem formKeeps2 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    FormKeeps (letters2 Q sentU O Cl).thread 2 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA _ hS
  obtain ⟨-, -, hFm, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hs : blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) := hS.2
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, -, -, -, e1, e2, u⟩ := FlatAt.member2 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  have S := hQ.pub m.st.input.key
  refine ⟨⟨?_, Steps.order2 S u (first_kept rdE Q.codes _ fun _ _ _ => 0).1⟩, ?_⟩
  · show (form2 Q O.shape 3 D.d2 && _) = true
    rw [form2_eq Q O.shape 3 _ (by omega), Bool.and_eq_true, Bool.and_eq_true]
    have hf : (form2 Q O.shape 2 s && _) = true := hFm.1
    rw [Bool.and_eq_true, form2_eq Q O.shape 2 s (by omega), Bool.and_eq_true] at hf
    obtain ⟨x, ids, t⟩ := S.to2 u
    have h3 : shapeK Q.par 0 (0 + 2) Q.par.S.fold.columns 3 D.d2 = true :=
      shape_next2 Q "send o_u" (parU Q sentU) none [] sentU S.facts.goes (parK1_sent Q 2 _ sentU)
        S.facts.goesTwo 0 _ D.d1 D.d2 _ [] (t.s2.decides Q "send o_u" none [] [])
        (by rw [e1]; exact hf.1.1)
    exact ⟨⟨h3, Steps.codes2 S u _⟩, rfl⟩
  · refine (keepsAll_eq Q sentU O.keeps 2 s D.d2 (by omega)).mpr ?_
    have hl := F.at2 hblk
    rw [hl.step] at hs
    refine ⟨fun h => by omega, fun h => by omega, fun _ => ?_, fun h => by omega,
      (laid2_step hQ.facts.goes hQ.facts.two hQ.facts.ahead hQ.planU hQ.planO B 0 _ _ _ _ _).2.1
        hs⟩
    subst e1
    obtain ⟨x, ids, t⟩ := S.to2 u
    obtain ⟨n1, k1, p1⟩ := S.notes1 t.front rfl
    have A := S.at2 t
    have n2 := A.notes
    have e2 : uRK Q.par D.d2 = D.d2 := uRK_seated Q.par D.d2 (A.stands S.facts)
    rw [e2]
    exact ⟨n2.psi.trans p1.symm, n2.psi.trans n1.psi.symm, n2.u.trans n1.u.symm,
      A.carried.key.trans k1.symm⟩

/-- **Under Plan2: the form behind and keeps at "(rec_gamma)".** -/
theorem formKeeps3 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    FormKeeps (letters2 Q sentU O Cl).thread 3 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA _ hS
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hs : blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) := hS.2
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, -, -, -, e1, e2, u⟩ := FlatAt.member3 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  have S := hQ.pub m.st.input.key
  refine ⟨⟨?_, Steps.order3 S u (first_kept rdE Q.codes _ fun _ _ _ => 0).1⟩, ?_⟩
  · show (form2 Q O.shape 4 D.d3 && _) = true
    rw [form2_eq Q O.shape 4 _ (by omega), Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨Steps.shape3 S u, Steps.codes3 S u _⟩, rfl⟩
  · refine (keepsAll_eq Q sentU O.keeps 3 s D.d3 (by omega)).mpr ?_
    refine ⟨fun _ => ?_, fun h => by omega, fun h => by omega, fun h => by omega,
      fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega⟩
    have hl := F.at3 hblk
    rw [hl.step] at hs
    have hd' := ((step_ok_iff 0 B.b3 _ _ _ _ _).1 hs).2.2.2
    exact (quiet_each Q hQ.facts.two B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made _ _ _
      _).1 hd'

/-- **Under Plan2: the form behind and keeps at "LOC".** -/
theorem formKeeps4 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    FormKeeps (letters2 Q sentU O Cl).thread 4 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA _ hS
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hs : blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) := hS.2
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, -, -, -, -, e1, e2, u⟩ := FlatAt.member4 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  have S := hQ.pub m.st.input.key
  refine ⟨⟨?_, Steps.order4 S u (first_kept rdE Q.codes _ fun _ _ _ => 0).1⟩, ?_⟩
  · show (form2 Q O.shape 5 D.d4 && _) = true
    rw [form2_eq Q O.shape 5 _ (by omega), Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨Steps.shape4 S u, Steps.codes4 S u _⟩, rfl⟩
  · refine (keepsAll_eq Q sentU O.keeps 4 s D.d4 (by omega)).mpr ?_
    refine ⟨fun _ => ?_, fun h => by omega, fun h => by omega, fun h => by omega,
      fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega⟩
    have hl := F.at4 hblk
    rw [hl.step] at hs
    have hd' := ((step_ok_iff 0 B.b4 _ _ _ _ _).1 hs).2.2.2
    exact (quiet_each Q hQ.facts.two B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made _ _ _
      _).2.1 hd'

/-- **Under Plan2: the form behind and keeps at the sending of o_omega and o_sp.** -/
theorem formKeeps5 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    FormKeeps (letters2 Q sentU O Cl).thread 5 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA _ hS
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hs : blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) := hS.2
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, -, -, -, e1, e2, u⟩ := FlatAt.member5 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  have S := hQ.pub m.st.input.key
  refine ⟨⟨?_, Steps.order5 S u (first_kept rdE Q.codes _ fun _ _ _ => 0).1⟩, ?_⟩
  · show (form2 Q O.shape 6 D.d5 && _) = true
    rw [form2_eq Q O.shape 6 _ (by omega), Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨Steps.shape5 S u, Steps.codes5 S u _⟩, rfl⟩
  · refine (keepsAll_eq Q sentU O.keeps 5 s D.d5 (by omega)).mpr ?_
    have hl := F.at5 hblk
    rw [hl.step] at hs
    refine ⟨fun h => by omega, fun h => by omega, fun h => by omega, fun _ => ?_,
      (laid2_step hQ.facts.goes hQ.facts.two hQ.facts.ahead hQ.planU hQ.planO B 0 _ _ _ _ _).2.2.1
        hs⟩
    subst e1
    obtain ⟨x, ids, x', ids', t⟩ := S.to5 u
    have A4 := S.at4 t.front
    have A5 := S.at5 t
    have l4 : D.d4.loc = _ := A4.loc
    have l5 : D.d5.loc = _ := A5.loc
    have s4 : uRK Q.par D.d4 = D.d4 := uRK_seated Q.par D.d4 (A4.stands S.facts)
    have s5 : uRK Q.par D.d5 = D.d5 := by
      obtain ⟨y, hy, hsy, _⟩ := A5.hasU.u
      exact uRK_seated Q.par D.d5 ((seatedUB_iff Q.par D.d5).2
        ⟨⟨y, hy, hsy⟩, A5.hasU.lay, by rw [A5.carried.codes]; exact linOk_of S.facts⟩)
    obtain ⟨_, _, ex⟩ := (decideSend_iff (parO Q) none (inFrontOf D.d4) x' _ _ ids').1 t.s5.sent
    have est : D.d5.st = x'.st := t.s5.st
    obtain ⟨c1, c2, _, _, _, c6, _⟩ := behind_rest (parO Q) (inFrontOf D.d4)
      (VerifiableInference.Desc.K1.seedsOf (parO Q) W.view.r5a)
      (VerifiableInference.Desc.K1.answersIn W.view.r5b)
    rw [s4, s5]
    refine ⟨by rw [l5, l4]; rfl, by rw [l5, l4]; rfl, by rw [l5, l4]; rfl, ?_⟩
    rw [est, ex]
    exact ⟨c1, c2, c6⟩

/-- **Under Plan2: the form behind and keeps at the joinings.** -/
theorem formKeeps6 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    FormKeeps (letters2 Q sentU O Cl).thread 6 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA _ hS
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hs : blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) := hS.2
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, -, -, -, e1, e2, u⟩ := FlatAt.member6 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  have S := hQ.pub m.st.input.key
  refine ⟨⟨?_, Steps.order6 S u (first_kept rdE Q.codes _ fun _ _ _ => 0).1⟩, ?_⟩
  · show (form2 Q O.shape 7 D.d6 && _) = true
    rw [form2_eq Q O.shape 7 _ (by omega), Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨Steps.shape6 S u, Steps.codes6 S u _⟩, rfl⟩
  · refine (keepsAll_eq Q sentU O.keeps 6 s D.d6 (by omega)).mpr ?_
    refine ⟨fun _ => ?_, fun h => by omega, fun h => by omega, fun h => by omega,
      fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega⟩
    have hl := F.at6 hblk
    rw [hl.step] at hs
    have hd' := ((step_ok_iff 0 B.b6 _ _ _ _ _).1 hs).2.2.2
    exact (quiet_each Q hQ.facts.two B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made _ _ _
      _).2.2.1 hd'

/-- **Under Plan2: the form behind and keeps at "LIN zeta".** -/
theorem formKeeps7 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    FormKeeps (letters2 Q sentU O Cl).thread 7 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA _ hS
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hs : blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) := hS.2
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, -, -, -, e1, e2, u⟩ := FlatAt.member7 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  have S := hQ.pub m.st.input.key
  refine ⟨⟨?_, Steps.order7 S u (first_kept rdE Q.codes _ fun _ _ _ => 0).1⟩, ?_⟩
  · show (form2 Q O.shape 8 D.d7 && _) = true
    rw [form2_eq Q O.shape 8 _ (by omega), Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨Steps.shape7 S u, Steps.codes7 S u _⟩, rfl⟩
  · refine (keepsAll_eq Q sentU O.keeps 7 s D.d7 (by omega)).mpr ?_
    have hl := F.at7 hblk
    rw [hl.step] at hs
    obtain ⟨R, -, -, kz, -⟩ := B.back7 hQ.facts.goes 0 _ _ _ _ _ hs
    refine ⟨fun h => by omega, fun _ => ?_, fun h => by omega, fun h => by omega,
      (laid2_step hQ.facts.goes hQ.facts.two hQ.facts.ahead hQ.planU hQ.planO B 0 _ _ _ _ _).2.2.2
        hs⟩
    rw [linZeta_inv _ _ _ kz]
    exact ⟨rfl, rfl⟩

/-- **Under Plan2: the form behind and keeps at "SPLIT".** -/
theorem formKeeps8 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    FormKeeps (letters2 Q sentU O Cl).thread 8 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA _ hS
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hs : blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) := hS.2
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, -, -, -, e1, e2, u⟩ := FlatAt.member8 (B := B) F hQ.facts.goes
    hQ.facts.two 0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  have S := hQ.pub m.st.input.key
  refine ⟨⟨?_, Steps.order8 S u (first_kept rdE Q.codes _ fun _ _ _ => 0).1⟩, ?_⟩
  · show (form2 Q O.shape 9 D.d8 && _) = true
    rw [form2_eq Q O.shape 9 _ (by omega), Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨Steps.shape8 S u, Steps.codes8 S u _⟩, rfl⟩
  · refine (keepsAll_eq Q sentU O.keeps 8 s D.d8 (by omega)).mpr ?_
    refine ⟨fun _ => ?_, fun h => by omega, fun h => by omega, fun h => by omega,
      fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega⟩
    have hl := F.at8 hblk
    rw [hl.step] at hs
    have hd' := ((step_ok_iff 0 B.b8 _ _ _ _ _).1 hs).2.2.2
    exact (quiet_each Q hQ.facts.two B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made _ _ _
      _).2.2.2 hd'

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.Plan2.pub
#print axioms ProofFile.Honest.K14.Plan2.eight
#print axioms ProofFile.Honest.K14.formKeepsS_of
#print axioms ProofFile.Honest.K14.behind_of_formKeeps
#print axioms ProofFile.Honest.K14.behindS_of_formKeeps
#print axioms ProofFile.Honest.K14.laid2_step
#print axioms ProofFile.Honest.K14.formKeeps1
#print axioms ProofFile.Honest.K14.formKeeps2
#print axioms ProofFile.Honest.K14.formKeeps3
#print axioms ProofFile.Honest.K14.formKeeps4
#print axioms ProofFile.Honest.K14.formKeeps5
#print axioms ProofFile.Honest.K14.formKeeps6
#print axioms ProofFile.Honest.K14.formKeeps7
#print axioms ProofFile.Honest.K14.formKeeps8
