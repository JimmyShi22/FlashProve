-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OmegaEnd.lean: kind K14: WHAT THE KIND's OWN SUB-PROTOCOLS OF THE
SHARED CHAIN LAY FOR "K14, second part" (Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean), which takes Omega over
from the shared chain's end: three tests with code on a state of the shared chain, and: all three
are true BEHIND "SPLIT", the last of the kind's eight, at every run of the eight steps from a first
state, under the public premises. Definitions with code, and statements with their proofs.

  omegaEndL S o   **THE LIST**, on the four things that the last chain takes of the shared chain's
                  end (the library's SharedOut; of a state d: the library's oOf d,
                  Johnson/Desc/Third/Law/Row0AtWords.lean): Omega has a place in the book; its tree
                  is there; it is in the statement (each listed only where it is false); it has a
                  tree to itself; it has the plan's shape; it is sampled; the shared point has as
                  many coordinates as a column's number has bits. The first six are tests of
                  secondDoor (Honest/K14/SecondDoor.lean), under the same names, written out here
                  once more; how the two lists meet: Honest/K14/OmegaDoor.lean: door_of_omega
  omegaEndB S d   the list is all true at oOf d, and the first mask's number is not Omega's
  omegaPadB S d   Omega's pad lies at the places that the plan's shape S.omega gives; false where
                  Omega is not in the statement
  notesB d o g, thereB d g the message number o is there and notes the group number g; the group
                  number g is there
  notedB d        o_u notes the group G_u, o_omega notes G_omega, o_sp notes both, and the two
                  groups are there
  OmegaFacts p d  all that as facts, in the terms of Johnson/Desc/K14/Honest/YesFacts.lean and
                  YesBorders.lean
  notes_grows, there_grows, noted_grows a note of a group stays where the statement grows (the
                  library's Grows, Johnson/Desc/Grows.lean); so does a group; so notedB, where the
                  five numbers stay
  omegaFacts_split **THE FACTS GO OVER "SPLIT"**, where Omega's number is not o_sp's (hne) and the
                  shape splits the row (Fold) (hS): by the library's SplitLaid
                  (Johnson/Desc/Key/Laid/SplitDef.lean) and onward_split. It has no premise Plan2
  omegaFacts_at8  **behind a run of all eight steps the facts hold**, under Public8
                  (Johnson/Desc/K14/Honest/RunsTo.lean)
  omegaEnd_of_facts, omegaPad_of_facts the facts give the first two tests; the third is one of them
  omega_of_fold   so where the fold over a flat list's first nine members returns, under Public8, at
                  a list of the form FlatAt
  omega_at_nine   **so at border 9 of a Thread of the shared chain (Thread and Thr:
                  Honest/Thread/Thr.lean), wherever Thr holds**: general in the Thread
  one_plan        the shared chain's parameters and the last chain's, both out of the planner's
                  chains, have one shape and one table of codes: by unfolding, at every list bp

WHO LAYS WHAT. "LIN point" notes the shared point. "send o_u" notes the first mask's number.
"(rec_gamma)" lets o_u note its group. "send o_omega" notes Omega's number and lays its entry in the
statement, its place and its tree in the book, and its pad. The joinings let o_omega and o_sp note
their groups. "LIN zeta" and "SPLIT" keep all that.

THE PUBLIC PREMISES ARE Plan2 (Honest/K14/Debts2.lean), SO PlanFacts
(Johnson/Desc/K14/Honest/YesChain.lean): AMONG THEM: THE ROW (Fold) IS SPLIT OVER TWO CODES (two:
fold.u's code is not omega's), AND THE MASKS ARE SENT AHEAD (ahead). (The row (Dot) is another
matter: the last chain's start asks that it is NOT split: w's code is omega's. The two hold
together: so at the small shape of Johnson/Desc/K14/Honest/Toy.lean, by that shape's typed numbers:
u's code is 0, omega's and w's are 1; no statement there says the half on (Dot).) At a shape whose
row (Fold) has one code, or with masks not sent ahead, no theorem of this file that takes Plan2 or
Public8 (omegaFacts_at8, omega_of_fold, omega_at_nine) says anything. omegaFacts_split asks of the
two only that the row (Fold) is split (hS); the other theorems have no such premise. Plan2 at the
shared chain's own parameters: Honest/K14/PlanAtHead.lean.

What is not claimed. THAT THE TESTS HOLD AT THE SHARED CHAIN's END: behind "SPLIT" stand the two
proximity tests and the chain's closing sub-protocol: Honest/K14/OmegaDoor.lean says what they keep,
and OmegaTwelve.lean has the tests at the borders 10, 11 and 12. That a run of the eight steps
exists. Where the library's Send.pad returns nothing (the row is too short for the pad) omegaPadB
asks an empty pad. Nothing on what a message holds. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondDoor
import Johnson.Desc.ProofFile.Honest.K14.AcceptedAt
import Johnson.Desc.K14.Honest.FlatSteps
import Johnson.Desc.Key.Laid.Split
import Johnson.Desc.Third.Law.Row0AtWords
import Johnson.Desc.Own.AloneMeans
import Johnson.Desc.K14.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (OracleNotice TreeLay TableKey)
open VerifiableInference.Desc (OpenedColumn foldBlocks Grows)
open VerifiableInference.Desc.Own (aloneIn aloneIn_iff)
open VerifiableInference.Desc.Ground (Clauses ok)
open VerifiableInference.Desc.Third (SharedOut)
open VerifiableInference.Desc.Third.Law (oOf)
open VerifiableInference.Desc.Key (laid_split laid_rec joined_joins)
open VerifiableInference.Desc.Key.LaidW (send_laid)
open Desc.Plain (Par)
open Desc.K14 (P14 St first p14Of)
open Desc.K14.Law (onward_split onward_loc onward_joins)
open Desc.K14.Honest (MsgIs Eight Public8 StepTo8 Seen8 States8 FlatAt)

/-- **THE LIST.** The first three say that something is there and are listed only where they are
false. These three and the next three stand in secondDoor too (Honest/K14/SecondDoor.lean), under
the same names: they are written out here once more. -/
def omegaEndL (S : OnBytes.Params.LinShape) (o : SharedOut) : Clauses :=
  match o.book.place[o.omega]? with
  | none => [("Omega: it has a place in the shared chain's book", false)]
  | some q =>
  match o.book.trees[q.1]? with
  | none => [("Omega: its tree is in the shared chain's book", false)]
  | some t =>
  match o.st.oracles[o.omega]? with
  | none => [("Omega: it is in the shared chain's statement", false)]
  | some y =>
    [("Omega: it has a tree to itself", t.parts.size == 1),
     ("Omega: it has the plan's shape", decide (y.shape = S.omega)),
     ("elsewhere: sampled there", y.sampled),
     ("the shared point has as many coordinates as a column's number has bits",
       o.psi.length == S.kCol)]

/-- The list is all true at a state of the shared chain, and the first mask's number is not
Omega's. -/
def omegaEndB (S : OnBytes.Params.LinShape) (d : St) : Bool :=
  ok (omegaEndL S (oOf d)) && (d.loc.firstMask != some d.loc.oOmega)

/-- Omega's pad lies at the places that the plan's shape S.omega gives (not the entry's own shape).
Where the library's Send.pad returns nothing the test asks an empty pad (getD []); where Omega is
not in the statement the test is false. -/
def omegaPadB (S : OnBytes.Params.LinShape) (d : St) : Bool :=
  match d.st.oracles[d.loc.oOmega]? with
  | some y => decide (y.pad = ((OnBytes.Send.pad d.st.codes S.omega).getD []).map fun p =>
      (p.part, p.index))
  | none => false

/-- The message number o is there and notes the group number g, as a test. -/
def notesB (d : St) (o g : Nat) : Bool := (d.st.oracles[o]?).any (·.groups.contains g)

/-- The group number g is there, as a test. -/
def thereB (d : St) (g : Nat) : Bool := (d.st.groups[g]?).isSome

/-- o_u notes G_u, o_omega notes G_omega, o_sp notes both, and the two groups are there. -/
def notedB (d : St) : Bool :=
  notesB d d.loc.oU.oracle d.loc.gU && notesB d d.loc.oOmega d.loc.gOmega &&
    notesB d d.loc.oSp d.loc.gOmega && notesB d d.loc.oSp d.loc.gU && thereB d d.loc.gU &&
    thereB d d.loc.gOmega

/-- A note of a group stays where the statement grows. -/
theorem notes_grows {d e : St} (g : Grows d.st e.st) {o n : Nat} (h : notesB d o n = true) :
    notesB e o n = true := by
  unfold notesB at h ⊢
  cases hx : d.st.oracles[o]? with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    obtain ⟨x', hx', -, -, hg⟩ := g.2.2 o x hx
    rw [hx']
    have h' : x.groups.contains n = true := h
    show x'.groups.contains n = true
    rw [List.contains_iff_mem] at h' ⊢
    exact hg n h'

/-- So does a group. -/
theorem there_grows {d e : St} (g : Grows d.st e.st) {n : Nat} (h : thereB d n = true) :
    thereB e n = true := by
  unfold thereB at h ⊢
  obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨G', hG', -⟩ := g.2.1 n G hG
  rw [hG']
  rfl

/-- So notedB stays where the statement grows and what the kind notes of the five numbers stays. -/
theorem noted_grows {d e : St} (g : Grows d.st e.st) (hu : e.loc.oU = d.loc.oU)
    (ho : e.loc.oOmega = d.loc.oOmega) (hs : e.loc.oSp = d.loc.oSp) (h1 : e.loc.gU = d.loc.gU)
    (h2 : e.loc.gOmega = d.loc.gOmega) (h : notedB d = true) : notedB e = true := by
  unfold notedB at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  rw [hu, ho, hs, h1, h2]
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d'⟩, e'⟩, f⟩ := h
  exact ⟨⟨⟨⟨⟨notes_grows g a, notes_grows g b⟩, notes_grows g c⟩, notes_grows g d'⟩,
    there_grows g e'⟩, there_grows g f⟩

/-- All that as facts. -/
structure OmegaFacts (p : Par) (d : St) : Prop where
  msg : MsgIs d.st d.loc.oOmega p.S.omega
  alone : aloneIn d.book d.loc.oOmega = true
  psi : d.loc.psiSh.length = p.S.kCol
  mask : d.loc.firstMask ≠ some d.loc.oOmega
  noted : notedB d = true

/-- **The facts go over "SPLIT"**, where Omega's number is not o_sp's (hne), the shape splits the
row (Fold) (hS), and the step's function returns (k). -/
theorem omegaFacts_split {p : Par} {d d' : St} {r : Fmt.RoundView} (h : OmegaFacts p d)
    (hne : d.loc.oOmega ≠ d.loc.oSp) (hS : p.S.sharedSplitNeeded = true)
    (k : Desc.K14.split p d [r] = some d') : OmegaFacts p d' := by
  obtain ⟨GU, GO, x, l, n, row, mu, L⟩ := laid_split p d d' r hS k
  obtain ⟨y, hy, h1, h2, h3⟩ := h.msg
  have g := (onward_split p d d' r hS k).1.grows
  refine ⟨⟨y, ?_, h1, h2, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [L.loc, L.msgs _ hne]
    exact hy
  · rw [L.codes]
    exact h3
  · rw [L.loc, L.book]
    exact h.alone
  · rw [L.loc]
    exact h.psi
  · rw [L.loc]
    exact h.mask
  · exact noted_grows g (by rw [L.loc]) (by rw [L.loc]) (by rw [L.loc]) (by rw [L.loc])
      (by rw [L.loc]) h.noted

/-- The facts give the first test. -/
theorem omegaEnd_of_facts {p : Par} {d : St} (h : OmegaFacts p d) : omegaEndB p.S d = true := by
  obtain ⟨y, hy, h1, h2, -⟩ := h.msg
  obtain ⟨q, t, hq, ht, hp⟩ := (aloneIn_iff _ _).1 h.alone
  have hq' : (oOf d).book.place[(oOf d).omega]? = some q := hq
  have ht' : (oOf d).book.trees[q.1]? = some t := ht
  have hy' : (oOf d).st.oracles[(oOf d).omega]? = some y := hy
  unfold omegaEndB omegaEndL
  rw [hq']
  dsimp only
  rw [ht']
  dsimp only
  rw [hy']
  simp only [ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨⟨?_, decide_eq_true h1, h2, ?_⟩, ?_⟩
  · rw [hp]
    rfl
  · show (d.loc.psiSh.length == p.S.kCol) = true
    rw [h.psi]
    exact beq_self_eq_true _
  · simpa using h.mask

/-- The facts give the second. -/
theorem omegaPad_of_facts {p : Par} {d : St} (h : OmegaFacts p d) : omegaPadB p.S d = true := by
  obtain ⟨y, hy, -, -, h3⟩ := h.msg
  unfold omegaPadB
  rw [hy]
  exact decide_eq_true h3

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay} {d0 : St} {B : Eight P} {ft : Nat}
  {W : Seen8} {D : States8}

/-- **Behind a run of all eight steps the facts hold**, under the public premises Public8. -/
theorem omegaFacts_at8 (S : Public8 P sentU layO d0) (u : StepTo8 B ft d0 W D) :
    OmegaFacts P.par D.d8 := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to7 u.front
  have A := S.at6 t.front
  have A5 := S.at5 t.front.front
  have A4 := S.at4 t.front.front.front
  have A3 := S.at3 t.front.front.front.front
  have A2 := S.at2 t.front.front.front.front.front
  have e7 : D.d7 = { D.d6 with loc := { D.d6.loc with zFd := Desc.K14.drawn W.view.r7 } } :=
    t.d7_eq
  -- o_u notes its group behind "(rec_gamma)"
  obtain ⟨GU3, rows3, L3⟩ := laid_rec P.par D.d2 D.d3 _ t.front.front.front.front.k3
  obtain ⟨xu, hxu, -⟩ := A2.hasU.u
  have n3 : notesB D.d3 D.d2.loc.oU.oracle D.d2.loc.gU = true := by
    unfold notesB
    rw [L3.u xu hxu]
    show (xu.groups ++ [D.d2.loc.gU]).contains D.d2.loc.gU = true
    simp
  have eU2 : D.d2.loc.oU.oracle = d0.st.oracles.size := by rw [A2.loc]; rfl
  have eG2 : D.d2.loc.gU = d0.st.groups.size := by rw [A2.loc]; rfl
  have eU6 : D.d6.loc.oU.oracle = d0.st.oracles.size := by rw [A.loc]; rfl
  have eG6 : D.d6.loc.gU = d0.st.groups.size := by rw [A.loc]; rfl
  rw [eU2, eG2] at n3
  -- it stays over "LOC", the second sending and the joinings
  have n4 : notesB D.d4 d0.st.oracles.size d0.st.groups.size = true :=
    notes_grows (onward_loc P.par D.d3 D.d4 _ _ t.front.front.front.k4).1.grows n3
  have SL := send_laid (Desc.K14.Law.parO P) none _ _ _ _ _ t.front.front.s5.sent
  have n5 : notesB D.d5 d0.st.oracles.size d0.st.groups.size = true := by
    unfold notesB at n4 ⊢
    rw [t.front.front.s5.st]
    have ho : d0.st.oracles.size < D.d4.st.oracles.size := by rw [A4.size]; omega
    rw [SL.older _ ho]
    exact n4
  have g6 := (onward_joins P.par D.d5 D.d6 _ t.front.k6).1.grows
  have n6 : notesB D.d6 d0.st.oracles.size d0.st.groups.size = true := notes_grows g6 n5
  -- o_omega and o_sp note their groups at the joinings
  obtain ⟨GU, GO, J⟩ := joined_joins P.par D.d5 D.d6 _ S.facts.two t.front.k6
  obtain ⟨xo, hxo, -⟩ := A5.hasO.omega
  obtain ⟨xs, hxs, -⟩ := A5.hasO.sp
  have nO : notesB D.d6 D.d5.loc.oOmega D.d5.loc.gOmega = true := by
    unfold notesB
    rw [J.omega xo hxo]
    show (xo.groups ++ [D.d5.loc.gOmega]).contains D.d5.loc.gOmega = true
    simp
  have nS : notesB D.d6 D.d5.loc.oSp D.d5.loc.gOmega = true := by
    unfold notesB
    rw [J.sp xs hxs]
    show (xs.groups ++ [D.d5.loc.gOmega, D.d5.loc.gU]).contains D.d5.loc.gOmega = true
    simp
  have nS' : notesB D.d6 D.d5.loc.oSp D.d5.loc.gU = true := by
    unfold notesB
    rw [J.sp xs hxs]
    show (xs.groups ++ [D.d5.loc.gOmega, D.d5.loc.gU]).contains D.d5.loc.gU = true
    simp
  rw [← J.loc] at nO nS nS'
  obtain ⟨G1, hG1, -⟩ := A.carried.gU
  obtain ⟨G2, hG2, -⟩ := A.carried.gO
  have F7 : OmegaFacts P.par D.d7 := by
    rw [e7]
    refine ⟨A.hasO.omega, A.hasO.alone, A.carried.psi, ?_, ?_⟩
    · show D.d6.loc.firstMask ≠ some D.d6.loc.oOmega
      rw [A.loc]
      show some (d0.st.oracles.size + 1) ≠ some (d0.st.oracles.size + 2)
      intro h
      have := Option.some.inj h
      omega
    · show (notesB D.d6 D.d6.loc.oU.oracle D.d6.loc.gU &&
        notesB D.d6 D.d6.loc.oOmega D.d6.loc.gOmega && notesB D.d6 D.d6.loc.oSp D.d6.loc.gOmega &&
        notesB D.d6 D.d6.loc.oSp D.d6.loc.gU && thereB D.d6 D.d6.loc.gU &&
        thereB D.d6 D.d6.loc.gOmega) = true
      have t1 : thereB D.d6 D.d6.loc.gU = true := by unfold thereB; rw [hG1]; rfl
      have t2 : thereB D.d6 D.d6.loc.gOmega = true := by unfold thereB; rw [hG2]; rfl
      have n6' : notesB D.d6 D.d6.loc.oU.oracle D.d6.loc.gU = true := by rw [eU6, eG6]; exact n6
      rw [n6', nO, nS, nS', t1, t2]
      rfl
  have hne : D.d7.loc.oOmega ≠ D.d7.loc.oSp := by
    rw [e7]
    exact A.hasO.apart
  obtain ⟨c, n, h⟩ := u.s8
  obtain ⟨R, -, -, k⟩ := B.back8 S.facts.goes S.facts.two ft D.d7 D.d8 _ c n h
  exact omegaFacts_split F7 hne S.facts.two k

/-- So where the fold over a flat list's first nine members returns, under Public8, at a list of the
form FlatAt. -/
theorem omega_of_fold {Cl : Type} {xs : List (VerifiableInference.Desc.Block St Cl)}
    {c : OnBytes.Model.Verify.Chains} (F : FlatAt xs c B) (S : Public8 P sentU layO d0) (s : St)
    (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 9) d0 rs cl = .ok (s, rs', cl')) : OmegaFacts P.par s := by
  obtain ⟨W, D, -, -, rfl, u⟩ := F.stepTo8 S.facts.goes S.facts.two ft d0 s rs rs' cl cl' h
  exact omegaFacts_at8 S u

/-- **So at border 9 of a Thread of the shared chain, wherever Thr holds**: all three
tests. -/
theorem omega_at_nine {Bk : ProverCoinCounts} {Cl V Wt X Pb : Type} {Q : P14}
    {T : Thread Bk St Cl V Wt X Pb} {c : OnBytes.Model.Verify.Chains} {key : Wt → TableKey}
    (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key) {k : Coins Bk} {s : St} {m : Mid Wt X}
    {E : Env} (hA : Thr T 9 k s m E) :
    omegaEndB Q.S s = true ∧ omegaPadB Q.S s = true ∧ notedB s = true := by
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  have F := omega_of_fold (hT.bs B) (hQ.pub (key m.st.input)) s _ _ _ _ hfold
  exact ⟨omegaEnd_of_facts F, omegaPad_of_facts F, F.noted⟩

/-- **One plan**: the last chain's parameters (left: ToldDesc.p14At,
Johnson/ToldDescR/RcLastCode.lean) and the shared chain's (right: p14Of) have one shape and one
table of codes: by unfolding, at every list bp. -/
theorem one_plan (Z : ProofFile.Pub) (bp : List (Nat × Nat)) :
    (ToldDesc.p14At Z).S = (p14Of Z.p.chains bp).S ∧
      (ToldDesc.p14At Z).codes = (p14Of Z.p.chains bp).codes := ⟨rfl, rfl⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.notes_grows
#print axioms ProofFile.Honest.K14.there_grows
#print axioms ProofFile.Honest.K14.noted_grows
#print axioms ProofFile.Honest.K14.omegaFacts_split
#print axioms ProofFile.Honest.K14.omegaEnd_of_facts
#print axioms ProofFile.Honest.K14.omegaPad_of_facts
#print axioms ProofFile.Honest.K14.omegaFacts_at8
#print axioms ProofFile.Honest.K14.omega_of_fold
#print axioms ProofFile.Honest.K14.omega_at_nine
#print axioms ProofFile.Honest.K14.one_plan
