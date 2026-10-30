-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OmegaJoin.lean: kind K14: THE PIECES OF Honest/K14/OmegaEnd.lean,
OmegaDoor.lean, OmegaTwelve.lean, DotPads.lean AND SecondDoor.lean JOINED: the eleven tests that
"K14, second part" leaves (secondDoor, Honest/K14/SecondDoor.lean: a list of this kind's own; that
it is all true is by itself no accept of the sub-protocol: door_owed there) are all true, from: Thr
(Honest/Thread/Thr.lean) at the shared chain's last border, at a state s₂; the return of the start
of the last chain of the IOP as written in Lean (FileDescription.start₃ of P5J.F0T; the library's start₃E
beneath) at that same s₂; the premises at the shared chain (below); AND, AS A PREMISE, WHAT IS LEFT
OF THE ELEVEN (secondRest; or secondRest5, hW and sW). s₂ IS A VARIABLE: that the state which the
start is handed is the shared chain's last is a premise in the statements' form: the one variable s₂
stands in both premises. Statements with their proofs; one definition with code.

  pad_of_test     what omegaPadB says of Omega's entry, as facts on the library's oOf of the state
  weights_of_form **the book-keeping at the last chain's border 0 (the library's shapeAt) gives
                  WeightsFit of the border's weights**: the library's atDot_of_shape
                  (Johnson/Desc/Last/ShapeGives.lean) has that they are well formed
  start_has_w     a state that the start returns has W's entry in its statement. (A later file has
                  more of the start of the last chain of the IOP as written in Lean: W's entry has
                  the plan's shape and W is among the own group's members: start_w_member,
                  Honest/K14/SecondTerms.lean)
  padsW_behind    PadsBehind at W in the state s gives PadsBehind at W in the state that takeOver
                  returns of s: takeOver leaves the codes and every entry below the old size (the
                  library's carries_takeOver, takeOver_says)
  secondRest5 p s secondRest without its last test: five tests where the taking-over and linDotRow
                  return; four where one of the two does not; none where the state holds no border
  joined_facts    what Thr at border 12 at s₂ and the start's return at s₂ give together, six parts:
                  the border of s holds oOf s₂; omegaEndL and omegaPadB there; linOk at the codes of
                  s; one table of codes; W's entry is in the statement of s
  padsW_at_start  sW from the like fact on the first chain's last statement, at W's number there
  second_door_joined **THE JOIN**: Thr T 12 k s₂ m E; the start returns s of s₁ and s₂; secondRest
                  is all true at s: all eleven of secondDoor are true at s
  rest_of_five    **THE LAST TEST OF secondRest FOLLOWS FROM hW AND sW**: hW: WeightsFit of the
                  border's weights; sW: PadsBehind at W, AT THE STATE s THAT THE START RETURNS (its
                  statement and W's number are the first chain's last: start_gives' fifth and
                  seventh part). Omega's half of the test's premise is had by calls:
                  omega_padsBehind (DotPads.lean) from omegaPadB at s₂; rest24 is called
  second_door_five **so secondDoor from secondRest5, hW and sW**: of the eleven tests six come off
                  the run (that is: are read off the fold's return that Thr holds), the last follows
                  from hW, sW and the run, and the rest are premises: three of secondRest5's five
                  are entries of secondDoor to the letter

PREMISES AT THE SHARED CHAIN, in joined_facts, second_door_joined, rest_of_five and
second_door_five: Plan2 at Q := p14Of Zp.p.chains bp, at any bp (so: the row (Fold) is split over
two codes, and the masks are sent ahead; the start's return gives in the same theorems that the row
(Dot) is NOT split: two fields of the shape, which hold together at the small shape of
Johnson/Desc/K14/Honest/Toy.lean, by that shape's numbers (u's code is 0, omega's and w's 1): no
statement there says so), ChainAt and TailAt.

What is not claimed. That the state which is handed to the start is one at which Thr holds at border
12. ChainAt and TailAt at a Thread that is laid for the shared chain
(Honest/K14/OmegaAtShared.lean). That Thr holds at any run. hW where no book-keeping at border 0 is
at hand. sW: BY READING, no clause of the library's start (Johnson/Desc/Third/State.lean: numbersOk)
or of its book-keeping at border 0 (Johnson/Desc/Last/ShapeAt.lean: handedClauses, memberClauses,
clausesAt) asks where W's pad lies. The five tests of secondRest5 at any run (a later file has the
whole list true, under the library's head, Thr at the shared chain's last border, the start's
return, and where the first chain's fold returns the state that the start is handed: rest5_at_fold,
Honest/K14/SecondAtRun.lean; that the taking-over and linDotRow return, so that the fifth test is
listed, is not shown there). Nothing on any property of the protocol: nothing on completeness, on
soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaTwelve
import Johnson.Desc.ProofFile.Honest.K14.DotPads
import Johnson.Desc.Last.ShapeGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (OracleNotice TreeLay TableKey linDotRow linLayOmega linLayW tensorBelow)
open VerifiableInference.Desc (Block Own.tensorInOrder Own.placeFits)
open VerifiableInference.Desc.Ground (Clauses ok has)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut FirstEnd₃ takeOver start₃E)
open VerifiableInference.Desc.Third.Law (oOf sharedOfEnd_ended takeOver_says carries_takeOver
  numbersOk_inv start₃E_inv firstOutFrom_inv start₃_inv)
open VerifiableInference.Desc.Last (shapeAt atDot_of_shape)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St p14Of)

/-! ## Omega's pad, the weights, W's pad -/

/-- What omegaPadB says, as facts on oOf of the state. -/
theorem pad_of_test {S : OnBytes.Params.LinShape} {d : St} (h : omegaPadB S d = true) :
    ∃ y, (oOf d).st.oracles[(oOf d).omega]? = some y ∧
      y.pad = ((OnBytes.Send.pad (oOf d).st.codes S.omega).getD []).map fun q =>
        (q.part, q.index) := by
  unfold omegaPadB at h
  cases hy : d.st.oracles[d.loc.oOmega]? with
  | none => rw [hy] at h; cases h
  | some y =>
    rw [hy] at h
    exact ⟨y, hy, of_decide_eq_true h⟩

/-- **The book-keeping at the last chain's border 0 gives WeightsFit of the border's weights.** -/
theorem weights_of_form {p : P₁₄} {R : List Fmt.DeclaredRound} {h : FirstEnd₃} {o : SharedOut}
    {s : S₃} (hs : shapeAt p R 0 h o s = true) (x : VerifiableInference.Desc.Third.Border)
    (hx : s.loc.border = some x) : WeightsFit x.g :=
  weightsFit_of_ok ((atDot_of_shape hs).weights x hx)

/-- A state that the start returns has W's entry in its statement. -/
theorem start_has_w (p : P₁₄) (h : FirstEnd₃) (o : SharedOut) (s : S₃)
    (hs : start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o = .ok s) :
    ∃ x, s.st.oracles[s.loc.w]? = some x := by
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hs
  obtain ⟨hn, -⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  obtain ⟨-, -, rfl⟩ := start₃_inv _ _ _ _ hst
  obtain ⟨x, _, hx, -⟩ := numbersOk_inv _ _ hn
  exact ⟨x, hx⟩

/-- PadsBehind at W in the state s gives PadsBehind at W in the state that takeOver returns of s. -/
theorem padsW_behind (p : P₁₄) (s : S₃) (o : SharedOut)
    (a : Nat × Desc.Plain.DState VerifiableInference.Desc.Third.Loc₃)
    (ha : takeOver p.S s.loc.own o (s.withCols []) = .ok a) (n : Nat)
    (hw : ∃ x, s.st.oracles[s.loc.w]? = some x)
    (h : PadsBehind s.st s.loc.w (linLayW s.st.codes p.S) n) :
    PadsBehind a.2.st s.loc.w (linLayW a.2.st.codes p.S) n := by
  have hc : a.2.st.codes = s.st.codes := (carries_takeOver _ _ _ _ a ha).1.1.codes
  obtain ⟨_, _, -, -, -, -, -, -, -, -, hold, -⟩ := takeOver_says _ _ _ _ a ha
  obtain ⟨x, hx⟩ := hw
  have hlt : s.loc.w < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  rw [hc]
  intro y hy
  rw [hold _ hlt] at hy
  exact h y hy

/-! ## The join -/

/-- secondRest (Honest/K14/OmegaDoor.lean) without its last test: at most five tests. THREE ARMS
LIST LESS. Where the state holds no border the list is empty, so all of it is true. Where takeOver
returns an error, and where linDotRow returns nothing, it has four tests: the fifth, "the terms fit
their places", is not listed. So that the list is all true asks less than five tests there. By
itself it is no test of the member. -/
def secondRest5 (p : P₁₄) (s : S₃) : Clauses :=
  match s.loc.border with
  | none => []
  | some x =>
    ("adopt: statement and book are in step", s.st.oracles.size == s.book.place.size) ::
    ("join: no member twice",
      has s.st.groups[s.loc.own]? (!·.members.contains s.st.oracles.size)) ::
    ("the weights have as many variables as a row's number has bits",
      x.g.all (·.vars == p.S.kRow)) ::
    ("each of the weights can be cut below the matrix's rows",
      x.g.all fun g => (tensorBelow g 0 p.S.kRow p.S.matrixRows).isSome) ::
    match takeOver p.S s.loc.own x.shared (s.withCols []) with
    | .error _ => []
    | .ok a =>
      match linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
          (linLayW a.2.st.codes p.S) with
      | none => []
      | some dot =>
        [("addRow: the terms fit their places", has a.2.st.groups[s.loc.own]? fun G =>
            dot.terms.all fun t =>
              Own.tensorInOrder t.v && Own.placeFits a.2.st G t.oracle t.part t.v.vars 0)]

section join
variable {Bk : ProverCoinCounts} {Cl V Wt X Pb : Type} {sentU : Array OracleNotice} {layO : TreeLay}
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl)
  (bp : List (Nat × Nat)) {T : Thread Bk St Cl V Wt X Pb} {c : OnBytes.Model.Verify.Chains}
  {key : Wt → TableKey} {p₉ p₁₀ : P12} {front : List (Block St Unit)}

/-- What Thr at the shared chain's last border, at s₂, and the start's return at s₂ give
together. -/
theorem joined_facts (hQ : Plan2 (p14Of Zp.p.chains bp) sentU layO)
    (hT : ChainAt T (p14Of Zp.p.chains bp) c key) (hL : TailAt T.bs p₉ p₁₀ front) {k : Coins Bk}
    {s₂ : St} {m : Mid Wt X} {E : Env} (hA : Thr T 12 k s₂ m E) (x : ProofFile.InstPub) (s₁ : P5J.TS)
    (s : S₃) (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s) :
    ∃ g, s.loc.border = some { g := g, shared := oOf s₂ } ∧
      ok (omegaEndL (ToldDesc.p14At Zp).S (oOf s₂)) = true ∧
      omegaPadB (ToldDesc.p14At Zp).S s₂ = true ∧
      OnBytes.linOk s.st.codes (ToldDesc.p14At Zp).S = true ∧ (oOf s₂).st.codes = s.st.codes ∧
      ∃ y, s.st.oracles[s.loc.w]? = some y := by
  obtain ⟨a, b, -⟩ := omega_at_twelve hQ hT hL hA
  obtain ⟨f, e, -, -, he, hst⟩ := start_at_last Zp Np cF x s₁ s₂ s hs
  rw [sharedOfEnd_ended s₂ e he] at hst
  obtain ⟨⟨g, hb⟩, hlin, -, -, -, -, -, -, hc1, hc2, -⟩ := start_gives _ f _ s hst
  rw [← (one_plan Zp bp).1] at a b
  unfold omegaEndB at a
  rw [Bool.and_eq_true] at a
  exact ⟨g, hb, a.1, b, by rw [hc1]; exact hlin, hc2.trans hc1.symm, start_has_w _ f _ s hst⟩

/-- PadsBehind at W in the first chain's last statement, at W's number there (f: what the library's
firstOfS takes of the first chain's last state), gives sW: PadsBehind at W in the state that the
start returns. -/
theorem padsW_at_start (x : ProofFile.InstPub) (s₁ : P5J.TS) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s) (f : FirstEnd₃)
    (hf : VerifiableInference.Desc.Third.firstOfS s₁ = some f) (n : Nat)
    (h : PadsBehind f.st f.w (linLayW f.st.codes (ToldDesc.p14At Zp).S) n) :
    PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S) n := by
  obtain ⟨f', e, -, hf', -, hst⟩ := start_at_last Zp Np cF x s₁ s₂ s hs
  obtain rfl : f = f' := Option.some.inj (hf.symm.trans hf')
  obtain ⟨-, -, -, -, e5, -, e7, -⟩ := start_gives _ f _ s hst
  rw [e5, e7]
  exact h

/-- **THE JOIN**: from Thr at the shared chain's last border at s₂, the start's return s at that
same s₂, and secondRest at s: all eleven tests of secondDoor at s. -/
theorem second_door_joined (hQ : Plan2 (p14Of Zp.p.chains bp) sentU layO)
    (hT : ChainAt T (p14Of Zp.p.chains bp) c key) (hL : TailAt T.bs p₉ p₁₀ front) {k : Coins Bk}
    {s₂ : St} {m : Mid Wt X} {E : Env} (hA : Thr T 12 k s₂ m E) (x : ProofFile.InstPub) (s₁ : P5J.TS)
    (s : S₃) (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (hR : ok (secondRest (ToldDesc.p14At Zp) s) = true) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true := by
  obtain ⟨g, hb, hO, -⟩ := joined_facts Zp Np cF bp hQ hT hL hA x s₁ s hs
  exact door_of_omega _ s _ hb hO hR

/-- **The last test of secondRest follows from hW and sW**, under Plan2, ChainAt and TailAt, Thr at
the shared chain's last border at s₂ and the start's return s at that s₂. hW: the facts on the
border's weights. sW: where W's pad lies, at the state that the start returns. h5: secondRest5 is
all true at s: where the taking-over or linDotRow does not return, neither list has a test behind
the fourth. -/
theorem rest_of_five (hQ : Plan2 (p14Of Zp.p.chains bp) sentU layO)
    (hT : ChainAt T (p14Of Zp.p.chains bp) c key) (hL : TailAt T.bs p₉ p₁₀ front) {k : Coins Bk}
    {s₂ : St} {m : Mid Wt X} {E : Env} (hA : Thr T 12 k s₂ m E) (x : ProofFile.InstPub) (s₁ : P5J.TS)
    (s : S₃) (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (hW : ∀ b, s.loc.border = some b → WeightsFit b.g)
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol))
    (h5 : ok (secondRest5 (ToldDesc.p14At Zp) s) = true) :
    ok (secondRest (ToldDesc.p14At Zp) s) = true := by
  obtain ⟨g, hb, -, hP, hlin, hcs, hw⟩ := joined_facts Zp Np cF bp hQ hT hL hA x s₁ s hs
  obtain ⟨y, hy, hpad⟩ := pad_of_test hP
  unfold secondRest5 at h5
  unfold secondRest
  rw [hb] at h5 ⊢
  dsimp only at h5 ⊢
  rw [ok_cons, ok_cons, ok_cons, ok_cons] at h5 ⊢
  simp only [Bool.and_eq_true] at h5 ⊢
  obtain ⟨r1, r2, r3, r4, h5⟩ := h5
  refine ⟨r1, r2, r3, r4, ?_⟩
  cases ha : takeOver (ToldDesc.p14At Zp).S s.loc.own (oOf s₂) (s.withCols []) with
  | error e => rfl
  | ok a =>
    rw [ha] at h5
    dsimp only at h5 ⊢
    cases hd : linDotRow (ToldDesc.p14At Zp).S g (oOf s₂).psi a.1
        (linLayOmega a.2.st.codes (ToldDesc.p14At Zp).S) s.loc.w
        (linLayW a.2.st.codes (ToldDesc.p14At Zp).S) with
    | none => rfl
    | some dot =>
      rw [hd] at h5
      dsimp only at h5 ⊢
      rw [ok_cons] at h5 ⊢
      rw [ok_cons]
      simp only [Bool.and_eq_true] at h5 ⊢
      refine ⟨h5.1, ?_, rfl⟩
      exact rest24 _ s { g := g, shared := oOf s₂ } a dot ha hd (hW _ hb) hlin
        (omega_padsBehind _ s { g := g, shared := oOf s₂ } a ha y hy hpad hcs hlin)
        (padsW_behind _ s (oOf s₂) a ha _ hw sW)

/-- **So secondDoor from secondRest5, hW and sW**, under rest_of_five's other premises: Plan2,
ChainAt and TailAt, Thr at the shared chain's last border at s₂, the start's return s at that s₂. -/
theorem second_door_five (hQ : Plan2 (p14Of Zp.p.chains bp) sentU layO)
    (hT : ChainAt T (p14Of Zp.p.chains bp) c key) (hL : TailAt T.bs p₉ p₁₀ front) {k : Coins Bk}
    {s₂ : St} {m : Mid Wt X} {E : Env} (hA : Thr T 12 k s₂ m E) (x : ProofFile.InstPub) (s₁ : P5J.TS)
    (s : S₃) (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (hW : ∀ b, s.loc.border = some b → WeightsFit b.g)
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol))
    (h5 : ok (secondRest5 (ToldDesc.p14At Zp) s) = true) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true :=
  second_door_joined Zp Np cF bp hQ hT hL hA x s₁ s hs
    (rest_of_five Zp Np cF bp hQ hT hL hA x s₁ s hs hW sW h5)

end join

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.pad_of_test
#print axioms ProofFile.Honest.K14.weights_of_form
#print axioms ProofFile.Honest.K14.start_has_w
#print axioms ProofFile.Honest.K14.padsW_behind
#print axioms ProofFile.Honest.K14.joined_facts
#print axioms ProofFile.Honest.K14.padsW_at_start
#print axioms ProofFile.Honest.K14.second_door_joined
#print axioms ProofFile.Honest.K14.rest_of_five
#print axioms ProofFile.Honest.K14.second_door_five
