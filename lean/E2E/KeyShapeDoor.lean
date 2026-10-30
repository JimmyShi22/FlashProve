--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeDoor.lean: THE KEY FILE's THIRD CHAIN's START, ON SHAPES: the third chain's first shape
as a function of what is read off the two earlier chains' last states' shapes. All that the start
asks (E2E/KeyStartThird.lean, `Start₃`: nine clauses) is on the structure: NO test on values is
left. Definitions, statements and proofs. One step of the verifier's: NOTHING IS SHOWN OF ANY
PROVER.

  `LinSh`, `linSh`: of the first chain's claim: three numbers and the mark on its row weights
    (`weightsB`, E2E/KeyDotFits.lean).
  `SharedSh`, `sharedSh`: of the shared chain's last state: the mark on its statement, its
    statement's and its book's shapes, the shared point's length, Omega's number.
  `numbersS`, `numbersS_at`, `numbersS_eq`; `testedS`, `testedS_eq`: two of the start's tests as
    functions of shapes.
  **`doorS`**: the start on shapes.
  **`door_law`**: where it returns t: the nine clauses hold, and t is the shape of the state that
    the start returns.
  **`door_returns`**, **`door_carries`**: so the description's own start returns there; and whatever
    it returns has the shape t.

Limits.
- The shared chain's shape is another hand's; `SharedSh` says what this start reads of it.
- The first chain's shape is not typed: `doorS` takes the core's shape and `LinSh` of it.


-/
import E2E.KeyShapeThird
import E2E.KeyStartThird

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.Key (FirstState)
open VerifiableInference.Desc.Third (S₃ numbersOk plainArm)
open VerifiableInference.Desc.Third.Law (ok_of_bind some_of_named true_of_need)

/-- Of the first chain's claim. -/
structure LinSh where
  w : Nat
  own : Nat
  mask : Option Nat
  weights : Bool
  deriving DecidableEq, Repr

def linSh (S : LinShape) (codes : Codes) (l : LinFirst) : LinSh :=
  ⟨l.w, l.own, l.mask,
    weightsB S (linLayOmega codes S) (VerifiableInference.Desc.Key.rowOfLinClaim l.claim).g⟩

/-- Of the shared chain's last state. -/
structure SharedSh where
  tidy : Bool
  st : StSh
  book : BookSh
  psi : Nat
  omega : Nat
  deriving DecidableEq, Repr

def sharedSh (s₂ : _root_.Desc.K14.St) : SharedSh :=
  ⟨stTidyB s₂.st, stSh s₂.st, bookSh s₂.book, s₂.loc.psiSh.length, s₂.loc.oOmega⟩

/-- The test on the three numbers, on the shape. -/
def numbersS (S : LinShape) (a : StSh) (l : LinSh) : Bool :=
  match a.oracles[l.w]?, a.groups[l.own]? with
  | some x, some G =>
    decide (x.shape = S.w) && G.members.contains l.w && G.code == S.w.code &&
      G.maskCode == S.ownMaskCode && !G.inRun &&
      (match l.mask with
        | none => true
        | some m =>
          match a.oracles[m]? with
          | some y => !y.sampled && y.shape.answers == 0
          | none => false)
  | _, _ => false

theorem numbersS_at (S : LinShape) (f : VerifiableInference.Desc.Third.FirstOut) (wt : Bool) :
    numbersS S (stSh f.st) ⟨f.w, f.own, f.mask, wt⟩ = numbersOk S f := by
  obtain ⟨st, book, roots, g, w, own, mask⟩ := f
  unfold numbersS numbersOk
  dsimp only
  rw [orc_get, grp_get]
  cases st.oracles[w]? with
  | none => rfl
  | some x =>
    cases st.groups[own]? with
    | none => rfl
    | some G =>
      cases mask with
      | none =>
        show (decide (x.shape = S.w) && G.members.toList.contains w && G.code == S.w.code &&
          G.maskCode == S.ownMaskCode && !G.inRun && true) = _
        rw [Array.contains_toList]
      | some m =>
        show (decide (x.shape = S.w) && G.members.toList.contains w && G.code == S.w.code &&
          G.maskCode == S.ownMaskCode && !G.inRun &&
          (match (stSh st).oracles[m]? with
            | some y => !y.sampled && y.shape.answers == 0
            | none => false)) =
          (decide (x.shape = S.w) && G.members.contains w && G.code == S.w.code &&
          G.maskCode == S.ownMaskCode && !G.inRun &&
          (match st.oracles[m]? with
            | some y => !y.sampled && y.shape.answers == 0
            | none => false))
        rw [Array.contains_toList, orc_get]
        cases st.oracles[m]? <;> rfl

theorem numbersS_eq (S : LinShape) (codes : Codes) (s₁ : FirstState) (l : LinFirst) :
    numbersS S (stSh s₁.d.st) (linSh S codes l) = numbersOk S (firstOutOf s₁ l) :=
  numbersS_at S (firstOutOf s₁ l) _

/-- "Every group's test has begun, and every sampled message is in a group", on the shape. -/
def testedS (a : StSh) : Bool :=
  a.groups.all (·.inRun) && a.oracles.all fun x => !x.sampled || !x.groups.isEmpty

theorem testedS_eq (s₂ : _root_.Desc.K14.St) :
    testedS (stSh s₂.st) = _root_.Desc.K14.tested s₂ := by
  unfold testedS _root_.Desc.K14.tested
  congr 1
  · show (s₂.st.groups.toList.map grpSh).all (·.inRun) = _
    rw [List.all_map, ← Array.all_toList]
    rfl
  · show (s₂.st.oracles.toList.map orcSh).all _ = _
    rw [List.all_map, ← Array.all_toList]
    rfl

/-- **The start on shapes.** codes, S: the sized key's: public. tidy: the mark on the first chain's
last statement: handed on, not asked. -/
def doorS (codes : Codes) (S : LinShape) (a : CoreSh) (tidy : Bool) (lin : Option LinSh)
    (b : SharedSh) : Except String Sh₃ := do
  let l ← named "the first chain's end names no W" lin
  need "the shared chain's end: something is untested" (testedS b.st)
  need "the codes and the shape are lawful" (codes.lengthsOk && linOk codes S)
  need "the shape does not split the row (Dot)" (plainArm S)
  need "a mask's number just where masks are sent ahead" (l.mask.isSome == S.masksAhead)
  need "the three numbers" (numbersS S a.st l)
  need "the first chain's codes" (decide (a.st.codes = codes))
  need "a root for each tree" (a.roots == a.book.trees.length)
  need "the shared chain's codes" (decide (b.st.codes = codes))
  pure (⟨a.st, a.book, 0⟩,
    ⟨tidy, l.w, l.own, l.mask, some ⟨l.weights, b.tidy, b.st, b.book, b.psi, b.omega⟩, noId,
      a.roots + 1⟩)

/-- **Where it returns: the nine clauses hold, and it returns the shape of the state that the start
returns.** -/
theorem door_law (codes : Codes) (S : LinShape) (s₁ : FirstState) (s₂ : _root_.Desc.K14.St)
    (t : Sh₃)
    (h : doorS codes S (coreSh ⟨s₁.d.st, s₁.d.book, s₁.d.roots⟩) (stTidyB s₁.d.st)
      (s₁.lin.map (linSh S codes)) (sharedSh s₂) = .ok t) :
    ∃ l, Start₃ codes S s₁ s₂ l ∧ t = sh₃ S (thirdFirst s₁ s₂ l) := by
  unfold doorS at h
  obtain ⟨l', hl, h⟩ := ok_of_bind h
  obtain ⟨_, h1, h⟩ := ok_of_bind h
  obtain ⟨_, h2, h⟩ := ok_of_bind h
  obtain ⟨_, h3, h⟩ := ok_of_bind h
  obtain ⟨_, h4, h⟩ := ok_of_bind h
  obtain ⟨_, h5, h⟩ := ok_of_bind h
  obtain ⟨_, h6, h⟩ := ok_of_bind h
  obtain ⟨_, h7, h⟩ := ok_of_bind h
  obtain ⟨_, h8, h⟩ := ok_of_bind h
  obtain ⟨l, hlin, rfl⟩ := Option.map_eq_some_iff.1 (some_of_named hl)
  have hc : s₁.d.st.codes = codes := of_decide_eq_true (true_of_need h6)
  subst hc
  refine ⟨l, ⟨true_of_need h2, true_of_need h3, hlin, beq_iff_eq.1 (true_of_need h4), ?_,
    rfl, ?_, ?_, of_decide_eq_true (true_of_need h8)⟩, (Except.ok.inj h).symm⟩
  · exact (numbersS_eq S _ s₁ l).symm.trans (true_of_need h5)
  · have := beq_iff_eq.1 (true_of_need h7)
    exact this.trans (tree_size s₁.d.book)
  · exact (testedS_eq s₂).symm.trans (true_of_need h1)

section
variable (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- **The description's own start returns there.** -/
theorem door_returns (x : KeyInst) (s₁ : FirstState) (s₂ : _root_.Desc.K14.St) (t : Sh₃)
    (h : doorS X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape
      (coreSh ⟨s₁.d.st, s₁.d.book, s₁.d.roots⟩) (stTidyB s₁.d.st)
      (s₁.lin.map (linSh X.chains.made.sized.key.once.shape X.chains.made.sized.key.codes))
      (sharedSh s₂) =
        .ok t) :
    ∃ s₃, (keyFileDescription X N P).start₃ x s₁ s₂ = .ok s₃ ∧
      t = sh₃ X.chains.made.sized.key.once.shape s₃ := by
  obtain ⟨l, hs, e⟩ := door_law _ _ s₁ s₂ t h
  exact ⟨_, start₃_passes X N P x s₁ s₂ l hs, e⟩

/-- **Whatever it returns has that shape.** -/
theorem door_carries (x : KeyInst) (s₁ : FirstState) (s₂ : _root_.Desc.K14.St) (t : Sh₃)
    (s₃ : S₃) (hs : (keyFileDescription X N P).start₃ x s₁ s₂ = .ok s₃)
    (h : doorS X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape
      (coreSh ⟨s₁.d.st, s₁.d.book, s₁.d.roots⟩) (stTidyB s₁.d.st)
      (s₁.lin.map (linSh X.chains.made.sized.key.once.shape X.chains.made.sized.key.codes))
      (sharedSh s₂) =
        .ok t) : t = sh₃ X.chains.made.sized.key.once.shape s₃ := by
  obtain ⟨s', h1, e⟩ := door_returns X N P x s₁ s₂ t h
  obtain rfl : s' = s₃ := Except.ok.inj (h1.symm.trans hs)
  exact e

end

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.numbersS_at
#print axioms AtPublicFiles.AtFiles.numbersS_eq
#print axioms AtPublicFiles.AtFiles.testedS_eq
#print axioms AtPublicFiles.AtFiles.door_law
#print axioms AtPublicFiles.AtFiles.door_returns
#print axioms AtPublicFiles.AtFiles.door_carries
