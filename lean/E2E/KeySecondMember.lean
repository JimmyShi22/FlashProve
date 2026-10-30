--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySecondMember.lean: A MEMBER: THE PREMISES UNDER WHICH "K14, SECOND PART" IS SHOWN TO ACCEPT
(E2E/KeyDotRow.lean, `k14Second_passes'`) CAN BE MET TOGETHER, AT THE FULL SIZE's OWN SHAPES AND
CODES. One synthetic state of the key file's third chain, written out; each premise is shown of it,
the closed ones by the kernel. So that theorem is not idle. Statements and proofs. NOTHING IS SHOWN
OF ANY PROVER AND NOTHING OF ANY RUN: the state is made by hand, not reached.

THE STATE `sF`. The shape of the test on the table and the codes are the library's written values of
the full size's sized key (`Lk6.AtPlan.keyFull`). The statement is smaller than a run's: three
messages (the index masks, W, the mask of the own test's first fold) with the written shapes and the
pads that the library's `padMade` makes of them; one group, the own one, with one open row. The copy
of the shared chain's end holds Omega alone, with its written shape and pad, in one group whose test
has begun. The row weights are one
tensor and the shared point one list, each at a point all of whose coordinates are (5, 7, 11): no
coordinate is 0 or 1, so the cut at the matrix's rows is not trivial: `dot_terms`: the row (Dot) has
nine terms: eight on Omega's copy, one on W.

What is shown.
  `listedB`, `listed_of_B`: `Listed` (E2E/KeyListed.lean) as a test with code.
  `allZero_eq`, `padsClear_of_list`, `termsFit_of_list`: the two premises on the row from their
    forms over lists, which the kernel can evaluate.
  **`taken_member`**: `Taken` at `sF`: all seventeen clauses.
  **`pads_member`**: `PadsClear` at `sF` and its row (Dot): BY THE KERNEL: AT OMEGA's COPY, WHOSE
    PAD LIES IN ITS MAIN TABLE, THE ROW's COEFFICIENT ON THE PAD IS 0 AS WORDS. `omega_pad_main`:
    that pad does lie there. `pads_teeth`: a negative test: the same row weights laid WITHOUT the
    cut at the matrix's rows have a coefficient there that is not 0.
  **`terms_member`**: `TermsFit` there: by the kernel.
  **`second_member_at`**, `second_member`: so the sub-protocol accepts `sF`, at any public
    parameters with the written shape: by `k14Second_passes'`, every premise met.

Limits.
- ONE state, ONE point. That the coefficient on Omega's pad is 0 at all row weights without a
  written-out factor and all points: E2E/KeyPadClear.lean.
- The state is synthetic: three messages in place of a run's eleven; no sample row; the trees'
  shapes in the two books are empty.


-/
import E2E.KeyDotRow
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params OnBytes.Slice
open Lk6.AtPlan (keyFull)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Third (S₃ SharedOut P₁₄ batchLinearConstraintsSecondPart plainArm firstStepB)

/-! ## Tests with code -/

/-- `Listed` as a test with code. -/
def listedB (T : Statement) : Bool :=
  (List.range T.groups.size).all fun g =>
    match T.groups[g]? with
    | some G => G.members.toList.all fun o =>
        match T.oracles[o]? with
        | some x => x.groups.contains g
        | none => false
    | none => true

theorem listed_of_B (T : Statement) (h : listedB T = true) : Listed T := by
  intro g G o hG hm
  have t := List.all_eq_true.1 h g (List.mem_range.2 (Array.getElem?_eq_some_iff.1 hG).1)
  rw [hG] at t
  have u := List.all_eq_true.1 t o (Array.mem_toList_iff.2 hm)
  cases hx : T.oracles[o]? with
  | none =>
    rw [hx] at u
    cases u
  | some x =>
    rw [hx] at u
    exact ⟨x, rfl, List.contains_iff_mem.1 u⟩

/-- An element all of whose words are 0 is the element 0. -/
theorem allZero_eq (a : E) (h : VerifiableInference.Desc.Own.allZero a = true) : a = zeroE := by
  obtain ⟨x, y, z⟩ := a
  simp only [VerifiableInference.Desc.Own.allZero, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rfl

theorem padsClear_of_list {st : Statement} {G : OnBytes.Group} {row : OnBytes.Row}
    (h : ∀ o ∈ G.members.toList, ∀ q ∈ ((st.oracles[o]?).map (·.pad)).getD [],
      (q.1 == Part.mask || VerifiableInference.Desc.Own.allZero (row.coefficient o q.1 q.2)) =
        true) : PadsClear st G row := by
  intro o ho x hx q hq
  have t := h o ho q (by rw [hx]; exact hq)
  rcases Bool.or_eq_true_iff.1 t with c | c
  · exact Or.inl (beq_iff_eq.1 c)
  · exact Or.inr (allZero_eq _ c)

theorem termsFit_of_list {st : Statement} {G : OnBytes.Group} {row : OnBytes.Row}
    (h : ∀ t ∈ row.terms.toList, (VerifiableInference.Desc.Own.tensorInOrder t.v &&
      VerifiableInference.Desc.Own.placeFits st G t.oracle t.part t.v.vars 0) = true) :
    TermsFit st G row :=
  Array.all_eq_true_iff_forall_mem.2 fun t ht => h t (Array.mem_toList_iff.2 ht)

/-! ## The state -/

/-- The written shape of the test on the table, and the written codes. -/
abbrev SF : LinShape := keyFull.once.shape
abbrev CF : Codes := keyFull.codes

/-- The pad that the library makes of a shape at these codes. -/
def padF (s : OracleShape) : List (Part × Nat) :=
  ((VerifiableInference.Desc.Own.padMade CF s).getD []).map fun p => (p.part, p.index)

/-- A sampled message of a shape, with its pad, in the groups gs. -/
def msgF (s : OracleShape) (gs : List Nat) : OnBytes.Oracle :=
  { shape := s, sampled := true, pad := padF s, groups := gs }

/-- The own group in front. -/
def groupF : OnBytes.Group :=
  { code := SF.w.code, maskCode := SF.ownMaskCode, members := #[0, 1], kept := #[false, false]
    rows := #[{}] }

def stF : Statement :=
  { codes := CF
    oracles := #[msgF keyFull.once.input.shape [0], msgF SF.w [0],
      { shape := { code := noId, mainRows := 0, maskRows := 1, maskCode := SF.ownMaskCode
                   answers := 0 } }]
    groups := #[groupF] }

def bookF : TreeBook :=
  { trees := #[{ shape := {}, number := 0, parts := #[0] },
      { shape := {}, number := 5, parts := #[1, 2] }]
    place := #[(0, 0), (1, 0), (1, 1)] }

/-- A coordinate that is neither 0 nor 1. -/
def ptF : E := ⟨5, 7, 11⟩

def treeF : Tree := { shape := {}, number := 1, parts := #[0] }

/-- Omega in the shared chain's last statement: sampled, in a group whose test has begun. -/
def omegaF : OnBytes.Oracle := msgF SF.omega [0]

def sharedF : SharedOut :=
  { st := { codes := CF, oracles := #[omegaF]
            groups := #[{ code := SF.omega.code, members := #[0], kept := #[false]
                          inRun := true }] }
    book := { trees := #[treeF], place := #[(0, 0)] }
    psi := List.replicate SF.kCol ptF, omega := 0 }

def gF : List Tensor := [Tensor.eq (List.replicate SF.kRow ptF)]

/-- **The state.** -/
def sF : S₃ :=
  { st := stF, book := bookF, roots := 0
    loc := { w := 1, own := 0, mask := some 2, border := some ⟨gF, sharedF⟩, omega := noId
             firstTree := 3 } }

def pF : P₁₄ := ⟨CF, SF, 1⟩

/-- What the layout of Omega alone is, at these codes. -/
def layF : TreeLay :=
  (VerifiableInference.Desc.Own.treesMade CF
    #[{ shape := SF.omega, leafClass := SF.omegaLeafClass }]).getD default

/-- The row (Dot) at the state. -/
def dotF : OnBytes.Row :=
  (linDotRow SF gF sharedF.psi 3 (linLayOmega CF SF) 1 (linLayW CF SF)).getD {}

/-! ## The premises -/

theorem getD_of_isSome {α : Type} (x : Option α) (d : α) (h : x.isSome = true) :
    x = some (x.getD d) := by
  cases x with
  | none => cases h
  | some a => rfl

theorem lay_made : VerifiableInference.Desc.Own.treesMade CF
    #[{ shape := SF.omega, leafClass := SF.omegaLeafClass }] = some layF :=
  getD_of_isSome _ _ (by decide +kernel)

theorem dot_made : linDotRow SF gF sharedF.psi 3 (linLayOmega CF SF) 1 (linLayW CF SF) =
    some dotF := getD_of_isSome _ _ (by decide +kernel)

/-- The row is not degenerate: eight terms on Omega's copy, one on W. -/
theorem dot_terms : dotF.terms.toList.map (·.oracle) = [3, 3, 3, 3, 3, 3, 3, 3, 1] := by
  decide +kernel

/-- **`Taken` at the state.** -/
theorem taken_member : Taken SF sF sharedF (0, 0) treeF omegaF groupF layF where
  place := rfl
  tree := rfl
  alone := rfl
  omega := rfl
  shape := rfl
  sampled := rfl
  fits := by decide +kernel
  answers := by decide +kernel
  step := rfl
  made := lay_made
  one := by decide +kernel
  mainSame := by
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1
      (show (CF.base[SF.omega.code]?).isSome = true by decide +kernel)
    exact Or.inr ⟨c, hc, hc⟩
  maskSame := Or.inl (by decide +kernel)
  group := rfl
  fresh := rfl
  mainCode := Or.inr (by decide +kernel)
  maskCode := Or.inl (by decide +kernel)

theorem listed_member : Listed sF.st := listed_of_B _ (by decide +kernel)

/-- Omega's pad lies in its main table. -/
theorem omega_pad_main : (padF SF.omega).map (·.1) = [Part.main] := by decide +kernel

/-- **`PadsClear` at the state and its row (Dot)**: by the kernel. -/
theorem pads_member : PadsClear (stTaken SF sF omegaF groupF) (groupTaken sF groupF)
    dotF := padsClear_of_list (by decide +kernel)

/-- **A negative test**: the same row weights laid on Omega's copy WITHOUT the cut at the matrix's
rows have a coefficient on Omega's pad that is not 0: so the clause can fail, and the cut is what
meets it. -/
theorem pads_teeth : (padF SF.omega).all (fun q => VerifiableInference.Desc.Own.allZero
    ((addLaid {} 3 (linLayOmega CF SF) gF).coefficient 3 q.1 q.2)) = false := by decide +kernel

/-- **`TermsFit` there**: by the kernel. -/
theorem terms_member : TermsFit (stTaken SF sF omegaF groupF) (groupTaken sF groupF)
    dotF := termsFit_of_list (by decide +kernel)

/-- **So the sub-protocol accepts the state**, at any public parameters with the written shape:
every premise of `k14Second_passes'` is met. -/
theorem second_member_at (p : P₁₄) (hp : p.S = SF) :
    ∃ s', (batchLinearConstraintsSecondPart (Cl := Unit) p).decide sF [] [] = .ok s' ∧ s'.loc.omega = 3 := by
  obtain ⟨c, S, n⟩ := p
  obtain rfl : S = SF := hp
  obtain ⟨s', h1, -, -, h4⟩ := k14Second_passes' (Cl := Unit) ⟨c, SF, n⟩ sF ⟨gF, sharedF⟩ (0, 0)
    treeF omegaF groupF layF dotF rfl (show plainArm SF = true by decide +kernel)
    (by decide +kernel) taken_member listed_member dot_made pads_member terms_member [] []
  exact ⟨s', h1, by rw [h4]; rfl⟩

theorem second_member : ∃ s', (batchLinearConstraintsSecondPart (Cl := Unit) pF).decide sF [] [] = .ok s' ∧
    s'.loc.omega = 3 := second_member_at pF rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.listed_of_B
#print axioms AtPublicFiles.AtFiles.allZero_eq
#print axioms AtPublicFiles.AtFiles.padsClear_of_list
#print axioms AtPublicFiles.AtFiles.termsFit_of_list
#print axioms AtPublicFiles.AtFiles.getD_of_isSome
#print axioms AtPublicFiles.AtFiles.lay_made
#print axioms AtPublicFiles.AtFiles.dot_made
#print axioms AtPublicFiles.AtFiles.dot_terms
#print axioms AtPublicFiles.AtFiles.taken_member
#print axioms AtPublicFiles.AtFiles.listed_member
#print axioms AtPublicFiles.AtFiles.omega_pad_main
#print axioms AtPublicFiles.AtFiles.pads_member
#print axioms AtPublicFiles.AtFiles.pads_teeth
#print axioms AtPublicFiles.AtFiles.terms_member
#print axioms AtPublicFiles.AtFiles.second_member_at
#print axioms AtPublicFiles.AtFiles.second_member
