-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FiveNumbers.lean (kind K10): FIVE COMPARISONS OF PUBLIC NUMBERS AT A STATE IN FRONT OF THE CLOSING: AS TESTS WITH CODE, AND
FROM WHAT EACH FOLLOWS. Definitions and theorems.

Why. K10's condition in front (`K10OnS`, Close/Law/AtBlockSelf.lean), `CubeFits`' el and ez (Close/Law/CubeAt.lean) and `K10On`'s clause code ask
five equations between numbers that the STATE holds and the typed stage's. They stand as premises everywhere; nobody paid them.
  (N1) (planOf es (rdK a)).k = s.h + s.g      (N2) (planOf es (rdK a)).h = s.h
  (N3) 2 ^ lay.logEll = s.C.l                 (N4) 2 ^ lay.logEllZk = s.Z.l     (lay: the begun statement's layout of the frame's group)
  (N5) ((rdK a).2.2.codes.mask.getD (planOf es (rdK a)).maskCode default).ell = s.Z.l

What is said.
  `n1B` .. `n5B`: the five as Bools at a state, for a walk to evaluate. `n1B_iff` .. : each is its equation (N3 | N4: at the layout that is there).
  `plan_of_frame`: the frame's groups are `reqGroups` of its shape, its shape is sh, its link is l ⊢ the plan's k, h and maskCode are
    ((reqGroups sh)[l]?.getD default).k, .h and sh.maskCode. (The three premises are fields of `FoldFacts`: liveGroups, liveShape, frameIs.)
  `logEll_of_shapes`: **`LayFacts T G L`, `ShapesAre T G lo kb no`, T.codes = cs, a member a, its main code's length a power of two ⊢
    2 ^ L.logEll = s.C.l.** `logEllZk_of_shapes`: the like at a member that has a mask row.
  `code_of_member`: T.codes = cs, the plan's maskCode is that of a member with a mask row ⊢ (N5).
How (N3). The layout's exponent is every member's own number of place bits (`LayFacts.main_places`); that is its written shape's code's logEll at the
statement's codes (`placeBits`' text; `ShapesAre.shape`); the stage's code is that code (hM).

Limits. `ShapesAre`, `LayFacts`, T.codes = cs and the frame's three facts are shown of no state here. (N4) and (N5) want a member WITH A MASK ROW: a group
without one is not treated. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.BlockOfShapes
import Johnson.Desc.First.Close.Law.AtBlockSelf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Means Johnson.Pack Johnson.Top.H Johnson.G
open Cb
open VerifiableInference.Desc.First.Close

/-! ## The five as tests with code -/

def n1B (s : Sg) (a : VerifiableInference.Desc.First.S) : Bool :=
  (planOf [] (rdK a)).k == s.h + s.g
def n2B (s : Sg) (a : VerifiableInference.Desc.First.S) : Bool := (planOf [] (rdK a)).h == s.h

/-- A test on the begun statement's layout of the frame's group; no where there is none. -/
def atLayB (a : VerifiableInference.Desc.First.S) (f : GroupLayout → Bool) : Bool :=
  match (rdK a).2.2.groups[(rdK a).2.1.group]? with
  | some G =>
    match (begun (rdK a).2.2 (rdK a).2.1.group G).layout (rdK a).2.1.group with
    | some lay => f lay
    | none => false
  | none => false

def n3B (s : Sg) (a : VerifiableInference.Desc.First.S) : Bool :=
  atLayB a fun lay => 2 ^ lay.logEll == s.C.l
def n4B (s : Sg) (a : VerifiableInference.Desc.First.S) : Bool :=
  atLayB a fun lay => 2 ^ lay.logEllZk == s.Z.l
def n5B (s : Sg) (a : VerifiableInference.Desc.First.S) : Bool :=
  ((rdK a).2.2.codes.mask.getD (planOf [] (rdK a)).maskCode default).ell == s.Z.l

theorem n1B_iff (s : Sg) (a : VerifiableInference.Desc.First.S) (es : List Fmt.Entry) :
    n1B s a = true ↔ (planOf es (rdK a)).k = s.h + s.g := by
  unfold n1B
  exact beq_iff_eq

theorem n2B_iff (s : Sg) (a : VerifiableInference.Desc.First.S) (es : List Fmt.Entry) :
    n2B s a = true ↔ (planOf es (rdK a)).h = s.h := by
  unfold n2B
  exact beq_iff_eq

theorem n5B_iff (s : Sg) (a : VerifiableInference.Desc.First.S) (es : List Fmt.Entry) :
    n5B s a = true ↔
      ((rdK a).2.2.codes.mask.getD (planOf es (rdK a)).maskCode default).ell = s.Z.l := by
  unfold n5B
  exact beq_iff_eq

/-- A yes of a test on the layout holds at every group and layout that are there. -/
theorem atLayB_says {a : VerifiableInference.Desc.First.S} {f : GroupLayout → Bool}
    (h : atLayB a f = true) (G : Group) (lay : GroupLayout)
    (hG : (rdK a).2.2.groups[(rdK a).2.1.group]? = some G)
    (hl : (begun (rdK a).2.2 (rdK a).2.1.group G).layout (rdK a).2.1.group = some lay) :
    f lay = true := by
  unfold atLayB at h
  simp only [hG, hl] at h
  exact h

/-! ## (N1), (N2) and the plan's maskCode, from the frame -/

/-- **The plan's numbers are the written shape's, where the frame is the link's.** -/
theorem plan_of_frame (es : List Fmt.Entry) (x : Option Nat × ReqFrame × Statement)
    {sh : ReqShape} {l : ℕ} (hg : x.2.1.groups = reqGroups x.2.1.shape) (hs : x.2.1.shape = sh)
    (hl : x.2.1.link = l) :
    (planOf es x).k = ((reqGroups sh)[l]?.getD default).k ∧
      (planOf es x).h = ((reqGroups sh)[l]?.getD default).h ∧
      (planOf es x).maskCode = sh.maskCode := by
  unfold planOf
  simp [hg, hs, hl]

/-! ## (N3), (N4), (N5), from the members' written shapes -/

variable {cs : Codes} {lo : List (OracleShape × ℕ)} {s : Sg} {kb : Fin lo.length → Bool}
  {no : Fin lo.length → ℕ} {T : Statement} {G : Group} {L : GroupLayout}

/-- A member's number of place bits is its written shape's code's. -/
theorem placeBits_of_shape {o : ℕ} {sh : OracleShape}
    (h : (T.oracles[o]?).map (fun x : OnBytes.Oracle => x.shape) = some sh) (hc : T.codes = cs) :
    (sh.mainRows ≠ 0 → T.placeBits o .main = (pMain cs sh).logEll) ∧
      (sh.maskRows ≠ 0 → T.placeBits o .mask = (pMask cs sh).logEll) := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  subst hc
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · unfold Statement.placeBits
    rw [hx]
    have e : (x.shape.rows .main == 0) = false := by
      show (x.shape.mainRows == 0) = false
      simpa using h0
    simp only [e]
    rfl
  · unfold Statement.placeBits
    rw [hx]
    have e : (x.shape.rows .mask == 0) = false := by
      show (x.shape.maskRows == 0) = false
      simpa using h0
    simp only [e]
    rfl

/-- **(N3).** -/
theorem logEll_of_shapes
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (Y : LayFacts T G L) (H : ShapesAre T G lo kb no) (hc : T.codes = cs)
    (a : {i // memMain lo i}) (hp : powerOfTwo (pMain cs (lo.get a.1).1).ell = true) :
    2 ^ L.logEll = s.C.l := by
  have hm : a.1 ∈ membersOf lo := mem_members.2 a.2
  have hin : no a.1 ∈ G.members.toList := by
    rw [H.members]
    exact List.mem_map_of_mem hm
  have hhas : T.has (no a.1) .main = true := by
    rw [(has_of_shape (H.shape _ hm) .main).1]
    exact decide_eq_true (Nat.pos_of_ne_zero a.2)
  rw [← Y.main_places _ hin hhas, (placeBits_of_shape (H.shape _ hm) hc).1 a.2, ← hM a.1 a.2 a.2]
  unfold powerOfTwo at hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact hp.2

/-- **(N4)**, at a member that has a mask row. -/
theorem logEllZk_of_shapes
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    (Y : LayFacts T G L) (H : ShapesAre T G lo kb no) (hc : T.codes = cs)
    (a : {i // memMain lo i}) (hz : (lo.get a.1).1.maskRows ≠ 0)
    (hp : powerOfTwo (pMask cs (lo.get a.1).1).ell = true) : 2 ^ L.logEllZk = s.Z.l := by
  have hm : a.1 ∈ membersOf lo := mem_members.2 a.2
  have hin : no a.1 ∈ G.members.toList := by
    rw [H.members]
    exact List.mem_map_of_mem hm
  have hhas : T.has (no a.1) .mask = true := by
    rw [(has_of_shape (H.shape _ hm) .mask).1]
    exact decide_eq_true (Nat.pos_of_ne_zero hz)
  rw [← Y.mask_places _ hin hhas, (placeBits_of_shape (H.shape _ hm) hc).2 hz, ← hZ a.1 a.2 hz]
  unfold powerOfTwo at hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact hp.2

/-- **(N5)**, where the plan's maskCode is that of a member with a mask row. -/
theorem code_of_member
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    (hc : T.codes = cs) (a : {i // memMain lo i}) (hz : (lo.get a.1).1.maskRows ≠ 0) {mc : ℕ}
    (hmc : mc = (lo.get a.1).1.maskCode) : (T.codes.mask.getD mc default).ell = s.Z.l := by
  rw [hc, hmc, ← hZ a.1 a.2 hz]
  rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.n1B_iff
#print axioms VerifiableInference.Desc.LinkJoin.n2B_iff
#print axioms VerifiableInference.Desc.LinkJoin.n5B_iff
#print axioms VerifiableInference.Desc.LinkJoin.atLayB_says
#print axioms VerifiableInference.Desc.LinkJoin.plan_of_frame
#print axioms VerifiableInference.Desc.LinkJoin.placeBits_of_shape
#print axioms VerifiableInference.Desc.LinkJoin.logEll_of_shapes
#print axioms VerifiableInference.Desc.LinkJoin.logEllZk_of_shapes
#print axioms VerifiableInference.Desc.LinkJoin.code_of_member
