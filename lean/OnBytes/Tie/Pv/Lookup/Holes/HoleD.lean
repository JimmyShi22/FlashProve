-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Holes/HoleD.lean.
The knowledge soundness of the lookup on the digits of the smallness test, as closed statements
with their proofs.

The smallness test writes each tested number in a low and a high digit and looks the low digits up
in the table of the numbers below q and the high digits in the table of the numbers below H. Both
are calls of one lookup: the verifier draws a shift theta, under which the two calls become one
lookup of a joint key vector in a joint table, and then runs that lookup with the short sumcheck
messages. The block is the one of a sub-proof's lookup
(OnBytes/Tie/Pv/Lookup/Holes/HoleC.lean, `HCgen`), taken at the digits.

What the digits are is the record `CbQ.DatQ I J` (Cb/Pv/Lookup/Digits/DatQ.lean): the digits' places
among the entries J, the numbering of the joint keys and rows, the call of each, the places of the
planes of the counts' bits, and the public padding. Its laws are `DatOK q H p`, fifteen bounded
statements on maps of numbers.

Definitions.
 * `PlD E J d`: what the one lookup needs beside `DatQ`: three numbers, the places of its masks and
   shown values, and the four families of orders in which its sumchecks bind their variables. All
   are fields of the record; none has a default.
 * `digA St Q Pl`: the record of the one lookup at the shifted joint vectors of `Q`. The size of the
   table, the places of the planes and the padding are those of `Q`.
 * `digB St Q Pl`: the block: the draw of theta, then the whole lookup, at the named short sumcheck
   blocks `V₀`, `V₀C`.
 * `digOwn`, `digIn`: the joint before the block, in the block's own words ("each joint key is a row
   of its own call") and in the digits' words ("each low digit is a number below q, each high digit
   a number below H"). `digIn_eq`: under `DatOK` the two are equal.
 * `digOut`: the joint behind the block: the claim on the joint keys and all rows that the block
   hands on hold.
 * `NumOK Q Pl p`: four conditions on public numbers.

Statements. Each is a definition of a proposition in which every variable is bound, and a theorem
without binders proves it.
 * `HD₀`, `hD₀`: for every finite field E of characteristic p, every caller's state, every `Q` and
   `Pl`, every joint `R0` and reading `msg` of the committed messages: under `DatOK q H p` and
   `NumOK Q Pl p`, `KnowAt` of the block from `digOwn` to `digOut`, with the identity on the further
   witness as extractor, at the block's own errors.
 * `HDdig`, `hDdig`: the same from `digIn`.
 * `HDk`, `hDk`: the field `know` of `HDdig` alone, written out.
 * `hD_point`, `hD_local`, `hD_onOut`: the three other fields, under the same two premises.
 * `hD_eps`, `hD_shape`: the block's errors and rounds as lists. `hD_small`: each error is below the
   number of its round's challenges. These three ask that the layer of the table's leaves binds its
   variables from the last to the first (`Pl.oE = Fin.revPerm`). `hD_small` also asks that E has
   characteristic p and that `NumOK Q Pl p` holds. It says that each round's quotient is below 1,
   and no more: no sum of quotients is bounded here. `hD_shape` holds for every `wk`: an entry's
   name and its bits of work are tied to the round by nothing.
No premise of `HD₀`, `HDdig` or `HDk` reads the committed messages, a witness or a transcript.

Not claimed here. That a given verifier's numbering of the digits is a value of `DatQ` with
`DatOK`, or its places and orders a value of `PlD`. That the claims in `digOut` are the values that
the program's verifier computes, or that they are proved further on. What the smallness test
concludes from digits in range, and the rest of its block. Which messages are committed before
theta is drawn: `msg` and `R0` are variables, and no caller's frame is shown to have a value of
them.
Anything about an honest prover.

-/
import OnBytes.Tie.Pv.Lookup.Holes.HoleC0
import OnBytes.Tie.Pv.Lookup.Shift.ShiftKArith
import Cb.Pv.Lookup.Digits.DatQ
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

namespace Cb.Fo
open Finset Prob Cb.Lkp Cb.LdLkp Cb.LdLkp.Kn Cb.Rng Iop IOR TWhole TwRound TwPlan TwErr OnBytes.G4
open CbQ (DatQ)

/-- What the one lookup needs beside the digits' record. d: the joint table's log size. -/
structure PlD (E J : Type) [Field E] [Fintype E] (d : ℕ) where
  /-- a joint key's number has v' + 1 bits -/
  v' : ℕ
  /-- 2 ^ w slots of planes, of which n + 2 count -/
  w : ℕ
  n : ℕ
  /-- the tie of the roots: masks, shown values -/
  wAt : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → J
  cZ : J
  cAt : ℕ → Bool → J
  /-- the tree of the keys -/
  wK : (l : ℕ) → PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) → J
  cK : ℕ → Bool → J
  /-- the tree of the table -/
  wT : (l : ℕ) → PIdx (List.replicate (w + l) (pfCube E 2) ++ [pDummy E 2]) → J
  cT : ℕ → Bool → J
  /-- the layer of the table's leaves -/
  oE : Equiv.Perm (Fin (w + d))
  wE : PIdx (pfMix E (w + d) (dgEnd w d oE)) → J
  /-- the test that the counts' bits are bits -/
  oB : Equiv.Perm (Fin (w + d))
  wB : PIdx (List.replicate (w + d) (pfCube E 2) ++ [pDummy E 2]) → J
  cB : J
  /-- the orders of the levels of the two trees -/
  oK : (l : ℕ) → Equiv.Perm (Fin (0 + l))
  oT : (l : ℕ) → Equiv.Perm (Fin (w + l))

section
variable {E : Type} [Field E] [Fintype E] (St : Type) {I J : Type} [Fintype J] [DecidableEq J]
  (Q : DatQ I J) (Pl : PlD E J Q.d)

/-- The one lookup at the shifted joint vectors of the digits. -/
def digA : LkAsmH E where
  St := St × E
  J := J
  v' := Pl.v'
  d := Q.d
  w := Pl.w
  n := Pl.n
  key := fun x μ => shKeyQ Q.fK (Q.key μ) Q.tagE x.2
  tab := fun x => shTabQ Q.fT Q.tab Q.tagE x.2
  bAt := Q.bAt
  pads := Q.pads
  wAt := Pl.wAt
  cZ := Pl.cZ
  cAt := Pl.cAt
  wK := Pl.wK
  cK := Pl.cK
  wT := Pl.wT
  cT := Pl.cT
  oE := Pl.oE
  wE := Pl.wE
  oB := Pl.oB
  wB := Pl.wB
  cB := Pl.cB
  oK := Pl.oK
  oT := Pl.oT

/-- The assembly at the shifted vectors, at this record, is this record. -/
theorem digA_asmH : (Q.sh St).asmH (digA St Q Pl) = digA St Q Pl := rfl

/-- The block: the draw of theta, then the whole lookup, at the named short sumcheck blocks. -/
noncomputable def digB {Ex : ExtSpec} : BkK St (TX (St × E) E J) Ex :=
  (Q.sh St).allK (digA St Q Pl) true V₀ V₀C

variable {St}

/-- All digits are in range: the low ones below q, the high ones below H. -/
def InRange (q H : ℕ) (μ : J → E) : Prop :=
  (∀ i, InTab q (μ (Q.lo i))) ∧ ∀ i, InTab H (μ (Q.hi i))

variable {Kc M Wp : Type} {Ex : ExtSpec}

/-- The joint before, in the block's own words: each joint key is a row of its own call. -/
def digOwn (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E) : Rels Kc St Ex (M × Wp) :=
  ((Q.sh St).on msg).jIn R0

/-- The joint before, in the digits' words. -/
def digIn (q H : ℕ) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E) : Rels Kc St Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x y w ∧ InRange Q q H (msg w.1),
    fun a w => R0.relR a w ∧ InRange Q q H (msg w.1), R0.on, R0.core⟩

/-- The joint behind: the claim on the joint keys and the rows. -/
def digOut (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E) :
    Rels Kc (TX (St × E) E J) Ex (M × Wp) :=
  cj (ShiftQ.ride R0) msg Prod.fst ((digA St Q Pl).lk.out id id) ((digA St Q Pl).lk.out id id)

/-- The conditions on public numbers beside the digits' laws: a joint key's number has v' + 1 bits;
all slots of planes count; a count fits in the planes; the counts' sum does not wrap. -/
def NumOK (p : ℕ) : Prop :=
  Q.v = Pl.v' + 1 ∧ Pl.n + 1 + 1 = 2 ^ Pl.w ∧ Q.v < Pl.n + 2 ∧
    2 ^ Q.d * (2 ^ (Pl.n + 2) - 1) < p

omit [Fintype E] [Fintype J] [DecidableEq J] in
/-- Under the digits' laws the two forms of the joint before are one. -/
theorem digIn_eq {q H p : ℕ} (h : Q.DatOK q H p) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E) :
    digOwn Q R0 msg = digIn Q q H R0 msg := by
  have e : ((Q.sh (E := E) St).on msg).inC = fun _ m => InRange Q q H (msg m) :=
    funext fun _ => funext fun m => propext (CbQ.dgQ_in Q h (msg m))
  unfold digOwn digIn ShiftQ.jIn
  rw [e]

variable {Q Pl}

theorem NumOK.adm {p : ℕ} (h : NumOK Q Pl p) : (digA St Q Pl).H.lkb.Adm p := by
  obtain ⟨hv, hF, hW, hp⟩ := h
  refine ⟨le_of_eq hF, ?_, hp⟩
  show 2 ^ (Pl.v' + 1) < 2 ^ (Pl.n + 2)
  rw [← hv]
  exact Nat.pow_lt_pow_right (by norm_num) hW

omit [Fintype J] [DecidableEq J] in
theorem NumOK.pads {q H p : ℕ} (h : NumOK Q Pl p) (hQ : Q.DatOK q H p) :
    padsOK (Pl.v' + 1) Q.d Q.pads = true := by
  rw [← h.1]
  exact hQ.pads

end

/-! ### the statements -/

/-- The lookup on the digits, between the block's own joints. -/
def HD₀ : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (St I J : Type) [Fintype J]
    [DecidableEq J] (Q : DatQ I J) (Pl : PlD E J Q.d) (q H : ℕ) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E),
    Q.DatOK q H p → NumOK Q Pl p →
    KnowAt (digB St Q Pl (Ex := Ex)).R (digOwn Q R0 msg) (digOut Q Pl R0 msg)
      (fun _ _ _ wp => wp) (digB St Q Pl (Ex := Ex)).e

/-- The same, the joint before in the digits' words. -/
def HDdig : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (St I J : Type) [Fintype J]
    [DecidableEq J] (Q : DatQ I J) (Pl : PlD E J Q.d) (q H : ℕ) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E),
    Q.DatOK q H p → NumOK Q Pl p →
    KnowAt (digB St Q Pl (Ex := Ex)).R (digIn Q q H R0 msg) (digOut Q Pl R0 msg)
      (fun _ _ _ wp => wp) (digB St Q Pl (Ex := Ex)).e

/-- Knowledge soundness alone, written out, for each fixed tuple of committed messages. -/
def HDk : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (St I J : Type) [Fintype J]
    [DecidableEq J] (Q : DatQ I J) (Pl : PlD E J Q.d) (q H : ℕ) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E),
    Q.DatOK q H p → NumOK Q Pl p → ∀ m : M,
    (digB St Q Pl (Ex := Ex)).R.red.Know R0.on
      (fun a wp => R0.relR a (m, wp) ∧ InRange Q q H (msg m))
      (fun b wp => R0.relR (b.1.1.1, b.2) (m, wp) ∧ (digA St Q Pl).lk.out id id b.1 (msg m))
      (fun _ _ wp => wp) (digB St Q Pl (Ex := Ex)).e

theorem hD₀ : HD₀ := fun E _ _ p _ St _ _ _ _ Q Pl _ _ Ex Kc M Wp R0 msg hQ hN =>
  hCgen E p St (digA St Q Pl) (Q.sh St) true V₀ V₀C Ex Kc M Wp R0 msg (CbQ.dgQ_tags Q hQ St) hN.1
    rfl hN.adm (hN.pads hQ) hN.2.1

theorem hDdig : HDdig := fun E _ _ p _ St I J _ _ Q Pl q H Ex Kc M Wp R0 msg hQ hN =>
  digIn_eq Q hQ R0 msg ▸ hD₀ E p St I J Q Pl q H Ex Kc M Wp R0 msg hQ hN

theorem hDk : HDk := fun E _ _ p _ St I J _ _ Q Pl q H Ex Kc M Wp R0 msg hQ hN m =>
  (hDdig E p St I J Q Pl q H Ex Kc M Wp R0 msg hQ hN).know m

/-! ### beside them -/

section
variable {E : Type} [Field E] [Fintype E] (p : ℕ) [CharP E p] (St : Type) {I J : Type} [Fintype J]
  [DecidableEq J] (Q : DatQ I J) (Pl : PlD E J Q.d) {q H : ℕ} (Ex : ExtSpec)

/-- The shape is of the point kind. -/
theorem hD_point (hQ : Q.DatOK q H p) (hN : NumOK Q Pl p) :
    Nonempty (digB St Q Pl (Ex := Ex)).R.shape.IsPoint :=
  (hD₀ E p St I J Q Pl q H Ex Unit (J → E) Unit
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ id hQ hN).point

/-- The reduction is local. -/
theorem hD_local (hQ : Q.DatOK q H p) (hN : NumOK Q Pl p) :
    (digB St Q Pl (Ex := Ex)).R.IsLocal :=
  (hD₀ E p St I J Q Pl q H Ex Unit (J → E) Unit
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ id hQ hN).isLocal

/-- The caller's condition holds again behind the block. -/
theorem hD_onOut {Kc M Wp : Type} (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E)
    (hQ : Q.DatOK q H p) (hN : NumOK Q Pl p) (a : St × Ex.Str)
    (τ : Tr (digB St Q Pl (Ex := Ex)).R.red.shape) (b : TX (St × E) E J × Ex.Str) (ha : R0.on a)
    (hb : (digB St Q Pl (Ex := Ex)).R.red.out a τ = some b) : R0.on (b.1.1.1, b.2) :=
  (hD₀ E p St I J Q Pl q H Ex Kc M Wp R0 msg hQ hN).onOut a τ b ha hb

omit [CharP E p] in
/-- The errors as a list of numbers: theta's, then the one lookup's. -/
theorem hD_eps (ho : Pl.oE = Fin.revPerm) :
    errList (digB St Q Pl (Ex := Ex)).e =
      2 ^ Q.d :: epsN Pl.v' Q.d Pl.w Pl.n (Fintype.card E) :=
  allK_eps V₀ V₀C Ex (digA St Q Pl) (Q.sh St) true ho

omit [CharP E p] in
/-- The rounds as a list of entries: theta's, then the one lookup's. -/
theorem hD_shape (wk : ℕ) (ho : Pl.oE = Fin.revPerm) :
    ShapeIs E (digB St Q Pl (Ex := Ex)).R.shape (shiftN wk :: entN wk Pl.v' Q.d Pl.w Pl.n) :=
  allK_shape V₀ V₀C Ex (digA St Q Pl) (Q.sh St) true wk ho

/-- Each error is below the number of its round's challenges. -/
theorem hD_small (hN : NumOK Q Pl p) (ho : Pl.oE = Fin.revPerm) :
    List.Forall₂ (· < ·) (errList (digB St Q Pl (Ex := Ex)).e)
      ((digB St Q Pl (Ex := Ex)).R.shape.map fun r => Nat.card r.Chal) := by
  obtain ⟨hv, hF, hW, hp⟩ := hN
  obtain ⟨k, hpr, hq⟩ := FiniteField.card E p
  have hpq : p ≤ Fintype.card E := by
    rw [hq]
    exact Nat.le_self_pow k.ne_zero p
  have hvW : 2 ^ (Pl.v' + 1) < 2 ^ (Pl.n + 2) := by
    rw [← hv]
    exact Nat.pow_lt_pow_right (by norm_num) hW
  have hd1 : Q.d + 1 ≤ 2 ^ Q.d := Nat.lt_two_pow_self
  have hw1 : Pl.w + 1 ≤ 2 ^ Pl.w := Nat.lt_two_pow_self
  have hn1 : Pl.n + 2 + 1 ≤ 2 ^ (Pl.n + 2) := Nat.lt_two_pow_self
  have h22 : 2 ^ 2 ≤ 2 ^ (Pl.n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb : Pl.w + 1 ≤ 2 ^ (Pl.n + 2) - 1 := by omega
  have hmul : (Q.d + 1) * (Pl.w + 1) ≤ 2 ^ Q.d * (2 ^ (Pl.n + 2) - 1) := Nat.mul_le_mul hd1 hb
  have hle : 2 ^ (Pl.n + 2) - 1 ≤ 2 ^ Q.d * (2 ^ (Pl.n + 2) - 1) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have hle2 : 2 ^ Q.d ≤ 2 ^ Q.d * (2 ^ (Pl.n + 2) - 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h4q : 4 < Fintype.card E := by
    have h3 : 3 < p := by omega
    have : p ≠ 4 := by
      rintro rfl
      exact absurd hpr (by norm_num)
    omega
  refine allK_small V₀ V₀C Ex (digA St Q Pl) (Q.sh St) true ho h4q ?_ ?_ ?_
  · show 2 ^ (Pl.v' + 1) ≤ Fintype.card E
    omega
  · show Pl.w + Q.d < Fintype.card E
    have : Pl.w + Q.d < (Q.d + 1) * (Pl.w + 1) := by nlinarith
    omega
  · show 2 ^ Q.d < Fintype.card E
    omega

end
end Cb.Fo
