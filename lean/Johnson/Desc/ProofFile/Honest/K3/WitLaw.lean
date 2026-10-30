-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitLaw.lean: the honest side of the kind "lookup" (K3): what
a theorem on a lookup's row may take from Honest/K3/Wit.lean. Twelve small theorems and seven
definitions.

Terms. Honest/K3/GLOSSARY.md: see there keys and bits are honest, relation after the challenge,
settled, sources, shape, shift, call and planes. In this file: the row computes in the program's
elements (`OnBytes.E`); the library's relation on keys and bits (`Cb.Lkp.MidP`,
Cb/Pv/Lookup/Alg/PadAlg.lean) is stated in the library's field (`Cb.Gl.E`). These lemmas carry the
row's structure back. `PremF` is the specification's own hypothesis on a proof file's lookup
(Johnson/HonestTrace/LookDefs.lean).

What is shown.
  `inE_outE`: an element of the library's field, written into words and read back, is itself. The
    library has it as `D6.Bridge.liftGl_val` (OnBytes/Desc/First/NormBridge/HonestGl.lean), in its
    own two names.
  `hidden_key`, `hidden_bit`: what the row's structure holds, read in the library's field, is the
    key vector at the shift as read, and the bit.
  `askOf_calls`: on a link's calls the structure does not depend on the challenges heard.
  `Ask.Settled`, `tritsAt_append`, `askOf_settled`: behind the challenges in front of the lookup
    (the first base of them) the structure no longer moves, not at the lookup's own first challenge
    either, if on the digits the matrix's round stands in front of the lookup.
  `LookIn.Meets`: a hypothesis for theorems, no theorem: keys and bits are honest at a lookup's
    shape: in the clauses of `PremF` (zero and mid), with what ties this folder's structure to its
    letters: the key vector is the joint vector of the calls' key vectors; a bit is what a reading
    of the verifier's places reads at the bit's place.
  `pairShape`, `pairLook`, `pairNu`, `pair_mid`, `pair_bit`, `pairLook_meets`: an instance with two
    calls, by proof.
  `strayShape`, `strayLook`, `stray_mid`, `strayLook_mid`, `strayLook_not_meets`: a structure of
    which the library's relation holds and the hypothesis does not: its count lies at a row of no
    call.

Hypotheses that remain.
  `h`: in `tritsAt_append`: the matrix's round has been heard (rng < front.length).
  `h0`, `h1`: in `pair_mid` and `stray_mid`: the keys are rows of the table (key 0 = t 0 and
    key 1 = t 1; key 0 = t 1).
  `hw`: in `askOf_calls`: the lookup is not on the digits. In `askOf_settled`: on the digits the
    round that samples the matrix stands in front of the lookup (rng < base); on the calls nothing
    is asked.

Users. Honest/K3/WitFill.lean, Honest/K3/Law/KeysAreKvG.lean, Honest/K3/Law/SpecMember.lean,
Honest/K3/Law/Keep/StoreStays.lean and Honest/K3/Law/Keep/SiteRng.lean import this file.

Limits. `LookIn.Meets` is a definition. It holds where the trace's files prove `MidP` of the terms
with which `Sources` is filled; on the digits at every sampled matrix (`digits_meets`,
Honest/K3/WitDigits.lean, under two public hypotheses): outside its window a combination's digits
are in range and do not give it back.
What "there is a reading nu" is worth (by reading; no theorem says it): where a bit's place
determines row and plane (5 ≤ lm ≤ kT + 5) every structure of bits that is 0 at the rows of no call
has such a reading. So that clause says these zeros and no more: it ties the bits to no cell of a
trace, and kv to nothing that a caller's key form reads: both are for whoever fills the structure
(WitFill.lean). On the digits lm is no number of the array BZ, which has an address rule of its own:
there the library reaches BZ at lm = 5. An lm outside 5 ... kT + 5 is not excluded here: that test
is public (the clauses lm5 and lmT of `PremF`).
The one instance given here is small: two calls, a key and a row each; its shape passes none of the
verifier's tests on a lookup's numbers (a tree of 2 ^ 10 keys at least). It shows that the form of
the hypothesis can hold at more than one call, with every bit at a place where the verifier has a
cell; it is no lookup of a proof file. The other clauses of `PremF` (the tests on the numbers; the
shift 0 where there is one call; the challenges' lengths) are public and are not in the hypothesis.
No statement of this file says that outE (inE x) is x: that holds at words below the prime alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Wit
import OnBytes.Tie.Pv.Lookup.Ends.Joint
import OnBytes.Tie.Pv.Lookup.Forest.FoV
import Cb.Pv.Lookup.Alg.PadAlg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E)

/-- An element of the library's field, written into words and read back, is itself. -/
theorem inE_outE (x : Cb.Gl.E) : inE (outE x) = x := by
  unfold inE outE
  rw [OnBytes.E.triple_ofTriple]
  exact OnBytes.Slice.toE_ofE x

/-- The row's key, read in the library's field: the key vector at the shift as read; at every part's
number. -/
theorem hidden_key (L : LookIn) (theta : E) (i n : Nat) :
    inE (L.hidden.key theta i n) = L.key (inE theta) n :=
  inE_outE _

/-- The row's bit, read in the library's field. -/
theorem hidden_bit (L : LookIn) (u j : Nat) : inE (L.hidden.bit u j) = L.bit u j :=
  inE_outE _

/-- On a link's calls the structure does not depend on the challenges heard. -/
theorem askOf_calls {W₀ Rc Xi Tr : Type} (S : Sources W₀ Xi Tr) (w : Who)
    (hw : ∀ link rng, w ≠ .digits link rng) (t : Local W₀ Rc Xi Tr) (h₁ h₂ : List Fmt.Drawn) :
    askOf S w t h₁ = askOf S w t h₂ := by
  cases w with
  | layers g => rfl
  | attention g => rfl
  | head => rfl
  | digits link rng => exact absurd rfl (hw link rng)

/-- **An Ask is settled at base**: behind the first base challenges it no longer moves: all parts of
a row, each of which is given the challenges in front of itself, see one structure. -/
def Ask.Settled (base : Nat) (w : Ask) : Prop :=
  ∀ front more : List Fmt.Drawn, base ≤ front.length → w (front ++ more) = w front

/-- The sampled matrix does not move once its round has been heard. -/
theorem tritsAt_append (front more : List Fmt.Drawn) {rng : Nat} (h : rng < front.length) :
    tritsAt (front ++ more) rng = tritsAt front rng := by
  unfold tritsAt
  rw [List.getElem?_append_left h]

/-- **What a lookup's row is given is settled at the lookup's first round.** Conditional on: on
the digits the round that samples the matrix stands in front of the lookup (rng < base). On the
calls nothing is asked. Instances: every lookup on calls; on the digits the five places of the
small example's description, by the test of the table of
places (Honest/K3/Lot.lean) (by evaluation, in a run of Honest/K3/LotSheet.lean, as the head of
Honest/K3/Law/SiteFits.lean tells; the run's print is not in the library). -/
theorem askOf_settled {W₀ Rc Xi Tr : Type} (S : Sources W₀ Xi Tr) (w : Who)
    (t : Local W₀ Rc Xi Tr) (base : Nat) (hw : ∀ link rng, w = .digits link rng → rng < base) :
    Ask.Settled base (askOf S w t) := by
  intro front more hb
  cases w with
  | layers g => rfl
  | attention g => rfl
  | head => rfl
  | digits link rng =>
    show (S.digits link (S.cells t.trace) (tritsAt (front ++ more) rng)).hidden = _
    rw [tritsAt_append front more (lt_of_lt_of_le (hw link rng rfl) hb)]
    rfl

/-- **A hypothesis for theorems**: keys and bits are honest at a lookup of shape h whose planes'
matrix has 2 ^ lm rows. In the clauses of the specification's own hypothesis on a proof file's
lookup (OnBytes.HonestTrace.Look.PremF, Johnson/HonestTrace/LookDefs.lean: zero, mid): there are key
vectors kv of the calls and a reading nu of the verifier's places such that: nu reads 0 at the place
that reads 0; the key vector is the joint vector of kv; a bit is what nu reads at the bit's place,
so it is 0 at a row of the joint table that belongs to no call, where the verifier has no cell; and
at every shift and every point of comparison the library's relation MidP holds of the joint vector,
the joint table, the public padding and nu at the bits' places. -/
def LookIn.Meets (L : LookIn) (h : OnBytes.Model.Forest.Shape) (lm : Nat) : Prop :=
  ∃ (kv : ℕ → ℕ → Cb.Gl.E) (nu : _root_.Fo.Pl → Cb.Gl.E),
    nu .zero = 0 ∧
    (∀ theta n, L.key theta n = OnBytes.Ends.jointKey h kv theta n) ∧
    (∀ (theta : Cb.Gl.E) (jLK u j : ℕ), u < 2 ^ h.d → j < 32 →
      L.bit u j = nu ((_root_.Fo.numsF h lm jLK theta).bAt u j)) ∧
    ∀ (theta al : Cb.Gl.E) (jLK : ℕ),
      Cb.Lkp.MidP h.v h.d 5 32 (OnBytes.Ends.jointKey h kv theta) (OnBytes.Ends.jointTab h theta)
        (FoNums.pads h) (fun u j => nu ((_root_.Fo.numsF h lm jLK theta).bAt u j)) al

/-! ## An instance with two calls -/

/-- Two calls, each with one tree of one key and a table of one row with the value 0. -/
def pairShape : OnBytes.Model.Forest.Shape :=
  { calls := #[{}, {}], dT := 0, kT := 0, NT := 2, rK := 1, NC := 2, cK := 1, first := #[0, 1]
    callOf := #[0, 1] }

/-- Its keys: each call's one key is its table's one row; its counts: 1 at either row: the bit of
plane 0. -/
def pairLook : LookIn :=
  ⟨fun theta n => OnBytes.Ends.jointKey pairShape (fun _ _ => 0) theta n,
   fun _ j => if j = 0 then 1 else 0⟩

/-- The reading: 1 in row 0 of the planes' matrix, 0 elsewhere. -/
def pairNu : _root_.Fo.Pl → Cb.Gl.E
  | .cell r _ => if r = 0 then 1 else 0
  | _ => 0

/-- The library's relation at two keys that are the table's two rows, padding of no key, and the
count 1 at either row. -/
theorem pair_mid (key t : ℕ → Cb.Gl.E) (h0 : key 0 = t 0) (h1 : key 1 = t 1) (r0 r1 : ℕ)
    (al : Cb.Gl.E) :
    Cb.Lkp.MidP 1 1 5 32 key t [(r0, 0), (r1, 0)]
      (fun _ j => if j = 0 then (1 : Cb.Gl.E) else 0) al := by
  refine ⟨?_, ?_, ?_⟩
  · intro u _ j _
    dsimp only
    split <;> simp
  · unfold Cb.Lkp.NumKeysP
    have hin : (∑ j ∈ Finset.range 32, (2 : Cb.Gl.E) ^ j * (if j = 0 then 1 else 0)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_range.2 (by norm_num)) h
    rw [Finset.sum_congr rfl fun _ _ => hin]
    simp [Cb.Lkp.padNum]
  · have hR : (∏ j ∈ Finset.range 32, (∏ u ∈ Finset.range (2 ^ 1),
        (1 + (if j = 0 then (1 : Cb.Gl.E) else 0) * (al - 1 - t u))) ^ 2 ^ j) =
        (al - t 0) * (al - t 1) := by
      rw [Finset.prod_eq_single 0]
      · simp [Finset.prod_range_succ]
        ring
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_range.2 (by norm_num)) h
    unfold Cb.Lkp.keyProd Cb.Lkp.tabProd Cb.Lkp.padFac
    beta_reduce
    rw [hR]
    simp [Finset.prod_range_succ, h0, h1]

/-- At the instance's shape a bit's place lies in the row of its plane. -/
theorem pair_bit (theta : Cb.Gl.E) (jLK u j : ℕ) :
    pairNu ((_root_.Fo.numsF pairShape 5 jLK theta).bAt u j) = if j = 0 then 1 else 0 := by
  have hu : u % 2 ^ pairShape.cK < pairShape.NC := Nat.mod_lt _ (by decide)
  show pairNu (match FoNums.cellOf pairShape u j with
    | some x => .cell (FoNums.cellRC pairShape 5 x).1 (FoNums.cellRC pairShape 5 x).2
    | none => .zero) = _
  unfold FoNums.cellOf
  rw [if_pos hu]
  show (if (u / 2 ^ pairShape.cK % 2 ^ (5 - FoNums.w)) * FoNums.planes + j = 0 then (1 : Cb.Gl.E)
    else 0) = _
  have : (u / 2 ^ pairShape.cK % 2 ^ (5 - FoNums.w)) * FoNums.planes + j = j := by
    have e : (2 : ℕ) ^ (5 - FoNums.w) = 1 := rfl
    rw [e, Nat.mod_one, Nat.zero_mul, Nat.zero_add]
  rw [this]

/-- **The hypothesis can hold at a shape with two calls.** -/
theorem pairLook_meets : pairLook.Meets pairShape 5 := by
  refine ⟨fun _ _ => 0, pairNu, rfl, fun _ _ => rfl, fun theta jLK u j _ _ =>
    (pair_bit theta jLK u j).symm, fun theta al jLK => ?_⟩
  have hb : (fun u j => pairNu ((_root_.Fo.numsF pairShape 5 jLK theta).bAt u j)) =
      fun _ j => if j = 0 then (1 : Cb.Gl.E) else 0 := by
    funext u j
    exact pair_bit theta jLK u j
  rw [hb]
  have hp : FoNums.pads pairShape = [(0, 0), (1, 0)] := by decide
  rw [hp]
  exact pair_mid _ _ (by simp [OnBytes.Ends.jointKey, OnBytes.Ends.jointTab, OnBytes.Ends.tauN,
      OnBytes.Ends.kN, pairShape, OnBytes.Model.Call.tauAt])
    (by simp [OnBytes.Ends.jointKey, OnBytes.Ends.jointTab, OnBytes.Ends.tauN, OnBytes.Ends.kN,
      pairShape, OnBytes.Model.Call.tauAt]) 0 1 al

/-! ## A structure of which the relation holds and the hypothesis does not -/

/-- One call, but a bit for a call's number: the joint table has two rows, of which the second
belongs to no call and repeats the first. One key. -/
def strayShape : OnBytes.Model.Forest.Shape :=
  { calls := #[{}], dT := 0, kT := 0, NT := 1, rK := 0, NC := 1, cK := 1, first := #[0]
    callOf := #[0] }

/-- The one key is the table's row; its count is set at the row that belongs to no call. -/
def strayLook : LookIn :=
  ⟨fun theta n => OnBytes.Ends.jointKey strayShape (fun _ _ => 0) theta n,
   fun u j => if u = 1 ∧ j = 0 then 1 else 0⟩

/-- The library's relation at one key, a table of two rows with the key's value, and the count 1 at
the second row. -/
theorem stray_mid (key t : ℕ → Cb.Gl.E) (h1 : key 0 = t 1) (r0 : ℕ) (al : Cb.Gl.E) :
    Cb.Lkp.MidP 0 1 5 32 key t [(r0, 0)]
      (fun u j => if u = 1 ∧ j = 0 then (1 : Cb.Gl.E) else 0) al := by
  refine ⟨?_, ?_, ?_⟩
  · intro u _ j _
    dsimp only
    split <;> simp
  · unfold Cb.Lkp.NumKeysP
    have hin : ∀ u, (∑ j ∈ Finset.range 32,
        (2 : Cb.Gl.E) ^ j * (if u = 1 ∧ j = 0 then 1 else 0)) = if u = 1 then 1 else 0 := by
      intro u
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_range.2 (by norm_num)) h
    rw [Finset.sum_congr rfl fun u _ => hin u]
    simp [Cb.Lkp.padNum]
  · have hR : (∏ j ∈ Finset.range 32, (∏ u ∈ Finset.range (2 ^ 1),
        (1 + (if u = 1 ∧ j = 0 then (1 : Cb.Gl.E) else 0) * (al - 1 - t u))) ^ 2 ^ j) =
        al - t 1 := by
      rw [Finset.prod_eq_single 0]
      · simp [Finset.prod_range_succ]
        ring
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_range.2 (by norm_num)) h
    unfold Cb.Lkp.keyProd Cb.Lkp.tabProd Cb.Lkp.padFac
    beta_reduce
    rw [hR]
    simp [h1]

/-- The library's relation holds of it at its own keys and bits, at every shift and point. -/
theorem strayLook_mid (theta al : Cb.Gl.E) :
    Cb.Lkp.MidP strayShape.v strayShape.d 5 32 (strayLook.key theta)
      (OnBytes.Ends.jointTab strayShape theta) (FoNums.pads strayShape) strayLook.bit al := by
  have hp : FoNums.pads strayShape = [(0, 0)] := by decide
  rw [hp]
  exact stray_mid _ _ (by simp [strayLook, OnBytes.Ends.jointKey, OnBytes.Ends.jointTab,
    OnBytes.Ends.tauN, OnBytes.Ends.kN, strayShape, OnBytes.Model.Call.tauAt]) 0 al

/-- **The hypothesis does not hold of it**: at the row of no call the verifier has no cell. -/
theorem strayLook_not_meets (lm : ℕ) : ¬ strayLook.Meets strayShape lm := by
  rintro ⟨kv, nu, h0, -, hb, -⟩
  have h := hb 0 0 1 0 (by decide) (by norm_num)
  have e : (_root_.Fo.numsF strayShape lm 0 (0 : Cb.Gl.E)).bAt 1 0 = .zero := rfl
  rw [e, h0] at h
  exact one_ne_zero h

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.stray_mid
#print axioms ProofFile.Honest.K3.strayLook_mid
#print axioms ProofFile.Honest.K3.strayLook_not_meets
#print axioms ProofFile.Honest.K3.tritsAt_append
#print axioms ProofFile.Honest.K3.askOf_settled
#print axioms ProofFile.Honest.K3.pair_mid
#print axioms ProofFile.Honest.K3.pair_bit
#print axioms ProofFile.Honest.K3.pairLook_meets
#print axioms ProofFile.Honest.K3.inE_outE
#print axioms ProofFile.Honest.K3.hidden_key
#print axioms ProofFile.Honest.K3.hidden_bit
#print axioms ProofFile.Honest.K3.askOf_calls
