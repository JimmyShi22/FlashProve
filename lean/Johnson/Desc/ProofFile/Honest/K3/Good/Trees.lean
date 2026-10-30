-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Trees.lean: the parts' steps and the parts' key trees, from
their return, at any number of parts of keys: for each step and each level the row that it leaves,
with its coefficients as `SumOut` tells them, and the form from which it starts; and the forms that
the key trees leave. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md: see there stage, sumcheck, row, form, slot, ledger, hearing, sample,
key tree and level. In this file: f is the lookup's face, lo the ledger's count of slots in front of
the lookup, rs the rounds. `Pos` and `SumOut` are those of Honest/K3/Good/Step.lean; `startOf` and
`endOf` are those of Honest/K3/Good/Levels.lean.

What is shown.
  `splitStart`, `rootOf`: the form in front of the parts' step number i; the form of the root of
    part i.
  `parts_out`: the parts' steps.
  `keyStart`: the form in front of level m of the key tree of part i; at m := the number of its
    levels, the form that the tree leaves.
  `keys_out`: the key trees.
Helper: `jKey_succ`.

Hypotheses that remain.
  `hok`: every sampled element's words are below the prime (`Ok`, Levels.lean).
Besides, in the statements themselves: how many steps or parts stand in front; where the hearing
stands (`Pos`); that the forms carried name slots between lo and the ledger's next slot alone; and
the return of `partsV` or `keysV`: all without a name, in front of arrows. `h`: (in `jKey_succ`)
part i is there, of v bits.

Users. Honest/K3/Good/Join.lean imports this file.

Limits. These two pieces of the hearing alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Tie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open OnBytes (E zeroE oneE subE mulE okE isZeroE)
open OnBytes.Model (Fork Aff Reading)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Call Ends Heard ownSlots)
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)
open VerifiableInference.Desc.K3 (Hr sumV partsV keysV noVar)
open VerifiableInference.Desc.First.ProdV (Carried)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (In in_slot in_mono atP_split atP_key jSplit jJoin jKey)

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

variable {f : LFace} {lo : Nat} {rs : List Fmt.RoundView}

/-! ## The parts' steps -/

/-- The form in front of the parts' step number i. -/
def splitStart (f : LFace) (lo : Nat) : Nat → Aff
  | 0 => Aff.slot (e0 f lo)
  | i + 1 => Aff.slot (endOf f lo (.split i) + 1)

/-- The form of part i's root. -/
def rootOf (f : LFace) (lo : Nat) (i : Nat) : Aff :=
  if i + 1 < f.parts.length then Aff.slot (endOf f lo (.split i))
  else splitStart f lo (f.parts.length - 1)

/-- **The parts' steps, from their return.** Here i0 says how many steps stand in front. -/
theorem parts_out (hok : Ok rs) : ∀ (n i0 : Nat) (rows : Array Aff) (C : Aff) (F : Fork)
    (rest : List Fmt.RoundView) (rows' : Array Aff) (roots : List Aff) (G : Fork) (rest' : List Fmt.RoundView),
    i0 + n = f.parts.length - 1 → Pos f lo rs (jSplit f i0) F rest → C = splitStart f lo i0 →
    In lo F.next C → partsV n rows C F rest = some ((rows', roots), G, rest') →
    Pos f lo rs (jJoin f) G rest' ∧ (∀ y ∈ rows.toList, y ∈ rows'.toList) ∧
      (∀ i, i0 ≤ i → i < f.parts.length - 1 → ∃ y ∈ rows'.toList,
        SumOut f lo rs (.split i) (splitStart f lo i) y (endOf f lo (.split i))) ∧
      (∀ i, i ≤ n → roots[i]? = some (rootOf f lo (i0 + i))) ∧ roots.length = n + 1 ∧
      (∀ y ∈ roots, In lo G.next y) ∧ F.next ≤ G.next
  | 0, i0, rows, C, F, rest, rows', roots, G, rest', hn, P, hC, hI, h => by
    unfold partsV at h
    obtain ⟨a, b, c⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2 b c
    have hi : i0 = f.parts.length - 1 := by omega
    refine ⟨?_, fun _ hy => hy, fun i h1 h2 => absurd h2 (by omega), ?_, rfl, ?_, Nat.le_refl _⟩
    · unfold jJoin
      rw [← hi]
      exact P
    · intro i hi0
      obtain rfl : i = 0 := by omega
      have e : rootOf f lo (i0 + 0) = C := by
        unfold rootOf
        rw [if_neg (by omega), hC, ← hi]
      rw [e]
      rfl
    · intro y hy
      obtain rfl : y = C := by simpa using hy
      exact hI
  | n + 1, i0, rows, C, F, rest, rows', roots, G, rest', hn, P, hC, hI, h => by
    unfold partsV at h
    obtain ⟨w, F1, r1, e1', h⟩ := bindHr_some h
    obtain ⟨x, F2, r2, e2', h⟩ := bindHr_some h
    obtain ⟨a, b, c⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2 b c
    have hi : i0 < f.parts.length - 1 := by omega
    obtain ⟨p1, o1, _, n1⟩ := sum_step (k := noVar 2 2) (atP_split f hi) rfl rfl rfl rfl
      (fun v hv => by simp [noVar] at hv) hok P hI e1'
    have n1' : F1.next = w.1.sEnd + 2 := n1
    have hw : w.1.sEnd = endOf f lo (.split i0) := o1.sEnd
    have hge : F.next ≤ w.1.sEnd := by
      rw [hw, P.next, ← (slotsIn_at (atP_split f hi)).1]
      unfold endOf
      omega
    have hlo : lo ≤ F.next := by rw [P.next]; omega
    have ej : jSplit f (i0 + 1) = jSplit f i0 + 1 := by unfold jSplit; omega
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := parts_out hok n (i0 + 1) (rows.push w.2)
      (Aff.slot (w.1.sEnd + 1)) F1 r1 x.1 x.2 _ _ (by omega) (by rw [ej]; exact p1)
      (by rw [hw]; rfl) (in_slot (by omega) (by omega)) e2'
    refine ⟨c1, fun y hy => c2 y (mem_push_of hy), ?_, ?_, by simp [c5], ?_, by omega⟩
    · intro i h1 h2
      by_cases hii : i = i0
      · subst hii
        refine ⟨w.2, c2 _ (mem_push_self _ _), ?_⟩
        have := o1
        rw [hC, hw] at this
        exact this
      · exact c3 i (by omega) h2
    · intro i hi'
      cases i with
      | zero =>
        have e : rootOf f lo (i0 + 0) = Aff.slot w.1.sEnd := by
          unfold rootOf
          rw [if_pos (by omega), hw]
          rfl
        rw [e]
        rfl
      | succ i =>
        have e : i0 + (i + 1) = i0 + 1 + i := by omega
        rw [e, List.getElem?_cons_succ]
        exact c4 i (by omega)
    · intro y hy
      rcases List.mem_cons.1 hy with h1 | h1
      · rw [h1]
        exact in_slot (by omega) (by omega)
      · exact c6 y h1

/-! ## The key trees -/

/-- The form in front of level m of part i's key tree. -/
def keyStart (f : LFace) (lo : Nat) (rs : List Fmt.RoundView) (i : Nat) : Nat → Aff :=
  startOf f lo rs (Stage.key i) (Stage.keyLine i) (rootOf f lo i)

theorem jKey_succ {i v : Nat} (h : f.parts[i]? = some v) : jKey f (i + 1) 0 = jKey f i 0 + 2 * v :=
    by
  unfold jKey
  rw [take_succ_get h, List.sum_append]
  simp
  omega

/-- **The key trees, from their return.** Here l lists the parts that are still to come, and i0 says
how many stand in front. -/
theorem keys_out (hok : Ok rs) : ∀ (l : List Nat) (i0 : Nat) (Cs : List Aff) (rows : Array Aff)
    (F : Fork) (rest : List Fmt.RoundView) (rows' : Array Aff) (keys : List (Array E × Aff)) (G : Fork)
    (rest' : List Fmt.RoundView),
    f.parts.drop i0 = l → Cs.length = l.length →
    (∀ t, t < l.length → Cs[t]? = some (rootOf f lo (i0 + t))) → (∀ C ∈ Cs, In lo F.next C) →
    Pos f lo rs (jKey f i0 0) F rest →
    keysV f (l.zipIdx i0) Cs rows F rest = some ((rows', keys), G, rest') →
    Pos f lo rs (jKey f (i0 + l.length) 0) G rest' ∧ (∀ y ∈ rows.toList, y ∈ rows'.toList) ∧
      (∀ i v m, i0 ≤ i → f.parts[i]? = some v → m < v → ∃ y ∈ rows'.toList,
        SumOut f lo rs (.key i m) (keyStart f lo rs i m) y (endOf f lo (.key i m))) ∧
      (∀ i v, i0 ≤ i → f.parts[i]? = some v → ∃ y ∈ keys, y.2 = keyStart f lo rs i v) ∧
      F.next ≤ G.next
  | [], i0, Cs, rows, F, rest, rows', keys, G, rest', hd, _, _, _, P, h => by
    unfold keysV at h
    obtain ⟨a, b, c⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2 b c
    have hlen : f.parts.length ≤ i0 := by
      have := congrArg List.length hd
      simp at this
      omega
    have none_ : ∀ i v, i0 ≤ i → f.parts[i]? = some v → False := by
      intro i v hi hv
      have := (List.getElem?_eq_some_iff.1 hv).1
      omega
    exact ⟨P, fun _ hy => hy, fun i v m hi hv _ => (none_ i v hi hv).elim,
      fun i v hi hv => (none_ i v hi hv).elim, Nat.le_refl _⟩
  | v :: l, i0, [], rows, F, rest, rows', keys, G, rest', _, hc, _, _, _, _ => by
    simp at hc
  | v :: l, i0, C :: Cs, rows, F, rest, rows', keys, G, rest', hd, hc, hC, hI, P, h => by
    rw [List.zipIdx_cons] at h
    unfold keysV at h
    obtain ⟨k, F1, r1, e1', h⟩ := bindHr_some h
    obtain ⟨y, F2, r2, e2', h⟩ := bindHr_some h
    obtain ⟨a, b, c⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2 b c
    have e1'' : vRun 0 v (f.orders i0) { rows := rows, point := #[], form := C } F rest =
        some (k, F1, r1) := e1'
    have hv : f.parts[i0]? = some v := by
      have := congrArg (fun x => x[0]?) hd
      simpa using this
    have hC0 : C = rootOf f lo i0 := by
      have := hC 0 (by simp)
      simpa using this
    obtain ⟨p1, q1, i1, n1⟩ := run_out (A := Stage.key i0) (B := Stage.keyLine i0) (m0 := 0)
      (s := { rows := rows, point := #[], form := C }) hok P (hI C (by simp)) v
      (fun m hm => by
        obtain ⟨x1, x2⟩ := atP_key f hv hm
        have e : jKey f i0 m = jKey f i0 0 + 2 * m := by unfold jKey; omega
        rw [e] at x1 x2
        refine ⟨x1, x2, ?_, rfl⟩
        rw [Nat.zero_add]
        rfl) e1''
    have hd' : f.parts.drop (i0 + 1) = l := by
      have := congrArg List.tail hd
      simpa using this
    obtain ⟨c1, c2, c3, c4, c5⟩ := keys_out hok l (i0 + 1) Cs k.rows F1 r1 y.1 y.2 _ _ hd'
      (by simpa using hc)
      (fun t ht => by
        have := hC (t + 1) (by simp; omega)
        rw [List.getElem?_cons_succ] at this
        rw [this]
        congr 2
        omega)
      (fun D hD => in_mono (hI D (List.mem_cons_of_mem _ hD)) n1)
      (by rw [jKey_succ hv]; exact p1) e2'
    refine ⟨?_, fun z hz => c2 z (q1.keep z hz), ?_, ?_, by omega⟩
    · have e : i0 + (v :: l).length = i0 + 1 + l.length := by simp; omega
      rw [e]
      exact c1
    · intro i v' m hi hv' hm
      by_cases hii : i = i0
      · subst hii
        obtain rfl : v' = v := by rw [hv] at hv'; exact (Option.some.inj hv').symm
        obtain ⟨z, hz, hS⟩ := q1.row m hm
        refine ⟨z, c2 z hz, ?_⟩
        unfold keyStart
        rw [← hC0]
        exact hS
      · exact c3 i v' m (by omega) hv' hm
    · intro i v' hi hv'
      by_cases hii : i = i0
      · subst hii
        obtain rfl : v' = v := by rw [hv] at hv'; exact (Option.some.inj hv').symm
        refine ⟨(k.point, k.form), by simp, ?_⟩
        unfold keyStart
        rw [← hC0]
        exact q1.form
      · obtain ⟨z, hz, e⟩ := c4 i v' (by omega) hv'
        exact ⟨z, List.mem_cons_of_mem _ hz, e⟩

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.parts_out
#print axioms ProofFile.Honest.K3.Good.jKey_succ
#print axioms ProofFile.Honest.K3.Good.keys_out
