-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MergesByName.lean: CONDITIONAL. OF THE PARTS OF THE LAYERS'
OWN ROUNDS (kind K4) THE LIST OF MERGES THAT IS READ OFF THE NAMES AND COUNTS (`mergesByName`,
Honest/BookWhole.lean) HOLDS THE LAST PART ALONE.

What is here. PUBLIC DATA ALONE. `mergesByName bs` lists, in its field ends, the address of every
part of the sub-protocols bs that is a masked sumcheck with just one end value and stands at a place
of the kind K4 or K11. It is the list that the function which builds the honest prover (`onlineProverFromPublicFiles`,
Honest/AtPure.lean) hands the book's maker. By Law/W/PlanRow.lean the parts of K4's sub-protocol are
a written row. Its last part is a masked sumcheck with one end value. Of the parts in front none is,
WHERE nEndT y IS NOT 1 (hE): they are single rounds, or masked sumchecks with 2, ledNO xl * NI,
nEndT y, at least 3, 2 and 2 end values; ledNO xl is 4 or 3, so the second of these is never 1.
Definitions, statements and proofs.

  `K4Ends`: a definition; it claims nothing: two counts of the plan are not 1: the end values of
      the two sumchecks over the tokens.
  `k4Ends_first`: its first half holds at every plan: no hypothesis. `k4Ends_of_second`: so the
      second half gives the whole.
  `k4Ends_of_layout`, `k4Ends_of_public`: both hold at every layout that the verifier's own
      function returns (the library's `laySizes_of_layout`, Johnson/Road/K4/PlanSizes.lean).
  `k4Ends_no`: where nEndT y = 1 the definition is false: an implication; NO SUCH PLAN IS
      EXHIBITED.
  `k4FrontUnits`, `k4Units_split`, `NoMerge`, `noMerge_test`, `k4Front_noMerge`: the row's units
      in front of the last; under hE none passes the list's test.
  `k4_merges_byName`: **of K4's addresses the list holds the last part's alone**: the two
      premises hfront and hmerge of Law/W/RowIsPlan.lean, at that list.
  `k4_rowIsPlan_byName`: **the ten fields of `K4RowIsPlan` at that list, with no premise on
      it.**
  `k4_noSeed`: no round of a sub-protocol that declares K4's entries is named "SEND seed".

Not shown here. hE: WHERE nEndT y IS 1 THE LIST HOLDS A SECOND ADDRESS OF K4's [by reading; no
theorem here shows it]; Honest/BookWhole.lean names that gap in its own docstring. The other
hypotheses: hnd, that no two of the sub-protocols stand at one place; hb, that b is one of them; hpl
and hr, that it stands at K4's place and declares the entries of K4's table; hpos, `K4Counts`. THAT
`mergesByName` IS THE FORMAT's LIST OF MERGES IS NOT SPOKEN OF: its own docstring says on which
three texts it rests. Nothing on a book, on coins, or on what a part sends. No example of the
hypotheses together has been through Lean.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RowIsPlan
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.Road.K4.PlanSizes
import Johnson.Road.HeadMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Road.K4 (laySizes_of_layout)
open OnBytes.Desc.First.K4 (entries k0)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block KindName)

variable {S Cl : Type} {Q : K4Pub}

/-! ## 1 Two counts are not 1 -/

/-- **Two counts of the plan are not 1**: the end values of the first and of the second sumcheck
over the tokens. A definition; it claims nothing. -/
def K4Ends (Q : K4Pub) : Prop :=
  ledNO Q.P.y.h.xl * Q.P.y.NI ≠ 1 ∧ nEndT Q.P.y ≠ 1

/-- **The first half holds at every plan**: ledNO xl is 4 or 3. No hypothesis. -/
theorem k4Ends_first (Q : K4Pub) : ledNO Q.P.y.h.xl * Q.P.y.NI ≠ 1 := by
  unfold ledNO
  split <;> omega

/-- CONDITIONAL: on h. So the second half gives the whole. -/
theorem k4Ends_of_second (h : nEndT Q.P.y ≠ 1) : K4Ends Q := ⟨k4Ends_first Q, h⟩

/-- CONDITIONAL: on hy. **BOTH AT A LAYOUT THAT THE VERIFIER's FUNCTION RETURNS.** -/
theorem k4Ends_of_layout {h : OnBytes.Model.Layer.Shape} {pc : List (List String)}
    (hy : OnBytes.Model.Layer.layout h pc = .ok Q.P.y) : K4Ends Q := by
  have L := laySizes_of_layout hy
  have h2 : 0 < 2 ^ h.ll := Nat.two_pow_pos h.ll
  refine ⟨?_, ?_⟩
  · rw [L.NI]
    unfold ledNO
    split <;> omega
  · unfold nEndT
    rw [L.NN, L.Lam]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega) (Nat.le_add_right _ _))

/-- CONDITIONAL: on hX and hQ. At the layers' record of the verifier's public part. -/
theorem k4Ends_of_public {pol KL : ByteArray} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hX : OnBytes.Model.Verify.publicOf pol KL lay = .ok X)
    (hQ : Q.P = X.layers) : K4Ends Q :=
  k4Ends_of_layout (by rw [hQ]; exact (OnBytes.Road.Hd.publicH_of_public hX).lay)

/-- CONDITIONAL: on h. Where nEndT y = 1 the definition is false. No such plan is exhibited. -/
theorem k4Ends_no (h : nEndT Q.P.y = 1) : ¬ K4Ends Q := fun c => c.2 h

/-! ## 2 The units in front of the last -/

/-- K4's row without its last unit. -/
def k4FrontUnits (Q : K4Pub) : List (List (String × Nat)) :=
  List.replicate (k0 Q.g) [("ZERO", 0)] ++
  [[("BAT-sigma", ledNS Q.P.y.h.xl * Q.P.y.NI)], [("JOIN", 0)], maskedP Q.P.rd.muV 1 2 2,
   [("LINE", 0)], [("BAT-sigma", ledNP Q.P.y.h.xl * Q.P.y.NI)],
   maskedP Q.P.y.h.lt 2 2 (ledNO Q.P.y.h.xl * Q.P.y.NI), maskedP Q.P.y.h.lt 2 1 (nEndT Q.P.y),
   [("BAT-sigma", 0)], maskedP Q.hp.lamS 1 2 (nStack Q.P Q.hp Q.g), maskedP Q.P.rd.muH 1 2 2,
   [("LINE", 0)], [("JOIN", 0)], maskedP Q.P.rd.muH2 1 2 2, [("LINE", 0)],
   [("BAT-sigma", if Q.g == 0 then 1 else 0)]]

/-- The row is these units and the merge's. -/
theorem k4Units_split (Q : K4Pub) :
    k4Units Q = k4FrontUnits Q ++ [maskedP Q.P.wsLay.lk 1 1 1] := by
  rw [k4Units_eq]
  unfold k4TailUnits k4FrontUnits
  rw [List.append_assoc]
  rfl

theorem k4FrontUnits_len (Q : K4Pub) : (k4FrontUnits Q).length = k0 Q.g + 15 := by
  unfold k4FrontUnits
  rw [List.length_append, List.length_replicate]
  rfl

/-- A unit that the list's test does not pass: one round under one of K4's four other names, or a
masked sumcheck whose end values are not one. A definition; it claims nothing. -/
def NoMerge (u : List (String × Nat)) : Prop :=
  (∃ n c, n ∈ plainNames ∧ u = [(n, c)]) ∨ ∃ k f y e, e ≠ 1 ∧ u = maskedP k f y e

/-- CONDITIONAL: on h. Such a unit is no masked sumcheck with one end value. -/
theorem noMerge_test {u : List (String × Nat)} (h : NoMerge u) (a : Addr) :
    ((⟨a, u⟩ : PartAt).isSum && (⟨a, u⟩ : PartAt).endScalars == 1) = false := by
  rcases h with ⟨n, c, hn, rfl⟩ | ⟨k, f, y, e, he, rfl⟩
  · have hs : (⟨a, [(n, c)]⟩ : PartAt).isSum = false := by
      show ((some n : Option String) == some "PSC epsilon") = false
      simp only [plainNames, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> decide
    rw [hs, Bool.false_and]
  · rw [endScalars_masked, beq_false_of_ne he, Bool.and_false]

/-- CONDITIONAL: on hE. **No unit in front of the last passes the test.** -/
theorem k4Front_noMerge (hE : K4Ends Q) : ∀ u ∈ k4FrontUnits Q, NoMerge u := by
  intro u hu
  unfold k4FrontUnits at hu
  rcases List.mem_append.1 hu with h | h
  · rw [List.eq_of_mem_replicate h]
    exact Or.inl ⟨_, _, by simp [plainNames], rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
      first
        | exact Or.inl ⟨_, _, by simp [plainNames], rfl⟩
        | exact Or.inr ⟨_, _, _, _, hE.1, rfl⟩
        | exact Or.inr ⟨_, _, _, _, hE.2, rfl⟩
        | exact Or.inr ⟨_, _, _, 2, by decide, rfl⟩
        | exact Or.inr ⟨_, _, _, _, (by unfold nStack; omega), rfl⟩

/-- The written row: the parts in front, and the merge's. -/
theorem k4PlanRow_split (Q : K4Pub) :
    k4PlanRow Q = ((k4FrontUnits Q).zipIdx.map fun x => (⟨k4Addr Q x.2, x.1⟩ : PartAt)) ++
      [⟨k4Addr Q (k0 Q.g + 15), maskedP Q.P.wsLay.lk 1 1 1⟩] := by
  unfold k4PlanRow
  rw [k4Units_split, List.zipIdx_append, List.map_append, k4FrontUnits_len, Nat.zero_add]
  rfl

/-! ## 3 The list of merges at K4's addresses -/

variable {b : Block S Cl}

/-- CONDITIONAL: on all five hypotheses. **OF K4's ADDRESSES THE LIST THAT IS READ OFF THE NAMES AND
COUNTS HOLDS THE LAST PART's ALONE.** -/
theorem k4_merges_byName {bs : List (Block S Cl)} (hnd : (bs.map (·.place)).Nodup) (hb : b ∈ bs)
    (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound))
    (hE : K4Ends Q) :
    (∀ i, i + 1 < (k4RowIn Q).length → k4Addr Q i ∉ (mergesByName bs).ends) ∧
      k4Addr Q ((k4RowIn Q).length - 1) ∈ (mergesByName bs).ends := by
  have hP : planParts b = k4PlanRow Q := k4_planParts hpl hr
  have hlast : (k4RowIn Q).length - 1 = k0 Q.g + 15 := by
    rw [k4RowIn_len]
    rfl
  refine ⟨fun i hi hmem => ?_, ?_⟩
  · rw [k4RowIn_len] at hi
    obtain ⟨p, hp, ea⟩ := List.mem_map.1 hmem
    obtain ⟨hp1, ht⟩ := List.mem_filter.1 hp
    obtain ⟨b', hb', hp'⟩ := List.mem_flatMap.1 hp1
    have hplace : p.addr.place = b'.place := by
      unfold planParts at hp'
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp'
      rfl
    have e0 : b' = b := by
      refine List.inj_on_of_nodup_map hnd hb' hb ?_
      rw [← hplace, ea, hpl]
      rfl
    rw [e0, hP, k4PlanRow_split] at hp'
    rcases List.mem_append.1 hp' with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      have hu : NoMerge x.1 := k4Front_noMerge hE x.1 (List.fst_mem_of_mem_zipIdx hx)
      have hf := noMerge_test hu (k4Addr Q x.2)
      rw [hf, Bool.false_and] at ht
      exact Bool.false_ne_true ht
    · obtain rfl := List.mem_singleton.1 h
      have e1 : k0 Q.g + 15 = i := congrArg Addr.part ea
      omega
  · rw [hlast]
    refine List.mem_map.2 ⟨⟨k4Addr Q (k0 Q.g + 15), maskedP Q.P.wsLay.lk 1 1 1⟩, ?_, rfl⟩
    refine List.mem_filter.2 ⟨List.mem_flatMap.2 ⟨b, hb, ?_⟩, ?_⟩
    · rw [hP, k4PlanRow_split]
      exact List.mem_append_right _ (List.mem_singleton.2 rfl)
    · have hs : (⟨k4Addr Q (k0 Q.g + 15), maskedP Q.P.wsLay.lk 1 1 1⟩ : PartAt).isSum = true := by
        show ((some "PSC epsilon" : Option String) == some "PSC epsilon") = true
        decide
      rw [hs, endScalars_masked]
      rfl

/-- CONDITIONAL: on all six hypotheses. **THE FORM's TEN FIELDS AT THAT LIST: NO PREMISE ON THE LIST
OF MERGES.** -/
theorem k4_rowIsPlan_byName {bs : List (Block S Cl)} (hnd : (bs.map (·.place)).Nodup)
    (hb : b ∈ bs) (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound))
    (hpos : K4Counts Q) (hE : K4Ends Q) :
    ∃ A m, K4RowIsPlan (mergesByName bs) b Q A m ∧
      m.addr = k4Addr Q ((k4RowIn Q).length - 1) :=
  k4_rowIsPlan hpl hr hpos (k4_merges_byName hnd hb hpl hr hE).1
    (k4_merges_byName hnd hb hpl hr hE).2

/-- CONDITIONAL: on hr. No round of a sub-protocol that declares K4's entries is named "SEND seed".
-/
theorem k4_noSeed
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed" := by
  intro r hrm
  rw [hr] at hrm
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hrm
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 he
  show d.name.name ≠ "SEND seed"
  cases d.name <;> decide

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4Ends_first
#print axioms ProofFile.Honest.K4.W.k4Ends_of_second
#print axioms ProofFile.Honest.K4.W.k4Ends_of_layout
#print axioms ProofFile.Honest.K4.W.k4Ends_of_public
#print axioms ProofFile.Honest.K4.W.k4Ends_no
#print axioms ProofFile.Honest.K4.W.k4Units_split
#print axioms ProofFile.Honest.K4.W.k4FrontUnits_len
#print axioms ProofFile.Honest.K4.W.noMerge_test
#print axioms ProofFile.Honest.K4.W.k4Front_noMerge
#print axioms ProofFile.Honest.K4.W.k4PlanRow_split
#print axioms ProofFile.Honest.K4.W.k4_merges_byName
#print axioms ProofFile.Honest.K4.W.k4_rowIsPlan_byName
#print axioms ProofFile.Honest.K4.W.k4_noSeed
