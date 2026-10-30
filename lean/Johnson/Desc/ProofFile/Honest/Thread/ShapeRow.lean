-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ShapeRow.lean: the division into structure and values
(Honest/Thread/Shape.lean) at a toy example. At the `Thread` over the toy list of parts
(Honest/Thread/ThrRow.lean) all four hypotheses hold, the named public hypothesis is evaluated by
Lean's kernel, and the rule `accepted_of_shape` gives that list's acceptance once more. With one
general lemma: where there is a prover's side, what was played and read passes the step's own tests
on rounds and columns. Theorems about these files' own made-up objects, but for that lemma. None is
one of the library's goals.

  1  `fitsAt_half`   general: `FitsAt` at a sub-protocol at which there is a prover's side
  2  `Zy`   the example's shape: the verifier's three fields, the second as a Bool
  3  `typed_row`, `yes_row` (by `decide`), `first_row`, `carries_row`, `returns_row`, `fitsAt_row`,
     `values_row`, `accepted_by_shape`   the shape is typed; the rule's six hypotheses hold; the
     acceptance

Limits.
  * A toy example: no sub-protocol of the three has a guard on the shape: `g` passes the shape on,
    and returns an error beyond the third sub-protocol; one of the three has a named test on values.
    So the hypothesis is met by a run of three steps that do nothing: it shows that the hypotheses
    fit together and that the kernel can evaluate such a hypothesis at a toy description, not that a
    real kind's guards can be written so.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Shape
import Johnson.Desc.ProofFile.Honest.Thread.ThrRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

/-! ## 1 Where there is a prover's side -/

/-- **Where there is a prover's side, what was played and read passes the step's own tests on rounds
and columns.** A lemma on this folder's own functions and definitions. -/
theorem fitsAt_half {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : Nat}
    {blk : Block S Cl} {g : Placed V W X} (hblk : T.bs[b]? = some blk)
    (hf : (T.hs.find? fun g => g.place == blk.place) = some g)
    (hr : g.rounds = blk.rounds.length) (ho : blk.oracles.length = blk.rounds.length) :
    FitsAt T b := by
  intro blk' hblk' k m E ds y cols hd hMv
  rw [hblk] at hblk'
  cases hblk'
  unfold Thread.Moved at hMv
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hMv
  obtain ⟨c, -, rfl⟩ := steps_one_half hf hl
  exact (fits_played hr ho hy hd hc).1

namespace Toy
open VerifiableInference.Desc (need noDigest step_iff)
open VerifiableInference.Desc.BlockToy (St send₃)

/-! ## 2 The example's shape -/

/-- **The example's shape.** -/
def Zy : Shape St :=
  { Sh := Nat × Bool × Nat
    sh := fun s => (s.total, s.own.isSome, s.claimed)
    g := fun b a => if b < 3 then .ok a else .error "the row has three members"
    vals := fun b _ rs gs => if b == 1 then sameWord gs (rs.map (·.vals)) else true }

/-! ## 3 The hypotheses hold -/

/-- The example's type of shapes holds no field element. -/
theorem typed_row : Zy.Typed := .prod .nat (.prod .bool .nat)

/-- **The named public hypothesis, evaluated by the kernel.** -/
theorem yes_row : Zy.yes (0, false, 0) 3 = true := by decide

theorem first_row : ∀ (k : Coins By) (w : L) (h : List Fmt.Drawn) (s₀ : St),
    Ty.valid w → Ty.begun k w h s₀ → Zy.sh s₀ = (0, false, 0) := by
  intro _ _ _ s₀ _ h
  have h' : s₀ = st₀ := h
  rw [h']
  rfl

theorem carries_row (j : Nat) : Carries Ty.bs Ty.ft Zy j := by
  intro blk hblk s rs cols s' n t h hg
  have e := step_same (List.mem_of_getElem? hblk) h
  subst e
  match j, hblk, hg with
  | 0, _, hg => exact (Except.ok.inj hg).symm
  | 1, _, hg => exact (Except.ok.inj hg).symm
  | 2, _, hg => exact (Except.ok.inj hg).symm
  | _ + 3, hblk, _ => cases hblk

theorem returns_row (b : Nat) : Returns Ty.bs Ty.ft Zy b := by
  intro blk hblk s rs cols t _ _ hv
  match b, hblk, hv with
  | 0, hblk, _ =>
    cases Option.some.inj hblk
    exact ⟨s, rfl⟩
  | 1, hblk, hv =>
    cases Option.some.inj hblk
    have hv' : sameWord (tellB.shown Fy.lastChainFirstTreeNumber rs cols) ((rs.map noDigest).map (·.vals)) =
      true := hv
    refine ⟨s, ?_⟩
    show (need "tell.the-word" (sameWord (tellB.shown Fy.lastChainFirstTreeNumber rs cols)
      ((rs.map noDigest).map (·.vals)))).map (fun _ => s) = .ok s
    rw [hv']
    rfl
  | 2, hblk, _ =>
    cases Option.some.inj hblk
    exact ⟨s, rfl⟩
  | _ + 3, hblk, _ => cases hblk

theorem fitsAt_row (b : Nat) : FitsAt Ty b := by
  match b with
  | 0 => exact fitsAt_half Ty (blk := send₃) rfl find_send rfl rfl
  | 1 => exact fitsAt_half Ty (blk := tellB) rfl find_tell rfl rfl
  | 2 => exact fitsAt_half Ty (blk := askQ) rfl find_ask rfl rfl
  | _ + 3 =>
    intro blk hblk
    cases hblk

theorem values_row (b : Nat) : Values Ty Zy (fun _ _ _ => none) b := by
  intro blk hblk k s m E ds y cols hA hd _ _ hMv
  match b, hblk, hA with
  | 0, _, _ => rfl
  | 1, hblk, hA =>
    have hS := stepped_of_runs hMv (runs_member hblk hA hd)
    cases Option.some.inj hblk
    unfold Thread.Stepped at hS
    have hdec := ((step_iff _ _ _ _ _ _ _).1 hS.2).2.1
    have h' : (need "tell.the-word" (sameWord (tellB.shown Fy.lastChainFirstTreeNumber (roundsOf y.1) cols)
      (((roundsOf y.1).map noDigest).map (·.vals)))).map (fun _ => s) = .ok s := hdec
    show sameWord (tellB.shown Fy.lastChainFirstTreeNumber (roundsOf y.1) cols)
      (((roundsOf y.1).map noDigest).map (·.vals)) = true
    cases hw : sameWord (tellB.shown Fy.lastChainFirstTreeNumber (roundsOf y.1) cols)
      (((roundsOf y.1).map noDigest).map (·.vals)) with
    | true => rfl
    | false =>
      rw [hw] at h'
      cases h'
  | 2, _, _ => rfl
  | _ + 3, hblk, _ => cases hblk

/-- **The example's acceptance once more, by the rule.** -/
theorem accepted_by_shape {b : Nat} (hb : b < 3) : Accepted Ty (fun _ _ _ => none) b :=
  accepted_of_shape Ty Zy (n := 3) (Nat.le_refl 3) hb yes_row first_row carries_row
    (returns_row b) (fitsAt_row b) (values_row b)

end Toy
end ProofFile.Honest

#print axioms ProofFile.Honest.fitsAt_half
#print axioms ProofFile.Honest.Toy.typed_row
#print axioms ProofFile.Honest.Toy.yes_row
#print axioms ProofFile.Honest.Toy.first_row
#print axioms ProofFile.Honest.Toy.carries_row
#print axioms ProofFile.Honest.Toy.returns_row
#print axioms ProofFile.Honest.Toy.fitsAt_row
#print axioms ProofFile.Honest.Toy.values_row
#print axioms ProofFile.Honest.Toy.accepted_by_shape
