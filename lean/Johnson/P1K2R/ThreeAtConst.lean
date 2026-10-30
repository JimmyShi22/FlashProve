-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/ThreeAtConst.lean: AT EVERY PLACE OF THE CODE SWITCH IN THE COMPOSED MEANING's
    CONSTANT's OWN LIST OF PLACES, OF THE PIECE THAT STANDS THERE IN ITS OWN ROW: THE FIRST THREE
    CLAUSES OF WHAT IS OWED AT A PLACE (`K2PlaceOwes`, Johnson/Top/H0/K2Ties/Counted.lean), UNDER
    THE CONSTANT's HEAD ALONE. Two definitions, five theorems. A law file: no sub-protocol imports
    it.

Why. Johnson/P1K2R/PlaceThree.lean left three joins open: that the head's chain is the chain of the
    proof file's description of which Johnson/P1K2R/SitsNoMark.lean speaks; that the numbers 14 l +
    2, 339 and 353 are the places of the kind; that the sub-protocol behind the last segment stands
    at number 353 of the flat list. They are made here.

What is said.
  `spotB`, `spotAtB`, `spots_full`: BY LEAN's KERNEL, at the written full list of segments: a place
      of the kind
      K2 stands at a number i with i = 14 l + 2 for some 1 ≤ l ≤ 23, or 339, or 353: ONE WAY ONLY;
          the other way is `places_full` (Johnson/Top/H0/K2Ties/Table.lean). `spots_can_fail`: a
          negative test. `k2_spots`: the same as a sentence.
  `sitsLeftU_same`: `SitsLeftU` passes to a sub-protocol with the same rounds and decision and a
      narrower test on the plan.
  `k02_leftU_at`: under the head `P5J.AtMg` at the second hash function: at every place i of the
      kind in `P5J.At.ps` the head's chain holds a sub-protocol b at i with `SitsLeftU b`. CALLS:
      `k02_leftU_file`; `IM.Open.unique` (Johnson/IMR/SeatOpen.lean: the parameters
      are functions of the three files) and `IM.back_numbers` (Johnson/IMR/BackSeat.lean); the
      head's own fields laid.value, laid.planOk, laid.opened.
  `k2_three_at_const`: so, with L's three lists the description's own: the piece q at i is `k2Q
      ((below B).lift …) q.base d₁ d₂ extq`, it accepts at no marked state (in `K2PlaceOwes`' own
      form), B sits on the kind's at numbers p behind a door with `LeftDoor`, and the two written
      rounds have the declared entries and kinds.

Limits. THE NUMBERS p ARE "SOME p": that they are the numbers at which the sentence on the carried
    claim is spent is another file's (by its head: K2Caller/SitsAtP.lean, under a named test); NOT
    JOINED. THE FOURTH CLAUSE, `K2AllOwes`, IS NOT TOUCHED. A member of the head is proved at
    `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.PlaceThree
import Johnson.IMR.BackSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes.Maker Iop
open VerifiableInference.Desc (Block Chain Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind ownPiece)
open VerifiableInference.Desc.First.K2Caller (k2Q)
open H2K.JointK (Sits)
open _root_.Run (ckP)
open ProofFile (Cl)

/-- The numbers at which a code switch stands. -/
def spotB (i : ℕ) : Bool := (i % 14 == 2 && decide (16 ≤ i) && decide (i ≤ 324)) || i == 339 || i ==
    353

/-- At number i of the written full list: no code switch, or one of these numbers. -/
def spotAtB (i : ℕ) : Bool :=
  match (flatPlacesOf linksFull true)[i]? with
  | some a => !(a.kind == KindName.K2) || spotB i
  | none => true

theorem spots_full : (List.range 358).all spotAtB = true := by decide +kernel

/-- A negative test: "every place of the kind stands at number 353" rejects. -/
theorem spots_can_fail : (List.range 358).all (fun i => ((flatPlacesOf linksFull true)[i]?).all fun
    a => !(a.kind == KindName.K2) || decide (i = 353)) = false := by decide +kernel

theorem k2_spots (i : ℕ) (a : Place) (ha : (flatPlacesOf linksFull true)[i]? = some a) (hk : a.kind
    = KindName.K2) : (∃ l, 1 ≤ l ∧ l < 24 ∧ i = 14 * l + 0 + 2) ∨ i = 14 * 24 + 1 + 2 ∨ i = 353 :=
    by
  have hi : i < 358 := by
    have h1 := (List.getElem?_eq_some_iff.1 ha).1
    have h2 : (flatPlacesOf linksFull true).length = 358 := by decide +kernel
    omega
  have h := List.all_eq_true.1 spots_full i (List.mem_range.2 hi)
  unfold spotAtB at h
  rw [ha] at h
  have h' : (!(a.kind == KindName.K2) || spotB i) = true := h
  have hs : spotB i = true := by
    rw [hk] at h'
    simpa using h'
  unfold spotB at hs
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  rcases hs with (⟨⟨h1, h2⟩, h3⟩ | h) | h
  · exact Or.inl ⟨i / 14, by omega, by omega, by omega⟩
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr h)

theorem sitsLeftU_same {b b' : Block S Cl} (h : SitsLeftU b) (hr : b'.rounds = b.rounds) (hd :
    b'.decide = b.decide) (hp : b'.planOk = true → b.planOk = true) : SitsLeftU b' := by
  obtain ⟨p, enter, leave, hS, hD, hE⟩ := h
  exact ⟨p, enter, leave, hS.same b' hr hd hp, hD, hE⟩

/-- **At every place of the kind in the constant's own list.** -/
theorem k02_leftU_at {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np :
                  H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (i : ℕ) (a
                                    : Place) (ha : P5J.At.ps[i]? = some a) (hk : a.kind = KindName.K2) : ∃ b : Block S Cl,
    cF.blocksInOrder[i]? = some b ∧ SitsLeftU b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Z', Bs', base', c', A', B', O', h1, h2, h3⟩ := k02_leftU_file h.scope h.reads h.laid.value
      h.laid.planOk
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := O.unique O'
  rcases k2_spots i a ha hk with ⟨l, a1, a24, rfl⟩ | rfl | rfl
  · exact h1 l a1 a24
  · exact h2
  · obtain ⟨b, hb, hU⟩ := h3
    exact ⟨_, (IM.back_numbers h.scope h.reads O).1 0 b hb, sitsLeftU_same hU rfl rfl fun e =>
        (Bool.and_eq_true _ _ ▸ e : _ ∧ _).1⟩

/-- **The first three clauses, at every place of the kind, under the head alone.** -/
theorem k2_three_at_const {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np :
                  H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (L :
                                    P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (q₁ : (P5J.F0T
                                                OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁) (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np
                                                                     cF).shared.blocksInOrder = L.c₂ :: L.k₂) (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ ::
                                                                              L.k₃) (i : ℕ) (q) (a : Place) (hq : (h.row L)[i]? = some q) (ha : P5J.At.ps[i]? = some a) (hk :
                                                                              a.kind = KindName.K2) :
    ∃ (B : Block S Cl) (p : P2) (enter : S → Except String S) (leave : S → S → Except String S) (d₁
        d₂ : RDT) (extq : _), cF.blocksInOrder[i]? = some B ∧ Sits B (codeSwitchKind p : Block S Unit) enter leave ∧
        LeftDoor enter leave ∧ q = k2Q ((below B).lift Prod.snd fun t s => (t.1, s)) q.base d₁ d₂
        extq ∧ (∀ a τ b, (ownPiece (k2Q ((below B).lift Prod.snd fun t s => (t.1, s)) q.base d₁ d₂
        extq) B (fun _ _ w => w) (k2Q ((below B).lift Prod.snd fun t s => (t.1, s)) q.base d₁ d₂
        extq).err).ior.red.out a τ = some b → a.1.failed = none) ∧ [d₁, d₂].map (·.entry) =
        (VerifiableInference.Desc.First.K2.rounds p).map (·.entry) ∧ ∀ d ∈ [d₁, d₂], Fmt.kindOf
        d.entry.name = some d.kind := by
  obtain ⟨B, hB, p, enter, leave, hS, hD, hE⟩ := k02_leftU_at h i a ha hk
  have hi : i < 357 := by
    rcases k2_spots i a ha hk with ⟨l, _, _, rfl⟩ | rfl | rfl <;> omega
  obtain ⟨d₁, d₂, extq, e, he, hkk⟩ := k2_written_at_row h L q₁ q₂ q₃ i q hq hi B hB p hS.rounds
  exact ⟨B, p, enter, leave, d₁, d₂, extq, hB, hS, hD, e, k2_unmarked_at p B enter leave hS hD hE _
      _ d₁ d₂ extq, he, hkk⟩

end P1K2

#print axioms P1K2.spots_full
#print axioms P1K2.spots_can_fail
#print axioms P1K2.k2_spots
#print axioms P1K2.sitsLeftU_same
#print axioms P1K2.k02_leftU_at
#print axioms P1K2.k2_three_at_const
