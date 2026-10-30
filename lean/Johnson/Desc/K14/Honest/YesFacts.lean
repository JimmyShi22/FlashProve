--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesFacts.lean: facts on a state of the linear claim's shared rounds, in
which the places' premises are said.

The shared rounds (Johnson/Desc/K14/Text.lean) test no equation. What a place asks is asked of
public shapes, of the key, of the form of a round, and of the state that the places in front have
left. No fact here speaks of a value that the prover sends.

Main names:
  GroupIs T g code maskCode ms   the group number g is there, has these codes, is in no test, and
                      its members are those of the list ms
  MsgIs T o s         the message number o is there with the shape s, is sampled, and its pad's
                      places are those that the shape gives
  contains_of, not_contains_of   membership as the ground's test reads it
  FrontU p d ms       the facts in front of "(rec_gamma)" (ms = []) and of "LOC" (ms = [o_u])
  ShapeSizes, shapeSizes_of     the numbers that the places read off the public shape's conditions
  sits_u, sits_omega  o_u and o_omega sit in every group that has them as members, their own pads
                      behind the vectors that they hold
  Sits.mono, weights_size   small tools

What is not claimed. That the facts hold at any state. Nothing on what a laid constraint means, on
soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesLoc
import Johnson.Desc.K14.Honest.YesFold
import Johnson.Desc.K14.Honest.YesState
import Johnson.Desc.K14.Law.Weights
import Johnson.Desc.K14.Law.Run
import Johnson.Desc.Own.RoomAtU
import Johnson.Desc.Own.LinAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc.Own (linFits)
open Desc.K14.Law (eqTable_size le_roundUp vectorRoom_le)

/-! ## Facts on a state -/

/-- The group number g as the shared rounds need it. ms: its members. -/
def GroupIs (T : Statement) (g code maskCode : Nat) (ms : List Nat) : Prop :=
  ∃ G, T.groups[g]? = some G ∧ G.code = code ∧ G.maskCode = maskCode ∧ G.inRun = false ∧
    ∀ o, o ∈ G.members ↔ o ∈ ms

/-- The message number o as a sending leaves it, but for the groups that it notes and its ledger
(the statement's field of that name, which counts a message's free mask entries). -/
def MsgIs (T : Statement) (o : Nat) (s : OracleShape) : Prop :=
  ∃ x, T.oracles[o]? = some x ∧ x.shape = s ∧ x.sampled = true ∧
    x.pad = ((Send.pad T.codes s).getD []).map fun p => (p.part, p.index)

/-- Membership as the ground's test reads it. -/
theorem contains_of {G : Group} {ms : List Nat} (h : ∀ o, o ∈ G.members ↔ o ∈ ms) (o : Nat)
    (ho : o ∈ ms) : G.members.contains o = true :=
  Array.contains_iff_mem.2 ((h o).2 ho)

@[inherit_doc contains_of]
theorem not_contains_of {G : Group} {ms : List Nat} (h : ∀ o, o ∈ G.members ↔ o ∈ ms) (o : Nat)
    (ho : o ∉ ms) : G.members.contains o = false := by
  cases hc : G.members.contains o with
  | false => rfl
  | true => exact absurd ((h o).1 (Array.contains_iff_mem.1 hc)) ho

/-- In front of "(rec_gamma)" and of "LOC": the public shape fits; the shared point is noted; o_u is
noted with its layout and stands as its sending left it; its group is there. ms: that group's
members. -/
structure FrontU (p : Par) (d : St) (ms : List Nat) : Prop where
  lin : linFits d.st.codes p.S = true
  psi : d.loc.psiSh.length = p.S.kCol
  lay : d.loc.oU.lay = vectorLay d.st.codes p.S.fold.u p.S.fold.rowsHigh
  gU : GroupIs d.st d.loc.gU p.S.fold.u.code p.S.sharedMaskCode ms
  u : MsgIs d.st d.loc.oU.oracle p.S.fold.u

/-- The numbers that the places read off the public shape. -/
structure ShapeSizes (codes : Codes) (S : LinShape) : Prop where
  indexOk : S.fold.index.ok = true
  cube : S.fold.index.cubeBits ≤ (vectorLay codes S.fold.u S.fold.rowsHigh).bits
  tail : S.fold.tailFirst + S.fold.index.code.r ≤
    2 ^ (vectorLay codes S.fold.u S.fold.rowsHigh).bits
  aligned : S.fold.tailFirst % 2 ^ S.fold.index.code.logR = 0
  ell : S.fold.index.code.ell ≤ S.fold.entries
  matrix : S.matrixRows * 2 ^ S.kLo ≤ S.fold.entries
  kRow : S.kRow ≤ (vectorLay codes S.omega S.omegaRowsHigh).bits
  kBoth : S.kLo + S.kRow ≤ (vectorLay codes S.fold.u S.fold.rowsHigh).bits

/-- The public shape's conditions give these numbers. -/
theorem shapeSizes_of (codes : Codes) (S : LinShape) (h : linFits codes S = true) :
    ShapeSizes codes S := by
  have hok : linOk codes S = true := (VerifiableInference.Desc.Own.linFits_eq _ _).symm.trans h
  have hi := Law.index_ok_of_linOk codes S hok
  obtain ⟨hs, hf, _, _, _, _, hrO, _⟩ := (VerifiableInference.Desc.Own.linFits_iff codes S).1 h
  have hE : S.fold.entries ≤ 2 ^ (vectorLay codes S.fold.u S.fold.rowsHigh).bits := by
    have := hf.2.2
    rw [VerifiableInference.Desc.Own.roomOf_eq] at this
    exact Nat.le_trans this (vectorRoom_le _ _ _)
  have hO : S.matrixRows ≤ 2 ^ (vectorLay codes S.omega S.omegaRowsHigh).bits := by
    rw [VerifiableInference.Desc.Own.roomOf_eq] at hrO
    exact Nat.le_trans hrO (vectorRoom_le _ _ _)
  have e2 : S.fold.index.code.ell ≤ S.fold.tailFirst := le_roundUp _ _ (Nat.two_pow_pos _)
  have e3 : S.fold.entries = S.fold.tailFirst + S.fold.index.code.r := rfl
  have e1 : S.fold.index.plain ≤ S.fold.index.code.ell := Nat.sub_le _ _
  have a6 : S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain := hs.2.2.2.2.2.1
  have a2 : 1 ≤ S.matrixRows := hs.2.1
  have hU : S.matrixRows * 2 ^ S.kLo ≤ 2 ^ (vectorLay codes S.fold.u S.fold.rowsHigh).bits := by
    omega
  refine ⟨hi, Law.ceilLog2_le _ _ (by omega), by omega, ?_, by omega, by omega,
    Law.ceilLog2_le _ _ hO, ?_⟩
  · unfold FoldeqShape.tailFirst
    exact Nat.mul_mod_left _ _
  · have k1 : 2 ^ S.kLo ≤ 2 ^ (vectorLay codes S.fold.u S.fold.rowsHigh).bits :=
      Nat.le_trans (Nat.le_mul_of_pos_left _ a2) hU
    have k2 : S.kLo ≤ (vectorLay codes S.fold.u S.fold.rowsHigh).bits :=
      (Nat.pow_le_pow_iff_right (by decide)).1 k1
    have k3 : S.matrixRows ≤ 2 ^ ((vectorLay codes S.fold.u S.fold.rowsHigh).bits - S.kLo) := by
      refine Nat.le_of_mul_le_mul_right ?_ (Nat.two_pow_pos S.kLo)
      rw [← Nat.pow_add, Nat.sub_add_cancel k2]
      exact hU
    have k4 := Law.ceilLog2_le _ _ k3
    unfold LinShape.kRow
    omega

/-- o_u sits in every group that has it as a member, its own pad behind the folded row. -/
theorem sits_u {T : Statement} {S : LinShape} {o : Nat} (hlin : linFits T.codes S = true)
    (hu : MsgIs T o S.fold.u) (G : Group) (hm : G.members.contains o = true) :
    Sits T G o (vectorLay T.codes S.fold.u S.fold.rowsHigh) S.fold.entries := by
  obtain ⟨x, hx, hs, _, hp⟩ := hu
  obtain ⟨_, hf, _⟩ := (VerifiableInference.Desc.Own.linFits_iff T.codes S).1 hlin
  obtain ⟨hsh, _, hroom⟩ := hf
  exact sits_of_msg T G o x S.fold.u S.fold.rowsHigh S.fold.entries hx hs hp hm hsh.2.2.1
    hsh.2.2.2.1 (by have := hsh.2.2.2.2.1; omega)
    (VerifiableInference.Desc.Own.entries_pos S.fold hsh.1.1.2.2.1) hroom

/-- o_omega sits in every group that has it as a member, its own pad behind the matrix's rows. -/
theorem sits_omega {T : Statement} {S : LinShape} {o : Nat} (hlin : linFits T.codes S = true)
    (ho : MsgIs T o S.omega) (G : Group) (hm : G.members.contains o = true) :
    Sits T G o (vectorLay T.codes S.omega S.omegaRowsHigh) S.matrixRows := by
  obtain ⟨x, hx, hs, _, hp⟩ := ho
  obtain ⟨hsh, _, _, _, _, _, hroom, _⟩ :=
    (VerifiableInference.Desc.Own.linFits_iff T.codes S).1 hlin
  have hv := hsh.2.2.2.2.2.2.1
  exact sits_of_msg T G o x S.omega S.omegaRowsHigh S.matrixRows hx hs hp hm
    (Nat.pos_of_ne_zero hv.2.1) hv.2.2.1 (by have := hv.2.2.2; omega) hsh.2.1 hroom

/-- A smaller bound on where a pad may begin. -/
theorem Sits.mono {T : Statement} {G : Group} {o : Nat} {lay : VectorLay} {n m : Nat}
    (h : Sits T G o lay n) (hm : m ≤ n) : Sits T G o lay m :=
  ⟨h.member, h.table, h.bits, h.small, fun x hx q hq e =>
    ⟨(h.pad x hx q hq e).1, Nat.le_trans hm (h.pad x hx q hq e).2⟩⟩

/-- The weights of the committed table's rows are as many as the rows. -/
theorem weights_size (p : Par) (d : St) (hpsi : d.loc.psiSh.length = p.S.kCol) :
    (weights p.S d.loc).size = p.S.fold.index.rows := by
  unfold weights
  rw [eqTable_size]
  unfold gamma IndexShape.rows
  rw [List.length_drop, hpsi]
  unfold LinShape.kCol
  congr 1
  omega

end Desc.K14.Honest

#print axioms Desc.K14.Honest.contains_of
#print axioms Desc.K14.Honest.not_contains_of
#print axioms Desc.K14.Honest.shapeSizes_of
#print axioms Desc.K14.Honest.sits_u
#print axioms Desc.K14.Honest.sits_omega
#print axioms Desc.K14.Honest.Sits.mono
#print axioms Desc.K14.Honest.weights_size
