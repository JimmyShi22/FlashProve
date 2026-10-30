-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/Laid.lean: WHEN THE CODE SWITCH's SENDING IS LAID, AND OF WHAT:
`messageRows` and `rowsAll` (Honest/K2/Sending.lean) read back in full, and shown to RETURN under
the shared sending's public test. A definition that the statements speak of, statements and
proofs.

  `laidRows`     the rows that `messageRows` returns, of the four arrays of coins that it has read:
                 its own last lines, under a name
  `messageRows_laid`   a laying that returns: its two tests on the shape said yes; its stretch has
                 just the count `laidDue`; its four reads returned; its rows are `laidRows` of them
  `messageRows_returns`   the other way: where the shape fits and the stretch has that count, the
                 laying returns
  `rowsAll_fits`   a sending's laying that returns has passed the shared sending's public test
  `rowsAll_returns`   THE OTHER WAY: UNDER THAT TEST THE SENDING's LAYING RETURNS, at all coins,
                 main rows and tables: a criterion in one public test, with no run

Limits. Whether a laying returns, and which array is read where: no sentence on what a coin is for.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc.K2.Honest (zeroG)
open Johnson.Prover.Send (Rows)
open Reads

/-- **The rows that `messageRows` returns**, of what it has read: cF, cE: the main rows' coins in
their field; cM: the mask rows' entries, or a fresh mask's coefficients; cT: the mask rows'
tails. -/
def laidRows (table : FreshTable) (codes : OnBytes.Codes) (s : OnBytes.OracleShape)
    (fold : Option Nat) (data : Nat → Nat → Cb.Gl.E) (cF : Array Cb.Gl.F)
    (cE cM cT : Array Cb.Gl.E) : Rows :=
  { mainE := fun b j =>
      if !(s.mainDeg == 3 &&
          (decide (b < s.mainRows) && decide (j < (codes.base.getD s.code default).ell))) then
        zeroG else
      match padAtOf codes s b j with
      | some t => cE.getD (s.mainRows * (codes.base.getD s.code default).r + t) zeroG
      | none => data b j
    mainF := fun b j =>
      if s.mainDeg == 3 ||
          !(decide (b < s.mainRows) && decide (j < (codes.base.getD s.code default).ell)) then
        OnBytes.Slice.toF 0 else
      match padAtOf codes s b j with
      | some t =>
        cF.getD (s.mainRows * (codes.base.getD s.code default).r + t) (OnBytes.Slice.toF 0)
      | none => (data b j).c0
    mainTlE := fun b q =>
      if s.mainDeg == 3 &&
          (decide (b < s.mainRows) && decide (q < (codes.base.getD s.code default).r)) then
        cE.getD (b * (codes.base.getD s.code default).r + q) zeroG
      else zeroG
    mainTlF := fun b q =>
      if !(s.mainDeg == 3) &&
          (decide (b < s.mainRows) && decide (q < (codes.base.getD s.code default).r)) then
        cF.getD (b * (codes.base.getD s.code default).r + q) (OnBytes.Slice.toF 0)
      else OnBytes.Slice.toF 0
    mask := fun r i =>
      if !(decide (r < s.maskRows) && decide (i < (codes.mask.getD s.maskCode default).ell)) then
        zeroG else
      match fold with
      | some n => table n (OnBytes.ceilLog2 s.maskRows) (cM.getD · zeroG) r i
      | none => cM.getD (i * s.maskRows + r) zeroG
    maskTl := fun r q =>
      if decide (r < s.maskRows) && decide (q < (codes.mask.getD s.maskCode default).r) then
        cT.getD (r * (codes.mask.getD s.maskCode default).r + q) zeroG
      else zeroG }

/-- **A laying that returns, read back in full.** -/
theorem messageRows_laid {table : FreshTable} {codes : OnBytes.Codes} {s : OnBytes.OracleShape}
    {fold : Option Nat} {data : Nat → Nat → Cb.Gl.E} {k : Stretch} {R : Rows}
    (h : messageRows table codes s fold data k = .ok R) :
    VerifiableInference.Desc.Own.sentShapeFits codes s = true ∧
      (∀ n, fold = some n → K1.rideFits codes s ⟨n, OnBytes.ceilLog2 s.maskRows⟩ = true) ∧
      k.due = laidDue codes s fold ∧
      ∃ (cF : Array Cb.Gl.F) (cE cM cT : Array Cb.Gl.E),
        k.fs 0 (countF codes s) = .ok cF ∧ k.es 0 (fromE codes s) = .ok cE ∧
        k.es (fromE codes s) (inMaskOf codes s fold) = .ok cM ∧
        k.es (fromE codes s + inMaskOf codes s fold)
          (s.maskRows * (codes.mask.getD s.maskCode default).r) = .ok cT ∧
        R = laidRows table codes s fold data cF cE cM cT := by
  unfold messageRows at h
  rcases ite_eq h with ⟨_, h⟩ | ⟨h1, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  rcases ite_eq h with ⟨_, h⟩ | ⟨h2, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨cF, hF, h⟩ := bind_ok h
  obtain ⟨cE, hE, h⟩ := bind_ok h
  obtain ⟨cM, hM, h⟩ := bind_ok h
  obtain ⟨cT, hT, h⟩ := bind_ok h
  rcases ite_eq h with ⟨_, h⟩ | ⟨h3, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  refine ⟨?_, ?_, ?_, cF, cE, cM, cT, hF, hE, hM, hT, (Except.ok.inj h).symm⟩
  · cases hq : VerifiableInference.Desc.Own.sentShapeFits codes s with
    | true => rfl
    | false => exact absurd (by simp only [hq, Bool.not_false]) h1
  · intro n hn
    subst hn
    cases hq : K1.rideFits codes s ⟨n, OnBytes.ceilLog2 s.maskRows⟩ with
    | true => rfl
    | false => exact absurd (by simp only [Option.map_some, hq, beq_self_eq_true]) h2
  · exact Decidable.byContradiction fun hx => h3 (bne_iff_ne.2 hx)

/-- **Where the shape fits and the stretch has the count that the laying asks, it returns.** -/
theorem messageRows_returns (table : FreshTable) {codes : OnBytes.Codes} {s : OnBytes.OracleShape}
    {fold : Option Nat} (data : Nat → Nat → Cb.Gl.E) {k : Stretch} (H : ShapeFits codes s fold)
    (hd : k.due = laidDue codes s fold) : ∃ R, messageRows table codes s fold data k = .ok R := by
  have hdf : k.due.f = countF codes s := by rw [hd]; rfl
  have hde : k.due.e = fromE codes s + inMaskOf codes s fold +
      s.maskRows * (codes.mask.getD s.maskCode default).r := by rw [hd]; rfl
  cases hR : messageRows table codes s fold data k with
  | ok R => exact ⟨R, rfl⟩
  | error e =>
    exfalso
    unfold messageRows at hR
    rcases ite_eq hR with ⟨q, _⟩ | ⟨_, hR⟩
    · rw [H.shape] at q
      cases q
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · cases hx
    rcases ite_eq hR with ⟨q, _⟩ | ⟨_, hR⟩
    · cases fold with
      | none => cases q
      | some n =>
        have hr := H.ride n rfl
        simp only [Option.map_some, hr] at q
        cases q
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · cases hx
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · obtain ⟨_, h'⟩ := fs_of_le k (a := 0) (n := countF codes s) (by omega)
      cases h'.symm.trans hx
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · obtain ⟨_, h'⟩ := es_of_le k (a := 0) (n := fromE codes s) (by omega)
      cases h'.symm.trans hx
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · obtain ⟨_, h'⟩ := es_of_le k (a := fromE codes s) (n := inMaskOf codes s fold) (by omega)
      cases h'.symm.trans hx
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · obtain ⟨_, h'⟩ := es_of_le k (a := fromE codes s + inMaskOf codes s fold)
        (n := s.maskRows * (codes.mask.getD s.maskCode default).r) (by omega)
      cases h'.symm.trans hx
    rcases ite_eq hR with ⟨q, _⟩ | ⟨_, hR⟩
    · exact bne_iff_ne.1 q hd
    rcases bind_error hR with hx | ⟨_, _, hR⟩
    · cases hx
    cases hR

/-- A sending's laying that returns has passed the shared sending's public test. -/
theorem rowsAll_fits {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    {data : Nat → Nat → Nat → Cb.Gl.E} {c : Cs (sendingDue codes sent fresh)} {V : Nat → Rows}
    (h : rowsAll table codes sent fresh data c = .ok V) :
    K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true := by
  unfold rowsAll at h
  rcases ite_eq h with ⟨_, h⟩ | ⟨h1, _⟩
  · cases h
  cases hq : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) with
  | true => rfl
  | false => exact absurd (by simp only [hq, Bool.not_false]) h1

/-- **Under the shared sending's public test the sending's laying returns**: at all coins, main rows
and tables. -/
theorem rowsAll_returns {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)}
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (table : FreshTable)
    (data : Nat → Nat → Nat → Cb.Gl.E) (c : Cs (sendingDue codes sent fresh)) :
    ∃ V, rowsAll table codes sent fresh data c = .ok V := by
  obtain ⟨l, hl⟩ := mapM_of_all
    (fun k => ((Stretch.of c).cut (dueBefore codes sent fresh k)
      (messageDue codes (sent.getD k default).shape (foldAt fresh k))).bind
      (messageRows table codes (sent.getD k default).shape (foldAt fresh k) (data k)))
    (List.range sent.size) fun k hk => by
      have hk' : k < sent.size := List.mem_range.1 hk
      have H := shapeFits_of hf hk'
      have hle := dueBefore_le codes sent fresh (k := k + 1) sent.size hk' (Nat.le_refl _)
      rw [dueBefore_succ codes sent fresh hk'] at hle
      obtain ⟨c', hc'⟩ := cut_of_le c (a := dueBefore codes sent fresh k)
        (n := messageDue codes (sent.getD k default).shape (foldAt fresh k)) hle.1 hle.2
      obtain ⟨R, hR⟩ := messageRows_returns table (data k) (k := ⟨_, c'⟩) H (messageDue_laid H)
      refine ⟨R, ?_⟩
      show ((Stretch.of c).cut _ _).bind _ = _
      rw [stretch_cut_of hc']
      exact hR
  refine ⟨fun k => l.getD k zeroMessage, ?_⟩
  unfold rowsAll
  exact (if_neg (by rw [hf]; exact Bool.false_ne_true)).trans
    (congrArg (Except.map fun l k => l.getD k zeroMessage) hl)

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.messageRows_laid
#print axioms ProofFile.Honest.K2.messageRows_returns
#print axioms ProofFile.Honest.K2.rowsAll_fits
#print axioms ProofFile.Honest.K2.rowsAll_returns
#print axioms ProofFile.Honest.K2.laidRows
