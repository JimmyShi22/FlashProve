-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LibJoinNorm.lean: FROM THE RELATION ON THE FINAL NORMALISATION's CELLS (HeadNormLaw.lean: CellRelN) TO THE NORMALISATION's CLAUSES OF THE LIBRARY's FIELD RELATION OF THE HEAD (Law/LibJoin.lean: NormOwn); AND SO, FROM THE HEAD's TWO RELATIONS, THE WHOLE OF Policy.LedgerHead.RF. **PORTED, BY PROGRAM, FROM A TEXT OF THIS PROJECT
THAT IS NOT IN THIS REPOSITORY: EVERY DEFINITION, STATEMENT AND PROOF BELOW IS THAT TEXT's, TO THE LETTER,** but for the module's path, the namespace and the import's path.
  cellsN c   the library's record of cells of the kind's record with the stream.
  Dv_at · Dv_eq · bl_eq · xv_eq · nw_eq · rn_eq · nrm_eq   identities between integers.     cast_zero_of_modEq · keyN_cast
  normOwn_of_cellRelN   T = 1024 · d = 5120 · a block's size divides d · CellRelN c ⇒ NormOwn at cellsN c and the kind's own three numbers npOf, whatever the weights and the request.
  JoinWholeStatement · joinWhole   under JoinStatement's premises: CellRelH c.toCells tab ∧ CellRelN c ⇒ Policy.LedgerHead.RF npOf (weightsOf c.toCells) Y (cellsN c).
WHAT IT DOES NOT SAY. The converse. That a verifier's yes gives the two relations. That the premises hold of a description. That some cells have the two relations. The clause "y = 0 if e < T", which is no clause of RF. The relation over the base field. From a record of cells to arrays by label. A TOOL. What bears on the letters: Law/LibJoin.lean's head. No chance in it.

-/
import Johnson.Desc.Kinds.Law.LibJoin
import Johnson.Desc.Kinds.Law.NormProof
import Inst.Model.Head.NoWrapProgramN

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.HeadJoin

open Finset
open VerifiableInference.Desc.Kinds VerifiableInference.Desc.Kinds.Head
open Inst.Model (NormPar)

/-- The library's record of cells, of the kind's with the stream. -/
def cellsN (c : Law.NCells) : Inst.Model.Head.Cells ℤ := cellsOf c.toCells c.stream

section Ints
variable [Head.Sizes] {c : Law.NCells}

omit [Head.Sizes] in
/-- A digit of the row. -/
theorem Dv_at (n i : ℕ) : Inst.Model.Head.Dv (cellsN c) n i = Law.digZ c i n := by
  unfold Inst.Model.Head.Dv Law.digZ cellsN cellsOf
  exact add_comm _ _

omit [Head.Sizes] in
/-- The row's digits. -/
theorem Dv_eq (i : ℕ) : (fun n => Inst.Model.Head.Dv (cellsN c) n i) = Law.digZ c i := by
  funext n
  exact Dv_at n i

/-- A limb of the stream. -/
theorem bl_eq (hd : Norm.d = 5120) (l j i : ℕ) :
    Inst.Model.Head.bl (cellsN c) l j i = Law.limbZ c i l j := by
  unfold Inst.Model.Head.bl Law.limbZ cellsN cellsOf Inst.Model.Head.fX
  rw [hd, Nat.mul_comm]

/-- A value of the stream. -/
theorem xv_eq (hd : Norm.d = 5120) (j i : ℕ) :
    Inst.Model.Head.xv (cellsN c) j i = Law.str c i j := by
  unfold Inst.Model.Head.xv Inst.Model.Head.rd Law.str
  rw [Law.sumZ_eq]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (256 : ℤ) ^ l * Inst.Model.Head.bl (cellsN c) l j i = _
  rw [bl_eq hd]

/-- The rounded quotient. -/
theorem nw_eq (hd : Norm.d = 5120) (j i : ℕ) :
    Inst.Model.Head.nw (cellsN c) j i = Law.awZ c i j := by
  unfold Inst.Model.Head.nw Inst.Model.Head.rd Law.awZ cellsN cellsOf Inst.Model.Head.fNw
  rw [hd, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  show 0 + (256 : ℤ) ^ 0 * c.cell .wide (5120 * 0 + j) i +
    256 ^ 1 * c.cell .wide (5120 * 1 + j) i = _
  ring_nf

/-- The remainder's high part. -/
theorem rn_eq (hd : Norm.d = 5120) (j i : ℕ) :
    Inst.Model.Head.rn (cellsN c) j i = Law.remZ c i j := by
  unfold Inst.Model.Head.rn Inst.Model.Head.rd Law.remZ cellsN cellsOf Inst.Model.Head.fRn
  rw [hd, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  show 32896 + (0 + (256 : ℤ) ^ 0 * c.cell .wide (10240 + 5120 * 0 + j) i +
    256 ^ 1 * c.cell .wide (10240 + 5120 * 1 + j) i) =
    c.cell .wide (2 * 5120 + j) i + 256 * c.cell .wide (2 * 5120 + 5120 + j) i + 32896
  ring_nf

/-- The clamped output. -/
theorem nrm_eq (hd : Norm.d = 5120) (j i : ℕ) :
    Inst.Model.Head.nrm (cellsN c) j i = Law.act c.toCells i j := by
  unfold Inst.Model.Head.nrm Inst.Model.Head.rd Law.act cellsN cellsOf Inst.Model.Head.fNrm
  rw [hd, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  show 0 + (256 : ℤ) ^ 0 * c.cell .act (5120 * 0 + j) i +
    256 ^ 1 * c.cell .act (5120 * 1 + j) i = _
  ring_nf

end Ints

/-! ## From integers to the field -/

section Field
variable [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] {c : Law.NCells}

omit [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] in
/-- An integer that is 0 modulo the field's prime is 0 in the field. -/
theorem cast_zero_of_modEq {a : ℤ} (h : a ≡ 0 [ZMOD Law.pK]) : (a : Law.K) = 0 :=
  (CharP.intCast_eq_zero_iff Law.K Code.pGold a).2 (Int.modEq_zero_iff_dvd.1 h)

omit [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] in
/-- A key that reads neither the weights nor the request, on integer cells, read in the field. -/
theorem keyN_cast (np : NormPar) (t : Inst.Model.Head.Cells ℤ) (H : ℕ → ℕ → ℤ)
    (Y : Inst.Model.Head.Req) (s : Inst.Model.Head.Fam) (x i : ℕ) :
    Policy.LedgerHead.key np (t.cast Law.K) (fun j v => ((H j v : ℤ) : Law.K)) Y s x i =
      ((Policy.LedgerHead.key np t H Y s x i : ℤ) : Law.K) :=
  (Policy.LedgerHead.map_key (Int.castRingHom Law.K) np t H Y s x i).symm

/-- **From the kind's relation on the normalization's cells to the normalization's clauses.** -/
theorem normOwn_of_cellRelN (H : ℕ → ℕ → ℤ) (Y : Inst.Model.Head.Req) (hT : Norm.T = 1024)
    (hd : Norm.d = 5120) (hS : Norm.S2 ∣ Norm.d) (h : Law.CellRelN c) :
    NormOwn Law.npOf (fun j v => ((H j v : ℤ) : Law.K)) Y (cellsN c) where
  small := fun i _ φ _ => by
    have := h.smallS φ i
    show |c.stream φ i| < 2 ^ 18
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this
  keys := fun s hs x i hx hi => by
    have hi' : i < Norm.T := by rw [hT]; exact hi
    rw [keyN_cast]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · have hx' : x < Norm.d := by rw [hd]; exact hx
      obtain ⟨n, hn, e⟩ := h.remLow i hi' x hx'
      refine ⟨n, hn, ?_⟩
      have e1 := congrArg Law.rd e
      rw [Law.rd_keyN_remLow hi' hS hx', Law.rd_natCast] at e1
      show ((Inst.Model.Head.xv (cellsN c) x i *
          Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv (cellsN c) n i) +
          2 ^ (FinalNorm.KF - 1) - 2 ^ FinalNorm.KF * Inst.Model.Head.nw (cellsN c) x i -
          2 ^ 16 * Inst.Model.Head.rn (cellsN c) x i : ℤ) : Law.K) = (((n : ℕ) : ℤ) : Law.K)
      rw [xv_eq hd, Dv_eq, nw_eq hd, rn_eq hd, Int.cast_natCast]
      exact e1
    · have hx' : x < Norm.d := by rw [hd]; exact hx
      obtain ⟨n, hn, e⟩ := h.remHigh i hi' x hx'
      refine ⟨n, hn, ?_⟩
      have e1 := congrArg Law.rd e
      rw [Law.rd_keyN_remHigh hi' hS hx', Law.rd_natCast] at e1
      show ((((2 ^ (32 - FinalNorm.KF) : ℕ) : ℤ) * Inst.Model.Head.rn (cellsN c) x i : ℤ) :
        Law.K) = (((n : ℕ) : ℤ) : Law.K)
      have e2 : ((2 ^ (32 - FinalNorm.KF) : ℕ) : ℤ) * Law.remZ c i x =
          Inst.Model.Site.high (Law.remZ c i x) FinalNorm.KF 32 := by
        simp [Inst.Model.Site.high]
      rw [rn_eq hd, e2, Int.cast_natCast]
      exact e1
    · have hx' : x < Norm.d := by rw [hd]; exact hx
      obtain ⟨u, hu, e⟩ := h.clamp i hi' x hx'
      refine ⟨u, hu, ?_⟩
      have e1 := congrArg Law.rd e
      rw [Law.rd_keyN_clamp hi' hS hx', Law.rd_natCast] at e1
      show (((Inst.Model.Head.nw (cellsN c) x i + 2 ^ 15) +
          2 ^ 28 * (Inst.Model.Head.nrm (cellsN c) x i + 2 ^ 11) : ℤ) : Law.K) =
        (((u : ℤ) + 2 ^ 28 * (Inst.Model.clamp 2047 ((u : ℤ) - 2 ^ 15) + 2 ^ 11) : ℤ) : Law.K)
      rw [nw_eq hd, nrm_eq hd, e1]
      have hz : (0 : ℤ) ≤ Law.clampZ ((u : ℤ) - 2 ^ 15) + 2 ^ 11 := by
        have h1 : (-2047 : ℤ) ≤ Law.clampZ ((u : ℤ) - 2 ^ 15) :=
          le_min (le_max_right _ _) (by norm_num)
        linarith
      have e2 : (((Law.clampZ ((u : ℤ) - 2 ^ 15) + 2 ^ 11).toNat : ℕ) : ℤ) =
          Inst.Model.clamp 2047 ((u : ℤ) - 2 ^ 15) + 2 ^ 11 := Int.toNat_of_nonneg hz
      rw [← e2]
      push_cast
      rfl
  row := fun n i hn hi => by
    have hi' : i < Norm.T := by rw [hT]; exact hi
    obtain ⟨u, hu, e⟩ := h.digits i hi' n (by unfold NR; omega)
    refine ⟨u, hu, ?_⟩
    have e1 := congrArg Law.rd e
    rw [Law.rd_keyN_digits hi' (by unfold NR; omega), Law.rd_natCast] at e1
    rw [keyN_cast]
    show (((Inst.Model.Ledger.mu n : ℤ) * Inst.Model.Head.Dv (cellsN c) n i : ℤ) : Law.K) =
      (((u : ℕ) : ℤ) : Law.K)
    rw [Int.cast_natCast, ← e1, Law.mul_eq_mu, Dv_at]
  idns := fun i hi k _ => by
    have hi' : i < Norm.T := by rw [hT]; exact hi
    have e1 : Inst.Model.Head.N.idn Law.npOf ((cellsN c).cast Law.K) i k =
        ((Inst.Model.Head.N.idn Law.npOf (cellsN c) i k : ℤ) : Law.K) :=
      (Inst.Model.Head.N.map_idn' (Int.castRingHom Law.K) Law.npOf (cellsN c) i k).symm
    rw [e1]
    refine cast_zero_of_modEq ?_
    have e2 := Law.idn_modEq (c := c) hi' (h.rows i hi') k
    unfold Inst.Model.Head.N.idn
    rw [Dv_eq]
    have e3 : (fun l j => Inst.Model.Head.bl (cellsN c) l j i) = Law.limbZ c i := by
      funext l j
      exact bl_eq hd l j i
    rw [e3]
    rw [hd] at e2
    exact e2

end Field

/-- **The whole of the library's field relation of the head, from the kind's two relations.** -/
def JoinWholeStatement : Prop :=
  ∀ [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] (sT : ℕ) (tab : ℕ → ℕ)
    (c : Law.NCells) (Y : Inst.Model.Head.Req),
    planOk sT = true → Request.ok = true → Token.y < Head.V → Same Y → Wide → More Y →
    (∀ u, u < 2 ^ 16 → (tab u : ℤ) = Inst.Model.EX u) →
    Law.CellRelH c.toCells tab → Law.CellRelN c →
    Policy.LedgerHead.RF Law.npOf (weightsOf c.toCells) Y (cellsN c)


/-- **It holds.** -/
theorem joinWhole : JoinWholeStatement := fun sT tab c Y hplan hreq hy S Wd M htab hH hN =>
  rf_of_own
    (join Law.npOf sT tab c.toCells c.stream Y hplan hreq hy S Wd M htab
      ((Law.cellRel_iff c.toCells tab).2
        ⟨hN.small, fun _ ht _ hj => Law.bytes_of_digits hN ht hj, hH⟩))
    (normOwn_of_cellRelN c.Wh Y S.T Wd.d
      (Nat.dvd_of_mod_eq_zero (Law.planFacts hplan).hdS) hN)

end VerifiableInference.Desc.Kinds.HeadJoin

#print axioms VerifiableInference.Desc.Kinds.HeadJoin.Dv_at
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.Dv_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.bl_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.xv_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.nw_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.rn_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.nrm_eq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.cast_zero_of_modEq
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.keyN_cast
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.normOwn_of_cellRelN
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.joinWhole
