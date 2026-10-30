-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/Back/KeysOfHeadCl.lean: FROM THE LIBRARY's CLAUSE "every key of the nine
families is an entry of its table" (the first clause of `Policy.HeadCl`, Policy/Seg/Head.lean) BACK
TO THE NINE KEYS OF THE OUTPUT HEAD, as elements in the program's own writing (`NineKeys`,
Johnson/Desc/Kinds/Law/OutCallBack.lean). Statements with their proofs. Over the library.

What it is not. Nothing says that the library's clause holds at any cells: both statements are
CONDITIONAL on it. The full size alone (`Wide`). No bound on the cells is spent. No chance in it.
Nothing on soundness, completeness or hiding.

Beside the library's own way back. `nine_of_headCl` (Johnson/Desc/Kinds/Law/LibBackWhole.lean) ends
in `NineKeys tab c` too, and in the two guests' corner values besides, under the premises of
`keys_of_headCl` AND ONE MORE: the library's clause `Small` of `cellsN c`: it goes through the
library's field relation whole (`rf_of_headCl`, `nine_of_rf`). `keys_of_headCl` spends the
relation's first clause alone and asks no bound on the cells. There the nine arms are proved field
by field (Law/LibBack.lean, Law/LibBackNorm.lean); by these files' heads, from the equations that
are called here too.

  `nineKeys_of_castKeys`   CONDITIONAL: the nine arms, general in what the library's head reads of
                           the request and the policy
  `keys_of_headCl`         CONDITIONAL on the premises of `headCl_of_parts`
                           (Johnson/Desc/Kinds/Law/LibParts.lean), to the letter, with the library's
                           relation in the place of the four parts

How. The clause modulo the prime is the clause over the field (`Down.inLut_iff`,
`Down.ledgerKey_map`, Johnson/Road/HeadDown.lean). Then each arm: the library's key on integer cells
is the kind's integer (the equations of Law/LibJoin.lean and Law/LibJoinNorm.lean); the kind's key
at a corner, read in the field, is the image of that integer (Law/Values.lean, Law/NormProof.lean);
an element in the one canonical writing that is read as the image of a natural is that natural
(`eq_natCast_of_rd`, Law/TableTie.lean). Every equation between the two texts' integers, and between
a key and its integer, is one that the forward proofs call, read the other way; the step from the
field to the program's writing is wanted on the way back alone; the step from the prime field up is
the one that the forward road takes downwards inside `Down.ledgerRF_gl`, called here clause by
clause.

-/
import Mathlib
import Johnson.Desc.K6.Honest.Law.Back.CallsOfKeys
import Johnson.Desc.Kinds.Law.LibParts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (AcceptancePolicy Mat Instance ppref)
open VerifiableInference.Desc.Kinds.HeadJoin (Same Wide More cellsN)
open OnBytes (E okE)
open Norm (lt ls d S2 T)

/-- **The nine arms**: from the library's nine families, each key read in the field as the image of
an integer, to the nine keys. Y: what the library's head reads of the request and the policy. -/
theorem nineKeys_of_castKeys [Sizes] [Policy] [Request] [Token] (sT : Nat) (tab : Nat → Nat)
    (c : NCells) (Y : Inst.Model.Head.Req) (hplan : planOk sT = true)
    (hreq : Request.ok = true) (hy : Token.y < V) (S : Same Y) (Wd : Wide) (M : More Y)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hK : ∀ f a i, a < Inst.Model.Head.len f → i < Inst.Model.Head.nT →
      Inst.Model.Head.InLut (_root_.Policy.LedgerHead.tableOf f)
        ((_root_.Policy.LedgerHead.key npOf (cellsN c) c.Wh Y f a i : Int) : K)) :
    NineKeys tab c := by
  have P := planFacts hplan
  have hS : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have hpos : ∀ t, t < T → t < Inst.Model.Head.nT := by
    intro t ht
    have h := ht
    rw [S.T] at h
    exact h
  have hJ : ∀ x, x < JV → x < 202048 := by
    intro x hx
    have h := hx
    rw [Wd.JV] at h
    exact h
  have hD : ∀ x, x < d → x < 5120 := by
    intro x hx
    have h := hx
    rw [Wd.d] at h
    exact h
  unfold NineKeys
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the margin's top digit: the family HD0, whose table holds 2^23 u
    intro t ht x hx
    obtain ⟨u, hu, e⟩ := hK .HD0 x t (hJ x hx) (hpos t ht)
    have e' : ((Inst.Model.Head.mg (HeadJoin.cellsOf c.toCells c.stream) c.Wh Y x t -
        2 ^ 8 * Inst.Model.Head.K1 (HeadJoin.cellsOf c.toCells c.stream) Y x t -
        Inst.Model.Head.K2 (HeadJoin.cellsOf c.toCells c.stream) Y x t : Int) : K) =
        ((2 ^ 23 * (u : Int) : Int) : K) := e
    rw [HeadJoin.top_eq S Wd M (hJ x hx)] at e'
    have h23 : sh + 15 = 23 := by
      have h8 := M.sh
      omega
    refine ⟨u, hu, eq_natCast_of_rd (okE_keyAt c.toCells _ _) ?_⟩
    rw [rd_key_top P hreq hy hx ht, h23, e', inv_mul_eq_iff_eq_mul₀ (two_pow_ne_zero 23)]
    push_cast
    rfl
  · -- the margin's middle digit: HD1
    intro t ht x hx
    obtain ⟨u, hu, e⟩ := hK .HD1 x t (hJ x hx) (hpos t ht)
    have e' : ((Inst.Model.Head.K1 (HeadJoin.cellsOf c.toCells c.stream) Y x t : Int) : K) =
        (((u : Nat) : Int) : K) := e
    rw [HeadJoin.K1_eq S Wd (hJ x hx), Int.cast_natCast] at e'
    refine ⟨u, hu, eq_natCast_of_rd (okE_keyAt c.toCells _ _) ?_⟩
    rw [rd_key_mid P hx ht]
    exact e'
  · -- the margin's low digit: HD2
    intro t ht x hx
    obtain ⟨u, hu, e⟩ := hK .HD2 x t (hJ x hx) (hpos t ht)
    have e' : ((Inst.Model.Head.K2 (HeadJoin.cellsOf c.toCells c.stream) Y x t : Int) : K) =
        (((u : Nat) : Int) : K) := e
    rw [HeadJoin.K2_eq S Wd (hJ x hx), Int.cast_natCast] at e'
    refine ⟨u, hu, eq_natCast_of_rd (okE_keyAt c.toCells _ _) ?_⟩
    rw [rd_key_low P hx ht]
    exact e'
  · -- the table's first half: HE0
    intro t ht x hx
    have hxa : x < JVa := hx
    have hx0 : x < 131072 := by
      have h := hxa
      rw [M.JVa] at h
      exact h
    have hx' : x < 202048 := by omega
    obtain ⟨u, hu, e⟩ := hK .HE0 x t hx0 (hpos t ht)
    have e' : ((Inst.Model.Head.K1 (HeadJoin.cellsOf c.toCells c.stream) Y x t +
        2 ^ 16 * Inst.Model.Head.ex (HeadJoin.cellsOf c.toCells c.stream) x t : Int) : K) =
        (((u : Int) + 2 ^ 16 * Inst.Model.EX u : Int) : K) := e
    rw [HeadJoin.K1_eq S Wd hx', HeadJoin.ex_eq Wd, ← htab u hu] at e'
    refine ⟨u, hu, eq_natCast_of_rd (okE_keyAt c.toCells _ _) ?_⟩
    rw [rd_key_tableA P hxa ht, e']
    push_cast
    rfl
  · -- the table's second half: HE1, whose entry x stands for the token 131072 + x
    intro t ht x hx
    have hxb : x < JV - JVa := hx
    have hx0 : x < 70976 := by
      have h := hxb
      rw [Wd.JV, M.JVa] at h
      omega
    have hx' : 131072 + x < 202048 := by omega
    obtain ⟨u, hu, e⟩ := hK .HE1 x t hx0 (hpos t ht)
    have e' : ((Inst.Model.Head.K1 (HeadJoin.cellsOf c.toCells c.stream) Y (131072 + x) t +
        2 ^ 16 * Inst.Model.Head.ex (HeadJoin.cellsOf c.toCells c.stream) (131072 + x) t :
        Int) : K) = (((u : Int) + 2 ^ 16 * Inst.Model.EX u : Int) : K) := e
    rw [HeadJoin.K1_eq S Wd hx', HeadJoin.ex_eq Wd, ← htab u hu] at e'
    refine ⟨u, hu, eq_natCast_of_rd (okE_keyAt c.toCells _ _) ?_⟩
    rw [rd_key_tableB P hxb ht, M.JVa, e']
    push_cast
    rfl
  · -- the rounding's low key: NF
    intro t ht x hx
    obtain ⟨u, hu, e⟩ := hK .NF x t (hD x hx) (hpos t ht)
    have e' : ((Inst.Model.Head.xv (cellsN c) x t *
        Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv (cellsN c) n t) +
        2 ^ (FinalNorm.KF - 1) - 2 ^ FinalNorm.KF * Inst.Model.Head.nw (cellsN c) x t -
        2 ^ 16 * Inst.Model.Head.rn (cellsN c) x t : Int) : K) = (((u : Nat) : Int) : K) := e
    rw [HeadJoin.xv_eq Wd.d, HeadJoin.Dv_eq, HeadJoin.nw_eq Wd.d, HeadJoin.rn_eq Wd.d,
      Int.cast_natCast] at e'
    refine ⟨u, hu, eq_natCast_of_rd (Came.okE_keyNAt c _ _) ?_⟩
    rw [rd_keyN_remLow ht hS hx]
    exact e'
  · -- the rounding's high key: NFH
    intro t ht x hx
    obtain ⟨u, hu, e⟩ := hK .NFH x t (hD x hx) (hpos t ht)
    have e' : ((((2 ^ (32 - FinalNorm.KF) : Nat) : Int) *
        Inst.Model.Head.rn (cellsN c) x t : Int) : K) = (((u : Nat) : Int) : K) := e
    have e2 : ((2 ^ (32 - FinalNorm.KF) : Nat) : Int) * remZ c t x =
        Inst.Model.Site.high (remZ c t x) FinalNorm.KF 32 := by
      simp [Inst.Model.Site.high]
    rw [HeadJoin.rn_eq Wd.d, e2, Int.cast_natCast] at e'
    refine ⟨u, hu, eq_natCast_of_rd (Came.okE_keyNAt c _ _) ?_⟩
    rw [rd_keyN_remHigh ht hS hx]
    exact e'
  · -- the clamp: CNF
    intro t ht x hx
    obtain ⟨u, hu, e⟩ := hK .CNF x t (hD x hx) (hpos t ht)
    have e' : (((Inst.Model.Head.nw (cellsN c) x t + 2 ^ 15) +
        2 ^ 28 * (Inst.Model.Head.nrm (cellsN c) x t + 2 ^ 11) : Int) : K) =
        (((u : Int) + 2 ^ 28 * (Inst.Model.clamp 2047 ((u : Int) - 2 ^ 15) + 2 ^ 11) : Int) :
          K) := e
    rw [HeadJoin.nw_eq Wd.d, HeadJoin.nrm_eq Wd.d] at e'
    have hz : (0 : Int) ≤ clampZ ((u : Int) - 2 ^ 15) + 2 ^ 11 := by
      have h1 : (-2047 : Int) ≤ clampZ ((u : Int) - 2 ^ 15) :=
        le_min (le_max_right _ _) (by norm_num)
      linarith
    have e2 : (((clampZ ((u : Int) - 2 ^ 15) + 2 ^ 11).toNat : Nat) : Int) =
        Inst.Model.clamp 2047 ((u : Int) - 2 ^ 15) + 2 ^ 11 := Int.toNat_of_nonneg hz
    refine ⟨u, hu, eq_natCast_of_rd (Came.okE_keyNAt c _ _) ?_⟩
    rw [rd_keyN_clamp ht hS hx, e', ← e2]
    push_cast
    rfl
  · -- the row's digits: ROW, at all 120 of them
    intro t ht j hj
    have hj' : j < 120 := by
      have h := hj
      unfold NR at h
      omega
    obtain ⟨u, hu, e⟩ := hK .ROW j t hj' (hpos t ht)
    have e' : (((Inst.Model.Ledger.mu j : Int) * Inst.Model.Head.Dv (cellsN c) j t : Int) : K) =
        (((u : Nat) : Int) : K) := e
    rw [Int.cast_natCast, HeadJoin.Dv_at, ← mul_eq_mu] at e'
    refine ⟨u, hu, eq_natCast_of_rd (Came.okE_keyNAt c _ _) ?_⟩
    rw [rd_keyN_digits ht hj]
    exact e'

/-- **FROM THE LIBRARY's CLAUSE ON KEYS BACK TO THE NINE KEYS.** CONDITIONAL on the premises of
`headCl_of_parts` (Johnson/Desc/Kinds/Law/LibParts.lean), with the library's relation in the place
of the four parts. -/
theorem keys_of_headCl [Sizes] [Policy] [Request] [Token] (sT : Nat) (tab : Nat → Nat)
    (c : NCells) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (hplan : planOk sT = true)
    (hreq : Request.ok = true) (hy : Token.y < V) (S : Same (Inst.Model.Head.Req.of pol x))
    (Wd : Wide) (M : More (Inst.Model.Head.Req.of pol x))
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : c.Wh = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H)
    (H : _root_.Policy.HeadCl npOf pol Wz x (cellsN c)) : NineKeys tab c := by
  refine nineKeys_of_castKeys sT tab c (Inst.Model.Head.Req.of pol x) hplan hreq hy S Wd M htab ?_
  intro f a i ha hi
  -- from the prime field to the field in which the program's elements are read
  have h1 := (OnBytes.Road.Hd.Down.inLut_iff (algebraMap Cb.Gl.F Cb.Gl.E)
    (algebraMap Cb.Gl.F Cb.Gl.E).injective (_root_.Policy.LedgerHead.tableOf f)
    (OnBytes.Road.Hd.Down.ledgerKey_map (algebraMap Cb.Gl.F Cb.Gl.E) npOf
      (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H
      (Inst.Model.Head.Req.of pol x) (cellsN c) f a i)).2 (H.1 f a i ha hi)
  rw [← hW] at h1
  rw [HeadJoin.keyN_cast npOf (cellsN c) c.Wh (Inst.Model.Head.Req.of pol x) f a i] at h1
  exact h1

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.nineKeys_of_castKeys
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.keys_of_headCl
