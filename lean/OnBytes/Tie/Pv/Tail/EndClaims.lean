-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndClaims.lean: what one tie and one read of the smallness test
(OnBytes/Model/Tail.lean: linTie, linRead) add to the sub-proof's one equation.

Statements and proofs, from t2Lin_total (OnBytes/Model/TreesLaws.lean). For any reading of the field
in a commutative ring and any world: a value for each entry of each virtual row.
Main names:
  `lessBeta_value`, `highDigit_val`, `leadF_val`: the constant, the high digit's weight, and the
    factor that brings a claim's weight to theta ^ (planClaims + the first index).
  `linTie_total`, `linRead_total`: if the routine returns, the context is unchanged and the total
    grows by that power of theta times a bracket: weights on ZZ, on the symbol array or on the
    vector that holds the table, and a constant.
  `posOf`, `readEnts_value`: the place of a table's entry; what readEnts appends, as a value.
Limits: the entries are those of virtual rows. Nothing on a run that fails. The verifier's own
second
computation of the weights (tileSelfTestF) covers neither the reads' weights on the vector that
holds
a table nor the constants: of these the two statements here are the only account.

-/
import OnBytes.Tie.Pv.Tail.EndRun
import OnBytes.Model.TreesLaws
import OnBytes.Iop.RowLaws
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-! ## Small numbers, read at any Reading -/

theorem val_two_pow (n : Nat) (e : ofF (fOfNat (2 ^ n)) = powE (addE oneE oneE) n) :
    ρ.val (ofF (fOfNat (2 ^ n))) = (2 : K) ^ n := by
  rw [e, ρ.pow, ρ.add, ρ.one, one_add_one_eq_two]

theorem val_beta : ρ.val (ofF (fOfNat (2 ^ lbz))) = (2 : K) ^ 17 :=
  val_two_pow ρ 17 (by decide +kernel)

theorem val_d0' : ρ.val (ofF (fOfNat (2 ^ t2D0))) = (2 : K) ^ 10 :=
  val_two_pow ρ 10 (by decide +kernel)

/-- The constant -beta x, as a value. -/
theorem lessBeta_value (x : E) : (HTailF2.lessBeta x).value ρ W = -((2 : K) ^ 17 * ρ.val x) := by
  rw [HTailF2.lessBeta, Aff.value_ofConst, ρ.sub, ρ.zero, scaleNat, OnBytes.scaleE_val ρ, val_beta]
  ring

theorem highDigit_val (x : E) : ρ.val (HTailF2.highDigit x) = (2 : K) ^ 10 * ρ.val x := by
  rw [HTailF2.highDigit, scaleNat, OnBytes.scaleE_val ρ, val_d0']

/-- leadF's factor brings the next claim's own weight theta^nClaim to theta^(planClaims + first). -/
theorem leadF_val (F : Fork) (first : Nat) (lead : E) (h : HTailF2.leadF F first = some lead) :
    ρ.val F.theta ^ F.nClaim * ρ.val lead = ρ.val F.theta ^ (F.planClaimsF + first) := by
  unfold HTailF2.leadF at h
  split at h
  · cases h
  · rename_i hlt
    have := Option.some.inj h
    subst this
    rw [ρ.pow, ← pow_add]
    congr 1
    omega

/-! ## One tie -/

/-- What one tie adds. If linTie mu returns from F, the context is unchanged and Fork.total grows by
theta^(planClaims + eqFirst mu) times
  -2^17 (sum vp) (sum wl) + sum_{i < m} wl[i] (low + 2^10 high)(i) - sum_{p < J k} wr[p] symbol(p),
low, high: the entries c0 + i, c1 + i of ZZ's virtual row of the ties; symbol: entry p of the symbol
array's virtual row 0; wl, wr: tieLeft's and tieRight's weights. -/
theorem linTie_total (tl : HTailF2) (mu : Nat) (F G : Fork) (c c' : Ctx) (hs : F.LS.size = F.ns)
    (h : tl.linTie mu F c = .ok (((), G), c')) :
    c' = c ∧ ∃ wl wr c0 c1,
      tieLeft (tl.shp.getD mu {}) (tl.rowX.getD mu #[]) (tl.loX.getD mu #[]) = some wl ∧
      tieRight (tl.shp.getD mu {}) (tl.loX.getD mu #[]) (tl.gamX.getD mu #[]) = some wr ∧
      tl.zzCol mu 0 0 = some c0 ∧ tl.zzCol mu 1 0 = some c1 ∧
      G.total ρ W = F.total ρ W + ρ.val F.theta ^ (F.planClaimsF + tl.eqFirst.getD mu 0) *
        (-((2 : K) ^ 17 * (ρ.val (sumE tl.vp) * ρ.val (sumE wl)))
          + runSum (fun i => ρ.val (wl.getD i zeroE) * W.entry tl.ix.ZZ tl.zzRowTies (c0 + i))
              (tl.shp.getD mu {}).m 0
          + (2 : K) ^ 10 * runSum (fun i => ρ.val (wl.getD i zeroE)
              * W.entry tl.ix.ZZ tl.zzRowTies (c1 + i)) (tl.shp.getD mu {}).m 0
          - runSum (fun p => ρ.val (wr.getD p zeroE) * W.entry (tl.gtTree.getD mu 0) 0 p)
              ((tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k) 0) ∧
      G.nClaim = F.nClaim + 1 ∧ G.theta = F.theta ∧ G.ns = F.ns ∧ G.LS.size = G.ns ∧
      treesFrame G.trees = treesFrame F.trees := by
  unfold HTailF2.linTie at h
  simp only [bind_ok, get_ok, ask_ok] at h
  obtain ⟨wl, _, _, ⟨hwl, rfl, rfl⟩, wr, _, _, ⟨hwr, rfl, rfl⟩, lead, _, _, ⟨hlead, rfl, rfl⟩,
    c0, _, _, ⟨hc0, rfl, rfl⟩, c1, _, _, ⟨hc1, rfl, rfl⟩, h⟩ := h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := t2Lin_total ρ W _ _ _ _ _ _ hs h
  refine ⟨e1, wl, wr, c0, c1, hwl, hwr, hc0, hc1, ?_, e3, e4, e5, e6, e7⟩
  rw [e2, ← leadF_val ρ _ _ lead hlead, lessBeta_value]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Run2.value, ρ.mul, ρ.sub,
    ρ.zero, highDigit_val, Nat.zero_add, add_zero]
  ring

/-! ## One read -/

/-- testAs, in either run, leaves the context as it was. -/
theorem testAs_ctx (name : String) (b : Bool) (c c' : Ctx) (u : Unit)
    (h : testAs name b c = .ok (u, c')) : c' = c := by
  unfold testAs at h
  have h' : (StateT.bind Blk.isDry fun d => if b || d then pure () else refuse name) c
      = .ok (u, c') := h
  simp only [StateT.bind, Blk.isDry] at h'
  have h2 : (if (b || c.ch.dry) = true then (pure () : Blk Unit) else refuse name) c
      = .ok (u, c') := h'
  split at h2
  · have h3 : (Except.ok ((), c) : Except Failure (Unit × Ctx)) = .ok (u, c') := h2
    cases h3; rfl
  · simp [refuse, Blk.fail] at h2

/-- The entry of U1 or U3 for column c, segment sg of a table; 0 where tabAt gives none. -/
def posOf (tl : HTailF2) (Fn : HFun) (sg c : Nat) : Nat := (tl.tabAt Fn c sg).getD 0

/-- What readEnts appends, as a value: minus times the sum over the columns of gc[c] times the entry
at tabAt's place, by uEnt's rule (row pos / cols, index pos % cols). -/
theorem readEnts_value (tl : HTailF2) (Fn : HFun) (sg tU cols : Nat) (minus : E) (gc : Array E) :
    ∀ (count c : Nat) (ents : Array Ent) (nz : Bool) (ents' : Array Ent) (nz' : Bool),
      tl.readEnts Fn sg tU cols minus gc count c ents nz = some (ents', nz') →
      (ents'.toList.map (Ent.value ρ W)).sum = (ents.toList.map (Ent.value ρ W)).sum
        + ρ.val minus * runSum (fun d => ρ.val (gc.getD d zeroE)
            * W.entry tU (posOf tl Fn sg d / cols) (posOf tl Fn sg d % cols)) count c := by
  intro count
  induction count with
  | zero =>
    intro c ents nz ents' nz' h
    simp only [HTailF2.readEnts, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    simp only [runSum, mul_zero, add_zero]
  | succ n ih =>
    intro c ents nz ents' nz' h
    unfold HTailF2.readEnts at h
    cases hp : tl.tabAt Fn c sg with
    | none => simp [hp] at h
    | some pos =>
      simp only [hp] at h
      rw [ih _ _ _ _ _ h]
      simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil, Ent.value, ρ.mul, runSum, posOf, hp, Option.getD_some,
        add_zero]
      ring

/-- What one read adds. If linRead returns from F, the context is unchanged and Fork.total grows by
theta^(planClaims + eqFirst NM + laid stepF) times
  -2^17 sums - sum_{c < k} gamV[c] U(entry of column c) + sum_{j < len} phi[j] (low + 2^10 high)(j),
U: the vector's entry at tabAt's place; low, high: the entries c0 + j, c1 + j of ZZ's virtual row of
the reads. -/
theorem linRead_total (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E) (F G : Fork)
    (c c' : Ctx) (hs : F.LS.size = F.ns) (h : tl.linRead Fn sg laid sums F c = .ok (((), G), c')) :
    c' = c ∧ ∃ tU c0 c1,
      tl.ix.U.getD Fn.tree none = some tU ∧
      tl.zzCol Fn.mat 0 (sg * Fn.len) = some c0 ∧ tl.zzCol Fn.mat 1 (sg * Fn.len) = some c1 ∧
      G.total ρ W = F.total ρ W
        + ρ.val F.theta ^ (F.planClaimsF + (tl.eqFirst.getD tl.NM 0 + laid * tl.stepF)) *
        (-((2 : K) ^ 17 * ρ.val sums)
          - runSum (fun d => ρ.val ((tl.gamV.getD Fn.mat #[]).getD d zeroE)
              * W.entry tU (posOf tl Fn sg d / (((F.trees[tU]?).map (·.K)).getD 0))
                  (posOf tl Fn sg d % (((F.trees[tU]?).map (·.K)).getD 0)))
              (tl.mats.getD Fn.mat {}).k 0
          + runSum (fun j => ρ.val (Fn.phi.getD j zeroE) * W.entry tl.ix.ZZ tl.zzRowReads (c0 + j))
              Fn.len 0
          + (2 : K) ^ 10 * runSum (fun j => ρ.val (Fn.phi.getD j zeroE)
              * W.entry tl.ix.ZZ tl.zzRowReads (c1 + j)) Fn.len 0) ∧
      G.nClaim = F.nClaim + 1 ∧ G.theta = F.theta ∧ G.ns = F.ns ∧ G.LS.size = G.ns ∧
      treesFrame G.trees = treesFrame F.trees := by
  unfold HTailF2.linRead at h
  simp only [bind_ok, get_ok, ask_ok, lift_ok, mustAs_ok, Option.some.injEq] at h
  obtain ⟨tU, _, _, ⟨htU, rfl, rfl⟩, lead, _, _, ⟨hlead, rfl, rfl⟩, _, _, _, ⟨rfl, rfl, rfl⟩,
    _, _, _, ⟨⟨_, rfl⟩, rfl⟩, en, _, _, ⟨hen, rfl, rfl⟩, _, _, _, ⟨ht, rfl⟩, h⟩ := h
  have := testAs_ctx _ _ _ _ _ ht
  subst this
  obtain ⟨c0, _, _, ⟨hc0, rfl, rfl⟩, c1, _, _, ⟨hc1, rfl, rfl⟩, h⟩ := h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := t2Lin_total ρ W _ _ _ _ _ _ hs h
  refine ⟨e1, tU, c0, c1, htU, hc0, hc1, ?_, e3, e4, e5, e6, e7⟩
  have hv := readEnts_value ρ W tl Fn sg tU _ _ _ _ _ _ _ en.1 en.2 hen
  rw [e2, ← leadF_val ρ _ _ lead hlead]
  simp only [Aff.value, HTailF2.lessBeta, Aff.ofConst, hv, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Run2.value, ρ.mul, ρ.sub, ρ.zero, highDigit_val, Nat.zero_add,
    add_zero, scaleNat, OnBytes.scaleE_val ρ, val_beta, Array.toList_empty, Array.emptyWithCapacity]
  ring

#print axioms linTie_total
#print axioms linRead_total

end OnBytes.Tie.Pv.Tail.Port
