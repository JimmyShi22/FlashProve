-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/TieHash.lean: ALL HASHING OF A COMPILED RUN: the token side's hashT
(Johnson/TokenSide/Finish.lean), as an ordinary algorithm (plainOf, Johnson/TokenSide/Erased.lean),
does what the compiled prover's chain does at coins that are handed over at the start (Tie,
Johnson/TokenSide/Tie.lean). Definitions, and theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

Before its chain hashT draws the first salt (a token), the free bits of the string behind the slot
value and the sibling digests (values). Each is one coordinate of the coins (RunCo,
Johnson/TokenSide/Lens.lean). Behind these draws the compiled prover's coins coRun .. are coOf ..
(Johnson/TokenSide/TieChain.lean) at the drawn values (coRun_laid), and chain_tie
(Johnson/TokenSide/TieAll.lean) does the rest.

Main names (namespace OnBytes.TokenSide).
  patchP, get_patchP_ne, get_patchP_in   the coins with drawn sibling digests laid in.
  tie_digs    the draws of the sibling digests.
  coRun_laid  the compiled prover's coins behind the draws.
  cutCo       what finish reads of the coins.
  hash_tie    THE TIE. The family hands on the chain's outcome and cutCo of the coins. On the token
              side they are read off by outW and coinsK, at the store at the end.

Limits. All is said of the ERASED program (plainOf, Johnson/TokenSide/Erased.lean): tokens are
strings in a store, and the names fbw t k are written back to fb t. Nothing here speaks of these
names, or of the two modes of deferred programming (Rom/Defer.lean): they are the matter of
Johnson/HopSide/, Johnson/GhostSide/ and Compile/DeferRun/.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.TieAll
import Johnson.TokenSide.SpecSame

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
variable {Ω : Type} {μ : PMF Ω} {ln : RunLen lam L} {Z : RunCo → Prop}

/-! ## The sibling digests -/

/-- the coins with the sibling digests ds laid in, from number m on -/
def patchP (rl : RunLens Ω μ ln Z) : ℕ → List (Dig lam) → Ω → Ω
  | _, [], ω => ω
  | m, d :: ds, ω => rl.upd (.path m) d (patchP rl (m + 1) ds ω)

theorem get_patchP_ne (rl : RunLens Ω μ ln Z) (c : RunCo) (hc : ∀ n, c ≠ .path n) :
    ∀ (ds : List (Dig lam)) (m : ℕ) (ω : Ω), rl.get (patchP rl m ds ω) c = rl.get ω c
  | [], _, _ => rfl
  | d :: ds, m, ω => by
    show rl.get (rl.upd (.path m) d (patchP rl (m + 1) ds ω)) c = _
    rw [rl.get_ne (.path m) d _ c (hc m)]
    exact get_patchP_ne rl c hc ds (m + 1) ω

theorem get_patchP_in (rl : RunLens Ω μ ln Z) :
    ∀ (ds : List (Dig lam)) (m : ℕ) (ω : Ω) (n : ℕ) (d : Dig lam), ds[n]? = some d →
      Z (.path (m + n)) → rl.get (patchP rl m ds ω) (.path (m + n)) = List.ofFn d
  | [], _, _, _, _, h, _ => by simp at h
  | d0 :: ds, m, ω, 0, d, h, hz => by
    obtain rfl : d0 = d := by simpa using h
    exact rl.get_same (.path m) d0 _ hz
  | d0 :: ds, m, ω, n + 1, d, h, hz => by
    show rl.get (rl.upd (.path m) d0 (patchP rl (m + 1) ds ω)) (.path (m + (n + 1))) = _
    rw [rl.get_ne (.path m) d0 _ (.path (m + (n + 1))) (fun e => by
      have := RunCo.path.inj e
      omega), show m + (n + 1) = m + 1 + n by omega]
    exact get_patchP_in rl ds (m + 1) ω n d (by simpa using h)
      (by rwa [show m + 1 + n = m + (n + 1) by omega])

/-- The draws of the sibling digests: go on with the family read at the coins with the drawn digests
laid in. -/
theorem tie_digs {α β : Type} {φ : α → Ω → β} {Q : α → Prop} (rl : RunLens Ω μ ln Z)
    (vs : List Bits) :
    ∀ (n m : ℕ) (k : List (Dig lam) × List Bits → TypedOracleComputation lam K L α) (G : Ω → TypedOracleComputation lam K L β),
      (∀ j, m ≤ j → j < m + n → Z (.path j)) →
      (∀ ds : List (Dig lam), ds.length = n →
        Tie μ φ Q (k (ds, vs)) fun ω => G (patchP rl m ds ω)) →
      Tie μ φ Q ((plainOf (digsT (K := K) (L := L) n) vs).bind k) G
  | 0, _, _, _, _, h => h [] rfl
  | n + 1, m, k, G, hz, h => by
    show Tie μ φ Q (OComp.sample (2 ^ lam - 1) fun r =>
      (plainOf ((digsT (K := K) (L := L) n).bind fun ds =>
        Step.pure ((Life2.bitsE lam r : Dig lam) :: ds)) vs).bind k) G
    refine Tie.fresh lam (rl.upd (.path m)) (rl.law (.path m) (hz m (Nat.le_refl m) (by omega)))
      fun r => ?_
    rw [plainOf_bind, Tie.obind_assoc]
    exact tie_digs rl vs n (m + 1) (fun p => k ((Life2.bitsE lam r : Dig lam) :: p.1, p.2))
      (fun ω => G (rl.upd (.path m) (Life2.bitsE lam r) ω))
      (fun j h1 h2 => hz j (by omega) (by omega))
      fun ds hds => h ((Life2.bitsE lam r : Dig lam) :: ds) (by rw [List.length_cons, hds])

/-! ## The compiled prover's coins behind the draws -/

/-- **Behind the draws** of the first salt u0, the free bits u1 and the sibling digests ds. -/
theorem coRun_laid (rl : RunLens Ω μ ln Z) (pre : ℕ → Bool → Bits → Bits) (u0 : Fin ln.sFS → Bool)
    (u1 : Fin ln.rs → Bool) (ds : List (Dig lam)) (hds : ds.length = ln.dq) (h0 : Z .salt)
    (h1 : Z .rs) (h2 : ∀ n, n < ln.dq → Z (.path n)) (ω : Ω) :
    coRun rl pre (rl.upd .salt u0 (rl.upd .rs u1 (patchP rl 0 ds ω))) =
      coOf rl.leaf (List.ofFn u0) ⟨ln.pad, ln.slot, ds, List.ofFn u1 ++ ln.rsw⟩ pre ω := by
  have es : rl.get (rl.upd .salt u0 (rl.upd .rs u1 (patchP rl 0 ds ω))) .salt = List.ofFn u0 :=
    rl.get_same .salt u0 _ h0
  have er : rl.get (rl.upd .salt u0 (rl.upd .rs u1 (patchP rl 0 ds ω))) .rs = List.ofFn u1 := by
    rw [rl.get_ne .salt u0 _ .rs (by simp)]
    exact rl.get_same .rs u1 _ h1
  have el : ∀ i b k j, rl.get (rl.upd .salt u0 (rl.upd .rs u1 (patchP rl 0 ds ω))) (.leaf i b k j) =
      rl.get ω (.leaf i b k j) := fun i b k j => by
    rw [rl.get_ne .salt u0 _ _ (by simp), rl.get_ne .rs u1 _ _ (by simp),
      get_patchP_ne rl _ (fun n => by simp)]
  have ep : ((List.range ln.dq).map fun n =>
      digOf lam (rl.get (rl.upd .salt u0 (rl.upd .rs u1 (patchP rl 0 ds ω))) (.path n))) = ds := by
    refine List.ext_getElem (by rw [List.length_map, List.length_range, hds]) fun n hn1 hn2 => ?_
    rw [List.getElem_map, List.getElem_range, rl.get_ne .salt u0 _ _ (by simp),
      rl.get_ne .rs u1 _ _ (by simp)]
    have := get_patchP_in rl ds 0 ω n ds[n] (List.getElem?_eq_getElem hn2)
      (by rw [Nat.zero_add]; exact h2 n (hds ▸ hn2))
    rw [Nat.zero_add] at this
    rw [this, digOf_ofFn]
  unfold coRun coOf
  rw [es, er, ep]
  exact congrArg (fun f => (⟨List.ofFn u0, f, ln.pad, ln.slot, ds, List.ofFn u1 ++ ln.rsw⟩ :
    Coins lam L)) (funext fun i => funext fun b => funext fun k => funext fun j => by rw [el]; rfl)

/-- what finish reads of the coins -/
def cutCo (co : Coins lam L) : Coins lam L :=
  ⟨co.salt, fun _ _ _ _ => [], co.pad, co.slot, co.path, co.rsalt⟩

/-! ## The tie -/

/-- **All hashing of a compiled run.** -/
theorem hash_tie (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (σ : Strat Q.loc.shape Unit) (pre : ℕ → Bool → Bits → Bits)
    (cap : ℕ → ℕ) (rl : RunLens Ω μ ln Z) (vs : List Bits)
    (hC : CoversRun Z ln Q.loc.shape Q.ann wq.sh) :
    Tie μ
      (fun (p : (Tok × CoinsD lam L × Res (OutT lam L Q.loc.shape)) × List Bits) ω =>
        (p.1.2.2.map fun z =>
          (outW rl.leaf (fun i b => pre i b (p.2.getD p.1.1 [])) p.2 0 z ω).1,
          coinsK (p.2.getD p.1.1 []) p.1.2.1))
      (fun p => vs <+: p.2 ∧ p.1.1 < p.2.length ∧
        ∀ z, p.1.2.2 = .ok z → OutOK ln.fr Q.loc.shape Q.ann wq.sh z p.2)
      (plainOf (hashT t Q wq embS embP xin cms x σ ln pre cap) vs)
      (fun ω => (chainO t cms (xin x) (coRun rl pre ω) cap Q.loc.shape Q.ann wq.sh embS embP 0
        .first σ).bind fun r => .pure (r, cutCo (coRun rl pre ω))) := by
  obtain ⟨h0, h1, h2, h3⟩ := hC
  show Tie μ _ _ (OComp.sample (2 ^ ln.sFS - 1) fun r0 =>
    OComp.sample (2 ^ ln.rs - 1) fun r1 =>
      plainOf (((digsT (K := K) (L := L) ln.dq).bind fun ds =>
        Step.pure (⟨ln.pad, ln.slot, ds, List.ofFn (Life2.bitsE ln.rs r1) ++ ln.rsw⟩ :
          CoinsD lam L)).bind fun cd =>
        (chainT t cms (xin x) ln.fr pre vs.length cd cap Q.loc.shape Q.ann wq.sh embS embP 0 .first
          σ).bind fun r => Step.pure (vs.length, cd, r))
        (vs ++ [List.ofFn (Life2.bitsE ln.sFS r0)])) _
  refine Tie.fresh ln.sFS (rl.upd .salt) (rl.law .salt h0) fun r0 => ?_
  refine Tie.fresh ln.rs (rl.upd .rs) (rl.law .rs h1) fun r1 => ?_
  generalize Life2.bitsE ln.sFS r0 = u0
  generalize Life2.bitsE ln.rs r1 = u1
  rw [plainOf_bind, plainOf_bind, Tie.obind_assoc]
  refine tie_digs rl _ ln.dq 0 _ _ (fun j _ hj => h2 j (by omega)) fun ds hds => ?_
  have hsv : (vs ++ [List.ofFn u0]).getD vs.length [] = List.ofFn u0 := getD_length_append vs _ []
  have hT := chain_tie rl.leaf t cms (xin x) pre vs.length
    (⟨ln.pad, ln.slot, ds, List.ofFn u1 ++ ln.rsw⟩ : CoinsD lam L) cap Q.loc.shape Q.ann wq.sh embS
    embP 0 .first σ (vs ++ [List.ofFn u0]) (by simp) trivial h3
  rw [hsv] at hT
  show Tie μ _ _ (plainOf ((chainT t cms (xin x) ln.fr pre vs.length
      (⟨ln.pad, ln.slot, ds, List.ofFn u1 ++ ln.rsw⟩ : CoinsD lam L) cap Q.loc.shape Q.ann wq.sh
          embS
      embP 0 .first σ).bind fun r => Step.pure (vs.length,
        (⟨ln.pad, ln.slot, ds, List.ofFn u1 ++ ln.rsw⟩ : CoinsD lam L), r))
      (vs ++ [List.ofFn u0])) _
  rw [plainOf_bind]
  refine (hT.bind (f' := fun r' => .pure (r'.map Prod.fst,
    coinsK (List.ofFn u0) (⟨ln.pad, ln.slot, ds, List.ofFn u1 ++ ln.rsw⟩ : CoinsD lam L)))
    fun p hp => ?_).congr fun ω => ?_
  · have hp' : vs ++ [List.ofFn u0] <+: p.2 := hp.1
    have hv : p.2.getD vs.length [] = List.ofFn u0 := by
      rw [getD_of_prefix hp' (by simp), hsv]
    refine .done ⟨(List.prefix_append _ _).trans hp', ?_, hp.2⟩ fun ω => ?_
    · have := hp'.length_le
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      show vs.length < p.2.length
      omega
    · show OComp.pure _ = OComp.pure (p.1.map (fun z =>
        (outW rl.leaf (fun i b => pre i b (p.2.getD vs.length [])) p.2 0 z ω).1),
        coinsK (p.2.getD vs.length []) _)
      rw [hv]
      cases p.1 <;> rfl
  · beta_reduce
    rw [coRun_laid rl pre u0 u1 ds hds h0 h1 h2 ω, Tie.obind_assoc]
    refine congrArg _ (funext fun r => ?_)
    cases r <;> rfl

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.hash_tie
