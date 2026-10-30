-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/CountFAt.lean: chainF (Johnson/Prover/Law/CountF.lean: the compiled prover's hash
calls by the first-block exit) AS A CLOSED SUM over the written rounds' data, at caps that are
VALUES: 2^(work + 6) tries in a round with work.

Main names.
  capAt work    A DEFINITION: the cap of round number i: 2^(work i + 6) - 1 (so 2^(work i + 6)
    tries).
  roundF B p trees work   A DEFINITION: one written round in hash calls: its trees, the joining
    round's two queries and path (counted in every round, as chainN does), its search at that cap or
    one whole answer, and one whole answer more for the component that is not asked.
  Bare w        A DEFINITION: a round's wire record with no tree and no test.
  fsF_grOf, chainF_app, chainF_bare   steps.
  chainF_wiresSL, chainF_wiresLo, chainF_wiresSh   a stretch of written rounds.
  chainF_file, chainF_wqWhole, chainF_wqW   THE CLOSED SUMS. chainF_of_sums: the whole file's, from
    three sums that are given as numbers.

Limits. THE CAP IS A LETTER OF THE COMPILED PROVER (proveX): capAt is a value of our choosing for
it; no program's cap is spoken of. Equations between numbers that are read off lists: nothing on
which lists stand at any public files. The looseness of chainF is in the sums. p is the length of
the coins' path.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.CountF
import Johnson.Prover.Law.PassAt

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Run _root_.Run.PQ Compile.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Joined OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The cap of round number i: 2 ^ (work i + 6) - 1 (so 2 ^ (work i + 6) tries); 63 at work i = 0.
-/
def capAt (work : ℕ → ℕ) (i : ℕ) : ℕ := 2 ^ (work i + 6) - 1

/-- One written round in hash calls. B: the blocks of a whole answer; p: the path's length. -/
def roundF (B p : ℕ) (trees : List ℕ) (work : ℕ) : ℕ :=
  treesN trees + (2 + p) + ((if work = 0 then B else 2 ^ (work + 6) - 1 + B) + B)

theorem fsF_grOf (B n : ℕ) {Cc P : Type} : ∀ b : ℕ,
    fsF B ((grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr) n = if b = 0 then B else n + B
  | 0 => rfl
  | _ + 1 => rfl

theorem chainF_app {lam K : ℕ} : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K s A) (V : RoundsQueryLayout lam K u B) (cap : ℕ → ℕ) (i p : ℕ),
    chainF (s ++ u) (RoundSplits.app A B) (WireSB.app W V) cap i p =
      chainF s A W cap i p + chainF u B V cap (i + s.length) p
  | [], _, _, _, _, _, _, _, _ => (Nat.zero_add _).symm
  | r :: s, u, (_, A), B, (w, W), V, cap, i, p => by
    show treesN w.depthJ + treesN w.depth0 + (2 + p) +
        (fsF (K + 1) w.grJ (cap i) + fsF (K + 1) w.gr0 (cap i)) +
        chainF (s ++ u) (RoundSplits.app A B) (WireSB.app W V) cap (i + 1) p =
      treesN w.depthJ + treesN w.depth0 + (2 + p) +
        (fsF (K + 1) w.grJ (cap i) + fsF (K + 1) w.gr0 (cap i)) + chainF s A W cap (i + 1) p +
        chainF u B V cap (i + (r :: s).length) p
    rw [chainF_app W V cap (i + 1) p,
      show i + (r :: s).length = i + 1 + s.length by rw [List.length_cons]; omega]
    omega

section Wires
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (cap : ℕ → ℕ) (p : ℕ)

theorem chainF_wiresSL : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (i : ℕ),
    (∀ j (h : j < ds.length), cap (i + j) = 2 ^ (ds[j].entry.work + 6) - 1) →
    chainF (TypedOracleCompiler.Run.PQ.uL C ds) (Twin.allLo (TypedOracleCompiler.Run.PQ.SL C ds))
      (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) cap i p =
      (ds.map fun d => roundF (K + 2) p (d.trees.map (·.a)) d.entry.work).sum
  | [], _, _ => rfl
  | d :: ds, i, h => by
    have h0 : cap i = 2 ^ (d.entry.work + 6) - 1 := h 0 (Nat.succ_pos _)
    show treesN (d.trees.map (·.a)) + treesN [] + (2 + p) +
        (fsF (K + 1 + 1) ((grOf Dn (C.Ch d.entry d.kind) (PlainOf d.items) d.entry.work).map
          TypedOracleCompiler.Tagged.ofGr) (cap i) + (K + 1 + 1)) +
        chainF _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) cap (i + 1) p =
      roundF (K + 2) p (d.trees.map (·.a)) d.entry.work +
        (ds.map fun d => roundF (K + 2) p (d.trees.map (·.a)) d.entry.work).sum
    rw [chainF_wiresSL ds (i + 1) (fun j hj => by
        rw [show i + 1 + j = i + (j + 1) by omega]
        exact h (j + 1) (Nat.succ_lt_succ hj)), fsF_grOf, h0]
    unfold roundF
    rw [show treesN [] = 0 from rfl]
    generalize 2 ^ (d.entry.work + 6) - 1 = c
    by_cases hw : d.entry.work = 0
    · rw [if_pos hw]
      omega
    · rw [if_neg hw]
      omega

theorem chainF_wiresLo : ∀ (ds : List RDT) (i : ℕ),
    (∀ j (h : j < ds.length), cap (i + j) = 2 ^ (ds[j].entry.work + 6) - 1) →
    chainF (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) cap i p =
      (ds.map fun d => roundF (K + 2) p (d.trees.map (·.a)) d.entry.work).sum
  | [], _, _ => rfl
  | d :: ds, i, h => by
    have h0 : cap i = 2 ^ (d.entry.work + 6) - 1 := h 0 (Nat.succ_pos _)
    show treesN (d.trees.map (·.a)) + treesN [] + (2 + p) +
        (fsF (K + 1 + 1) ((grOf Dn (C.Ch d.entry d.kind) (PlainOf d.items) d.entry.work).map
          TypedOracleCompiler.Tagged.ofGr) (cap i) + (K + 1 + 1)) +
        chainF _ _ (wiresLo C K chal ds) cap (i + 1) p =
      roundF (K + 2) p (d.trees.map (·.a)) d.entry.work +
        (ds.map fun d => roundF (K + 2) p (d.trees.map (·.a)) d.entry.work).sum
    rw [chainF_wiresLo ds (i + 1) (fun j hj => by
        rw [show i + 1 + j = i + (j + 1) by omega]
        exact h (j + 1) (Nat.succ_lt_succ hj)), fsF_grOf, h0]
    unfold roundF
    rw [show treesN [] = 0 from rfl]
    generalize 2 ^ (d.entry.work + 6) - 1 = c
    by_cases hw : d.entry.work = 0
    · rw [if_pos hw]
      omega
    · rw [if_neg hw]
      omega

theorem chainF_wiresSh : ∀ (ds : List RDT) (i : ℕ),
    (∀ j (h : j < ds.length), cap (i + j) = 2 ^ (ds[j].entry.work + 6) - 1) →
    chainF (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) cap i p =
      (ds.map fun d => roundF (K + 2) p (d.trees.map (·.a)) d.entry.work).sum
  | [], _, _ => rfl
  | d :: ds, i, h => by
    have h0 : cap i = 2 ^ (d.entry.work + 6) - 1 := h 0 (Nat.succ_pos _)
    show treesN [] + treesN (d.trees.map (·.a)) + (2 + p) +
        ((K + 1 + 1) + fsF (K + 1 + 1) ((grOf Dn (C.Ch d.entry d.kind) (PlainOf d.items)
          d.entry.work).map TypedOracleCompiler.Tagged.ofGr) (cap i)) +
        chainF _ _ (wiresSh C K chal ds) cap (i + 1) p =
      roundF (K + 2) p (d.trees.map (·.a)) d.entry.work +
        (ds.map fun d => roundF (K + 2) p (d.trees.map (·.a)) d.entry.work).sum
    rw [chainF_wiresSh ds (i + 1) (fun j hj => by
        rw [show i + 1 + j = i + (j + 1) by omega]
        exact h (j + 1) (Nat.succ_lt_succ hj)), fsF_grOf, h0]
    unfold roundF
    rw [show treesN [] = 0 from rfl]
    generalize 2 ^ (d.entry.work + 6) - 1 = c
    by_cases hw : d.entry.work = 0
    · rw [if_pos hw]
      omega
    · rw [if_neg hw]
      omega

end Wires

/-! ## Whole files -/

/-- A round that sends no tree and has no test. -/
def Bare {lam K : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K r a) : Prop :=
  w.depthJ = [] ∧ w.depth0 = [] ∧ w.grJ = none ∧ w.gr0 = none

theorem chainF_bare {lam K : ℕ} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (h : Bare w) (cap : ℕ → ℕ) (i p : ℕ) :
    chainF (r :: s) (a, A) (w, W) cap i p = 2 + p + 2 * (K + 1) + chainF s A W cap (i + 1) p := by
  show treesN w.depthJ + treesN w.depth0 + (2 + p) +
    (fsF (K + 1) w.grJ (cap i) + fsF (K + 1) w.gr0 (cap i)) + chainF s A W cap (i + 1) p = _
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  show 0 + 0 + (2 + p) + (K + 1 + (K + 1)) + _ = _
  omega

/-- **Three stretches, each behind a bare round.** -/
theorem chainF_file {lam K : ℕ} {rF rJ r3 : Round} {s₁ s₂ s₃ : Shape} {aF : RAnn rF}
    {aJ : RAnn rJ} {a3 : RAnn r3} {A₁ : RoundSplits s₁} {A₂ : RoundSplits s₂} {A₃ : RoundSplits s₃}
    (wF : WireRB lam K rF aF) (wJ : WireRB lam K rJ aJ) (w3 : WireRB lam K r3 a3)
    (W₁ : RoundsQueryLayout lam K s₁ A₁) (W₂ : RoundsQueryLayout lam K s₂ A₂) (W₃ : RoundsQueryLayout lam K s₃ A₃)
    (hF : Bare wF) (hJ : Bare wJ) (h3 : Bare w3) (cap : ℕ → ℕ) (p : ℕ) :
    chainF (rF :: (s₁ ++ rJ :: (s₂ ++ r3 :: s₃))) (aF, RoundSplits.app A₁ (aJ, RoundSplits.app A₂ (a3, A₃)))
      (wF, WireSB.app (u := rJ :: (s₂ ++ r3 :: s₃)) (B := (aJ, RoundSplits.app A₂ (a3, A₃))) W₁
        (wJ, WireSB.app (u := r3 :: s₃) (B := (a3, A₃)) W₂ (w3, W₃))) cap 0 p =
      3 * (2 + p + 2 * (K + 1)) + (chainF s₁ A₁ W₁ cap 1 p +
        chainF s₂ A₂ W₂ cap (1 + s₁.length + 1) p +
        chainF s₃ A₃ W₃ cap (1 + s₁.length + 1 + s₂.length + 1) p) := by
  rw [chainF_bare wF _ hF, chainF_app (u := rJ :: (s₂ ++ r3 :: s₃))
      (B := (aJ, RoundSplits.app A₂ (a3, A₃))) W₁, chainF_bare wJ _ hJ,
    chainF_app (u := r3 :: s₃) (B := (a3, A₃)) W₂, chainF_bare w3 _ h3]
  simp only [Nat.zero_add]
  omega

section Files
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (p : ℕ)

/-- **THE COPY's FILE, AS A CLOSED SUM.** -/
theorem chainF_wqW (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {Y : Type}
    (dec : Y → View → Bool) :
    chainF (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.ann
      (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh (capAt (workL ds)) 0 p =
      2 + p + 2 * (K + 2) +
        (ds.map fun d => roundF (K + 2) p (d.trees.map (·.a)) d.entry.work).sum :=
  (chainF_bare (TypedOracleCompiler.Run.PQ.wire0S C K chal) (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds)
    ⟨rfl, rfl, rfl, rfl⟩ _ 0 p).trans (congrArg (2 + p + 2 * (K + 2) + ·)
      (chainF_wiresSL C K chal _ p ds (0 + 1) fun j h => by
        unfold capAt workL
        rw [show 0 + 1 + j = j + 1 by omega, List.getD_cons_succ, getD_map_at _ ds j h]))

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **A WHOLE FILE, AS A CLOSED SUM.** -/
theorem chainF_wqWhole :
    chainF (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wqWhole C K chal D tF tJ t3 silent run).sh (capAt (Page.workAt D)) 0 p =
      3 * (2 + p + 2 * (K + 2)) +
        ((D.ds₁.map fun d => roundF (K + 2) p (d.trees.map (·.a)) d.entry.work).sum +
          (D.ds₂.map fun d => roundF (K + 2) p (d.trees.map (·.a)) d.entry.work).sum +
          (D.ds₃.map fun d => roundF (K + 2) p (d.trees.map (·.a)) d.entry.work).sum) := by
  have l₁ : (uLT C D.ds₁).length = D.ds₁.length := length_uLT C D.ds₁
  have l₂ : (uLT C D.ds₂).length = D.ds₂.length := length_uLT C D.ds₂
  refine (chainF_file (wireSilent (K + 1) TF tF _) (wireSilent (K + 1) TJ tJ _)
    (wireSilent (K + 1) T3 t3 _) (wiresLo C K chal D.ds₁) (wiresSh C K chal D.ds₂)
    (wiresLo C K chal D.ds₃) ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ _
    p).trans ?_
  rw [chainF_wiresLo C K chal _ p D.ds₁ 1 (fun j h => by unfold capAt; rw [workAt_1 D j h]),
    chainF_wiresSh C K chal _ p D.ds₂ _ (fun j h => by unfold capAt; rw [l₁, workAt_2 D j h]),
    chainF_wiresLo C K chal _ p D.ds₃ _ (fun j h => by
      unfold capAt
      rw [l₁, l₂, workAt_3 D j h])]

/-- The same from three sums that are given as numbers. B: the blocks of a whole answer. -/
theorem chainF_of_sums (B : ℕ) (hB : K + 2 = B) (n₁ n₂ n₃ : ℕ)
    (h₁ : (D.ds₁.map fun d => roundF B p (d.trees.map (·.a)) d.entry.work).sum = n₁)
    (h₂ : (D.ds₂.map fun d => roundF B p (d.trees.map (·.a)) d.entry.work).sum = n₂)
    (h₃ : (D.ds₃.map fun d => roundF B p (d.trees.map (·.a)) d.entry.work).sum = n₃) :
    chainF (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wqWhole C K chal D tF tJ t3 silent run).sh (capAt (Page.workAt D)) 0 p =
      3 * (2 + p + 2 * B) + (n₁ + n₂ + n₃) := by
  subst hB
  rw [chainF_wqWhole, h₁, h₂, h₃]

end Files

end OnBytes.Prover

#print axioms OnBytes.Prover.fsF_grOf
#print axioms OnBytes.Prover.chainF_app
#print axioms OnBytes.Prover.chainF_wiresSL
#print axioms OnBytes.Prover.chainF_wiresLo
#print axioms OnBytes.Prover.chainF_wiresSh
#print axioms OnBytes.Prover.chainF_bare
#print axioms OnBytes.Prover.chainF_file
#print axioms OnBytes.Prover.chainF_wqW
#print axioms OnBytes.Prover.chainF_wqWhole
#print axioms OnBytes.Prover.chainF_of_sums
