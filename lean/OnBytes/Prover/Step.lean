-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Step.lean: the compiled prover's chain (OnBytes/Prover/Defs.lean) under fixed oracle
functions, one round at a time: the search for a nonce, a Fiat-Shamir query, what kind and phase say
of a round, and the value of the chain over a round and the rest.

Main names:
  `det_searchO_succ`, `search_some`, `search_none_iff`, `search_mono`   the search's value: the
        first nonce whose test bits are all 0; it runs out exactly if every nonce that it may try
        fails; more fuel keeps what less fuel has found
  `fs_some`, `fs_none`, `fs_mono`   the like for a Fiat-Shamir query with a test or without
  `act_own`, `act_shared`, `act_join`, `act_none`   what follows from the act of a round (actOf)
  `det_own`, `det_shared`, `det_join`, `det_noFormat`   the chain's value over a round and the rest,
        by the round's act, written without queries (`tJ`, `t0`, `rest`, `askJ`, `ask0`, `slotV`,
        `reqRoot`, `onFsF`)

Limits: nothing on probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Tree

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The search -/

section Search
variable {C P : Type} (g : Fam (typedOracleFamily lam K L)) (gr : GrW C P) (chal : (Fin K → Dig lam) → C)
  (ask : P → TypedOracleComputation lam K L (FsAns lam K)) (α : P)

theorem det_searchO_succ (fuel n : ℕ) :
    (searchO gr chal ask α (fuel + 1) n).det g =
      if gr.ok (chal ((ask (gr.put n α)).det g).1) then
        some (gr.put n α, (ask (gr.put n α)).det g)
      else (searchO gr chal ask α fuel (n + 1)).det g := by
  show ((ask (gr.put n α)).bind fun a =>
    if gr.ok (chal a.1) then OComp.pure (some (gr.put n α, a))
    else searchO gr chal ask α fuel (n + 1)).det g = _
  rw [OComp.det_bind, apply_ite (OComp.det g)]
  rfl

/-- What a search returns: a nonce that it may try, written in; the answer at it; the test passed.
-/
theorem search_some : ∀ (fuel n : ℕ) (β : P) (a : FsAns lam K),
    (searchO gr chal ask α fuel n).det g = some (β, a) →
    ∃ m, β = gr.put m α ∧ a = (ask β).det g ∧ gr.ok (chal a.1) = true
  | 0, _, _, _, h => by cases h
  | fuel + 1, n, β, a, h => by
    rw [det_searchO_succ] at h
    by_cases hk : gr.ok (chal ((ask (gr.put n α)).det g).1) = true
    · rw [if_pos hk] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨n, rfl, rfl, hk⟩
    · rw [if_neg hk] at h
      exact search_some fuel (n + 1) β a h

/-- **A search runs out exactly if every nonce that it may try fails.** -/
theorem search_none_iff : ∀ (fuel n₀ : ℕ),
    (searchO gr chal ask α fuel n₀).det g = none ↔
      ∀ k < fuel, gr.ok (chal ((ask (gr.put (n₀ + k) α)).det g).1) = false
  | 0, _ => ⟨fun _ _ hk => absurd hk (Nat.not_lt_zero _), fun _ => rfl⟩
  | fuel + 1, n₀ => by
    rw [det_searchO_succ]
    by_cases hk : gr.ok (chal ((ask (gr.put n₀ α)).det g).1) = true
    · rw [if_pos hk]
      constructor
      · intro h
        cases h
      · intro h
        have := h 0 (Nat.succ_pos _)
        rw [Nat.add_zero, hk] at this
        cases this
    · rw [if_neg hk, search_none_iff fuel (n₀ + 1)]
      constructor
      · intro h k hlt
        cases k with
        | zero => simpa using hk
        | succ k =>
          have := h k (by omega)
          rwa [show n₀ + 1 + k = n₀ + (k + 1) by omega] at this
      · intro h k hlt
        have := h (k + 1) (by omega)
        rwa [show n₀ + (k + 1) = n₀ + 1 + k by omega] at this

/-- More fuel keeps what less fuel has found. -/
theorem search_mono : ∀ (fuel fuel' n : ℕ) (r : P × FsAns lam K), fuel ≤ fuel' →
    (searchO gr chal ask α fuel n).det g = some r → (searchO gr chal ask α fuel' n).det g = some r
  | 0, _, _, _, _, h => by cases h
  | fuel + 1, 0, _, _, hle, _ => absurd hle (by omega)
  | fuel + 1, fuel' + 1, n, r, hle, h => by
    rw [det_searchO_succ] at h ⊢
    by_cases hk : gr.ok (chal ((ask (gr.put n α)).det g).1) = true
    · rw [if_pos hk] at h ⊢
      exact h
    · rw [if_neg hk] at h ⊢
      exact search_mono fuel fuel' (n + 1) r (by omega) h

end Search

/-! ## A Fiat-Shamir query -/

section Fs
variable {C P : Type} (g : Fam (typedOracleFamily lam K L)) (gr : Option (GrW C P)) (cap : ℕ)
  (chal : (Fin K → Dig lam) → C) (ask : P → TypedOracleComputation lam K L (FsAns lam K)) (α : P)

/-- What a Fiat-Shamir query returns: the plain part that was hashed is α, or α with a number
written in and the test passed; the answer is the oracle's at that plain part. -/
theorem fs_some {β : P} {a : FsAns lam K} (h : (fsO gr cap chal ask α).det g = some (β, a)) :
    a = (ask β).det g ∧
      ((gr = none ∧ β = α) ∨ ∃ r n, gr = some r ∧ β = r.put n α ∧ r.ok (chal a.1) = true) := by
  cases gr with
  | none =>
    have h' : some (α, (ask α).det g) = some (β, a) := by
      rw [← h]
      show _ = ((ask α).bind fun a => OComp.pure (some (α, a))).det g
      rw [OComp.det_bind]
      rfl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | some r =>
    obtain ⟨n, h1, h2, h3⟩ := search_some g r chal ask α (cap + 1) 0 β a h
    exact ⟨h2, Or.inr ⟨r, n, rfl, h1, h3⟩⟩

/-- It runs out only where there is a test. -/
theorem fs_none (h : (fsO gr cap chal ask α).det g = none) : gr.isSome = true := by
  cases gr with
  | none =>
    have h' : ((ask α).bind fun a => OComp.pure (some (α, a))).det g = none := h
    rw [OComp.det_bind] at h'
    cases h'
  | some _ => rfl

theorem fs_mono {cap' : ℕ} (hle : cap ≤ cap') {r : P × FsAns lam K}
    (h : (fsO gr cap chal ask α).det g = some r) : (fsO gr cap' chal ask α).det g = some r := by
  cases gr with
  | none => exact h
  | some q => exact search_mono g q chal ask α (cap + 1) (cap' + 1) 0 r (by omega) h

end Fs

/-! ## What kind and phase say of a round -/

section Act
variable {cms : List (Dig lam)} {x : Option X} {salt : Bits} {k : Kind} {ph : Phase lam}

theorem act_own {h : Head lam X} {next : Bits → Phase lam}
    (e : actOf cms x salt k ph = some (.one h true next)) :
    k = .lo ∧ (∀ v, fph (next v) = (fph ph).afterLo) ∧ ∀ v, (next v).slotVal = ph.slotVal := by
  cases k <;> cases ph <;> simp only [actOf, Option.some.injEq, Act.one.injEq, reduceCtorEq,
    Bool.false_eq_true, false_and, and_false] at e <;>
  · obtain ⟨-, -, rfl⟩ := e
    exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem act_shared {h : Head lam X} {next : Bits → Phase lam}
    (e : actOf cms x salt k ph = some (.one h false next)) :
    k = .sh ∧ fph ph = .shr ∧ (∀ v, fph (next v) = .shr) ∧ (∀ v, (next v).slotVal = ph.slotVal) ∧
      ph.slotVal ≠ none := by
  cases k <;> cases ph <;> simp only [actOf, Option.some.injEq, Act.one.injEq, reduceCtorEq,
    Bool.true_eq_false, false_and, and_false] at e
  obtain ⟨-, -, rfl⟩ := e
  exact ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, fun h => by cases h⟩

theorem act_join {ρ : Bits} (e : actOf cms x salt k ph = some (.join ρ)) : k = .sh ∧
    ph = .loc ρ := by
  cases k <;> cases ph <;> simp only [actOf, Option.some.injEq, Act.join.injEq, reduceCtorEq] at e
  subst e
  exact ⟨rfl, rfl⟩

theorem act_none (e : actOf cms x salt k ph = none) :
    k = .sh ∧ (fph ph = .first ∨ fph ph = .aft) := by
  cases k <;> cases ph <;> simp only [actOf, reduceCtorEq] at e
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩

end Act

/-! ## The chain over a round and the rest -/

/-- `onFs` on values -/
def onFsF {P β : Type} (i : ℕ) (k : P × FsAns lam K → Res β) : Option (P × FsAns lam K) → Res β
  | none => .ranOut i
  | some p => k p

theorem det_onFs (g : Fam (typedOracleFamily lam K L)) {P β : Type} (i : ℕ)
    (k : P × FsAns lam K → TypedOracleComputation lam K L (Res β)) (o : Option (P × FsAns lam K)) :
    (onFs i k o).det g = onFsF i (fun p => (k p).det g) o := by
  cases o <;> rfl

section Cons
variable (g : Fam (typedOracleFamily lam K L)) (t : Tag) (cms : List (Dig lam)) (x : Option X)
  (co : Coins lam L) (cap : ℕ → ℕ) {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
  (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (m : r.Msg)
  (k : r.Chal → Strat s Unit)

/-- the trees over the slot's component of the round, under g -/
def tJ : List (TreeK lam L) :=
  (treesO (K := K) co.pad (co.leaf i true) w.posAtJ (fun p => embS (.inl p)) m.1 0 w.depthJ).det g

/-- the trees over the shared component -/
def t0 : List (TreeK lam L) :=
  (treesO (K := K) co.pad (co.leaf i false) w.posAt0 (fun p => embS (.inl p)) m.1 0 w.depth0).det g

/-- the chain over the rest of the rounds, from the phase ph' on, after the verifier message c -/
def rest (ph' : Phase lam) (c : r.Chal) : Res (OutP lam L s) :=
  (chainO t cms x co cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) ph'
    (k c)).det g

/-- the round's Fiat-Shamir query with the slot's component -/
def askJ (h : Head lam X) (α : a.Pj) : TypedOracleComputation lam K L (FsAns lam K) :=
  askTypedOracle (L := L) (K := K) (OracleName.fb t)
    (⟨i, h, (tJ g co w embS i m).map TreeK.root, embP (.inl (.inr α))⟩ : FbIn lam L t)

/-- with the shared component -/
def ask0 (h : Head lam X) (α : a.P0) : TypedOracleComputation lam K L (FsAns lam K) :=
  askTypedOracle (L := L) (K := K) (OracleName.fb t)
    (⟨i, h, (t0 g co w embS i m).map TreeK.root, embP (.inl (.inl α))⟩ : FbIn lam L t)

/-- the slot value: the answer to the joining round's query to g -/
def slotV (ρ : Bits) : Dig lam :=
  g (OracleName.g t) (⟨i, ρ, (tJ g co w embS i m).map TreeK.root, embP (.inl (.inr (a.plain m.2).2))⟩ :
            JoiningRoundQuery lam L t)

/-- the request root that the prover makes from a slot value -/
def reqRoot (c : Dig lam) : Dig lam :=
  climbF (TypedOracleCompiler.Run.rnodeF g) co.path co.slot (g OracleName.rleaf (List.ofFn c ++ co.rsalt : Bits))

theorem det_own {h : Head lam X} {next : Bits → Phase lam}
    (e : actOf cms (x.map L.early) co.salt a.kind ph = some (.one h true next)) :
    (chainO t cms x co cap (r :: s) (a, A) (w, W) embS embP i ph (m, k)).det g =
      onFsF i (fun q => (rest g t cms x co cap W embS embP i k (next (List.ofFn q.2.2))
          (w.chal q.2.1)).map (consP (w.chal q.2.1)
            ((m.1, a.plain.symm ((a.plain m.2).1, q.1)), [], tJ g co w embS i m) none))
        ((fsO w.grJ (cap i) w.chal (askJ g t co w embS embP i m (h.withLate (lateInstancePart L i x)))
          (a.plain m.2).2).det g) := by
  simp only [chainO, e, OComp.det_bind, det_onFs]
  rfl

theorem det_shared {h : Head lam X} {next : Bits → Phase lam}
    (e : actOf cms (x.map L.early) co.salt a.kind ph = some (.one h false next)) :
    (chainO t cms x co cap (r :: s) (a, A) (w, W) embS embP i ph (m, k)).det g =
      onFsF i (fun q => (rest g t cms x co cap W embS embP i k (next (List.ofFn q.2.2))
          (w.chal q.2.1)).map (consP (w.chal q.2.1)
            ((m.1, a.plain.symm (q.1, (a.plain m.2).2)), t0 g co w embS i m, []) none))
        ((fsO w.gr0 (cap i) w.chal (ask0 g t co w embS embP i m h) (a.plain m.2).1).det g) := by
  simp only [chainO, e, OComp.det_bind, det_onFs]
  rfl

theorem det_join {ρ : Bits}
    (e : actOf cms (x.map L.early) co.salt a.kind ph = some (.join ρ)) :
    (chainO t cms x co cap (r :: s) (a, A) (w, W) embS embP i ph (m, k)).det g =
      onFsF i (fun q => (rest g t cms x co cap W embS embP i k
          (.shr (List.ofFn q.2.2) (slotV g t co w embS embP i m ρ)) (w.chal q.2.1)).map
            (consP (w.chal q.2.1)
              ((m.1, a.plain.symm (q.1, (a.plain m.2).2)), t0 g co w embS i m, tJ g co w embS i m)
              (some (reqRoot g co (slotV g t co w embS embP i m ρ)))))
        ((fsO w.gr0 (cap i) w.chal (ask0 g t co w embS embP i m
            (.f4 cms (List.ofFn (reqRoot g co (slotV g t co w embS embP i m ρ)))))
          (a.plain m.2).1).det g) := by
  have hc : ∀ d : Dig lam, (climbM (rnodeV (K := K) (L := L)) co.path co.slot d).det g =
      climbF (TypedOracleCompiler.Run.rnodeF g) co.path co.slot d := fun d =>
    Evaluates.climbM (evaluates_det g) (qN := rnodeV (K := K) (L := L))
      (hN := TypedOracleCompiler.Run.rnodeF g) (fun _ _ => rfl) co.path co.slot d
  simp only [chainO, e, OComp.det_bind, det_onFs, hc]
  rfl

theorem det_noFormat (e : actOf cms (x.map L.early) co.salt a.kind ph = none) :
    (chainO t cms x co cap (r :: s) (a, A) (w, W) embS embP i ph (m, k)).det g = .noFormat := by
  simp only [chainO, e]
  rfl

end Cons

end OnBytes.Prover
