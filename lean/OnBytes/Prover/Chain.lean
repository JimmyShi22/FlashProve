-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Chain.lean: under fixed oracle functions, whatever the compiled prover's chain yields
(OnBytes/Prover/Defs.lean), the verifier's chain recomputes from the roots and plain parts that the
prover has kept; and what is kept meets the invariant of OnBytes/Prover/Inv.lean.

Main names:
  `chain_after`   from a phase that holds a slot value on: no request root is made, the slot value
                  stays
  `chain_req`     from a phase without a slot value on: if the last phase holds the slot value c,
                  the request root that was made is the climb from the leaf of c
  `chain_joined`, `chain_unjoined`   where some round is shared the last phase holds a slot value
                  and a request root was made; where none is, neither
  `ChainAt`, `chain_at`   THE PIECE: the invariant; the verifier's chain (chainF) at the kept roots
                  and plain parts has the prover's verifier messages, these roots and the prover's
                  last phase for its value; no root is left over; all tests are passed; the
                  transcript as hashed is the strategy's own run but for nonces; every kept leaf's
                  salt is the coins'

Limits: nothing on probability. When the chain yields a value at all: OnBytes/Prover/Returns.lean.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Step

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run (chainF rnodeF)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Outcomes -/

theorem Res.map_eq_ok {α β : Type} {f : α → β} {r : Res α} {b : β} (h : r.map f = .ok b) :
    ∃ a, r = .ok a ∧ f a = b := by
  cases r with
  | ok a => exact ⟨a, rfl, Res.ok.inj h⟩
  | noFormat => cases h
  | ranOut i => cases h

theorem onFsF_eq_ok {P β : Type} {i : ℕ} {k : P × FsAns lam K → Res β}
    {o : Option (P × FsAns lam K)} {z : β} (h : onFsF i k o = .ok z) :
    ∃ p, o = some p ∧ k p = .ok z := by
  cases o with
  | none => cases h
  | some p => exact ⟨p, rfl, h⟩

/-! ## The request root -/

section
variable (g : Fam (typedOracleFamily lam K L)) (t : Tag) (cms : List (Dig lam)) (x : Option X)
  (co : Coins lam L) (cap : ℕ → ℕ)

/-- From a phase that holds a slot value on: no request root is made, and the slot value stays. -/
theorem chain_after : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (z : OutP lam L s) (c : Dig lam),
    (chainO t cms x co cap s A W embS embP i ph σ).det g = .ok z → ph.slotVal = some c →
    z.2.2.2 = none ∧ z.2.2.1.slotVal = some c
  | [], _, _, _, _, _, ph, _, z, c, hz, hc => by
    obtain rfl : ((), (), ph, none) = z := Res.ok.inj hz
    exact ⟨rfl, hc⟩
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), z, c, hz, hc => by
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      rw [det_noFormat g t cms x co cap w W embS embP i ph m k e] at hz
      cases hz
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          rw [det_own g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, -, hq⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq
          exact chain_after s A W _ _ (i + 1) _ _ z' c hz' (((act_own e).2.2 _).trans hc)
        | false =>
          rw [det_shared g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, -, hq⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq
          exact chain_after s A W _ _ (i + 1) _ _ z' c hz' (((act_shared e).2.2.2.1 _).trans hc)
      | join ρ =>
        rw [(act_join e).2] at hc
        cases hc

/-- From a phase without a slot value on: if the last phase holds the slot value c, the request root
that was made is the climb from the leaf of c. -/
theorem chain_req : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (z : OutP lam L s) (c : Dig lam),
    (chainO t cms x co cap s A W embS embP i ph σ).det g = .ok z → ph.slotVal = none →
    z.2.2.1.slotVal = some c → z.2.2.2 = some (reqRoot g co c)
  | [], _, _, _, _, _, ph, _, z, c, hz, hn, hc => by
    obtain rfl : ((), (), ph, none) = z := Res.ok.inj hz
    rw [show ph.slotVal = none from hn] at hc
    cases hc
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), z, c, hz, hn, hc => by
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      rw [det_noFormat g t cms x co cap w W embS embP i ph m k e] at hz
      cases hz
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          rw [det_own g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, -, hq⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq
          exact chain_req s A W _ _ (i + 1) _ _ z' c hz' (((act_own e).2.2 _).trans hn) hc
        | false => exact absurd hn (act_shared e).2.2.2.2
      | join ρ =>
        rw [det_join g t cms x co cap w W embS embP i ph m k e] at hz
        obtain ⟨q, -, hq⟩ := onFsF_eq_ok hz
        obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq
        have h2 := (chain_after g t cms x co cap s A W _ _ (i + 1) _ _ z' _ hz' rfl).2
        obtain rfl : slotV g t co w embS embP i m ρ = c :=
          Option.some.inj (h2.symm.trans hc)
        rfl

end

/-! ## Joined or not -/

section
variable (g : Fam (typedOracleFamily lam K L)) (t : Tag) (cms : List (Dig lam)) (x : Option X)
  (co : Coins lam L) (cap : ℕ → ℕ)

/-- Where some round is shared: the last phase holds a slot value, and a request root was made. -/
theorem chain_joined : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (z : OutP lam L s),
    (chainO t cms x co cap s A W embS embP i ph σ).det g = .ok z → ph.slotVal = none →
    anySh s A = true → z.2.2.1.slotVal.isSome = true ∧ z.2.2.2.isSome = true
  | [], _, _, _, _, _, _, _, _, _, _, h => by cases h
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), z, hz, hn, hA => by
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      rw [det_noFormat g t cms x co cap w W embS embP i ph m k e] at hz
      cases hz
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          rw [det_own g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, -, hq⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq
          simp only [anySh, (act_own e).1] at hA
          exact chain_joined s A W _ _ (i + 1) _ _ z' hz' (((act_own e).2.2 _).trans hn) hA
        | false => exact absurd hn (act_shared e).2.2.2.2
      | join ρ =>
        rw [det_join g t cms x co cap w W embS embP i ph m k e] at hz
        obtain ⟨q, -, hq⟩ := onFsF_eq_ok hz
        obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq
        have h2 := (chain_after g t cms x co cap s A W _ _ (i + 1) _ _ z' _ hz' rfl).2
        exact ⟨by show z'.2.2.1.slotVal.isSome = true; rw [h2]; rfl, rfl⟩

/-- Where no round is shared: the last phase holds no slot value, and no request root was made. -/
theorem chain_unjoined : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (z : OutP lam L s),
    (chainO t cms x co cap s A W embS embP i ph σ).det g = .ok z → ph.slotVal = none →
    anySh s A = false → z.2.2.1.slotVal = none ∧ z.2.2.2 = none
  | [], _, _, _, _, _, ph, _, z, hz, hn, _ => by
    obtain rfl : ((), (), ph, none) = z := Res.ok.inj hz
    exact ⟨hn, rfl⟩
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), z, hz, hn, hA => by
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      rw [det_noFormat g t cms x co cap w W embS embP i ph m k e] at hz
      cases hz
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          rw [det_own g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, -, hq⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq
          simp only [anySh, (act_own e).1] at hA
          exact chain_unjoined s A W _ _ (i + 1) _ _ z' hz' (((act_own e).2.2 _).trans hn) hA
        | false => exact absurd hn (act_shared e).2.2.2.2
      | join ρ =>
        simp only [anySh, (act_join e).1] at hA
        cases hA

end

/-! ## The piece -/

theorem takeRt_app {n : ℕ} {l r : List (Dig lam)} (h1 : l.length = n) (h2 : n ≤
    TypedOracleCompiler.Iop.maxRt) :
    takeRt n (l ++ r) = some (l, r) := by
  subst h1
  unfold takeRt
  rw [if_pos ⟨h2, by rw [List.length_append]; omega⟩, List.take_left', List.drop_left'] <;> rfl

theorem pass_lo {r : Round} {a : RAnn r} {w : WireRB lam K r a} {c : r.Chal} (hk : a.kind = .lo)
    (h : w.grJ = none ∨ ∃ q, w.grJ = some q ∧ q.ok c = true) : w.pass c = true := by
  unfold TypedOracleCompiler.Iop.WireRB.pass
  rw [hk]
  rcases h with h | ⟨q, h, hq⟩
  · simp only [h]
  · simp only [h, hq]

theorem pass_sh {r : Round} {a : RAnn r} {w : WireRB lam K r a} {c : r.Chal} (hk : a.kind = .sh)
    (h : w.gr0 = none ∨ ∃ q, w.gr0 = some q ∧ q.ok c = true) : w.pass c = true := by
  unfold TypedOracleCompiler.Iop.WireRB.pass
  rw [hk]
  rcases h with h | ⟨q, h, hq⟩
  · simp only [h]
  · simp only [h, hq]

theorem tJ_salt (g : Fam (typedOracleFamily lam K L)) (co : Coins lam L) {r : Round} {s : Shape} {a : RAnn r}
    (w : WireRB lam K r a) (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L) (i : ℕ)
    (m : r.Msg) (k : ℕ) (T : TreeK lam L) (h : (tJ g co w embS i m)[k]? = some T) (j : ℕ) :
    (T.inp j).salt = co.leaf i true k j := by
  have := treesO_salt g co.pad (co.leaf i true) w.posAtJ (fun p => embS (.inl p)) m.1 0 w.depthJ
    k T h j
  rwa [Nat.zero_add] at this

theorem t0_salt (g : Fam (typedOracleFamily lam K L)) (co : Coins lam L) {r : Round} {s : Shape} {a : RAnn r}
    (w : WireRB lam K r a) (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L) (i : ℕ)
    (m : r.Msg) (k : ℕ) (T : TreeK lam L) (h : (t0 g co w embS i m)[k]? = some T) (j : ℕ) :
    (T.inp j).salt = co.leaf i false k j := by
  have := treesO_salt g co.pad (co.leaf i false) w.posAt0 (fun p => embS (.inl p)) m.1 0 w.depth0
    k T h j
  rwa [Nat.zero_add] at this

/-- What the prover's chain has yielded (z), against the verifier's chain at the request root rq and
the roots R round by round. -/
structure ChainAt (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (co : Coins lam L) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (z : OutP lam L s) (rq : Dig lam) (R : RootsOfChain lam s) :
    Prop where
  /-- what is kept meets the invariant -/
  rounds : RoundsAt g sMT s A W embS z.2.1 R
  /-- the verifier's chain recomputes the prover's -/
  chain : chainF g t cms x co.salt rq s A W embP i ph (rootsK s z.2.1) (trK s z.2.1 z.1).plains =
    some (z.1, R, z.2.2.1)
  /-- no root is left over -/
  count : RootsOfChain.count s R = (rootsK s z.2.1).length
  /-- all tests are passed -/
  pass : RoundsQueryLayout.pass s A W z.1 = true
  /-- the transcript as hashed is the strategy's own run but for nonces -/
  puts : Puts s A W (σ.run z.1).1 (trK s z.2.1 z.1)
  /-- every kept leaf's salt is the coins' -/
  salts : SaltsAt co i s z.2.1

section
variable (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X)
  (co : Coins lam L) (cap : ℕ → ℕ) (hs : ∀ i b k j, (co.leaf i b k j).length = sMT)
include hs

/-- **Whatever the prover's chain yields, the verifier's chain recomputes.** rq: the request root of
the proof string: the one that the prover has made, if it has made one in these rounds. -/
theorem chain_at : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (z : OutP lam L s),
    (chainO t cms x co cap s A W embS embP i ph σ).det g = .ok z →
    RoundSplits.FmtFrom s A (fph ph) → FewJ s A W → Few0 s A W →
    ∀ rq : Dig lam, (∀ r, z.2.2.2 = some r → r = rq) →
    ∃ R : RootsOfChain lam s, ChainAt g sMT t cms x co s A W embS embP i ph σ z rq R
  | [], _, _, _, _, _, ph, _, z, hz, _, _, _, _, _ => by
    obtain rfl : ((), (), ph, none) = z := Res.ok.inj hz
    exact ⟨(), trivial, rfl, rfl, rfl, trivial, trivial⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), z, hz, hF, hJ, h0, rq, hrq => by
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      rw [det_noFormat g t cms x co cap w W embS embP i ph m k e] at hz
      cases hz
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          rw [det_own g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
          obtain ⟨hk, hn, -⟩ := act_own e
          obtain ⟨hans, hgr⟩ := fs_some g _ _ _ _ _ hq
          simp only [RoundSplits.FmtFrom, hk] at hF
          obtain ⟨R', ih⟩ := chain_at s A W _ _ (i + 1) _ _ z' hz' (by rw [hn]; exact hF.2)
            hJ.2 h0.2 rq hrq
          have hc : CompAt g sMT w.posAtJ (fun p => embS (.inl p)) m.1 w.depthJ
              (tJ g co w embS i m) := treesO_at0 g sMT _ _ _ _ _ (hs i true) _
          have hpl : (a.plain (a.plain.symm ((a.plain m.2).1, q.1))).2 = q.1 := by
            rw [Equiv.apply_symm_apply]
          refine ⟨((none, some ((tJ g co w embS i m).map TreeK.root)), R'), ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact ⟨Or.inl ⟨rfl, rfl, hF.1⟩, Or.inr ⟨rfl, hc⟩, ih.rounds⟩
          · show chainF g t cms x co.salt rq (r :: s) (a, A) (w, W) embP i ph
              ((tJ g co w embS i m).map TreeK.root ++ rootsK s z'.2.1)
              (a.plain.symm ((a.plain m.2).1, q.1), (trK s z'.2.1 z'.1).plains) = _
            have hT : takeRt w.depthJ.length
                ((tJ g co w embS i m).map TreeK.root ++ rootsK s z'.2.1) =
                  some ((tJ g co w embS i m).map TreeK.root, rootsK s z'.2.1) :=
              takeRt_app (by rw [List.length_map]; exact hc.1) hJ.1
            simp only [TypedOracleCompiler.Run.chainF, e, hT, hpl]
            rw [show g (OracleName.fb t) (⟨i, h.withLate (lateInstancePart L i x), (tJ g co w embS i m).map TreeK.root,
                      embP (.inl (.inr q.1))⟩ : FbIn lam L t) = q.2 from hans.symm, ih.chain]
            rfl
          · show ([] : List (Dig lam)).length + ((tJ g co w embS i m).map TreeK.root).length +
              RootsOfChain.count s R' = ((tJ g co w embS i m).map TreeK.root ++ rootsK s z'.2.1).length
            rw [ih.count, List.length_append]
            simp
          · show (w.pass (w.chal q.2.1) && RoundsQueryLayout.pass s A W z'.1) = true
            rw [ih.pass, Bool.and_true]
            refine pass_lo hk ?_
            rcases hgr with ⟨h1, -⟩ | ⟨u, n, h1, -, h3⟩
            · exact Or.inl h1
            · exact Or.inr ⟨u, h1, h3⟩
          · refine ⟨rfl, rfl, ?_, ih.puts⟩
            rcases hgr with ⟨-, h2⟩ | ⟨u, n, h1, h2, -⟩
            · refine Or.inl ?_
              show a.plain.symm ((a.plain m.2).1, q.1) = m.2
              rw [h2, Prod.mk.eta, Equiv.symm_apply_apply]
            · refine Or.inr (Or.inl ⟨u, n, hk, h1, ?_⟩)
              show a.plain.symm ((a.plain m.2).1, q.1) = _
              rw [h2]
          · exact ⟨fun k T h => by simp at h, tJ_salt g co w embS i m, ih.salts⟩
        | false =>
          rw [det_shared g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
          obtain ⟨hk, hp, hn, -, -⟩ := act_shared e
          obtain ⟨hans, hgr⟩ := fs_some g _ _ _ _ _ hq
          simp only [RoundSplits.FmtFrom, hk, hp] at hF
          obtain ⟨R', ih⟩ := chain_at s A W _ _ (i + 1) _ _ z' hz' (by rw [hn]; exact hF.2)
            hJ.2 h0.2 rq hrq
          have hc : CompAt g sMT w.posAt0 (fun p => embS (.inl p)) m.1 w.depth0
              (t0 g co w embS i m) := treesO_at0 g sMT _ _ _ _ _ (hs i false) _
          have hpl : (a.plain (a.plain.symm (q.1, (a.plain m.2).2))).1 = q.1 := by
            rw [Equiv.apply_symm_apply]
          refine ⟨((some ((t0 g co w embS i m).map TreeK.root), none), R'), ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact ⟨Or.inr ⟨rfl, hc⟩, Or.inl ⟨rfl, rfl, hF.1⟩, ih.rounds⟩
          · show chainF g t cms x co.salt rq (r :: s) (a, A) (w, W) embP i ph
              ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1)
              (a.plain.symm (q.1, (a.plain m.2).2), (trK s z'.2.1 z'.1).plains) = _
            have hT : takeRt w.depth0.length
                ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1) =
                  some ((t0 g co w embS i m).map TreeK.root, rootsK s z'.2.1) :=
              takeRt_app (by rw [List.length_map]; exact hc.1) h0.1
            simp only [TypedOracleCompiler.Run.chainF, e, hT, hpl]
            rw [show g (OracleName.fb t) (⟨i, h, (t0 g co w embS i m).map TreeK.root,
                      embP (.inl (.inl q.1))⟩ : FbIn lam L t) = q.2 from hans.symm, ih.chain]
            rfl
          · show ((t0 g co w embS i m).map TreeK.root).length + ([] : List (Dig lam)).length +
              RootsOfChain.count s R' = ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1).length
            rw [ih.count, List.length_append]
            simp
          · show (w.pass (w.chal q.2.1) && RoundsQueryLayout.pass s A W z'.1) = true
            rw [ih.pass, Bool.and_true]
            refine pass_sh hk ?_
            rcases hgr with ⟨h1, -⟩ | ⟨u, n, h1, -, h3⟩
            · exact Or.inl h1
            · exact Or.inr ⟨u, h1, h3⟩
          · refine ⟨rfl, rfl, ?_, ih.puts⟩
            rcases hgr with ⟨-, h2⟩ | ⟨u, n, h1, h2, -⟩
            · refine Or.inl ?_
              show a.plain.symm (q.1, (a.plain m.2).2) = m.2
              rw [h2, Prod.mk.eta, Equiv.symm_apply_apply]
            · refine Or.inr (Or.inr ⟨u, n, hk, h1, ?_⟩)
              show a.plain.symm (q.1, (a.plain m.2).2) = _
              rw [h2]
          · exact ⟨t0_salt g co w embS i m, fun k T h => by simp at h, ih.salts⟩
      | join ρ =>
        rw [det_join g t cms x co cap w W embS embP i ph m k e] at hz
        obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
        obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
        obtain ⟨hk, rfl⟩ := act_join e
        obtain ⟨hans, hgr⟩ := fs_some g _ _ _ _ _ hq
        simp only [RoundSplits.FmtFrom, hk, fph] at hF
        obtain rfl : reqRoot g co (slotV g t co w embS embP i m ρ) = rq := hrq _ rfl
        have hno := (chain_after g t cms x co cap s A W _ _ (i + 1) _ _ z' _ hz' rfl).1
        obtain ⟨R', ih⟩ := chain_at s A W _ _ (i + 1) _ _ z' hz' hF hJ.2 h0.2
          (reqRoot g co (slotV g t co w embS embP i m ρ)) (fun r hr => by rw [hno] at hr; cases hr)
        have hcJ : CompAt g sMT w.posAtJ (fun p => embS (.inl p)) m.1 w.depthJ
            (tJ g co w embS i m) := treesO_at0 g sMT _ _ _ _ _ (hs i true) _
        have hc0 : CompAt g sMT w.posAt0 (fun p => embS (.inl p)) m.1 w.depth0
            (t0 g co w embS i m) := treesO_at0 g sMT _ _ _ _ _ (hs i false) _
        have hpl : a.plain (a.plain.symm (q.1, (a.plain m.2).2)) = (q.1, (a.plain m.2).2) :=
          Equiv.apply_symm_apply _ _
        refine ⟨((some ((t0 g co w embS i m).map TreeK.root),
          some ((tJ g co w embS i m).map TreeK.root)), R'), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact ⟨Or.inr ⟨rfl, hc0⟩, Or.inr ⟨rfl, hcJ⟩, ih.rounds⟩
        · show chainF g t cms x co.salt _ (r :: s) (a, A) (w, W) embP i (.loc ρ)
            ((tJ g co w embS i m).map TreeK.root ++
              ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1))
            (a.plain.symm (q.1, (a.plain m.2).2), (trK s z'.2.1 z'.1).plains) = _
          have hTJ : takeRt w.depthJ.length ((tJ g co w embS i m).map TreeK.root ++
              ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1)) =
                some ((tJ g co w embS i m).map TreeK.root,
                  (t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1) :=
            takeRt_app (by rw [List.length_map]; exact hcJ.1) hJ.1
          have hT0 : takeRt w.depth0.length
              ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1) =
                some ((t0 g co w embS i m).map TreeK.root, rootsK s z'.2.1) :=
            takeRt_app (by rw [List.length_map]; exact hc0.1) h0.1
          simp only [TypedOracleCompiler.Run.chainF, e, hTJ, hT0, hpl]
          rw [show g (OracleName.fb t) (⟨i, .f4 cms (List.ofFn (reqRoot g co
                      (slotV g t co w embS embP i m ρ))), (t0 g co w embS i m).map TreeK.root,
                    embP (.inl (.inl q.1))⟩ : FbIn lam L t) = q.2 from hans.symm]
          rw [show g (OracleName.g t) (⟨i, ρ, (tJ g co w embS i m).map TreeK.root,
                    embP (.inl (.inr (a.plain m.2).2))⟩ : JoiningRoundQuery lam L t) =
              slotV g t co w embS embP i m ρ from rfl, ih.chain]
          rfl
        · show ((t0 g co w embS i m).map TreeK.root).length +
            ((tJ g co w embS i m).map TreeK.root).length + RootsOfChain.count s R' =
              ((tJ g co w embS i m).map TreeK.root ++
                ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1)).length
          rw [ih.count, List.length_append, List.length_append]
          omega
        · show (w.pass (w.chal q.2.1) && RoundsQueryLayout.pass s A W z'.1) = true
          rw [ih.pass, Bool.and_true]
          refine pass_sh hk ?_
          rcases hgr with ⟨h1, -⟩ | ⟨u, n, h1, -, h3⟩
          · exact Or.inl h1
          · exact Or.inr ⟨u, h1, h3⟩
        · refine ⟨rfl, rfl, ?_, ih.puts⟩
          rcases hgr with ⟨-, h2⟩ | ⟨u, n, h1, h2, -⟩
          · refine Or.inl ?_
            show a.plain.symm (q.1, (a.plain m.2).2) = m.2
            rw [h2, Prod.mk.eta, Equiv.symm_apply_apply]
          · refine Or.inr (Or.inr ⟨u, n, hk, h1, ?_⟩)
            show a.plain.symm (q.1, (a.plain m.2).2) = _
            rw [h2]
        · exact ⟨t0_salt g co w embS i m, tJ_salt g co w embS i m, ih.salts⟩

end

end OnBytes.Prover
