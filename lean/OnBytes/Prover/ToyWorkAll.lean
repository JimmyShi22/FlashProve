-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/ToyWorkAll.lean: the premises of the theorem on the compiled prover's string can be
met together WHERE ROUNDS HAVE TESTS AND AN EXTERNAL STRING LIES UNDER A TREE: at the small protocol
of OnBytes/Prover/ToyWork.lean all of them are proved, and so, under EVERY family of oracle
functions and at all caps, whatever string the compiled prover returns gets the compiled verifier's
yes.

Why. OnBytes/Prover/ToyWork.lean evaluates prover and verifier under 16 families; it calls no
theorem. OnBytes/Prover/ToyFileAll.lean calls the theorems at a file without a test and without an
external string. Here `yes_of_prove` and `proveX_returns` (OnBytes/Prover/Main.lean) are CALLED at a
protocol with tests in a local round, in the joining round and in a later shared round, and with an
outer tree that is built under the same oracle functions.

Main names:
  `gr_ok`, `w1_okg`, `wJ_okg`, `w2_okg`, `w3_okg`, `we_ok`, `wq_okg`   the laws of the wire record
  `isLocal`, `coherent`, `fmt`, `fewJ`, `few0`, `fit`   the other premises on the protocol and the
                    coins
  `xtG`, `cmsG`, `extAt`   the outer tree and its root under g; they meet `ExtAt`
  `accepts`        the interactive verifier accepts every transcript with all tests passed that is
                   the strategy's own run but for nonces
  `toyWork_all`    for every g and all caps: a returned string gets verifyOneProtocol's yes
  `toyWork_returns`   and the prover returns a string, or the search of round 0, 1 or 2 has run out

Limits: a toy. It says nothing of any intended file. No probability: how often a search runs out is
not said.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Main
import OnBytes.Prover.ToyWork
import Iop.WireOK

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover.ToyWork
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The laws of the wire record -/

theorem gr_ok : gr.OK where
  tst_set := fun (z : Fin 1 → Bool) (c : Blk) => funext fun (i : Fin 1) => by
    show (if (0 : Fin 4) = 0 then z 0 else c 0 0) = z i
    rw [if_pos rfl, Subsingleton.elim i 0]
  set_tst := fun c => funext fun i => funext fun j => by
    rw [Subsingleton.elim i 0]
    by_cases h : j = 0
    · subst h
      simp [gr]
    · simp [gr, h]
  set_set := fun z z' c => funext fun i => funext fun j => by
    by_cases h : j = 0 <;> simp [gr, h]
  get_put := fun _ _ _ => rfl

theorem w1_okg : w1.OKG where
  place_lt0 := fun _ e => by cases e
  place_ltJ := fun p _ => ⟨2, rfl, p.isLt⟩
  posAt0_place := fun _ e => by cases e
  posAtJ_place := fun p _ => by
    show (if (0 : ℕ) = 0 then (if h : p.val < 4 then some (⟨p.val, h⟩ : Fin 4) else none)
      else none) = some p
    rw [if_pos rfl, dif_pos p.isLt]
  place_posAt0 := fun _ _ _ e => by cases e
  place_posAtJ := fun k j p e => by
    have e' : (if k = 0 then (if h : j < 4 then some (⟨j, h⟩ : Fin 4) else none) else none) =
      some p := e
    by_cases hk : k = 0
    · rw [if_pos hk] at e'
      by_cases hj : j < 4
      · rw [dif_pos hj] at e'
        obtain rfl := Option.some.inj e'
        exact ⟨rfl, hk.symm, rfl⟩
      · rw [dif_neg hj] at e'
        cases e'
    · rw [if_neg hk] at e'
      cases e'
  no0 := fun _ _ _ => rfl
  noJ := fun k hk j => by
    have hk' : k ≠ 0 := fun e => by
      subst e
      exact absurd hk (by decide)
    show (if k = 0 then _ else none) = none
    rw [if_neg hk']
  chal_unif := PMF.map_id _
  gr0_ok := fun _ e => by cases e
  grJ_ok := fun g e => by
    obtain rfl : gr = g := Option.some.inj e
    exact gr_ok

theorem wJ_okg : wJ.OKG where
  place_lt0 := fun p => nomatch p
  place_ltJ := fun p => nomatch p
  posAt0_place := fun p => nomatch p
  posAtJ_place := fun p => nomatch p
  place_posAt0 := fun _ _ p => nomatch p
  place_posAtJ := fun _ _ p => nomatch p
  no0 := fun _ _ _ => rfl
  noJ := fun _ _ _ => rfl
  chal_unif := PMF.map_id _
  gr0_ok := fun g e => by
    obtain rfl : gr = g := Option.some.inj e
    exact gr_ok
  grJ_ok := fun _ e => by cases e

theorem w2_okg : w2.OKG where
  place_lt0 := fun p _ => match p with
    | .inl i => ⟨1, rfl, i.isLt⟩
    | .inr _ => ⟨0, rfl, Nat.one_pos⟩
  place_ltJ := fun _ e => by cases e
  posAt0_place := fun p _ => match p with
    | .inl i => by
      show (if (0 : ℕ) = 0 then
          (if h : i.val < 2 then some (Sum.inl (⟨i.val, h⟩ : Fin 2) : Fin 2 ⊕ Unit) else none)
        else if (0 : ℕ) = 1 then (if i.val = 0 then some (Sum.inr ()) else none) else none) =
          some (Sum.inl i)
      rw [if_pos rfl, dif_pos i.isLt]
    | .inr _ => rfl
  posAtJ_place := fun _ e => by cases e
  place_posAt0 := fun k j p e => by
    have e' : (if k = 0 then
        (if h : j < 2 then some (Sum.inl (⟨j, h⟩ : Fin 2) : Fin 2 ⊕ Unit) else none)
      else if k = 1 then (if j = 0 then some (Sum.inr ()) else none) else none) = some p := e
    by_cases hk : k = 0
    · rw [if_pos hk] at e'
      by_cases hj : j < 2
      · rw [dif_pos hj] at e'
        obtain rfl := Option.some.inj e'
        exact ⟨rfl, hk.symm, rfl⟩
      · rw [dif_neg hj] at e'
        cases e'
    · rw [if_neg hk] at e'
      by_cases hk1 : k = 1
      · rw [if_pos hk1] at e'
        by_cases hj : j = 0
        · rw [if_pos hj] at e'
          obtain rfl := Option.some.inj e'
          exact ⟨rfl, hk1.symm, hj.symm⟩
        · rw [if_neg hj] at e'
          cases e'
      · rw [if_neg hk1] at e'
        cases e'
  place_posAtJ := fun _ _ _ e => by cases e
  no0 := fun k hk j => by
    have h2 : 2 ≤ k := hk
    show (if k = 0 then _ else if k = 1 then _ else none) = none
    rw [if_neg (by omega), if_neg (by omega)]
  noJ := fun _ _ _ => rfl
  chal_unif := PMF.map_id _
  gr0_ok := fun g e => by
    obtain rfl : gr = g := Option.some.inj e
    exact gr_ok
  grJ_ok := fun _ e => by cases e

theorem w3_okg : w3.OKG where
  place_lt0 := fun p => nomatch p
  place_ltJ := fun p => nomatch p
  posAt0_place := fun p => nomatch p
  posAtJ_place := fun p => nomatch p
  place_posAt0 := fun _ _ p => nomatch p
  place_posAtJ := fun _ _ p => nomatch p
  no0 := fun _ _ _ => rfl
  noJ := fun _ _ _ => rfl
  chal_unif := PMF.map_id _
  gr0_ok := fun _ e => by cases e
  grJ_ok := fun _ e => by cases e

theorem we_ok : we.OK :=
  ⟨(WireE.one_ok 2 Bool false).nodup, (WireE.one_ok 2 Bool false).complete,
    (WireE.one_ok 2 Bool false).build_rd⟩

theorem wq_okg : wq.OKG where
  sh := ⟨w1_okg, wJ_okg, w2_okg, w3_okg, trivial⟩
  ext := we_ok
  opens := fun _ ρ _ => by
    show (rds ρ).card + ({_} : Finset (Fin 2)).card ≤ 5
    rw [Finset.card_singleton]
    exact Nat.add_le_add_right Finset.card_le_four 1
  depth := ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, trivial⟩

/-! ## The other premises -/

/-- the decision, from the verifier messages and the five symbols that are read -/
def accV (x : Bool) (ρ : RhoT) (a b c d e : Bool) : Bool :=
  x && !tb ρ.1 && !tb ρ.2.1 && !tb ρ.2.2.1 && a && b && c && d && e

theorem acc_eq (x : Bool) (y : Fin 2 → Bool) (τ : Tr sh) :
    acc x y τ = accV x τ.rho (τ.read (.inl (at4 (show RhoT from τ.rho).1)))
      (τ.read (.inl (at4 (show RhoT from τ.rho).1 + 1)))
      (τ.read (.inr (.inr (.inl (.inl (at2 (show RhoT from τ.rho).2.2.1))))))
      (τ.read (.inr (.inr (.inl (.inr ()))))) (y (at2 (show RhoT from τ.rho).2.2.2.1)) := rfl

theorem isLocal : P.IsLocal := by
  intro x y y' τ τ' hρ _ he hr
  show acc x y τ = acc x y' τ'
  rw [acc_eq, acc_eq, ← hρ,
    hr (.inl (at4 (show RhoT from τ.rho).1)) (by simp [P, rds]),
    hr (.inl (at4 (show RhoT from τ.rho).1 + 1)) (by simp [P, rds]),
    hr (.inr (.inr (.inl (.inl (at2 (show RhoT from τ.rho).2.2.1))))) (by simp [P, rds]),
    hr (.inr (.inr (.inl (.inr ())))) (by simp [P, rds]),
    show y (at2 (show RhoT from τ.rho).2.2.2.1) = y' (at2 (show RhoT from τ.rho).2.2.2.1) from
      he _ (by simp [P])]

theorem coherent : Q.ann.Coherent :=
  ⟨RAnn.ofSlot_coherent .lo r1, RAnn.ofShared_coherent .sh rJ, RAnn.ofShared_coherent .sh r2,
    RAnn.ofSlot_coherent .lo r3, trivial⟩

theorem fmt : Q.ann.Fmt := by
  show _ ∧ _ ∧ _ ∧ True
  exact ⟨RAnn.noShared_ofSlot .lo r1, RAnn.noSlot_ofShared .sh r2, RAnn.noShared_ofSlot .lo r3,
    trivial⟩

theorem fewJ : FewJ sh ann wq.sh := by
  show _ ∧ _ ∧ _ ∧ _ ∧ True
  exact ⟨by decide, by decide, by decide, by decide, trivial⟩

theorem few0 : Few0 sh ann wq.sh := by
  show _ ∧ _ ∧ _ ∧ _ ∧ True
  exact ⟨by decide, by decide, by decide, by decide, trivial⟩

theorem fit : co.Fit 2 3 1 where
  salt := rfl
  leaf := fun _ _ _ _ => rfl
  slot := by decide
  path := rfl

/-! ## The outer tree under g -/

/-- the inputs of the outer tree's leaves -/
def inpE (j : ℕ) : LeafIn L := ⟨if h : j < 2 then embE (y ⟨j, h⟩) else 0, [j % 2 == 0, true]⟩

/-- the tree over the external string, made under g -/
def xtG (g : Fam (typedOracleFamily 4 1 L)) : ℕ → TreeK 4 L := fun _ => (treeO (K := 1) 1 inpE).det g

def cmsG (g : Fam (typedOracleFamily 4 1 L)) : List (Dig 4) := [(xtG g 0).root]

theorem xt_eq (n : ℕ) : xt n = xtG (gN n) := rfl

theorem extAt (g : Fam (typedOracleFamily 4 1 L)) : ExtAt g 2 wq.ext embE (cmsG g) y (xtG g) where
  tree := fun _ => (treeO_at g 1 inpE).1
  root := fun _ => rfl
  body := fun p => by
    show (((treeO (K := 1) 1 inpE).det g).inp p.val).body = embE (y p)
    rw [(treeO_at g 1 inpE).2]
    show (if h : p.val < 2 then embE (y ⟨p.val, h⟩) else 0) = embE (y p)
    rw [dif_pos p.isLt]
  salt := fun p => by
    show (((treeO (K := 1) 1 inpE).det g).inp p.val).salt.length = 2
    rw [(treeO_at g 1 inpE).2]
    rfl
  leaf := fun p => p.isLt

/-! ## The decision at the strategy's own run -/

theorem tb_of_ok {c : Blk} (h : gr.ok c = true) : tb c = false :=
  congrFun (of_decide_eq_true h : gr.tst c = fun _ => false) (0 : Fin 1)

/-- The interactive verifier accepts every transcript with all tests passed that is the strategy's
own run but for nonces. -/
theorem accepts (τ : Tr sh) (hp : RoundsQueryLayout.pass sh ann wq.sh τ.rho = true)
    (h : Puts sh ann wq.sh ((σ true).run τ.rho).1 τ) : acc true y τ = true := by
  obtain ⟨m1, c1, mJ, cJ, m2, c2, m3, c3, u⟩ := τ
  have hp' : (gr.ok c1 && (gr.ok cJ && (gr.ok c2 && (true && true)))) = true := hp
  simp only [Bool.and_eq_true, and_true] at hp'
  obtain ⟨h1, hJ, h2⟩ := hp'
  have e1 : m1.1 = fun _ => true := h.1
  have e2 : m2.1 = (fun _ => true, true) := h.2.2.2.2.2.2.1
  show (true && !tb c1 && !tb cJ && !tb c2 && m1.1 _ && m1.1 _ && m2.1.1 _ && m2.1.2 && y _) = true
  rw [tb_of_ok h1, tb_of_ok hJ, tb_of_ok h2, e1, e2]
  rfl

/-! ## The theorems, called -/

/-- **Under every family of oracle functions and at all caps: whatever string the compiled prover
returns gets the compiled verifier's yes.** -/
theorem toyWork_all (g : Fam (typedOracleFamily 4 1 L)) (cap : ℕ → ℕ) (π : OneProtocolProof 4 Q) (τ : Tr sh)
    (h : (proveX (L := L) Tag.onl Q wq embS (fun z => z) some (cmsG g) true y (xtG g) (σ true) co
      cap).det g = .ok (π, τ)) :
    (verifyOneProtocol (L := L) 2 3 Tag.onl Q wq embS (fun z => z) some embE 1 (cmsG g) true π).det g =
      true := by
  have h2 := yes_of_prove 2 3 Tag.onl Q wq embS (fun z => z) some embE 1 (cmsG g) true y (xtG g)
    (σ true) co cap g wq_okg fewJ few0 isLocal coherent fmt (by decide) fit (extAt g) π τ h
  exact h2.2.2.2 (accepts τ h2.1 h2.2.1)

theorem noTest : ∀ d, hasTest sh ann wq.sh (d + 3) = false
  | 0 => rfl
  | _ + 1 => rfl

/-- And it returns a string, or the search of round 0, 1 or 2 has run out. -/
theorem toyWork_returns (g : Fam (typedOracleFamily 4 1 L)) (cap : ℕ → ℕ) :
    (∃ z, (proveX (L := L) Tag.onl Q wq embS (fun z => z) some (cmsG g) true y (xtG g) (σ true) co
      cap).det g = .ok z) ∨
    ∃ j, (proveX (L := L) Tag.onl Q wq embS (fun z => z) some (cmsG g) true y (xtG g) (σ true) co
      cap).det g = .ranOut j ∧ j < 3 := by
  rcases proveX_returns Tag.onl Q wq embS (fun z => z) some (cmsG g) true y (xtG g) (σ true) co cap
    g fmt with h | ⟨j, h, hj⟩
  · exact Or.inl h
  · refine Or.inr ⟨j, h, ?_⟩
    by_contra hn
    obtain ⟨d, rfl⟩ : ∃ d, j = d + 3 := ⟨j - 3, by omega⟩
    rw [noTest d] at hj
    cases hj

end OnBytes.Prover.ToyWork
