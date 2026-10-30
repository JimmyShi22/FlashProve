-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/FirstBlockLaws.lean: the compiled prover's chain (chainO,
OnBytes/Prover/Defs.lean) reads the answer of a try that fails through its first block alone: it
factors (OComp.FactorsBy, Rom/OverOneN.lean) by the relation agP (OnBytes/Prover/FirstBlock.lean),
where the wire's tests are the letter pass (TestsAt). The prover's text does not turn.

Main names.
  eq_of_agP          at a query that is asked whole, agP is equality.
  factors_of_whole   a program all of whose queries are asked whole factors.
  Small, asksIn_leavesO, asksIn_pairUpO, asksIn_levelsO, asksIn_treeO, asksIn_treesO,
    asksIn_climbO    the trees and the request tree's path ask the four tree oracles alone: any
                     property of all queries to these four holds of what they ask.
  TestQ              A DEFINITION: a premise's record: one record of a test against pass at the
                     queries of one search. It names no goal's form.
  factors_searchO, factors_fsO, factors_onFs, testIs_at   the search.
  factors_chainO, factors_proveX   THE STATEMENT.
  agP_of_agreeF, costF_eq_costP, firstIs_of    from the encoding's blocks to the typed answers:
                     under FirstIs; and FirstIs where blocks and splitting are the family's own.
  det_first, same_law   THE END AT ONE FILE, on values: by the third exit (Rom/OverOneF.lean) the
                     prover has at every hash function its law at the oracles read out.

It adds no strength. The walk is that of noCoin_chainO (OnBytes/Prover/Returns.lean); which record
of a test an arm of the chain uses: act_own, act_shared, act_join (OnBytes/Prover/Step.lean).

Limits. pass IS A LETTER AND TestsAt A PREMISE: that a wire's tests are a function of the first
block is shown at no wire here. FirstIs is a premise on the encoding. One slot, one chain. Nothing
on how many queries are asked (Johnson/Prover/Law/CountF.lean). Nothing on acceptance, soundness or
completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Asks
import OnBytes.Prover.FirstBlock
import OnBytes.Prover.Main

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The second form's names of oracles. (The first form's type ON is in sight too.) -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

/-! ## Queries that are asked whole -/

/-- At a query that is asked whole, agP is equality. -/
theorem eq_of_agP (hK : 0 < K) (pass : Pass lam L) : ∀ (o : ON₂) (q : domOf lam L o)
    (r r' : rngOf lam K o), AskedWhole pass o q → agP hK pass o q r r' → r = r'
  | .fb _, _, _, _, hw, h => by
    rcases h with h | ⟨hf, -⟩
    · exact h
    · rw [hw] at hf
      cases hf
  | .leaf, _, _, _, _, h => h
  | .node, _, _, _, _, h => h
  | .rleaf, _, _, _, _, h => h
  | .rnode, _, _, _, _, h => h
  | .g _, _, _, _, _, h => h
  | .ann, _, _, _, _, h => h
  | .other, _, _, _, _, h => h
  | .fbw _ _, _, _, _, _, h => h

/-- A program all of whose queries are asked whole factors. -/
theorem factors_of_whole (hK : 0 < K) (pass : Pass lam L) {α : Type} :
    ∀ c : TypedOracleComputation lam K L α, c.AsksIn (AskedWhole pass) → c.FactorsBy (agP hK pass)
  | .pure _, _ => trivial
  | .sample _ k, h => fun r => factors_of_whole hK pass (k r) (h r)
  | .query o q k, h =>
    ⟨fun r r' hr => by rw [eq_of_agP hK pass o q r r' h.1 hr],
      fun r => factors_of_whole hK pass (k r) (h.2 r)⟩

/-! ## What the trees ask -/

/-- A property that all queries to the four tree oracles have. -/
structure Small (P : (o : ON₂) → domOf lam L o → Prop) : Prop where
  leaf : ∀ q, P .leaf q
  node : ∀ q, P .node q
  rleaf : ∀ q, P .rleaf q
  rnode : ∀ q, P .rnode q

section
variable {P : (o : ON₂) → domOf lam L o → Prop}

theorem asksIn_askV (o : ON₂) (q : domOf lam L o) (h : P o q) :
    (askTypedOracle (L := L) (K := K) o q).AsksIn P := ⟨h, fun _ => trivial⟩

theorem asksIn_leavesO (hP : Small P) : ∀ l : List (LeafIn L),
    (leavesO (lam := lam) (K := K) l).AsksIn P
  | [] => trivial
  | _ :: xs =>
    asksIn_bind (asksIn_askV _ _ (hP.leaf _)) fun _ =>
      asksIn_bind (asksIn_leavesO hP xs) fun _ => trivial

theorem asksIn_pairUpO (hP : Small P) : ∀ l : List (Dig lam),
    (pairUp (hashTreeNode (K := K) (L := L)) l).AsksIn P
  | [] => trivial
  | [_] => trivial
  | _ :: _ :: l =>
    asksIn_bind (asksIn_askV _ _ (hP.node _)) fun _ =>
      asksIn_bind (asksIn_pairUpO hP l) fun _ => trivial

theorem asksIn_levelsO (hP : Small P) : ∀ (d : ℕ) (l : List (Dig lam)),
    (levelsM (hashTreeNode (K := K) (L := L)) d l).AsksIn P
  | 0, _ => trivial
  | d + 1, l =>
    asksIn_bind (asksIn_pairUpO hP l) fun u =>
      asksIn_bind (asksIn_levelsO hP d u) fun _ => trivial

theorem asksIn_treeO (hP : Small P) (d : ℕ) (inp : ℕ → LeafIn L) :
    (treeO (lam := lam) (K := K) d inp).AsksIn P :=
  asksIn_bind (asksIn_leavesO hP _) fun l =>
    asksIn_bind (asksIn_levelsO hP d l) fun _ => trivial

theorem asksIn_treesO (hP : Small P) {r : Round} (pad : Body L) (sl : ℕ → ℕ → Bits)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ∀ (k : ℕ) (ds : List ℕ), (treesO (lam := lam) (K := K) pad sl posAt emb o k ds).AsksIn P
  | _, [] => trivial
  | k, d :: ds =>
    asksIn_bind (asksIn_treeO hP d _) fun _ =>
      asksIn_bind (asksIn_treesO hP pad sl posAt emb o (k + 1) ds) fun _ => trivial

theorem asksIn_climbO (hP : Small P) : ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam),
    (climbM (rnodeV (K := K) (L := L)) path j c).AsksIn P
  | [], _, _ => trivial
  | s :: ss, j, c => by
    by_cases hb : j % 2 = 0
    · simp only [climbM, if_pos hb]
      exact asksIn_bind (asksIn_askV _ _ (hP.rnode _)) fun u => asksIn_climbO hP ss _ u
    · simp only [climbM, if_neg hb]
      exact asksIn_bind (asksIn_askV _ _ (hP.rnode _)) fun u => asksIn_climbO hP ss _ u

end

theorem small_whole (pass : Pass lam L) : Small (AskedWhole pass) :=
  ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial⟩

/-! ## The search -/

section Search
variable (hK : 0 < K) (pass : Pass lam L) {C P : Type} (chal : (Fin K → Dig lam) → C) (t : Tag)
  (qOf : P → FbIn lam L t)

/-- One record of a test against pass, at the queries qOf β. (TestIs,
OnBytes/Prover/FirstBlock.lean, at one head and one list of roots: testIs_at.) -/
def TestQ : Option (GrW C P) → Prop
  | none => ∀ β b, pass t (qOf β) b = true
  | some g => ∀ β u, g.ok (chal u) = pass t (qOf β) (u ⟨0, hK⟩)

/-- **The search reads a failed try through its first block alone.** -/
theorem factors_searchO (gr : GrW C P)
    (hT : ∀ β u, gr.ok (chal u) = pass t (qOf β) (u ⟨0, hK⟩)) (α : P) :
    ∀ fuel n : ℕ, (searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qOf β)) α fuel
      n).FactorsBy (agP hK pass)
  | 0, _ => trivial
  | fuel + 1, n => by
    show (OComp.query (S := typedOracleFamily lam K L) (OracleName.fb t) (qOf (gr.put n α)) fun a =>
      if gr.ok (chal a.1) then OComp.pure (some (gr.put n α, a))
      else searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qOf β)) α fuel
        (n + 1)).FactorsBy (agP hK pass)
    refine ⟨fun r r' hr => ?_, fun r => ?_⟩
    · rcases hr with rfl | ⟨hf, h0⟩
      · rfl
      · have e1 : gr.ok (chal r.1) = false := by rw [hT (gr.put n α)]; exact hf
        have e2 : gr.ok (chal r'.1) = false := by rw [hT (gr.put n α), ← h0]; exact hf
        simp only [e1, e2, Bool.false_eq_true, if_false]
    · by_cases hk : gr.ok (chal r.1) = true
      · simp only [if_pos hk]
        trivial
      · simp only [if_neg hk]
        exact factors_searchO gr hT α fuel (n + 1)

/-- A Fiat-Shamir query, with a test or without. -/
theorem factors_fsO (gr : Option (GrW C P)) (cap : ℕ) (hT : TestQ hK pass chal t qOf gr) (α : P) :
    (fsO gr cap chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qOf β)) α).FactorsBy
      (agP hK pass) := by
  cases gr with
  | none =>
    show (OComp.query (S := typedOracleFamily lam K L) (OracleName.fb t) (qOf α) fun a =>
      OComp.pure (some (α, a))).FactorsBy (agP hK pass)
    refine ⟨fun r r' hr => ?_, fun _ => trivial⟩
    rw [eq_of_agP hK pass (.fb t) (qOf α) r r' (hT α) hr]
  | some g => exact factors_searchO hK pass chal t qOf g hT α _ _

end Search

theorem factors_onFs {ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop}
    {P β : Type} (i : ℕ) (k : P × FsAns lam K → TypedOracleComputation lam K L (Res β))
    (hk : ∀ p, (k p).FactorsBy ag) : ∀ o, (onFs i k o).FactorsBy ag
  | none => trivial
  | some p => hk p

/-- From one record's tie to the form that the search takes. -/
theorem testIs_at (hK : 0 < K) (pass : Pass lam L) {C P : Type} (t : Tag) (i : ℕ)
    (chal : (Fin K → Dig lam) → C) (plOf : P → PlainPart (shapeOf L t) (annOf L t))
    (gr : Option (GrW C P)) (h : TestIs hK pass t i chal plOf gr) (hd : Head lam X)
    (rt : List (Dig lam)) :
    TestQ hK pass chal t (fun β => (⟨i, hd, rt, plOf β⟩ : FbIn lam L t)) gr := by
  cases gr with
  | none => exact fun β b => h hd rt β b
  | some g => exact fun β u => h hd rt β u

/-! ## The chain -/

/-- **THE CHAIN READS A FAILED TRY THROUGH ITS FIRST BLOCK ALONE.** -/
theorem factors_chainO (hK : 0 < K) (pass : Pass lam L) (t : Tag) (cms : List (Dig lam))
    (x : Option X) (co : Coins lam L) (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit),
      TestsAt hK pass t i s A W embP →
      (chainO t cms x co cap s A W embS embP i ph σ).FactorsBy (agP hK pass)
  | [], _, _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), H => by
    have tr : ∀ {α : Type} (c : TypedOracleComputation lam K L α), c.AsksIn (AskedWhole pass) →
        c.FactorsBy (agP hK pass) := fun c h => factors_of_whole hK pass c h
    have tail : ∀ ph' σ', (chainO t cms x co cap s A W (fun p => embS (.inr p))
        (fun z => embP (.inr z)) (i + 1) ph' σ').FactorsBy (agP hK pass) := fun ph' σ' =>
      factors_chainO hK pass t cms x co cap s A W _ _ _ ph' σ' H.2
    simp only [chainO]
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none => trivial
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          have hT : TestIs hK pass t i w.chal (fun α => embP (.inl (.inr α))) w.grJ := by
            have h1 := H.1
            rw [(act_own e).1] at h1
            exact h1
          exact OComp.FactorsBy.bind (tr _ (asksIn_treesO (small_whole pass) _ _ _ _ _ _ _))
            fun _ => OComp.FactorsBy.bind
              (factors_fsO hK pass w.chal t _ w.grJ (cap i)
                (testIs_at hK pass t i w.chal _ w.grJ hT _ _) _)
              (factors_onFs _ _ fun _ => OComp.FactorsBy.bind (tail _ _) fun _ => trivial)
        | false =>
          have hT : TestIs hK pass t i w.chal (fun α => embP (.inl (.inl α))) w.gr0 := by
            have h1 := H.1
            rw [(act_shared e).1] at h1
            exact h1
          exact OComp.FactorsBy.bind (tr _ (asksIn_treesO (small_whole pass) _ _ _ _ _ _ _))
            fun _ => OComp.FactorsBy.bind
              (factors_fsO hK pass w.chal t _ w.gr0 (cap i)
                (testIs_at hK pass t i w.chal _ w.gr0 hT _ _) _)
              (factors_onFs _ _ fun _ => OComp.FactorsBy.bind (tail _ _) fun _ => trivial)
      | join ρ =>
        have hT : TestIs hK pass t i w.chal (fun α => embP (.inl (.inl α))) w.gr0 := by
          have h1 := H.1
          rw [(act_join e).1] at h1
          exact h1
        exact OComp.FactorsBy.bind (tr _ (asksIn_treesO (small_whole pass) _ _ _ _ _ _ _))
          fun _ => OComp.FactorsBy.bind (tr _ (asksIn_treesO (small_whole pass) _ _ _ _ _ _ _))
          fun _ => OComp.FactorsBy.bind (tr _ (asksIn_askV _ _ trivial))
          fun _ => OComp.FactorsBy.bind (tr _ (asksIn_askV _ _ trivial))
          fun _ => OComp.FactorsBy.bind (tr _ (asksIn_climbO (small_whole pass) _ _ _))
          fun _ => OComp.FactorsBy.bind
            (factors_fsO hK pass w.chal t _ w.gr0 (cap i)
              (testIs_at hK pass t i w.chal _ w.gr0 hT _ _) _)
            (factors_onFs _ _ fun _ => OComp.FactorsBy.bind (tail _ _) fun _ => trivial)

/-- **So the compiled prover of one slot.** -/
theorem factors_proveX (hK : 0 < K) (pass : Pass lam L) (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
    (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ)
    (H : TestsAt hK pass t 0 Q.loc.shape Q.ann wq.sh embP) :
    (proveX t Q wq embS embP xin cms x y xt σ co cap).FactorsBy (agP hK pass) :=
  OComp.FactorsBy.bind
    (factors_chainO hK pass t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ H)
    fun _ => trivial

/-! ## From the encoding's blocks to the typed answers -/

section Enc
variable (hK : 0 < K) (pass : Pass lam L) (m : OracleCoding (typedOracleFamily lam K L) lam)

/-- The relation on typed answers holds wherever the encoding's blocks agree. -/
theorem agP_of_agreeF (F : FirstIs hK m) : ∀ (o : ON₂) (q : domOf lam L o) (r r' : rngOf lam K o),
    AgreeF m (moreP pass) o q r r' → agP hK pass o q r r' := by
  have all : ∀ (o : ON₂) (r r' : rngOf lam K o), (∀ j, m.rng o r j = m.rng o r' j) → r = r' :=
    fun o r r' e => (m.rng o).injective (funext e)
  intro o q r r' h
  cases o with
  | fb t =>
    by_cases hp : pass t q (r.1 ⟨0, hK⟩) = true
    · refine Or.inl (all _ r r' fun j => h j (Or.inr ?_))
      show pass t q (m.rng (.fb t) r ⟨0, _⟩) = true
      rw [F.first]
      exact hp
    · have hpos : 0 < m.blocks (.fb t) := by
        rw [F.blocks]
        exact Nat.succ_pos K
      have h0 := h ⟨0, hpos⟩ (Or.inl rfl)
      rw [F.first, F.first] at h0
      exact Or.inr ⟨by simpa using hp, h0⟩
  | leaf => exact all _ r r' fun j => h j (Or.inr rfl)
  | node => exact all _ r r' fun j => h j (Or.inr rfl)
  | rleaf => exact all _ r r' fun j => h j (Or.inr rfl)
  | rnode => exact all _ r r' fun j => h j (Or.inr rfl)
  | g _ => exact all _ r r' fun j => h j (Or.inr rfl)
  | ann => exact all _ r r' fun j => h j (Or.inr rfl)
  | other => exact all _ r r' fun j => h j (Or.inr rfl)
  | fbw _ _ => exact all _ r r' fun j => h j (Or.inr rfl)

/-- The two costs are one. -/
theorem costF_eq_costP (F : FirstIs hK m) : ∀ (o : ON₂) (q : domOf lam L o) (r : rngOf lam K o),
    costF m (moreP pass) o q r = costP hK pass o q r := by
  have one : ∀ (o : ON₂) (q : domOf lam L o) (r : rngOf lam K o), 0 < blk K o →
      (∀ b, moreP (K := K) pass o q b = true) → costF m (moreP pass) o q r = blk K o := by
    intro o q r hb hm
    have hpos : 0 < m.blocks o := by rw [F.blocks]; exact hb
    unfold costF
    rw [dif_pos hpos, if_pos (hm _), F.blocks]
  intro o q r
  cases o with
  | fb t =>
    have hpos : 0 < m.blocks (.fb t) := by
      rw [F.blocks]
      exact Nat.succ_pos K
    unfold costF
    rw [dif_pos hpos]
    show (if pass t q (m.rng (.fb t) r ⟨0, hpos⟩) = true then m.blocks (.fb t) else 1) =
      if pass t q (r.1 ⟨0, hK⟩) = true then K + 1 else 1
    rw [F.first, F.blocks]
    rfl
  | ann =>
    unfold costF
    rw [dif_neg (by rw [F.blocks]; exact Nat.lt_irrefl 0)]
    rfl
  | leaf => exact one _ q r Nat.one_pos fun _ => rfl
  | node => exact one _ q r Nat.one_pos fun _ => rfl
  | rleaf => exact one _ q r Nat.one_pos fun _ => rfl
  | rnode => exact one _ q r Nat.one_pos fun _ => rfl
  | g _ => exact one _ q r Nat.one_pos fun _ => rfl
  | other => exact one _ q r Nat.one_pos fun _ => rfl
  | fbw _ _ => exact one _ q r (Nat.succ_pos K) fun _ => rfl

/-- FirstIs where the encoding's blocks and splitting are the family's own. -/
theorem firstIs_of (hb : ∀ o, m.blocks o = blk K o)
    (hr : ∀ o r (j : Fin (m.blocks o)), m.rng o r j = rngEquiv lam K o r (Fin.cast (hb o) j)) :
    FirstIs hK m :=
  ⟨hb, fun t r h => by
    rw [hr]
    show Fin.snoc (α := fun _ : Fin (K + 1) => Dig lam) r.1 r.2 (Fin.castSucc ⟨0, hK⟩) =
      r.1 ⟨0, hK⟩
    exact Fin.snoc_castSucc (α := fun _ : Fin (K + 1) => Dig lam) r.2 r.1 ⟨0, hK⟩⟩

/-- A program that factors by agP factors by the encoding's relation. -/
theorem factorsF_of (F : FirstIs hK m) {α : Type} {c : TypedOracleComputation lam K L α}
    (h : c.FactorsBy (agP hK pass)) : c.FactorsBy (AgreeF m (moreP pass)) :=
  OComp.FactorsBy.mono (agP_of_agreeF hK pass m F) h

end Enc

/-- **THE END AT ONE FILE, ON VALUES**: the compiled prover, unturned, by the third exit: at every
hash function its law is the typed prover's at the oracles read out. -/
theorem same_law (hK : 0 < K) (pass : Pass lam L) (m : OracleCoding (typedOracleFamily lam K L) lam) (t : Tag)
    {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
    (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ) (F : FirstIs hK m)
    (H : TestsAt hK pass t 0 Q.loc.shape Q.ann wq.sh embP) (g : Fam (rom lam)) :
    ((proveX t Q wq embS embP xin cms x y xt σ co cap).overOneF m (moreP pass)).runEager g =
      (proveX t Q wq embS embP xin cms x y xt σ co cap).runEager (readBlocks m g) :=
  runEager_overOneF m (moreP pass) g _
    (factorsF_of hK pass m F (factors_proveX hK pass t Q wq embS embP xin cms x y xt σ co cap H))

end OnBytes.Prover

#print axioms OnBytes.Prover.eq_of_agP
#print axioms OnBytes.Prover.factors_of_whole
#print axioms OnBytes.Prover.asksIn_askV
#print axioms OnBytes.Prover.asksIn_leavesO
#print axioms OnBytes.Prover.asksIn_pairUpO
#print axioms OnBytes.Prover.asksIn_levelsO
#print axioms OnBytes.Prover.asksIn_treeO
#print axioms OnBytes.Prover.asksIn_treesO
#print axioms OnBytes.Prover.asksIn_climbO
#print axioms OnBytes.Prover.small_whole
#print axioms OnBytes.Prover.factors_searchO
#print axioms OnBytes.Prover.factors_fsO
#print axioms OnBytes.Prover.factors_onFs
#print axioms OnBytes.Prover.testIs_at
#print axioms OnBytes.Prover.factors_chainO
#print axioms OnBytes.Prover.factors_proveX
#print axioms OnBytes.Prover.agP_of_agreeF
#print axioms OnBytes.Prover.costF_eq_costP
#print axioms OnBytes.Prover.firstIs_of
#print axioms OnBytes.Prover.factorsF_of
#print axioms OnBytes.Prover.same_law
