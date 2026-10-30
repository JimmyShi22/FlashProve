-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Dry/Control.lean: CONTROL: the chain of the compiled prover of one slot (chainO, proveX,
OnBytes/Prover/Defs.lean) at any two strategies, outer roots, instances and sets of coins with
equally many sibling digests asks its deferred queries in step, and its verifier messages, and
whether and where a search for a nonce runs out, are the same. It proves Spec.control
(OnBytes/Dry/Spec.lean).

General lemmas. This file states no goal of the release.

How. A walk along the program's text, part by part, each part at two sets of letters: the leaves of
a tree, a level of inner nodes, all levels, a tree, a component's trees, the climb in the request
tree, the search for a nonce, a Fiat-Shamir query, what follows it, the chain. Each part asks a
number of queries that is fixed by the wire (the depths of trees, the length of the request path),
to oracles that are fixed by the text. The one test in the text is that of the search: are all test
bits of the verifier message 0, a function of the answer alone. What the strategy sends goes into
the POINTS of queries, into no test; so do the outer roots, the instance, the first salt, the slot
and the sibling digests. What a round does (actOf, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) goes by
the round's kind and the phase (ActLike, actLike). The phase of the chain (Phase,
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) holds a chain value, out of a Fiat-Shamir answer, and the
slot value, the answer of g: so both oracles must be deferred for the two runs to have one phase.
The walk's form follows that of chainO_round (Johnson/Prover/Law/Asks.lean).

Main names.
  Step m R c c'   InStep (Rom/Handle/Defs.lean) over the typed oracles, "deferred" by the name.
  step_askV .. step_fsO, step_onFs   the parts.
  SameC           two outcomes of the chain: of one kind; at "ran out" the same round; at a value
                  the same verifier messages and the same phase.
  step_chainO     the chain (SameC.cons, SameC.rho, rho_trK' beside it).
  control         THE STATEMENT: Spec.control.
  control_proveX  the same for the compiled prover.

Limits. One slot, one chain. Nothing on the points that are asked, nor on the proof string.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Dry.Spec
import Rom.Dry.Val

set_option autoImplicit false

namespace OnBytes.Dry
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

/-- In step, over the typed oracles, "deferred" by the oracle's name. -/
abbrev Step (m : ON₂ → Bool) {α β : Type} (R : α → β → Prop) (c : TypedOracleComputation lam K L α)
    (c' : TypedOracleComputation lam K L β) : Prop :=
  InStep (S := typedOracleFamily lam K L) (fun o _ => m o) R c c'

variable (m : ON₂ → Bool)

/-! ## The parts -/

/-- one query to one oracle, at any two points: the answers are one if the oracle is deferred -/
theorem step_askV (o : ON₂) (q q' : domOf lam L o) :
    Step m (fun r r' => m o = true → r = r') (askTypedOracle (L := L) (K := K) o q)
      (askTypedOracle (L := L) (K := K) o q') :=
  InStep.query_query (S := typedOracleFamily lam K L) fun _ _ h => .done h

theorem step_leavesO : ∀ xs ys : List (LeafIn L), xs.length = ys.length →
    Step m (fun u v : List (Dig lam) => u.length = v.length)
      (leavesO (lam := lam) (K := K) xs) (leavesO (lam := lam) (K := K) ys)
  | [], [], _ => .done rfl
  | x :: xs, y :: ys, h =>
    InStep.bind (step_askV m OracleName.leaf x y) fun _ _ _ =>
      InStep.bind (step_leavesO xs ys (by simpa using h)) fun _ _ e => .done (by simp [e])
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem step_pairUp : ∀ l l' : List (Dig lam), l.length = l'.length →
    Step m (fun u v : List (Dig lam) => u.length = v.length)
      (pairUp (hashTreeNode (K := K) (L := L)) l) (pairUp (hashTreeNode (K := K) (L := L)) l')
  | [], [], _ => .done rfl
  | [_], [_], _ => .done rfl
  | _ :: _ :: t, _ :: _ :: t', h =>
    InStep.bind (step_askV m OracleName.node _ _) fun _ _ _ =>
      InStep.bind (step_pairUp t t' (by simpa using h)) fun _ _ e => .done (by simp [e])
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | [_], _ :: _ :: _, h => by simp at h
  | _ :: _ :: _, [_], h => by simp at h

theorem step_levelsM : ∀ (d : ℕ) (l l' : List (Dig lam)), l.length = l'.length →
    Step m (fun _ _ => True)
      (levelsM (hashTreeNode (K := K) (L := L)) d l) (levelsM (hashTreeNode (K := K) (L := L)) d l')
  | 0, _, _, _ => .done trivial
  | d + 1, l, l', h =>
    InStep.bind (step_pairUp m l l' h) fun u v e =>
      InStep.bind (step_levelsM d u v e) fun _ _ _ => .done trivial

theorem step_treeO (d : ℕ) (inp inp' : ℕ → LeafIn L) :
    Step m (fun _ _ => True) (treeO (lam := lam) (K := K) d inp)
      (treeO (lam := lam) (K := K) d inp') :=
  InStep.bind (step_leavesO m _ _ (by simp)) fun l l' e =>
    InStep.bind (step_levelsM m d l l' e) fun _ _ _ => .done trivial

theorem step_treesO {r : Round} (pad pad' : Body L) (sl sl' : ℕ → ℕ → Bits)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o o' : r.Orc) :
    ∀ (k : ℕ) (ds : List ℕ),
      Step m (fun _ _ => True) (treesO (lam := lam) (K := K) pad sl posAt emb o k ds)
        (treesO (lam := lam) (K := K) pad' sl' posAt emb o' k ds)
  | _, [] => .done trivial
  | k, d :: ds =>
    InStep.bind (step_treeO m d _ _) fun _ _ _ =>
      InStep.bind (step_treesO pad pad' sl sl' posAt emb o o' (k + 1) ds) fun _ _ _ =>
        .done trivial

theorem step_climbM : ∀ (path path' : List (Dig lam)), path.length = path'.length →
    ∀ (j j' : ℕ) (c c' : Dig lam),
    Step m (fun _ _ => True) (climbM (rnodeV (K := K) (L := L)) path j c)
      (climbM (rnodeV (K := K) (L := L)) path' j' c')
  | [], [], _, _, _, _, _ => .done trivial
  | s :: ss, s' :: ss', e, j, j', c, c' => by
    have e' : ss.length = ss'.length := by simpa using e
    by_cases hb : j % 2 = 0 <;> by_cases hb' : j' % 2 = 0 <;> simp only [climbM, hb, hb', if_true,
      if_false] <;>
    exact InStep.bind (step_askV m OracleName.rnode _ _) fun u v _ => step_climbM ss ss' e' _ _ u v
  | [], _ :: _, e, _, _, _, _ => by simp at e
  | _ :: _, [], e, _, _, _, _ => by simp at e

/-! ## The search, a Fiat-Shamir query, and what follows it -/

section Fs
variable {C P : Type} (chal : (Fin K → Dig lam) → C) (t : Tag) (hfb : m (.fb t) = true)
  (qf qf' : P → FbIn lam L t) (α α' : P)
include hfb

/-- two searches over the same numbers: both run out, or both stop at one answer -/
theorem step_searchO (gr : GrW C P) : ∀ fuel n : ℕ,
    Step m (fun u v : Option (P × FsAns lam K) => u.map Prod.snd = v.map Prod.snd)
      (searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf β)) α fuel n)
      (searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf' β)) α' fuel n)
  | 0, _ => .done rfl
  | fuel + 1, n =>
    InStep.bind (step_askV m (OracleName.fb t) _ _) fun a a' e => by
      obtain rfl : a = a' := e hfb
      by_cases hk : gr.ok (chal a.1) = true
      · simp only [if_pos hk]
        exact .done rfl
      · simp only [if_neg hk]
        exact step_searchO gr fuel (n + 1)

theorem step_fsO (gr : Option (GrW C P)) (cap : ℕ) :
    Step m (fun u v : Option (P × FsAns lam K) => u.map Prod.snd = v.map Prod.snd)
      (fsO gr cap chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf β)) α)
      (fsO gr cap chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf' β)) α') := by
  cases gr with
  | none =>
    exact InStep.bind (step_askV m (OracleName.fb t) _ _) fun a a' e => by
      obtain rfl : a = a' := e hfb
      exact .done rfl
  | some g => exact step_searchO m chal t hfb qf qf' α α' g _ _

end Fs

theorem step_onFs {P β β' : Type} {R : Res β → Res β' → Prop} (i : ℕ)
    (k : P × FsAns lam K → TypedOracleComputation lam K L (Res β)) (k' : P × FsAns lam K → TypedOracleComputation lam K L (Res β'))
    (hR : R (.ranOut i) (.ranOut i)) (hk : ∀ p p' a, Step m R (k (p, a)) (k' (p', a))) :
    ∀ u v : Option (P × FsAns lam K), u.map Prod.snd = v.map Prod.snd →
      Step m R (onFs i k u) (onFs i k' v)
  | none, none, _ => .done hR
  | some (p, a), some (p', a'), e => by
    obtain rfl : a = a' := Option.some.inj e
    exact hk p p' a
  | none, some _, e => by simp at e
  | some _, none, e => by simp at e

/-! ## The chain -/

/-- Two outcomes of the chain: of one kind; at "ran out" the same round; at a value the same
verifier messages and the same phase. -/
def SameC (s : Shape) : Res (OutP lam L s) → Res (OutP lam L s) → Prop
  | .ok z, .ok z' => z.1 = z'.1 ∧ z.2.2.1 = z'.2.2.1
  | .noFormat, .noFormat => True
  | .ranOut i, .ranOut j => i = j
  | _, _ => False

theorem SameC.cons {r : Round} {s : Shape} (c : r.Chal)
    (kp kp' : r.Msg × List (TreeK lam L) × List (TreeK lam L)) (rq rq' : Option (Dig lam))
    (u v : Res (OutP lam L s)) (e : SameC s u v) :
    SameC (r :: s) (u.map (consP c kp rq)) (v.map (consP c kp' rq')) := by
  cases u <;> cases v <;> try exact e
  rename_i z z'
  have e' : z.1 = z'.1 ∧ z.2.2.1 = z'.2.2.1 := e
  show (consP c kp rq z).1 = (consP c kp' rq' z').1 ∧
    (consP c kp rq z).2.2.1 = (consP c kp' rq' z').2.2.1
  exact ⟨congrArg (Prod.mk c) e'.1, e'.2⟩

/-- What two rounds do is alike: both nothing; or both one Fiat-Shamir query, over the same
component, with the same next phase; or both join. -/
def ActLike : Option (Act lam X) → Option (Act lam X) → Prop
  | none, none => True
  | some (.one _ own next), some (.one _ own' next') => own = own' ∧ next = next'
  | some (.join _), some (.join _) => True
  | _, _ => False

/-- What a round does goes by its kind and the phase. -/
theorem actLike (cms cms' : List (Dig lam)) (x x' : Option X) (salt salt' : Bits) (k : Kind)
    (ph : Phase lam) : ActLike (actOf cms x salt k ph) (actOf cms' x' salt' k ph) := by
  cases k <;> cases ph <;> first
    | exact ⟨rfl, rfl⟩
    | exact trivial

section Chain
variable (t : Tag) (hfb : m (.fb t) = true) (hg : m (.g t) = true) (cms cms' : List (Dig lam))
  (x x' : Option X) (co co' : Coins lam L) (cap : ℕ → ℕ)
  (hco : co.path.length = co'.path.length)
include hfb hg hco

/-- **The chain at any two strategies, outer roots, instances, and coins with equally many sibling
digests.** -/
theorem step_chainO : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (ph : Phase lam) (σ σ' : Strat s Unit),
    Step m (SameC s) (chainO t cms x co cap s A W embS embP i ph σ)
      (chainO t cms' x' co' cap s A W embS embP i ph σ')
  | [], _, _, _, _, _, _, _, _ => .done ⟨rfl, rfl⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m₁, k), (m₂, k') => by
    have tail : ∀ (c : r.Chal) (ph' : Phase lam)
        (kp kp' : r.Msg × List (TreeK lam L) × List (TreeK lam L)) (rq rq' : Option (Dig lam)),
        Step m (SameC (r :: s))
          ((chainO t cms x co cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            ph' (k c)).bind fun r => .pure (r.map (consP c kp rq)))
          ((chainO t cms' x' co' cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            ph' (k' c)).bind fun r => .pure (r.map (consP c kp' rq'))) :=
      fun c ph' kp kp' rq rq' =>
        InStep.bind (step_chainO s A W _ _ (i + 1) ph' (k c) (k' c)) fun u v e =>
          .done (SameC.cons c kp kp' rq rq' u v e)
    have hrel := actLike cms cms' (x.map L.early) (x'.map L.early) co.salt co'.salt a.kind ph
    simp only [chainO]
    generalize actOf cms (x.map L.early) co.salt a.kind ph = act at hrel ⊢
    generalize actOf cms' (x'.map L.early) co'.salt a.kind ph = act' at hrel ⊢
    cases act with
    | none =>
      cases act' with
      | none => exact .done trivial
      | some _ => exact False.elim hrel
    | some ac =>
      cases act' with
      | none => cases ac <;> exact False.elim hrel
      | some ac' =>
        cases ac with
        | one h own next =>
          cases ac' with
          | join _ => exact False.elim hrel
          | one h' own' next' =>
            obtain ⟨rfl, rfl⟩ : own = own' ∧ next = next' := hrel
            cases own with
            | true =>
              exact InStep.bind (step_treesO m _ _ _ _ _ _ _ _ _ _) fun _ _ _ =>
                InStep.bind (step_fsO m w.chal t hfb _ _ _ _ _ _)
                  (step_onFs m i _ _ rfl fun _ _ _ => tail _ _ _ _ _ _)
            | false =>
              exact InStep.bind (step_treesO m _ _ _ _ _ _ _ _ _ _) fun _ _ _ =>
                InStep.bind (step_fsO m w.chal t hfb _ _ _ _ _ _)
                  (step_onFs m i _ _ rfl fun _ _ _ => tail _ _ _ _ _ _)
        | join ρ =>
          cases ac' with
          | one _ _ _ => exact False.elim hrel
          | join ρ' =>
            exact InStep.bind (step_treesO m _ _ _ _ _ _ _ _ _ _) fun _ _ _ =>
              InStep.bind (step_treesO m _ _ _ _ _ _ _ _ _ _) fun _ _ _ =>
              InStep.bind (step_askV m (OracleName.g t) _ _) fun c c' e => by
                obtain rfl : c = c' := e hg
                exact InStep.bind (step_askV m OracleName.rleaf _ _) fun _ _ _ =>
                  InStep.bind (step_climbM m _ _ hco _ _ _ _) fun _ _ _ =>
                  InStep.bind (step_fsO m w.chal t hfb _ _ _ _ _ _)
                    (step_onFs m i _ _ rfl fun _ _ _ => tail _ _ _ _ _ _)

end Chain

/-! ## The statement -/

/-- of two outcomes that are the same in this sense, the verifier messages are the same -/
theorem SameC.rho {s : Shape} (u v : Res (OutP lam L s)) (e : SameC s u v) :
    (u.map fun z => z.1) = v.map fun z => z.1 := by
  cases u <;> cases v <;> first
    | exact False.elim e
    | skip
  · rename_i z z'
    have e' : z.1 = z'.1 ∧ z.2.2.1 = z'.2.2.1 := e
    exact congrArg Res.ok e'.1
  · rfl
  · rename_i i j
    have e' : i = j := e
    exact congrArg Res.ranOut e'

/-- **THE STATEMENT.** -/
theorem control : Spec.control := by
  intro I X lam K L m t hfb hg cms cms' x x' co co' cap hco s A W embS embP i ph σ σ'
  exact InStep.map_left
    (step_chainO m t hfb hg cms cms' x x' co co' cap hco s A W embS embP i ph σ σ')
    fun u v e => SameC.rho u v e

theorem rho_trK' : ∀ (s : Shape) (kp : Kept lam L s) (ρ : Rho s), (trK s kp ρ).rho = ρ
  | [], _, () => rfl
  | _ :: s, (_, ks), (c, ρ) => congrArg (Prod.mk c) (rho_trK' s ks ρ)

/-- **The same for the compiled prover**: the first pass with proveX at σ, and proveX at σ'. -/
theorem control_proveX (t : Tag) (hfb : m (.fb t) = true) (hg : m (.g t) = true) {Y : Type}
    {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms cms' : List (Dig lam)) (x x' : Y) (y y' : E.Str) (xt xt' : ℕ → TreeK lam L)
    (σ σ' : Strat Q.loc.shape Unit) (co co' : Coins lam L) (cap : ℕ → ℕ)
    (hco : co.path.length = co'.path.length) :
    Step m (fun a b => a = b.map fun z => z.2.rho)
      (rhoX t Q wq embS embP xin cms x y xt σ co cap)
      (proveX t Q wq embS embP xin cms' x' y' xt' σ' co' cap) := by
  refine InStep.map_left (R := fun a b => a.map (fun z => z.2.rho) = b.map fun z => z.2.rho)
    (InStep.bind (step_chainO m t hfb hg cms cms' (xin x) (xin x') co co' cap hco Q.loc.shape Q.ann
      wq.sh embS embP 0 .first σ σ') fun u v e => .done ?_) fun _ _ e => e
  cases u <;> cases v <;> first
    | exact False.elim e
    | skip
  · rename_i z z'
    have e' : z.1 = z'.1 ∧ z.2.2.1 = z'.2.2.1 := e
    show Res.ok (trK Q.loc.shape z.2.1 z.1).rho = Res.ok (trK Q.loc.shape z'.2.1 z'.1).rho
    rw [rho_trK', rho_trK', e'.1]
  · rfl
  · rename_i i j
    have e' : i = j := e
    subst e'
    rfl

end OnBytes.Dry

#print axioms OnBytes.Dry.control
#print axioms OnBytes.Dry.control_proveX
