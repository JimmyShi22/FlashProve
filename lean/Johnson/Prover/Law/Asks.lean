-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/Asks.lean: WHAT THE COMPILED PROVER ASKS, AND WHERE ITS LAZY RUN CAN WRITE. The
trees, the request tree and the query to g never ask the Fiat-Shamir oracle fb t: so their lazy runs
leave its column as it was. Every query of the prover's chain to fb t holds a plain part of the
round whose number it holds. No probability.

Why. The law of the prover's outcome (Spec.prove_law, Johnson/Prover/Law/Defs.lean) is proved round
by round from a table that is fresh for the rounds to come (FreshFrom). These are the steps that
carry FreshFrom along.

Main names.
  avoids_askV, avoids_leavesO, avoids_pairUpO, avoids_levelsO, avoids_treeO, avoids_treesO,
    avoids_climbO   these programs never ask fb t (OComp.Avoids, Rom/SpecDerive.lean).
  fb_kept   after a program that never asks fb t the column fb t is as it was: the library's
    Rom.Derive.runLazy_avoids (Rom/Derive.lean), entry by entry.
  fb_kept_treesO, fb_kept_g, fb_kept_rleaf, fb_kept_climbO   that at the four programs of a round.
  asksIn_searchO, asksIn_fsO, asksIn_onFs   a property of all queries, through the search.
  chainO_round   THE PROVER's TWIN OF chainB_round (Johnson/TypedOracleCompiler/RecCompile/SeedsApart.lean): the
    chain asks in RoundAt t s A embP i.
  fresh_next   a table that is fresh from round i on is fresh from round i + 1 on.
  fresh_of_kept   FreshFrom reads the column fb t alone.

It adds no strength. The walks are those of noCoin_chainO (OnBytes/Prover/Returns.lean) and of
chainB_round.

Limits. On the support of a run's law alone. Nothing on which entries are written. The search turns
a plain part's value (put n α), never its place: that is why RoundAt does not see it.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Defs
import Johnson.Prover.Law.Keeps
import Rom.Derive

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Rom.Derive (Avoids.bind runLazy_avoids)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The second form's names of oracles. (Other types named ON are in sight: the first form's.) -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

/-! ## What never asks fb t -/

theorem avoids_askV (t : Tag) (o : ON₂) (q : domOf lam L o) (h : o ≠ OracleName.fb t) :
    (askTypedOracle (L := L) (K := K) o q).Avoids (OracleName.fb t) := ⟨h, fun _ => trivial⟩

theorem avoids_leavesO (t : Tag) : ∀ l : List (LeafIn L),
    (leavesO (lam := lam) (K := K) l).Avoids (OracleName.fb t)
  | [] => trivial
  | _ :: xs =>
    Avoids.bind (avoids_askV t _ _ (by intro h; cases h)) fun _ =>
      Avoids.bind (avoids_leavesO t xs) fun _ => trivial

theorem avoids_pairUpO (t : Tag) : ∀ l : List (Dig lam),
    (pairUp (hashTreeNode (K := K) (L := L)) l).Avoids (OracleName.fb t)
  | [] => trivial
  | [_] => trivial
  | _ :: _ :: l =>
    Avoids.bind (avoids_askV t _ _ (by intro h; cases h)) fun _ =>
      Avoids.bind (avoids_pairUpO t l) fun _ => trivial

theorem avoids_levelsO (t : Tag) : ∀ (d : ℕ) (l : List (Dig lam)),
    (levelsM (hashTreeNode (K := K) (L := L)) d l).Avoids (OracleName.fb t)
  | 0, _ => trivial
  | d + 1, l =>
    Avoids.bind (avoids_pairUpO t l) fun u =>
      Avoids.bind (avoids_levelsO t d u) fun _ => trivial

theorem avoids_treeO (t : Tag) (d : ℕ) (inp : ℕ → LeafIn L) :
    (treeO (lam := lam) (K := K) d inp).Avoids (OracleName.fb t) :=
  Avoids.bind (avoids_leavesO t _) fun l =>
    Avoids.bind (avoids_levelsO t d l) fun _ => trivial

theorem avoids_treesO (t : Tag) {r : Round} (pad : Body L) (sl : ℕ → ℕ → Bits)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ∀ (k : ℕ) (ds : List ℕ),
      (treesO (lam := lam) (K := K) pad sl posAt emb o k ds).Avoids (OracleName.fb t)
  | _, [] => trivial
  | k, d :: ds =>
    Avoids.bind (avoids_treeO t d _) fun _ =>
      Avoids.bind (avoids_treesO t pad sl posAt emb o (k + 1) ds) fun _ => trivial

theorem avoids_climbO (t : Tag) : ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam),
    (climbM (rnodeV (K := K) (L := L)) path j c).Avoids (OracleName.fb t)
  | [], _, _ => trivial
  | s :: ss, j, c => by
    by_cases hb : j % 2 = 0
    · simp only [climbM, if_pos hb]
      exact Avoids.bind (avoids_askV t _ _ (by intro h; cases h)) fun u => avoids_climbO t ss _ u
    · simp only [climbM, if_neg hb]
      exact Avoids.bind (avoids_askV t _ _ (by intro h; cases h)) fun u => avoids_climbO t ss _ u

/-! ## So the column fb t is kept -/

/-- **After a program that never asks fb t the column fb t is as it was.** -/
theorem fb_kept {α : Type} {t : Tag} {c : TypedOracleComputation lam K L α} (h : c.Avoids (OracleName.fb t))
    {T : Table (typedOracleFamily lam K L)} {x : α × Table (typedOracleFamily lam K L)} (hx : x ∈ (c.runLazy T).support)
    (q : FbIn lam L t) : x.2 (OracleName.fb t) q = T (OracleName.fb t) q := by
  have e := runLazy_avoids (S := typedOracleFamily lam K L) (OracleName.fb t) c h T x hx
  exact congrFun e q

theorem fb_kept_treesO (t : Tag) {r : Round} (pad : Body L) (sl : ℕ → ℕ → Bits)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) (k : ℕ)
    (ds : List ℕ) (T : Table (typedOracleFamily lam K L)) :
    ∀ x ∈ ((treesO (lam := lam) (K := K) pad sl posAt emb o k ds).runLazy T).support,
      ∀ q : FbIn lam L t, x.2 (OracleName.fb t) q = T (OracleName.fb t) q :=
  fun _ hx q => fb_kept (avoids_treesO t pad sl posAt emb o k ds) hx q

theorem fb_kept_g (t t' : Tag) (u : JoiningRoundQuery lam L t') (T : Table (typedOracleFamily lam K L)) :
    ∀ x ∈ ((askTypedOracle (L := L) (K := K) (OracleName.g t') u).runLazy T).support,
      ∀ q : FbIn lam L t, x.2 (OracleName.fb t) q = T (OracleName.fb t) q :=
  fun _ hx q => fb_kept (avoids_askV t _ _ (by intro h; cases h)) hx q

theorem fb_kept_rleaf (t : Tag) (u : Bits) (T : Table (typedOracleFamily lam K L)) :
    ∀ x ∈ ((askTypedOracle (L := L) (K := K) OracleName.rleaf u).runLazy T).support,
      ∀ q : FbIn lam L t, x.2 (OracleName.fb t) q = T (OracleName.fb t) q :=
  fun _ hx q => fb_kept (avoids_askV t _ _ (by intro h; cases h)) hx q

theorem fb_kept_climbO (t : Tag) (path : List (Dig lam)) (j : ℕ) (c : Dig lam)
    (T : Table (typedOracleFamily lam K L)) :
    ∀ x ∈ ((climbM (rnodeV (K := K) (L := L)) path j c).runLazy T).support,
      ∀ q : FbIn lam L t, x.2 (OracleName.fb t) q = T (OracleName.fb t) q :=
  fun _ hx q => fb_kept (avoids_climbO t path j c) hx q

/-! ## FreshFrom along -/

/-- FreshFrom reads the column fb t alone. -/
theorem fresh_of_kept {t : Tag} {s : Shape} {A : RoundSplits s}
    {embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ} {T T' : Table (typedOracleFamily lam K L)}
    (h : FreshFrom t s A embP i T) (e : ∀ q : FbIn lam L t, T' (OracleName.fb t) q = T (OracleName.fb t) q) :
    FreshFrom t s A embP i T' := fun q hq => (e q).trans (h q hq)

/-- A table that is fresh from round i on is fresh from round i + 1 on. -/
theorem fresh_next {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ}
    {T : Table (typedOracleFamily lam K L)} (h : FreshFrom t (r :: s) (a, A) embP i T) :
    FreshFrom t s A (fun z => embP (.inr z)) (i + 1) T := fun q ⟨z, h1, h2⟩ =>
  h q ⟨.inr z, h1, by rw [h2]; show i + 1 + _ = i + (_ + 1); omega⟩

/-! ## A property of all queries, through the search -/

section
variable {P : (o : ON₂) → domOf lam L o → Prop}

/-- OComp.AsksIn.bind (Rom/AsksIn.lean), the program's law first. -/
theorem asksIn_bind {α β : Type} {c : TypedOracleComputation lam K L α} {g : α → TypedOracleComputation lam K L β} (hc : c.AsksIn P)
    (hg : ∀ a, (g a).AsksIn P) : (c.bind g).AsksIn P := OComp.AsksIn.bind hg hc

theorem asksIn_searchO {C Pl : Type} (gr : GrW C Pl) (chal : (Fin K → Dig lam) → C)
    (ask : Pl → TypedOracleComputation lam K L (FsAns lam K)) (hask : ∀ β, (ask β).AsksIn P) (α : Pl) :
    ∀ fuel n : ℕ, (searchO gr chal ask α fuel n).AsksIn P
  | 0, _ => trivial
  | fuel + 1, n =>
    asksIn_bind (hask _) fun a => by
      by_cases hk : gr.ok (chal a.1) = true
      · rw [if_pos hk]
        trivial
      · rw [if_neg hk]
        exact asksIn_searchO gr chal ask hask α fuel (n + 1)

theorem asksIn_fsO {C Pl : Type} (gr : Option (GrW C Pl)) (cap : ℕ)
    (chal : (Fin K → Dig lam) → C) (ask : Pl → TypedOracleComputation lam K L (FsAns lam K))
    (hask : ∀ β, (ask β).AsksIn P) (α : Pl) : (fsO gr cap chal ask α).AsksIn P := by
  cases gr with
  | none => exact asksIn_bind (hask _) fun _ => trivial
  | some q => exact asksIn_searchO q chal ask hask α _ _

theorem asksIn_onFs {Pl β : Type} (i : ℕ) (k : Pl × FsAns lam K → TypedOracleComputation lam K L (Res β))
    (hk : ∀ p, (k p).AsksIn P) : ∀ o, (onFs i k o).AsksIn P
  | none => trivial
  | some p => hk p

/-- A program that never asks fb t asks in every property that binds the queries to fb t alone. -/
theorem asksIn_of_avoids {α : Type} {t : Tag}
    (hP : ∀ (o : ON₂) (q : domOf lam L o), o ≠ OracleName.fb t → P o q) :
    ∀ {c : TypedOracleComputation lam K L α}, c.Avoids (OracleName.fb t) → c.AsksIn P
  | .pure _, _ => trivial
  | .query _ _ _, h => ⟨hP _ _ h.1, fun r => asksIn_of_avoids hP (h.2 r)⟩
  | .sample _ _, h => fun r => asksIn_of_avoids hP (h r)

end

/-- RoundAt binds the queries to fb t alone. -/
theorem roundAt_other {t : Tag} {s : Shape} {A : RoundSplits s}
    {embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ} (o : ON₂) (q : domOf lam L o)
    (h : o ≠ OracleName.fb t) : RoundAt t s A embP i o q := fun _ e => absurd (Sigma.mk.inj e).1 h

/-- **Every query of the prover's chain to its Fiat-Shamir oracle holds a plain part of the round
whose number it holds.** -/
theorem chainO_round (t : Tag) (cms : List (Dig lam)) (x : Option X) (co : Coins lam L)
    (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit),
      (chainO t cms x co cap s A W embS embP i ph σ).AsksIn (RoundAt t s A embP i)
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k) => by
    have av : ∀ {α : Type} {c : TypedOracleComputation lam K L α}, c.Avoids (OracleName.fb t) →
        c.AsksIn (RoundAt t (_ :: s) (a, A) embP i) := fun h =>
      asksIn_of_avoids (fun o q ho => roundAt_other o q ho) h
    have tail : ∀ ph' σ', ((chainO t cms x co cap s A W (fun p => embS (.inr p))
        (fun z => embP (.inr z)) (i + 1) ph' σ')).AsksIn (RoundAt t (_ :: s) (a, A) embP i) :=
      fun ph' σ' => (chainO_round t cms x co cap s A W _ _ _ ph' σ').mono roundAt_next
    simp only [chainO]
    generalize actOf cms (x.map L.early) co.salt a.kind ph = act
    cases act with
    | none => trivial
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          exact asksIn_bind (av (avoids_treesO t _ _ _ _ _ _ _)) fun _ =>
            asksIn_bind (asksIn_fsO _ _ _ _ (fun _ => asksIn_askV _ _ (roundAt_fb _ _ _)) _)
              (asksIn_onFs _ _ fun _ => asksIn_bind (tail _ _) fun _ => trivial)
        | false =>
          exact asksIn_bind (av (avoids_treesO t _ _ _ _ _ _ _)) fun _ =>
            asksIn_bind (asksIn_fsO _ _ _ _ (fun _ => asksIn_askV _ _ (roundAt_fb _ _ _)) _)
              (asksIn_onFs _ _ fun _ => asksIn_bind (tail _ _) fun _ => trivial)
      | join ρ =>
        exact asksIn_bind (av (avoids_treesO t _ _ _ _ _ _ _)) fun _ =>
          asksIn_bind (av (avoids_treesO t _ _ _ _ _ _ _)) fun _ =>
          asksIn_bind (av (avoids_askV t _ _ (by intro h; cases h))) fun _ =>
          asksIn_bind (av (avoids_askV t _ _ (by intro h; cases h))) fun _ =>
          asksIn_bind (av (avoids_climbO t _ _ _)) fun _ =>
            asksIn_bind (asksIn_fsO _ _ _ _ (fun _ => asksIn_askV _ _ (roundAt_fb _ _ _)) _)
              (asksIn_onFs _ _ fun _ => asksIn_bind (tail _ _) fun _ => trivial)

end OnBytes.Prover

#print axioms OnBytes.Prover.avoids_treesO
#print axioms OnBytes.Prover.avoids_climbO
#print axioms OnBytes.Prover.fb_kept
#print axioms OnBytes.Prover.fb_kept_treesO
#print axioms OnBytes.Prover.fb_kept_g
#print axioms OnBytes.Prover.fb_kept_rleaf
#print axioms OnBytes.Prover.fb_kept_climbO
#print axioms OnBytes.Prover.fresh_of_kept
#print axioms OnBytes.Prover.fresh_next
#print axioms OnBytes.Prover.asksIn_fsO
#print axioms OnBytes.Prover.asksIn_of_avoids
#print axioms OnBytes.Prover.chainO_round
