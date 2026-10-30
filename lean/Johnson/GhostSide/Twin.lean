-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/GhostSide/Twin.lean: the token program of one compiled run (Johnson/TokenSide/) is routed.

Definitions, lemmas and proofs. This file states no goal of the release. A device of a proof: the
names fbw t k, the exchange of queries and "routed" stand in no statement on the scheme.

The token programs of Johnson/TokenSide/ (the committer and the prover of the scheme with the whole
key published, written a second time for one step of a proof) write try number n of a search as a
query to fb t for n = 0 and to the name fbw t (n - 1) else (fbT, Johnson/TokenSide/Chain.lean).
Here: the parts of which a compiled run is made are routed (Johnson/GhostSide/Defs.lean): each such
query holds the nonce for n. The committer, the prover and the challenger as wholes:
Johnson/GhostSide/TwinWhole.lean.

What is asked of a protocol's wires (Back): in every round with a test, each number up to the cap of
tries is read back from the plain part into which it was written. The laws of a wire give that up to
the wire's own number of tries (GrW.OK.get_put); the cap is a letter of the programs and may be
larger. Back.of_okg: it holds where the cap is at most that number (CapLe).

Main names (namespace OnBytes.GhostSide).
  Back, CapLe, Back.of_okg   the premise; when a well-formed wire meets it.
  ClsAt          the invariant of the induction over the rounds.
  rt_…           routed, program by program, in the order of Johnson/TokenSide/'s files: trees and
                 coins, the search, the chain (rt_chainT), all hashing of a run (rt_hashT), its end
                 (rt_endC), the whole run (rt_proveC; Johnson/TokenRules/Chunks.lean).
  not_routed_fbw   a negative test: a query to fbw t j at an input that does not hold the nonce for
                   j + 1 is not routed.
The proofs follow Compile/Batch/GhostRouted.lean closely, which has the like for the first form.
Limits: those of Compile/Batch/SpecGhost.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.GhostSide.Generic
import Johnson.TokenSide.Whole

set_option autoImplicit false

noncomputable section

namespace OnBytes.GhostSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms OnBytes.TokenSide Rom
open OnBytes.Prover OnBytes.WholeKey
open _root_.Compile.GlueB (GCall ownPf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The premises -/

section Prem
variable {lam : ℕ}

/-- In every round with a test, each number up to the cap is read back from the plain part into
which it was written. i: the number of the first of the rounds s. -/
def Back {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (ℕ → ℕ) → ℕ → Prop
  | [], _, _, _, _ => True
  | _ :: s, (a, A), (w, W), cap, i =>
      (match a.kind with
        | .lo => ∀ g, w.grJ = some g → ∀ k α, k ≤ cap i → g.get (g.put k α) = k
        | .sh => ∀ g, w.gr0 = some g → ∀ k α, k ≤ cap i → g.get (g.put k α) = k) ∧
        Back s A W cap (i + 1)

/-- the caps are at most the wires' own numbers of tries -/
def CapLe {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (ℕ → ℕ) → ℕ → Prop
  | [], _, _, _, _ => True
  | _ :: s, (_, A), (w, W), cap, i =>
      ((∀ g, w.grJ = some g → cap i ≤ g.more) ∧ ∀ g, w.gr0 = some g → cap i ≤ g.more) ∧
        CapLe s A W cap (i + 1)

/-- A well-formed wire meets Back where the caps are at most its own numbers of tries. -/
theorem Back.of_okg {K : ℕ} : ∀ {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A} {cap : ℕ → ℕ}
    {i : ℕ}, RoundsQueryLayout.OKG s A W → CapLe s A W cap i → Back s A W cap i
  | [], _, _, _, _, _, _ => trivial
  | _ :: _, (a, _), (w, _), cap, i, h, hc => by
    refine ⟨?_, Back.of_okg h.2 hc.2⟩
    cases a.kind with
    | lo => exact fun g hg k α hk => (h.1.grJ_ok g hg).get_put k α (hk.trans (hc.1.1 g hg))
    | sh => exact fun g hg k α hk => (h.1.gr0_ok g hg).get_put k α (hk.trans (hc.1.2 g hg))

end Prem

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} (W : QueryLayout lam L)

local notation "Rt" => RoutedT W

/-- A negative test: a query to fbw t j at an input that does not hold the nonce for j + 1 is not
routed. -/
theorem not_routed_fbw {α : Type} (t : Tag) (j : ℕ) (q : FbIn lam L t)
    (k : rngOf lam W.K (.fbw t j) → StT lam W.K L α) (h : cls W t q ≠ j + 1) :
    ¬ Rt (Step.plain (S := typedOracleFamily lam W.K L) (OracleName.fbw t j) q k) := fun hr => h hr.1

/-! ## Trees and coins: neither fb nor fbw -/

theorem rt_leafT (ℓ : ℕ) (us : List Tok) (pre : List Bits → Bits) (b : Body L) :
    Rt (leafT (K := W.K) ℓ us pre b) := fun _ _ _ => trivial

theorem rt_leavesT (ℓ : ℕ) (us : List Tok) (pre : List Bits → Bits) :
    ∀ l : List (Body L), Rt (TokenSide.leavesT (K := W.K) ℓ us pre l)
  | [] => trivial
  | b :: t => (rt_leafT W ℓ us pre b).bind fun _ => (rt_leavesT ℓ us pre t).bind fun _ => trivial

theorem rt_nodeT (a b : Dig lam) : Rt (nodeT (K := W.K) (L := L) a b) := fun _ => trivial

theorem rt_pairUp {D : Type} {node : D → D → StT lam W.K L D} (hn : ∀ a b, Rt (node a b)) :
    ∀ l : List D, Rt (pairUp node l)
  | [] => trivial
  | [_] => trivial
  | a :: b :: t => (hn a b).bind fun _ => (rt_pairUp hn t).bind fun _ => trivial

theorem rt_levelsM {D : Type} {node : D → D → StT lam W.K L D} (hn : ∀ a b, Rt (node a b)) :
    ∀ (d : ℕ) (l : List D), Rt (levelsM node d l)
  | 0, _ => trivial
  | d + 1, l => (rt_pairUp W hn l).bind fun u => (rt_levelsM hn d u).bind fun _ => trivial

theorem rt_treeT (ℓ : ℕ) (us : List Tok) (pre : List Bits → Bits) (d : ℕ) (body : ℕ → Body L) :
    Rt (treeT (K := W.K) ℓ us pre d body) :=
  (rt_leavesT W ℓ us pre _).bind fun l => (rt_levelsM W (rt_nodeT W) d l.1).bind fun _ => trivial

theorem rt_treesT {r : Round} (ℓ : ℕ) (us : List Tok) (pre : List Bits → Bits) (pad : Body L)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ∀ (k : ℕ) (ds : List ℕ), Rt (treesT (K := W.K) ℓ us pre pad posAt emb o k ds)
  | _, [] => trivial
  | k, d :: ds => (rt_treeT W ℓ us pre d _).bind fun _ =>
      (rt_treesT ℓ us pre pad posAt emb o (k + 1) ds).bind fun _ => trivial

theorem rt_bitsT (ℓ : ℕ) : Rt (bitsT (K := W.K) (L := L) ℓ) := fun _ => trivial
theorem rt_digT : Rt (digT (lam := lam) (K := W.K) (L := L)) := fun _ => trivial

theorem rt_digsT : ∀ n : ℕ, Rt (digsT (lam := lam) (K := W.K) (L := L) n)
  | 0 => trivial
  | n + 1 => (rt_digT W).bind fun _ => (rt_digsT n).bind fun _ => trivial

theorem rt_drawD (ln : RunLen lam L) : Rt (drawD (K := W.K) ln) :=
  (rt_bitsT W ln.rs).bind fun _ => (rt_digsT W ln.dq).bind fun _ => trivial

theorem rt_gT (t : Tag) (i : ℕ) (tk : Tok) (rt : List (Dig lam))
    (pl : PlainPart (shapeOf L t) (annOf L t)) : Rt (gT (K := W.K) t i tk rt pl) := fun _ _ => trivial

theorem rt_rleafT (c : Tok) (rs : Bits) : Rt (rleafT (lam := lam) (K := W.K) (L := L) c rs) :=
  fun _ _ => trivial

theorem rt_rnodeL (c : Tok) (s : Dig lam) : Rt (rnodeL (K := W.K) (L := L) c s) :=
  fun _ _ => trivial

theorem rt_rnodeR (s : Dig lam) (c : Tok) : Rt (rnodeR (K := W.K) (L := L) s c) :=
  fun _ _ => trivial

theorem rt_climbT : ∀ (ss : List (Dig lam)) (j : ℕ) (c : Tok),
    Rt (climbT (K := W.K) (L := L) ss j c)
  | [], _, _ => trivial
  | s :: ss, j, c => by
    have h : Rt (if j % 2 = 0 then rnodeL (K := W.K) (L := L) c s else rnodeR s c) := by
      split_ifs
      · exact rt_rnodeL W c s
      · exact rt_rnodeR W s c
    exact h.bind fun u => (rt_climbT ss (j / 2) u).bind fun _ => trivial

/-! ## The search for a nonce -/

theorem rt_fbT (t : Tag) (n i : ℕ) (tk : Tok) (us : List Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (rt : List (Dig lam))
    {pl : PlainPart (shapeOf L t) (annOf L t)} (hc : clsPB _ _ (shW W t) pl = n) :
    Rt (fbT (K := W.K) t n i tk us hd hinj rt pl) := by
  cases n with
  | zero => exact ⟨fun _ _ => hc, fun _ _ => trivial⟩
  | succ m => exact ⟨fun _ _ => hc, fun _ _ => trivial⟩

section Loop
variable {C P : Type} (chal : (Fin W.K → Dig lam) → C)
  (ask : ℕ → P → StT lam W.K L ((Fin W.K → Dig lam) × Tok)) (α : P)

theorem rt_searchT (gr : GrW C P) {cap : ℕ} (hask : ∀ n, n ≤ cap → Rt (ask n (gr.put n α))) :
    ∀ (fuel n : ℕ) (dd : List Tok), n + fuel ≤ cap + 1 → Rt (searchT gr chal ask α fuel n dd)
  | 0, _, _, _ => trivial
  | fuel + 1, n, dd, h => (hask n (by omega)).bind fun a => by
      show Rt (if gr.ok (chal a.1) then _ else _)
      cases gr.ok (chal a.1)
      · exact rt_searchT gr hask fuel (n + 1) (a.2 :: dd) (by omega)
      · trivial

theorem rt_fsT (gr : Option (GrW C P)) (cap : ℕ) (h0 : gr = none → Rt (ask 0 α))
    (hp : ∀ g, gr = some g → ∀ n, n ≤ cap → Rt (ask n (g.put n α))) :
    Rt (fsT gr cap chal ask α) := by
  cases gr with
  | none => exact (h0 rfl).bind fun _ => trivial
  | some g => exact rt_searchT W chal ask α g (hp g rfl) (cap + 1) 0 [] (by omega)

end Loop

theorem rt_onFsT {P β : Type} (i : ℕ) {k : Hit lam W.K P → StT lam W.K L (Res β)}
    (hk : ∀ p, Rt (k p)) : ∀ o, Rt (onFsT i k o)
  | none => trivial
  | some p => hk p

/-! ## The rounds -/

/-- The invariant of the induction over the rounds: embP keeps the number for which a nonce
stands. -/
def ClsAt (t : Tag) {s : Shape} {A : RoundSplits s} (Ws : RoundsQueryLayout lam W.K s A)
    (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) : Prop :=
  ∀ z, clsPB _ _ (shW W t) (embP z) = clsPB s A Ws z

section Cls
variable {K : ℕ} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} {w : WireRB lam K r a}
  {Ws : RoundsQueryLayout lam K s A}

theorem cls_J_none (h : w.grJ = none) (α : a.Pj) :
    clsPB (r :: s) (a, A) (w, Ws) (.inl (.inr α)) = 0 := by
  show (match w.grJ with
    | none => 0
    | some g => g.get α) = 0
  rw [h]

theorem cls_J_some {g : GrW r.Chal a.Pj} (h : w.grJ = some g) (α : a.Pj) :
    clsPB (r :: s) (a, A) (w, Ws) (.inl (.inr α)) = g.get α := by
  show (match w.grJ with
    | none => 0
    | some g => g.get α) = _
  rw [h]

theorem cls_0_none (h : w.gr0 = none) (α : a.P0) :
    clsPB (r :: s) (a, A) (w, Ws) (.inl (.inl α)) = 0 := by
  show (match w.gr0 with
    | none => 0
    | some g => g.get α) = 0
  rw [h]

theorem cls_0_some {g : GrW r.Chal a.P0} (h : w.gr0 = some g) (α : a.P0) :
    clsPB (r :: s) (a, A) (w, Ws) (.inl (.inl α)) = g.get α := by
  show (match w.gr0 with
    | none => 0
    | some g => g.get α) = _
  rw [h]

end Cls

/-- is the act one query on the slot's own component? -/
def ownOf {lam : ℕ} {X : Type} : ActT lam X → Option Bool
  | .one _ _ _ _ own _ => some own
  | .join _ => none

/-- A query on the slot's own component is made in a local round, all else in a shared round. -/
theorem kind_of_act (cms : List (Dig lam)) (x : Option X) (salt : Tok) {kd : Kind} {ph : PhT}
    {act : ActT lam X} (h : actT cms x salt kd ph = some act) :
    kd = if ownOf act = some true then .lo else .sh := by
  cases kd <;> cases ph <;> simp only [actT, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

theorem rt_chainT (t : Tag) (cms : List (Dig lam)) (x : Option X) (ℓ : ℕ)
    (pre : ℕ → Bool → Bits → Bits) (salt : Tok) (cd : CoinsD lam L) (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam W.K s A)
      (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
      (i : ℕ) (ph : PhT) (σ : Strat s Unit), ClsAt W t Ws embP → Back s A Ws cap i →
      Rt (chainT t cms x ℓ pre salt cd cap s A Ws embS embP i ph σ)
  | [], _, _, _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, Ws), embS, embP, i, ph, (m, k), hc, hb => by
    have hc' : ClsAt W t Ws fun z => embP (.inr z) := fun z => hc (.inr z)
    have hb1 := hb.1
    rw [chainT]
    split
    next tk us hd inj nx heq =>
      have hk : a.kind = .lo := kind_of_act cms _ salt heq
      rw [hk] at hb1
      exact (rt_treesT W _ _ _ _ _ _ _ _ _).bind fun TJ =>
        (rt_fsT W _ _ _ w.grJ (cap i)
          (fun hn => rt_fbT W t 0 i _ _ _ _ _ ((hc _).trans (cls_J_none hn _)))
          (fun g hg n hn => rt_fbT W t n i _ _ _ _ _
            ((hc _).trans ((cls_J_some hg _).trans (hb1 g hg n _ hn))))).bind
          (rt_onFsT W i fun q =>
            (rt_chainT t cms x ℓ pre salt cd cap s A Ws _ _ (i + 1) _ _ hc' hb.2).bind
              fun _ => trivial)
    next tk us hd inj nx heq =>
      have hk : a.kind = .sh := kind_of_act cms _ salt heq
      rw [hk] at hb1
      exact (rt_treesT W _ _ _ _ _ _ _ _ _).bind fun T0 =>
        (rt_fsT W _ _ _ w.gr0 (cap i)
          (fun hn => rt_fbT W t 0 i _ _ _ _ _ ((hc _).trans (cls_0_none hn _)))
          (fun g hg n hn => rt_fbT W t n i _ _ _ _ _
            ((hc _).trans ((cls_0_some hg _).trans (hb1 g hg n _ hn))))).bind
          (rt_onFsT W i fun q =>
            (rt_chainT t cms x ℓ pre salt cd cap s A Ws _ _ (i + 1) _ _ hc' hb.2).bind
              fun _ => trivial)
    next tk heq =>
      have hk : a.kind = .sh := kind_of_act cms _ salt heq
      rw [hk] at hb1
      exact (rt_treesT W _ _ _ _ _ _ _ _ _).bind fun TJ =>
        (rt_treesT W _ _ _ _ _ _ _ _ _).bind fun T0 =>
        (rt_gT W t i tk _ _).bind fun c =>
        (rt_rleafT W c _).bind fun d =>
        (rt_climbT W _ _ d).bind fun rq =>
        (rt_fsT W _ _ _ w.gr0 (cap i)
          (fun hn => rt_fbT W t 0 i _ _ _ _ _ ((hc _).trans (cls_0_none hn _)))
          (fun g hg n hn => rt_fbT W t n i _ _ _ _ _
            ((hc _).trans ((cls_0_some hg _).trans (hb1 g hg n _ hn))))).bind
          (rt_onFsT W i fun q =>
            (rt_chainT t cms x ℓ pre salt cd cap s A Ws _ _ (i + 1) _ _ hc' hb.2).bind
              fun _ => trivial)
    next heq => trivial

/-! ## A compiled run -/

section Prove
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam W.K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeT lam L) (preX : Bits)
  (σ : Strat Q.loc.shape Unit) (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits) (cap : ℕ → ℕ)
  (stop : Rho Q.loc.shape → Bool)

theorem rt_hashT (hc : ClsAt W t wq.sh embP) (hb : Back Q.loc.shape Q.ann wq.sh cap 0) :
    Rt (hashT t Q wq embS embP xin cms x σ ln pre cap) := fun salt =>
  (rt_drawD W ln).bind fun cd =>
    (rt_chainT W t cms (xin x) ln.fr pre salt cd cap _ _ wq.sh embS embP 0 .first σ hc hb).bind
      fun _ => trivial

/-! The end of a run: the reveals are made chunk by chunk (Johnson/TokenRules/Chunks.lean). -/

omit t embS embP xin cms σ ln cap stop Q wq x y xt preX pre in
theorem rt_revealsT : ∀ l : List (List Tok), Rt (revealsT (lam := lam) (K := W.K) (L := L) l)
  | [] => trivial
  | _ :: l => fun _ => rt_revealsT l

theorem rt_finishC (salt : Tok) (cd : CoinsD lam L) (z : OutT lam L Q.loc.shape) :
    Rt (finishC Q wq x y xt preX pre salt cd z) :=
  (rt_revealsT W _).bind fun _ _ => trivial

theorem rt_endC (a : Tok × CoinsD lam L × Res (OutT lam L Q.loc.shape)) :
    Rt (endC Q wq x y xt preX pre stop a) := by
  unfold endC
  split
  next z _ =>
    cases stop z.rho
    · exact (rt_finishC W Q wq x y xt preX pre a.1 a.2.1 z).bind fun _ => trivial
    · trivial
  next => trivial
  next => trivial

theorem rt_proveC (hc : ClsAt W t wq.sh embP) (hb : Back Q.loc.shape Q.ann wq.sh cap 0) :
    Rt (proveC t Q wq embS embP xin cms x y xt preX σ ln pre cap stop) :=
  (rt_hashT W t Q wq embS embP xin cms x σ ln pre cap hc hb).bind
    (rt_endC W Q wq x y xt preX pre stop)

end Prove

end OnBytes.GhostSide

#print axioms OnBytes.GhostSide.Back.of_okg
#print axioms OnBytes.GhostSide.not_routed_fbw
#print axioms OnBytes.GhostSide.rt_chainT
#print axioms OnBytes.GhostSide.rt_hashT
#print axioms OnBytes.GhostSide.rt_proveC
