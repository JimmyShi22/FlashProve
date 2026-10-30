-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Lump.lean: helper lemmas for the last game hop for batches (`lumpBP`,
Compile/Batch/PubLump.lean) (words of this library: lean/GLOSSARY.md).
This file does not prove the hop. Main lemma: `interact_lump_adm`: a map Φ of states that commutes
with all answers and with all allowed calls, on an invariant that these preserve, preserves the
distribution of output and state (not all hypotheses are named here: see its statement).
The hop, `lumpBP`: under the hypotheses of its statement, the challenger that rejects a batch on a
copy which has served s1 batches is, in the distribution of the output, the wrapped lifetime
experiment.

Notation:
  `W₁`, `W₂`: a `World S Out In` (Rom/World.lean): the challenger of an experiment, together with
    the oracles: a state, a randomized answer to each oracle query, a randomized reply to each call;
  `A`: an `Adv S Out In α` (Rom/World.lean): an adversary: it halts with an output, flips coins,
    queries an oracle, or makes a call m and receives an answer;
  `interact W A s` (Rom/World.lean): the run of an adversary against a challenger, from a state;
  `AllCalls okc A`: every call of the adversary is allowed, on every path.
-/
import Compile.Batch.Wr
import Compile.Batch.SpecEq
import Compile.Batch.RealB

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.GlueB (GCall SCall GAdm asW ownPf)
open Compile.BatchLife (LifeOutB LifeInB BRet LifeB linksGB placeB bsess vec)
open Compile.Lifetime (Sess sess)
open Compile.DefC (virtL)

/-! ## General tools -/

namespace LTools

variable {S : OSpec} {Out In α : Type}

/-- every call of the adversary is allowed, on every path -/
def AllCalls (okc : Out → Prop) : Adv S Out In α → Prop
  | .halt _ => True
  | .sample _ k => ∀ r, AllCalls okc (k r)
  | .query _ _ k => ∀ r, AllCalls okc (k r)
  | .call m k => okc m ∧ ∀ a, AllCalls okc (k a)

/-- A map Φ of states that commutes with all answers and with all allowed calls (`ha`, `hr`), on an
invariant that these preserve (`ia`, `ir`), preserves the distribution of output and state, from a
state that has the invariant, for an adversary that makes allowed calls only. -/
theorem interact_lump_adm (W₁ W₂ : World S Out In) (Φ : W₁.σ → W₂.σ) (Inv : W₁.σ → Prop)
    (okc : Out → Prop)
    (ha : ∀ s o q, Inv s → (W₁.answer s o q).map (Prod.map id Φ) = W₂.answer (Φ s) o q)
    (hr : ∀ s m, Inv s → okc m → (W₁.reply s m).map (Prod.map id Φ) = W₂.reply (Φ s) m)
    (ia : ∀ s o q, Inv s → ∀ x ∈ (W₁.answer s o q).support, Inv x.2)
    (ir : ∀ s m, Inv s → okc m → ∀ x ∈ (W₁.reply s m).support, Inv x.2) (A : Adv S Out In α) :
    AllCalls okc A → ∀ s, Inv s → (interact W₁ A s).map (Prod.map id Φ) = interact W₂ A (Φ s) := by
  induction A with
  | halt a => intro _ s _; simp only [interact, PMF.pure_map]; rfl
  | sample n k ih => intro hA s hs; simp only [interact, PMF.map_bind, ih _ (hA _) s hs]
  | query o q k ih =>
    intro hA s hs
    simp only [interact, PMF.map_bind]
    rw [← ha s o q hs, PMF.bind_map]
    refine bind_congr_support _ fun x hx => ?_
    exact ih _ (hA _) _ (ia s o q hs x hx)
  | call m k ih =>
    intro hA s hs
    simp only [interact, PMF.map_bind]
    rw [← hr s m hs hA.1, PMF.bind_map]
    refine bind_congr_support _ fun x hx => ?_
    exact ih _ (hA.2 _) _ (ir s m hs hA.1 x hx)

/-- the state with one more token, of no bits -/
def dummy (w : LSt S) : LSt S := { w with vals := w.vals ++ [[]] }

theorem lrun_fresh0 {sp : Split S} {β : Type} (k : ℕ → LStep S sp β) (d : LSt S) :
    (LStep.fresh 0 k).run d = (k d.vals.length).run (dummy d) := by
  have h : PMF.uniformOfFintype (Fin 0 → Bool) = PMF.pure fun j => j.elim0 := by
    refine PMF.ext fun u => ?_
    rw [Subsingleton.elim u fun j => j.elim0]
    simp
  simp only [LStep.run, h, PMF.pure_bind]
  rfl

theorem lreply_of_step {sp : Split S} {C : LChall S sp Out In} {s : C.τ} {c : Out}
    {Q : LStep S sp (In × C.τ)} (h : C.step s c = Q) (w : LSt S) :
    C.world.reply (s, w) c = (Q.run w).map fun y => (y.1.1, (y.1.2, y.2)) := by
  rw [← h]
  rfl

theorem lreply_pure {sp : Split S} {C : LChall S sp Out In} {s : C.τ} {c : Out} {a : In}
    (h : C.step s c = LStep.pure (a, s)) (w : LSt S) :
    C.world.reply (s, w) c = PMF.pure (a, (s, w)) := by
  rw [lreply_of_step h]
  exact PMF.pure_map _ _

end LTools

open LTools

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

abbrev LW (W : QueryLayout lam L) : Type := LSt (spec lam W.K L)

/-! ## Batches and their own requests -/

section Own

theorem isEmpty_ownX : ∀ b : ZKCP.Gen.Batch X Unit, b.ownX.isEmpty = !hasOwn b
  | [] => rfl
  | s :: b => by
      have ih := isEmpty_ownX b
      cases h : s.2.2
      · simpa [ZKCP.Gen.Batch.ownX, hasOwn, h] using ih
      · simp [ZKCP.Gen.Batch.ownX, hasOwn, h]

theorem ownPf_const {Pf : Type} (π₀ : Pf) :
    ∀ b : ZKCP.Gen.Batch X Unit, ownPf b ((reqs b).map fun _ => π₀) = b.ownX.map fun _ => π₀
  | [] => rfl
  | s :: b => by
      have e : (reqs (s :: b)).map (fun _ => π₀) = π₀ :: (reqs b).map fun _ => π₀ := by
        simp [reqs, ZKCP.Gen.Batch.pairs]
      rw [e, RealB.ownPf_cons, ownPf_const π₀ b]
      cases h : s.2.2 <;> simp [ZKCP.Gen.Batch.ownX, h]

theorem replyOf_const (b : ZKCP.Gen.Batch X Unit) (π₀ : Prf lam L) :
    replyOf b ((reqs b).map fun _ => π₀) = .inr (b.ownX.map fun _ => π₀) := by
  unfold replyOf
  rw [RealB.val_fitLen _ _ _ (by simp [RealB.length_reqs]), ownPf_const]

end Own

/-! ## The experiment's replies -/

section Game

variable (W : QueryLayout lam L) (p : Params) (i : I)

abbrev TheLifeB : World (spec lam W.K L) (LifeOutB X) (LifeInB L) :=
  LifeB (spec lam W.K L) L p.leaves i

theorem reply_LifeB_setup (g : Option (List L.EncodingRandomness) × Table (spec lam W.K L)) :
    (TheLifeB W p i).reply g (.inl ())
      = (unif L.EncodingRandomness).bind fun r₀ => (sess L.honestOfflineProver (i, r₀) ()).bind fun sT =>
          (linksGB (fun r r' => sess L.honestLinkProver (i, r, r') ()) r₀ (p.M + 1)).map fun ls =>
            (.inl (sT, ls.map Prod.snd), (some (ls.map Prod.fst), g.2)) := rfl

theorem reply_LifeB_none (rs : List L.EncodingRandomness) (T : Table (spec lam W.K L)) (j : ℕ)
    (xs : List X) (h : rs[j]? = none) :
    (TheLifeB W p i).reply (some rs, T) (.inr (j, xs)) = PMF.pure (.inr none, (some rs, T)) := by
  simp [LifeB, BatchLife.StarWB, h]

theorem reply_LifeB_some (rs : List L.EncodingRandomness) (T : Table (spec lam W.K L)) (j : ℕ) (xs : List X)
    (r : L.EncodingRandomness) (h : rs[j]? = some r) :
    (TheLifeB W p i).reply (some rs, T) (.inr (j, xs)) =
      (placeB L (fun J xs rest => bsess L.honestOnlineBatchProver (i, r) (vec J xs rest) J) xs).map fun o =>
        (.inr (some o), (some rs, T)) := by
  simp [LifeB, BatchLife.StarWB, h]

theorem length_linksGB (sL : L.EncodingRandomness → L.EncodingRandomness → PMF (Sess L.link)) (r₀ : L.EncodingRandomness) :
    ∀ (n : ℕ), ∀ ls ∈ (linksGB sL r₀ n).support, ls.length = n
  | 0, ls, h => by
      rw [linksGB, PMF.support_pure, Set.mem_singleton_iff] at h
      rw [h]
      rfl
  | n + 1, ls, h => by
      rw [linksGB] at h
      obtain ⟨r, -, h⟩ := (PMF.mem_support_bind_iff _ _ _).1 h
      obtain ⟨s, -, h⟩ := (PMF.mem_support_bind_iff _ _ _).1 h
      obtain ⟨t, ht, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 h
      rw [List.length_cons, length_linksGB sL r₀ n t ht]

end Game

/-! ## For the last hop -/

section Lump

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)



/-- If copy j does not exist (hl), the run returns a proof without proof strings for each request,
and the state stays. -/
theorem run_PpLJ_none (N₀ δ : ℕ) (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : Fin (p.M + 1))
    (hl : k.leaves[j.val]? = none) (st : LW W) :
    (virtL N₀ δ (PpLJ W WP p k fr xs j)).run st =
      PMF.pure (xs.map fun _ => ⟨j.val, default, none, none⟩, st) := by
  have e : PpLJ W WP p k fr xs j =
      (drawL WP.perm).bind fun _ => LStep.pure (xs.map fun _ => ⟨j.val, default, none, none⟩) := by
    unfold PpLJ PpJL
    simp only [hl]
    rfl
  rw [e]
  exact PMF.bind_const _ _

end Lump

section Final

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

/-- the calls for which the two challengers are compared: a batch has at most maxBatchSize requests -/
def okcB (L : BatchProtocol I X) : GCall X Unit → Prop
  | .setup => True
  | .batch b => b.pairs.length ≤ L.maxBatchSize

/-- An admissible adversary whose batches have at most maxBatchSize requests makes such calls only. -/
theorem allCalls_of_gAdm {S : OSpec} {α : Type} (ok : ZKCP.Gen.Batch X Unit → Prop)
    (hok : ∀ b, ok b → b.pairs.length ≤ L.maxBatchSize) (A : Adv S (GCall X Unit) (BIn lam L) α) :
    ∀ (b : Bool) (n : ℕ), GAdm ok A b n → AllCalls (okcB L) A := by
  induction A with
  | halt a => exact fun _ _ _ => trivial
  | sample m k ih => exact fun b n h r => ih r b n (h r)
  | query o q k ih => exact fun b n h r => ih r b n (h r)
  | call m k ih =>
    intro b n h
    rcases m with _ | bt
    · simp only [GAdm] at h
      exact ⟨trivial, fun a => ih a true n (h.2 a)⟩
    · cases n with
      | zero => exact h.elim
      | succ n =>
        simp only [GAdm] at h
        exact ⟨hok bt h.2.1, fun a => ih a b n (h.2.2 a)⟩


theorem index_of_mem_run_CpL (w : LW W) : ∀ y ∈ ((CpL W WP p i).run w).support, y.1.2.i = i := by
  intro y hy
  unfold CpL at hy
  simp only [DefC.run_bind, PMF.mem_support_bind_iff] at hy
  obtain ⟨a, -, b, -, c, -, hy⟩ := hy
  rw [(PMF.mem_support_pure_iff _ _).1 hy]

end Final

end Compile.Batch
