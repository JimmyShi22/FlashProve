-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/MapKey.lean: if a scheme has index privacy on a range of indices, then so has, at
the same bound, the scheme whose published key is a function of the old key. For schemes that serve
batches of requests, over any family of oracles (ZKCP/Gen.lean).
Terms and the limits that go with any quote: Spec.lean.

What this file has.
  mapKeyArg A f V'   the scheme: the committer publishes f of A's key; the prover is A's; the
                     verifier is a variable V', since A's verifier does not take the new key. Index
                     privacy does not read a verifier.
  mapKeySim Sim f    the simulator: f of Sim's key; all else is Sim's.
  privacyOn_mapKey   If A has ZKCP.Gen.PrivacyOn (ZKCP/OnRange.lean) with Sim and ζ on the range ok,
                     then mapKeyArg A f V' has it with mapKeySim Sim f, the same ζ and the same
                     range.
  asks_mapKey_C      the new committer queries what the old one queries.
By realExp_mapKey and idealExp_mapKey both experiments are the old ones, for the adversary that
first applies f, with f applied to the view's key (mapView f).

Why. Front.lean needs a value that the committer knows, a part of what was read off the hash
function, in the published key. The library's step for re-packings (ZKCP.PrivacyFor.wrap,
ZKCP/PrivacyWrap.lean) is over one hash function, with one request a call, and costs one query. This
one is a level lower and costs nothing.

Limits. f is any function: it may discard a part of the old key, or only change its form. A key that
holds something that cannot be computed from the old key is not covered. Nothing on completeness or
binding: they read V'.

Sources. The proofs follow the pattern of ZKCP/OnRange.lean (realLoop_range, whose proof is that of
realLoop_withC, Rom/Blocks.lean) and Rom/ExitPriv.lean (privacy_overOne).
-/
import ZKCP.OnRange
import Rom.AsksIn

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open Rom Prob ZKCP

variable {S : OSpec} {I X W PP IVK IVK' ISK Pf : Type}

/-- The scheme whose committer publishes f of A's key. The prover and the prover's key are A's; the
verifier is the variable V'. -/
def mapKeyArg (A : Gen.Arg S I X W IVK ISK Pf) (f : IVK → IVK')
    (V' : IVK' → X → Pf → Rom.OComp S Bool) : Gen.Arg S I X W IVK' ISK Pf where
  C := fun i => (A.C i).bind fun k => .pure (f k.1, k.2)
  P := A.P
  V := V'

/-- The simulator that publishes f of Sim's key; its state, answers and proofs are Sim's. -/
def mapKeySim (Sim : Gen.Simulator S PP IVK X Pf) (f : IVK → IVK') :
    Gen.Simulator S PP IVK' X Pf where
  St := Sim.St
  init := fun pp N => (Sim.init pp N).map fun o => (f o.1, o.2)
  answer := Sim.answer
  prove := Sim.prove

/-- A view with f applied to its key; sessions, trace and coins are unchanged. -/
def mapView (f : IVK → IVK') (v : Gen.View S IVK X Pf) : Gen.View S IVK' X Pf :=
  ⟨f v.ivk, v.sessions, v.trace, v.coins⟩

/-- If all queries of A's committer at i satisfy P, so do all queries of the new committer at i. -/
theorem asks_mapKey_C (A : Gen.Arg S I X W IVK ISK Pf) (f : IVK → IVK')
    (V' : IVK' → X → Pf → Rom.OComp S Bool) (P : (o : S.ι) → S.Dom o → Prop) (i : I)
    (h : (A.C i).AsksIn P) : ((mapKeyArg A f V').C i).AsksIn P :=
  Rom.OComp.AsksIn.bind (g := fun k : IVK × ISK => Rom.OComp.pure (f k.1, k.2)) (fun _ => trivial) h

/-! ## The real experiment -/

/-- The loop of the real experiment for mapKeyArg A f V', started at mapView f v, is the loop for A,
started at v with the environment that first applies mapView f, followed by mapView f. -/
theorem realLoop_mapKey (A : Gen.Arg S I X W IVK ISK Pf) (f : IVK → IVK')
    (V' : IVK' → X → Pf → Rom.OComp S Bool) (Z : Gen.ViewEnv S IVK' X W Pf) (isk : ISK)
    (V : Gen.AdvVerifier S X Pf) : ∀ (n : ℕ) (v : Gen.View S IVK X Pf),
    Gen.realLoop (mapKeyArg A f V') Z isk V n (mapView f v) =
      (Gen.realLoop A (fun v => Z (mapView f v)) isk V n v).bind fun v' =>
        .pure (mapView f v') := by
  induction V with
  | halt => intro n v; rfl
  | query o q k ih =>
    intro n v
    simp only [Gen.realLoop, Rom.OComp.bind]
    exact congrArg _ (funext fun r => ih r n { v with trace := v.trace ++ [⟨o, q, r⟩] })
  | sample m k ih =>
    intro n v
    simp only [Gen.realLoop, Rom.OComp.bind]
    exact congrArg _ (funext fun r => ih r n { v with coins := v.coins ++ [r.val] })
  | request k ih =>
    intro n v
    cases n with
    | zero => rfl
    | succ n =>
      cases hz : Z (mapView f v) with
      | none =>
        simp only [Gen.realLoop, hz]
        rfl
      | some b =>
        simp only [Gen.realLoop, hz]
        rw [Rom.OComp.bind_assoc]
        exact congrArg _ (funext fun πs =>
          ih _ n { v with sessions := v.sessions ++ [b.released πs.val] })

/-- The real experiment for mapKeyArg A f V' is the real experiment for A, with the adversary and
the environment that first apply f to the key, followed by mapView f. -/
theorem realExp_mapKey (A : Gen.Arg S I X W IVK ISK Pf) (f : IVK → IVK')
    (V' : IVK' → X → Pf → Rom.OComp S Bool) (Vt : IVK' → Gen.AdvVerifier S X Pf)
    (Z : Gen.ViewEnv S IVK' X W Pf) (i : I) (N : ℕ) :
    Gen.realExp (mapKeyArg A f V') Vt Z i N =
      (Gen.realExp A (fun k => Vt (f k)) (fun v => Z (mapView f v)) i N).bind fun v' =>
        .pure (mapView f v') := by
  show ((A.C i).bind fun k => Rom.OComp.pure (f k.1, k.2)).bind (fun key =>
      Gen.realLoop (mapKeyArg A f V') Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩) =
    ((A.C i).bind fun key =>
      Gen.realLoop A (fun v => Z (mapView f v)) key.2 (Vt (f key.1)) N ⟨key.1, [], [], []⟩).bind _
  rw [Rom.OComp.bind_assoc, Rom.OComp.bind_assoc]
  exact congrArg _ (funext fun key =>
    realLoop_mapKey A f V' Z key.2 (Vt (f key.1)) N ⟨key.1, [], [], []⟩)

/-! ## The ideal experiment -/

/-- The same as realLoop_mapKey for the loop of the ideal experiment, with mapKeySim Sim f and Sim.
-/
theorem idealLoop_mapKey (Sim : Gen.Simulator S PP IVK X Pf) (f : IVK → IVK')
    (Z : Gen.ViewEnv S IVK' X W Pf) (V : Gen.AdvVerifier S X Pf) :
    ∀ (n : ℕ) (v : Gen.View S IVK X Pf) (s : Sim.St),
      Gen.idealLoop (mapKeySim Sim f) Z V n (mapView f v) s =
        (Gen.idealLoop Sim (fun v => Z (mapView f v)) V n v s).map (mapView f) := by
  induction V with
  | halt => intro n v s; simp only [Gen.idealLoop, PMF.pure_map]
  | query o q k ih =>
    intro n v s
    simp only [Gen.idealLoop, PMF.map_bind]
    exact congrArg _ (funext fun out =>
      ih out.1 n { v with trace := v.trace ++ [⟨o, q, out.1⟩] } out.2)
  | sample m k ih =>
    intro n v s
    simp only [Gen.idealLoop, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r n { v with coins := v.coins ++ [r.val] } s)
  | request k ih =>
    intro n v s
    cases n with
    | zero => simp only [Gen.idealLoop, PMF.pure_map]
    | succ n =>
      cases hz : Z (mapView f v) with
      | none => simp only [Gen.idealLoop, hz, PMF.pure_map]
      | some b =>
        simp only [Gen.idealLoop, hz, PMF.map_bind]
        exact congrArg _ (funext fun out =>
          ih _ n { v with sessions := v.sessions ++ [b.ownX.zip out.1.val] } out.2)

/-- The same as realExp_mapKey for the ideal experiment, with mapKeySim Sim f and Sim. -/
theorem idealExp_mapKey (R : Gen.RelPair I X W PP) (Sim : Gen.Simulator S PP IVK X Pf)
    (f : IVK → IVK') (Vt : IVK' → Gen.AdvVerifier S X Pf) (Z : Gen.ViewEnv S IVK' X W Pf) (i : I)
    (N : ℕ) :
    Gen.idealExp R (mapKeySim Sim f) Vt Z i N =
      (Gen.idealExp R Sim (fun k => Vt (f k)) (fun v => Z (mapView f v)) i N).map (mapView f) := by
  show ((Sim.init (R.pp i) N).map fun o => (f o.1, o.2)).bind (fun out =>
      Gen.idealLoop (mapKeySim Sim f) Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2) =
    ((Sim.init (R.pp i) N).bind fun out =>
      Gen.idealLoop Sim (fun v => Z (mapView f v)) (Vt (f out.1)) N ⟨out.1, [], [], []⟩ out.2).map _
  rw [PMF.bind_map, PMF.map_bind]
  exact congrArg _ (funext fun out =>
    idealLoop_mapKey Sim f Z (Vt (f out.1)) N ⟨out.1, [], [], []⟩ out.2)

/-! ## The theorem -/

/-- If A has index privacy on the range ok (ZKCP.Gen.PrivacyOn) with the simulator Sim and the bound
ζ, then mapKeyArg A f V' has it on ok with mapKeySim Sim f and the same ζ, for every f and V'. -/
theorem privacyOn_mapKey (R : Gen.RelPair I X W PP) (A : Gen.Arg S I X W IVK ISK Pf) (B : ℕ)
    (Sim : Gen.Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) (f : IVK → IVK')
    (V' : IVK' → X → Pf → Rom.OComp S Bool) (h : Gen.PrivacyOn R A B Sim ζ ok) :
    Gen.PrivacyOn R (mapKeyArg A f V') B (mapKeySim Sim f) ζ ok := by
  intro i hi Z hZ tV Vt N hb
  obtain ⟨h1, h2⟩ := h i hi (fun v => Z (mapView f v)) (fun v b hv => hZ _ b hv) tV
    (fun k => Vt (f k)) N fun k => hb (f k)
  have hreal : ∀ T, Rom.Pr (Gen.realExp (mapKeyArg A f V') Vt Z i N) (fun _ => T) =
      Rom.Pr (Gen.realExp A (fun k => Vt (f k)) (fun v => Z (mapView f v)) i N)
        (fun _ => mapView f ⁻¹' T) := by
    intro T
    unfold Rom.Pr Rom.PrCoins
    refine MeasureTheory.lintegral_congr fun g => ?_
    rw [realExp_mapKey, Rom.OComp.runEager_bind]
    exact pr_map _ _ _
  have hideal : ∀ T, pr (Gen.idealExp R (mapKeySim Sim f) Vt Z i N) T =
      pr (Gen.idealExp R Sim (fun k => Vt (f k)) (fun v => Z (mapView f v)) i N)
        (mapView f ⁻¹' T) := by
    intro T
    rw [idealExp_mapKey, pr_map]
  constructor
  · simp only [hreal, hideal]
    exact (sd_comap_le _ _ (mapView f)).trans h1
  · rw [hideal]
    exact h2

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.privacyOn_mapKey
