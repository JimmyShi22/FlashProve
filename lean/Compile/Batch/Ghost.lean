-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Ghost.lean: the ghost names `fbw t k` and the exchange of queries to them with queries
to `fb t`: proofs of the statements of Compile/Batch/SpecGhost.lean, except `Spec.routedCp`,
`Spec.routedPp` and, which needs them, `Spec.argB_via` (Compile/Batch/GhostRouted.lean) (words of
this library: lean/GLOSSARY.md).

The programs `Cp`, `Pp` (Compile/Batch/Star.lean) write proof-of-work attempt k + 1 as a query to
`fbw t k`; `realQ` (Compile/Batch/Oracles.lean) turns it into the query to the Fiat-Shamir oracle
`fb t`.
  Part 1, generic in the family of oracles and in the scheme: `closeVia`, from three statements of
  Rom/SpecVia.lean and their proofs (Rom/Via.lean).
  Part 2, the compiled scheme: `ghostPerm` (the exchange `ghost W` is a bijection on queries and its
  own inverse, for every wire record), `realQ_via` (for a routed algorithm `realQ` is translation by
  `ghost W`), `routedErase`, `argB_via_of` (`Spec.argB_via` from `Spec.routedCp` and
  `Spec.routedPp`).

Notation: in Rom/SpecVia.lean: `QMap S`: a translation of queries: for the point (o, q) the point
(o', q') that is queried in its place, and how an answer of o' is read as an answer of o;
`QMap.Inv φ ψ`: ψ undoes φ; `c.via φ`: the algorithm that queries φ p where c queries p; `Sm.pre ψ`:
the challenger that answers the query p by its translated answer at ψ p; in
Compile/Batch/SpecGhost.lean: `cls W t q`: the number that the nonce of a Fiat-Shamir query denotes;
0 if the component has no proof-of-work bits; `ghost W`: the exchange of queries: (fb t, q) with the
nonce for k + 1 and (fbw t k, q); all other queries stay; `Routed W c`: fb t is queried only where
the input holds the nonce for 0 (`cls W t q` = 0), and fbw t k only where it holds the nonce for k +
1; `viaCP φ A`: the scheme with C and P translated, and V as it is; `argBT`: the scheme whose C and
P are what `erase` makes of the programs, queries to the ghost names included; `argB`
(Compile/Batch/Star.lean): the compiled scheme.

Limits: see the header of Compile/Batch/SpecGhost.lean.
-/
import Compile.Batch.SpecGhost
import Rom.Via
import Rom.ViaClose

noncomputable section

/-! ## Part 1: generic -/

namespace Rom

variable {S : OSpec} {α β : Type}

theorem OComp.via_pure (φ : QMap S) (a : α) : (OComp.pure a : OComp S α).via φ = .pure a := rfl

/- (OComp.via_bind: Rom/ViaClose.lean.) -/

/-- `via` at a query whose translation is given -/
theorem OComp.via_query_of {φ : QMap S} {o o' : S.ι} {q : S.Dom o} {q' : S.Dom o'}
    {f : S.Rng o' → S.Rng o} (h : φ o q = ⟨o', q', f⟩) (k : S.Rng o → OComp S α) :
    (OComp.query o q k).via φ = .query o' q' fun r => (k (f r)).via φ := by
  show OComp.query (φ o q).1 (φ o q).2.1 (fun r => (k ((φ o q).2.2 r)).via φ) = _
  rw [h]

/-- One query: if φ sends (o, q) to (o', q') and ψ sends that back, with maps between the ranges
that are inverse to each other, `QMap.Inv φ ψ` holds at (o, q). -/
theorem QMap.inv_at {φ ψ : QMap S} {o o' : S.ι} {q : S.Dom o} {q' : S.Dom o'}
    {f : S.Rng o' → S.Rng o} {g : S.Rng o → S.Rng o'} (h1 : φ o q = ⟨o', q', f⟩)
    (h2 : ψ o' q' = ⟨o, q, g⟩) (h3 : ∀ r, f (g r) = r) (h4 : ∀ r, g (f r) = r) :
    ∃ b : S.Rng o → S.Rng (φ o q).1,
      ψ (φ o q).1 (φ o q).2.1 = ⟨o, q, b⟩ ∧
      (∀ r, (φ o q).2.2 (b r) = r) ∧
      (∀ r, b ((φ o q).2.2 r) = r) := by
  rw [h1]
  exact ⟨g, h2, h3, h4⟩

end Rom

namespace Compile.GlueB
open Rom Prob ZKCP
open scoped ENNReal

variable {S : OSpec} {I X Wn PP IVK ISK Pf : Type}

theorem gadmVia : Spec.gadmVia := by
  intro S X Wn IVK Pf α ψ ok D
  induction D with
  | halt a => intro _ _ _; trivial
  | sample m k ih => intro b n h r; exact ih r b n (h r)
  | query o q k ih => intro b n h r; exact ih _ b n (h _)
  | call m k ih =>
      intro b n h
      cases m with
      | setup => exact ⟨h.1, fun a => ih a true n (h.2 a)⟩
      | batch c =>
          cases n with
          | zero => exact h
          | succ n => exact ⟨h.1, h.2.1, fun a => ih a b n (h.2.2 a)⟩

/-- the algorithms of the real experiment -/
def realStep (A : Gen.Arg S I X Wn IVK ISK Pf) (i : I) :
    Option ISK → GCall X Wn → OComp S (GIn IVK Pf × Option ISK) := fun s c => match c, s with
  | .setup, _ => (A.C i).bind fun o => pure (.inl o.1, some o.2)
  | .batch _, none => pure (.inr [], none)
  | .batch b, some k => (A.P k b.pairs).bind fun πs => pure (.inr (ownPf b πs.val), some k)

theorem realW_eq (A : Gen.Arg S I X Wn IVK ISK Pf) (i : I) :
    realW A i = World.ofOComp (realStep A i) := rfl

/-- The algorithms of the real experiment of the translated scheme: those of the real experiment of
A, translated. -/
theorem realStep_viaCP (φ : QMap S) (A : Gen.Arg S I X Wn IVK ISK Pf) (i : I) :
    realStep (viaCP φ A) i = fun s m => (realStep A i s m).via φ := by
  refine funext fun s => funext fun c => ?_
  cases c with
  | setup =>
      show ((A.C i).via φ).bind (fun o => pure (Sum.inl o.1, some o.2)) =
        ((A.C i).bind fun o => pure (Sum.inl o.1, some o.2)).via φ
      exact (OComp.via_bind φ (A.C i) fun o =>
        (pure (Sum.inl o.1, some o.2) : OComp S (GIn IVK Pf × Option ISK))).symm
  | batch b =>
      cases s with
      | none => rfl
      | some k =>
          show ((A.P k b.pairs).via φ).bind (fun πs => pure (Sum.inr (ownPf b πs.val), some k)) =
            ((A.P k b.pairs).bind fun πs => pure (Sum.inr (ownPf b πs.val), some k)).via φ
          exact (OComp.via_bind φ (A.P k b.pairs) fun πs =>
            (pure (Sum.inr (ownPf b πs.val), some k) : OComp S (GIn IVK Pf × Option ISK))).symm

/-- Privacy at the level of challengers (`Close`) carries over along a bijection on queries, given
three statements on translations. -/
theorem closeVia_of (hW : Rom.Spec.viaWorld) (hP : Rom.Spec.viaPre) (hB : Rom.Spec.viaBounds) :
    Spec.closeVia := by
  intro S I X Wn PP IVK ISK Pf R A B Sm s₀ ζ φ ψ hφ hC i α D t n hD hA
  have h1 : (interact (realW (viaCP φ A) i) D (none, Table.empty _)).map Prod.fst =
      (interact (realW A i) (D.via ψ) (none, Table.empty _)).map Prod.fst := by
    show (interact (World.ofOComp (realStep (viaCP φ A) i)) D (none, Table.empty _)).map Prod.fst =
      _
    rw [realStep_viaCP]
    exact hW S _ _ _ α φ ψ hφ (realStep A i) D none (Table.empty _)
  have h2 : interact (asW Wn (Sm.pre ψ)) D s₀ = interact (asW Wn Sm) (D.via ψ) s₀ :=
    hP S _ _ α ψ (asW Wn Sm) D s₀
  rw [h1, h2]
  exact hC i α (D.via ψ) t n ((hB S _ _ α ψ D).1 t (n + 1) hD)
    (gadmVia S X Wn IVK Pf α ψ _ D false n hA)

theorem closeVia : Spec.closeVia := closeVia_of Rom.viaWorld Rom.viaPre Rom.viaBounds

end Compile.GlueB

/-! ## Part 2: the compiled scheme -/

namespace Compile.Batch
open Iop Rom Compile.GlueB

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L)

theorem ghost_fb_zero {t : Tag} {q : FbIn lam L t} (h : cls W t q = 0) :
    ghost W (.fb t) q = ⟨.fb t, q, id⟩ := by
  show (match cls W t q with
      | 0 =>
        (⟨.fb t, q, id⟩ : Σ o' : OracleName, domOf lam L o' × (rngOf lam W.K o' → rngOf lam W.K (.fb t)))
      | k + 1 => ⟨.fbw t k, q, id⟩) = _
  rw [h]
  rfl

theorem ghost_fb_succ {t : Tag} {q : FbIn lam L t} {k : ℕ} (h : cls W t q = k + 1) :
    ghost W (.fb t) q = ⟨.fbw t k, q, id⟩ := by
  show (match cls W t q with
      | 0 =>
        (⟨.fb t, q, id⟩ : Σ o' : OracleName, domOf lam L o' × (rngOf lam W.K o' → rngOf lam W.K (.fb t)))
      | k + 1 => ⟨.fbw t k, q, id⟩) = _
  rw [h]
  rfl

theorem ghost_fbw_pos {t : Tag} {q : FbIn lam L t} {k : ℕ} (h : cls W t q = k + 1) :
    ghost W (.fbw t k) q = ⟨.fb t, q, id⟩ := if_pos h

theorem ghost_fbw_neg {t : Tag} {q : FbIn lam L t} {k : ℕ} (h : cls W t q ≠ k + 1) :
    ghost W (.fbw t k) q = ⟨.fbw t k, q, id⟩ := if_neg h

theorem ghost_inv : QMap.Inv (ghost W) (ghost W) := by
  intro o q
  cases o with
  | fb t =>
      rcases h : cls W t q with _ | k
      · exact QMap.inv_at (ghost_fb_zero W h) (ghost_fb_zero W h) (fun _ => rfl) fun _ => rfl
      · exact QMap.inv_at (ghost_fb_succ W h) (ghost_fbw_pos W h) (fun _ => rfl) fun _ => rfl
  | fbw t k =>
      by_cases h : cls W t q = k + 1
      · exact QMap.inv_at (ghost_fbw_pos W h) (ghost_fb_succ W h) (fun _ => rfl) fun _ => rfl
      · exact QMap.inv_at (ghost_fbw_neg W h) (ghost_fbw_neg W h) (fun _ => rfl) fun _ => rfl
  | leaf => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | node => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | rleaf => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | rnode => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | g t => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | ann => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | other => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩

theorem ghostPerm : Spec.ghostPerm := fun _ _ _ _ W => ⟨ghost_inv W, ghost_inv W⟩

theorem realQ_via : Spec.realQ_via := by
  intro I X lam L W α c
  induction c with
  | pure a => intro _; rfl
  | sample n k ih => intro h; exact congrArg (OComp.sample n) (funext fun r => ih r (h r))
  | query o q k ih =>
      intro h
      cases o with
      | fb t =>
        exact (congrArg (OComp.query (S := spec lam W.K L) (.fb t) q)
            (funext fun r => ih r (h.2 r))).trans
          (OComp.via_query_of (ghost_fb_zero W h.1) k).symm
      | fbw t j =>
        exact (congrArg (OComp.query (S := spec lam W.K L) (.fb t) q)
            (funext fun r => ih r (h.2 r))).trans
          (OComp.via_query_of (ghost_fbw_pos W h.1) k).symm
      | leaf =>
        exact congrArg (OComp.query (S := spec lam W.K L) .leaf q) (funext fun r => ih r (h r))
      | node =>
        exact congrArg (OComp.query (S := spec lam W.K L) .node q) (funext fun r => ih r (h r))
      | rleaf =>
        exact congrArg (OComp.query (S := spec lam W.K L) .rleaf q) (funext fun r => ih r (h r))
      | rnode =>
        exact congrArg (OComp.query (S := spec lam W.K L) .rnode q) (funext fun r => ih r (h r))
      | g t =>
        exact congrArg (OComp.query (S := spec lam W.K L) (.g t) q) (funext fun r => ih r (h r))
      | ann =>
        exact congrArg (OComp.query (S := spec lam W.K L) .ann q) (funext fun r => ih r (h r))
      | other =>
        exact congrArg (OComp.query (S := spec lam W.K L) .other q) (funext fun r => ih r (h r))

variable {W}

/-- a routed algorithm followed by routed algorithms is routed -/
theorem Routed.bind {α β : Type} :
    ∀ {c : TypedOracleComputation lam W.K L α} {g : α → TypedOracleComputation lam W.K L β},
      Routed W c → (∀ a, Routed W (g a)) → Routed W (c.bind g)
  | .pure a, _, _, hg => hg a
  | .sample _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query (.fb _) _ k, _, h, hg => ⟨h.1, fun r => Routed.bind (c := k r) (h.2 r) hg⟩
  | .query (.fbw _ _) _ k, _, h, hg => ⟨h.1, fun r => Routed.bind (c := k r) (h.2 r) hg⟩
  | .query .leaf _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query .node _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query .rleaf _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query .rnode _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query (.g _) _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query .ann _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query .other _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg

theorem routedErase : Spec.routedErase := by
  intro I X lam L W α c
  induction c with
  | pure a => intro _ _; trivial
  | sample n k ih => intro vs h r; exact ih r vs (h r)
  | plain o q k ih =>
      intro vs h
      cases o with
      | fb t => exact ⟨h.1, fun r => ih r vs (h.2 r)⟩
      | fbw t j => exact ⟨h.1, fun r => ih r vs (h.2 r)⟩
      | leaf => exact fun r => ih r vs (h r)
      | node => exact fun r => ih r vs (h r)
      | rleaf => exact fun r => ih r vs (h r)
      | rnode => exact fun r => ih r vs (h r)
      | g t => exact fun r => ih r vs (h r)
      | ann => exact fun r => ih r vs (h r)
      | other => exact fun r => ih r vs (h r)
  | fresh ℓ k ih => intro vs h r; exact ih _ _ (h _)
  | marked o t us pt inj k ih =>
      intro vs h
      cases o with
      | fb t' => exact ⟨h.1 _ _, fun r => ih _ _ _ (h.2 _ _)⟩
      | fbw t' j => exact ⟨h.1 _ _, fun r => ih _ _ _ (h.2 _ _)⟩
      | leaf => exact fun r => ih _ _ _ (h _ _)
      | node => exact fun r => ih _ _ _ (h _ _)
      | rleaf => exact fun r => ih _ _ _ (h _ _)
      | rnode => exact fun r => ih _ _ _ (h _ _)
      | g t' => exact fun r => ih _ _ _ (h _ _)
      | ann => exact fun r => ih _ _ _ (h _ _)
      | other => exact fun r => ih _ _ _ (h _ _)
  | reveal ts k ih => intro vs h; exact ih _ vs (h _)

/-- For `W.OKG`, if the two programs are routed: the scheme is `argBT` with C and P translated by
`ghost W`. -/
theorem argB_via_of (hC : Spec.routedCp) (hP : Spec.routedPp) : Spec.argB_via := by
  intro I X lam L W WP p hW
  have e1 : (argB W WP p).C = (viaCP (ghost W) (argBT W WP p)).C := funext fun i =>
    realQ_via I X lam L W _ _
      (Routed.bind (routedErase I X lam L W _ _ [] (hC I X lam L W WP p i hW)) fun _ => trivial)
  have e2 : (argB W WP p).P = (viaCP (ghost W) (argBT W WP p)).P := funext fun k => funext fun b =>
    realQ_via I X lam L W _ _
      (Routed.bind
        (routedErase I X lam L W _ _ k.2
          (hP I X lam L W WP p k.1 (fun _ => true) (b.map Prod.fst) hW))
        fun _ => trivial)
  show (⟨(argB W WP p).C, (argB W WP p).P, V W p⟩ : ZKCP.Gen.Arg _ _ _ _ _ _ _) =
    ⟨(viaCP (ghost W) (argBT W WP p)).C, (viaCP (ghost W) (argBT W WP p)).P, V W p⟩
  rw [e1, e2]

end Compile.Batch
