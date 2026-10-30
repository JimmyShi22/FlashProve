-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/TieJoin.lean: THE CHAIN OF THE TOKEN SIDE AGAINST THE COMPILED PROVER's CHAIN, THE
THIRD CASE OF A ROUND: THE JOINING ROUND: the trees over both components, the query to g, the slot's
leaf of the request tree, the climb to the request root, the Fiat-Shamir query (F4) with a search or
without. Definitions, and theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

  plainOf_gT_bind, plainOf_rleafT_bind, plainOf_rnodeL_bind, plainOf_rnodeR_bind   the marked
      evaluations of the joining round as ordinary queries.
  tie_climb   the climb along given sibling digests.
  act_join    the case split of the two sides agrees.
  joinO, joinO2, joinO3, joinO4   the compiled prover's text of the joining round behind its trees,
      cut at its queries: names for this file's proofs alone.
  chain_join  from ChainTie (Johnson/TokenSide/TieChain.lean) for the later rounds to the tie for a
      joining round and the later rounds.

Limits. All is said of the ERASED program (plainOf, Johnson/TokenSide/Erased.lean): tokens are
strings in a store, and the names fbw t k are written back to fb t. Nothing here speaks of these
names, or of the two modes of deferred programming (Rom/Defer.lean): they are the matter of
Johnson/HopSide/, Johnson/GhostSide/ and Compile/DeferRun/.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.TieChain

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
variable {Ω : Type} {μ : PMF Ω} {ℓ : ℕ} {Z : ℕ → Bool → ℕ → ℕ → Prop}

/-! ## The marked evaluations as ordinary queries -/

theorem plainOf_gT_bind {β : Type} (t : Tag) (i : ℕ) (tk : Tok) (rt : List (Dig lam))
    (pl : PlainPart (shapeOf L t) (annOf L t)) (f : Tok → StT lam K L β) (vs : List Bits) :
    plainOf ((gT (K := K) t i tk rt pl).bind f) vs =
      .query (S := typedOracleFamily lam K L) (OracleName.g t) (⟨i, vs.getD tk [], rt, pl⟩ : JoiningRoundQuery lam L t) fun c =>
        plainOf (f vs.length) (vs ++ [List.ofFn (show Dig lam from c)]) := rfl

theorem plainOf_rleafT_bind {β : Type} (c : Tok) (rs : Bits) (f : Tok → StT lam K L β)
    (vs : List Bits) :
    plainOf ((rleafT (K := K) (L := L) c rs).bind f) vs =
      .query (S := typedOracleFamily lam K L) OracleName.rleaf (vs.getD c [] ++ rs : Bits) fun d =>
        plainOf (f vs.length) (vs ++ [List.ofFn (show Dig lam from d)]) := rfl

theorem plainOf_rnodeL_bind {β : Type} (c : Tok) (s : Dig lam) (f : Tok → StT lam K L β)
    (vs : List Bits) :
    plainOf ((rnodeL (K := K) (L := L) c s).bind f) vs =
      .query (S := typedOracleFamily lam K L) OracleName.rnode ((vs.getD c [], List.ofFn s) : Bits × Bits) fun d =>
        plainOf (f vs.length) (vs ++ [List.ofFn (show Dig lam from d)]) := rfl

theorem plainOf_rnodeR_bind {β : Type} (c : Tok) (s : Dig lam) (f : Tok → StT lam K L β)
    (vs : List Bits) :
    plainOf ((rnodeR (K := K) (L := L) s c).bind f) vs =
      .query (S := typedOracleFamily lam K L) OracleName.rnode ((List.ofFn s, vs.getD c []) : Bits × Bits) fun d =>
        plainOf (f vs.length) (vs ++ [List.ofFn (show Dig lam from d)]) := rfl

/-- **The climb.** The coins are handed on unchanged. -/
theorem tie_climb : ∀ (path : List (Dig lam)) (j : ℕ) (c : Tok) (vs : List Bits) (d : Dig lam),
    c < vs.length → vs.getD c [] = List.ofFn d →
    Tie μ (fun (p : (Tok × List Tok) × List Bits) (ω : Ω) => (digOf lam (p.2.getD p.1.1 []), ω))
      (fun p => vs <+: p.2 ∧ p.1.1 < p.2.length ∧
        (∃ d' : Dig lam, p.2.getD p.1.1 [] = List.ofFn d') ∧ (p.1.1 = c ∨ p.1.1 ∈ p.1.2))
      (plainOf (climbT (K := K) (L := L) path j c) vs)
      (fun ω => (climbM (rnodeV (K := K) (L := L)) path j d).bind fun rq => .pure (rq, ω))
  | [], j, c, vs, d, hc, hd => .done ⟨List.prefix_rfl, hc, ⟨d, hd⟩, Or.inl rfl⟩ fun ω => by
      show OComp.pure (d, ω) = OComp.pure (digOf lam (vs.getD c []), ω)
      rw [hd, digOf_ofFn]
  | s :: ss, j, c, vs, d, hc, hd => by
    have step : ∀ u : Dig lam, Tie μ
        (fun (p : (Tok × List Tok) × List Bits) (ω : Ω) => (digOf lam (p.2.getD p.1.1 []), ω))
        (fun p => vs <+: p.2 ∧ p.1.1 < p.2.length ∧
          (∃ d' : Dig lam, p.2.getD p.1.1 [] = List.ofFn d') ∧ (p.1.1 = c ∨ p.1.1 ∈ p.1.2))
        (plainOf ((climbT (K := K) (L := L) ss (j / 2) vs.length).bind fun r =>
          Step.pure (r.1, vs.length :: r.2)) (vs ++ [List.ofFn u]))
        (fun ω => (climbM (rnodeV (K := K) (L := L)) ss (j / 2) u).bind fun rq =>
          .pure (rq, ω)) := fun u => by
      rw [plainOf_bind]
      refine ((tie_climb ss (j / 2) vs.length (vs ++ [List.ofFn u]) u (by simp)
        (getD_length_append vs _ [])).bind (f' := fun y => .pure y) fun p hp => ?_).congr
        fun ω => ?_
      · refine .done ⟨(List.prefix_append _ _).trans hp.1, hp.2.1, hp.2.2.1, Or.inr ?_⟩ fun _ => rfl
        rcases hp.2.2.2 with e | e
        · exact e ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ e
      · rw [Tie.obind_assoc]
        rfl
    by_cases hj : j % 2 = 0
    · have e : climbM (rnodeV (K := K) (L := L)) (s :: ss) j d =
          (rnodeV d s).bind fun u => climbM rnodeV ss (j / 2) u := by
        simp only [climbM, if_pos hj]; rfl
      have eT : climbT (K := K) (L := L) (s :: ss) j c = (rnodeL c s).bind fun u =>
          (climbT ss (j / 2) u).bind fun r => Step.pure (r.1, u :: r.2) := by
        simp only [climbT, if_pos hj]
      rw [e, eT, plainOf_rnodeL_bind, hd]
      exact Tie.query (fun ω u => (climbM (rnodeV (K := K) (L := L)) ss (j / 2)
        (show Dig lam from u)).bind fun rq => .pure (rq, ω)) (fun _ => rfl) fun u => step u
    · have e : climbM (rnodeV (K := K) (L := L)) (s :: ss) j d =
          (rnodeV s d).bind fun u => climbM rnodeV ss (j / 2) u := by
        simp only [climbM, if_neg hj]; rfl
      have eT : climbT (K := K) (L := L) (s :: ss) j c = (rnodeR s c).bind fun u =>
          (climbT ss (j / 2) u).bind fun r => Step.pure (r.1, u :: r.2) := by
        simp only [climbT, if_neg hj]
      rw [e, eT, plainOf_rnodeR_bind, hd]
      exact Tie.query (fun ω u => (climbM (rnodeV (K := K) (L := L)) ss (j / 2)
        (show Dig lam from u)).bind fun rq => .pure (rq, ω)) (fun _ => rfl) fun u => step u

/-- **The two sides' case splits agree**, at the joining round. -/
theorem act_join {cms : List (Dig lam)} {x : Option X} {salt : Tok} {kd : Kind} {ph : PhT}
    {tk : Tok} (h : actT cms x salt kd ph = some (.join tk)) {vs : List Bits}
    (hph : PhOK lam vs ph) :
    actOf cms x (vs.getD salt []) kd (ph.val lam fun u => vs.getD u []) =
      some (.join (vs.getD tk [])) ∧ tk < vs.length := by
  cases kd with
  | lo => cases ph <;> simp [actT] at h
  | sh =>
    cases ph with
    | first => simp [actT] at h
    | shr tk0 c => simp [actT] at h
    | aft tk' c => simp [actT] at h
    | loc tk' =>
      simp only [actT, Option.some.injEq, ActT.join.injEq] at h
      subst h
      exact ⟨rfl, hph⟩

/-! ## The compiled prover's text behind the trees, cut at its queries -/

section Text
variable (t : Tag) (cms : List (Dig lam)) (x : Option X) (cap : ℕ → ℕ) {r : Round} {s : Shape}
  (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (m : r.Msg)
  (k : r.Chal → Strat s Unit) (co : Coins lam L)

def joinO4 (c : Dig lam) (TJ T0 : List (TreeK lam L)) (rq : Dig lam) :
    TypedOracleComputation lam K L (Res (OutP lam L (r :: s))) :=
  (fsO w.gr0 (cap i) w.chal (fun α => askTypedOracle (L := L) (K := K) (OracleName.fb t)
      (⟨i, .f4 cms (List.ofFn rq), T0.map TreeK.root, embP (.inl (.inl α))⟩ :
        FbIn lam L t)) (a.plain m.2).1).bind <| onFs i fun q =>
    (chainO t cms x co cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
      (.shr (List.ofFn q.2.2) c) (k (w.chal q.2.1))).bind fun r =>
    .pure (r.map (consP (w.chal q.2.1)
      ((m.1, a.plain.symm (q.1, (a.plain m.2).2)), T0, TJ) (some rq)))

def joinO3 (c : Dig lam) (TJ T0 : List (TreeK lam L)) (d : Dig lam) :
    TypedOracleComputation lam K L (Res (OutP lam L (r :: s))) :=
  (climbM (rnodeV (K := K) (L := L)) co.path co.slot d).bind
    (joinO4 t cms x cap a A w W embS embP i m k co c TJ T0)

def joinO2 (TJ T0 : List (TreeK lam L)) (c : Dig lam) : TypedOracleComputation lam K L (Res (OutP lam L (r :: s))) :=
  (askTypedOracle (L := L) (K := K) OracleName.rleaf (List.ofFn c ++ co.rsalt)).bind
    (joinO3 t cms x cap a A w W embS embP i m k co c TJ T0)

def joinO (ρ : Bits) (TJ T0 : List (TreeK lam L)) : TypedOracleComputation lam K L (Res (OutP lam L (r :: s))) :=
  (askTypedOracle (L := L) (K := K) (OracleName.g t)
    (⟨i, ρ, TJ.map TreeK.root, embP (.inl (.inr (a.plain m.2).2))⟩ : JoiningRoundQuery lam L t)).bind
    (joinO2 t cms x cap a A w W embS embP i m k co TJ T0)

end Text

/-- **The joining round.** -/
theorem chain_join (ll : LeafLens Ω μ ℓ Z) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (pre : ℕ → Bool → Bits → Bits) (salt : Tok) (cd : CoinsD lam L) (cap : ℕ → ℕ) {r : Round}
    {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
    (IH : ChainTie ll t cms x pre salt cd cap s A W)
    (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (m : r.Msg)
    (k : r.Chal → Strat s Unit) (vs : List Bits) (hs : salt < vs.length) (hph : PhOK lam vs ph)
    (hc : Covers Z (r :: s) (a, A) (w, W) i) {tk : Tok}
    (h : actT cms (x.map L.early) salt a.kind ph = some (.join tk)) :
    Tie μ
      (fun (p : Res (OutT lam L (r :: s)) × List Bits) ω =>
        p.1.map fun z => outW ll (fun i b => pre i b (vs.getD salt [])) p.2 i z ω)
      (fun p => vs <+: p.2 ∧ ∀ z, p.1 = .ok z → OutOK ℓ (r :: s) (a, A) (w, W) z p.2)
      (plainOf (chainT t cms x ℓ pre salt cd cap (r :: s) (a, A) (w, W) embS embP i ph (m, k)) vs)
      (fun ω => (chainO t cms x (coOf ll (vs.getD salt []) cd pre ω) cap (r :: s) (a, A) (w, W) embS
        embP i (ph.val lam fun u => vs.getD u []) (m, k)).bind
        fun r => .pure (r.map fun z => (z, ω))) := by
  obtain ⟨hO, htk⟩ := act_join h hph
  have eT : chainT t cms x ℓ pre salt cd cap (r :: s) (a, A) (w, W) embS embP i ph (m, k) =
      (treesT (K := K) ℓ [salt] (fun vs => pre i true (vs.headD [])) cd.pad w.posAtJ
        (fun p => embS (.inl p)) m.1 0 w.depthJ).bind fun TJ =>
      (treesT (K := K) ℓ [salt] (fun vs => pre i false (vs.headD [])) cd.pad w.posAt0
        (fun p => embS (.inl p)) m.1 0 w.depth0).bind fun T0 =>
      (gT (K := K) t i tk (TJ.map TreeT.root) (embP (.inl (.inr (a.plain m.2).2)))).bind fun c =>
      (rleafT (K := K) (L := L) c cd.rsalt).bind fun d =>
      (climbT (K := K) (L := L) cd.path cd.slot d).bind fun rq =>
      (fsT w.gr0 (cap i) w.chal (fun n α => fbT (K := K) t n i rq.1 []
          (fun _ v => .f4 cms v) (fun _ => f4_inj cms)
          (T0.map TreeT.root) (embP (.inl (.inl α)))) (a.plain m.2).1).bind <| onFsT i fun q =>
        (chainT t cms x ℓ pre salt cd cap s A W (fun p => embS (.inr p))
          (fun z => embP (.inr z)) (i + 1) (.shr q.tl c) (k (w.chal q.bl))).bind fun r =>
        .pure (r.map (consT (w.chal q.bl)
          ((m.1, a.plain.symm (q.pl, (a.plain m.2).2)), T0, TJ) (some rq.1)
          (c :: d :: (rq.2 ++ q.tl :: q.dead)))) := by
    rw [chainT, h]
  have eO : ∀ ω, chainO t cms x (coOf ll (vs.getD salt []) cd pre ω) cap (r :: s) (a, A) (w, W) embS
      embP i (ph.val lam fun u => vs.getD u []) (m, k) =
      (treesO (K := K) cd.pad (fun k j => pre i true (vs.getD salt []) ++ ll.get ω i true k j)
        w.posAtJ (fun p => embS (.inl p)) m.1 0 w.depthJ).bind fun TJ =>
      (treesO (K := K) cd.pad (fun k j => pre i false (vs.getD salt []) ++ ll.get ω i false k j)
        w.posAt0 (fun p => embS (.inl p)) m.1 0 w.depth0).bind fun T0 =>
      joinO t cms x cap a A w W embS embP i m k (coOf ll (vs.getD salt []) cd pre ω)
        (vs.getD tk []) TJ T0 := by
    intro ω
    rw [chainO]
    show (match actOf cms (x.map L.early) (vs.getD salt []) a.kind
      (ph.val lam fun u => vs.getD u []) with
      | some (.one h true next) => _
      | some (.one h false next) => _
      | some (.join ρ) => _
      | none => _) = _
    rw [hO]
    rfl
  rw [eT, plainOf_bind]
  -- the trees over the slot's component
  refine (Tie.bindW (tie_trees ll [salt] (fun vs => pre i true (vs.headD []))
    (pre i true (vs.getD salt [])) i true cd.pad w.posAtJ (fun p => embS (.inl p)) m.1 w.depthJ 0 vs
    hc.1 (fun u hu => by rw [List.mem_singleton.mp hu]; exact hs) rfl)
    (f' := fun ω TJ =>
      ((treesO (K := K) cd.pad (fun k j => pre i false (vs.getD salt []) ++ ll.get ω i false k j)
        w.posAt0 (fun p => embS (.inl p)) m.1 0 w.depth0).bind fun T0 =>
      joinO t cms x cap a A w W embS embP i m k (coOf ll (vs.getD salt []) cd pre ω)
        (vs.getD tk []) TJ T0).bind fun r => .pure (r.map fun z => (z, ω)))
    fun p hp => ?_).congr fun ω => ?_
  swap
  · rw [eO, Tie.obind_assoc]
  obtain ⟨TJ, vs₁⟩ := p
  have hp1 : vs <+: vs₁ := hp.1
  rw [plainOf_bind]
  -- the trees over the shared component
  refine (Tie.bindW (tie_trees ll [salt] (fun vs => pre i false (vs.headD []))
    (pre i false (vs.getD salt [])) i false cd.pad w.posAt0 (fun p => embS (.inl p)) m.1 w.depth0 0
    vs₁ hc.2.1
    (fun u hu => by
      rw [List.mem_singleton.mp hu]
      exact Nat.lt_of_lt_of_le hs hp1.length_le)
    (by
      show pre i false (vs₁.getD salt []) = _
      rw [getD_of_prefix hp1 hs]))
    (f' := fun ω T0 =>
      (joinO t cms x cap a A w W embS embP i m k
        (coOf ll (vs.getD salt []) cd pre (patchTs ll i true 0 TJ vs₁ ω)) (vs.getD tk [])
        (mkKs ll (pre i true (vs.getD salt [])) i true (patchTs ll i true 0 TJ vs₁ ω) 0 TJ) T0).bind
        fun r => .pure (r.map fun z => (z, patchTs ll i true 0 TJ vs₁ ω)))
    fun p2 hp2 => ?_).congr fun ω => ?_
  swap
  · beta_reduce
    have eF : (fun k j => pre i false (vs.getD salt []) ++
        ll.get (patchTs ll i true 0 TJ vs₁ ω) i false k j) =
        fun k j => pre i false (vs.getD salt []) ++ ll.get ω i false k j :=
      funext fun k' => funext fun j => by
        rw [get_patchTs_ne ll i true vs₁ i false k' j (fun e => Bool.noConfusion e.2)]
    rw [eF, Tie.obind_assoc]
  obtain ⟨T0, vs₂⟩ := p2
  have hp2' : vs₁ <+: vs₂ := hp2.1
  have h02 : vs <+: vs₂ := hp1.trans hp2'
  -- the query to g
  rw [plainOf_gT_bind, getD_of_prefix h02 htk]
  refine Tie.query (fun ω c =>
    (joinO2 t cms x cap a A w W embS embP i m k
      (coOf ll (vs.getD salt []) cd pre
        (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω)))
      (mkKs ll (pre i true (vs.getD salt [])) i true
        (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω)) 0 TJ)
      (mkKs ll (pre i false (vs.getD salt [])) i false (patchTs ll i false 0 T0 vs₂ ω) 0 T0)
      (show Dig lam from c)).bind
      fun r => .pure (r.map fun z =>
        (z, patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω))))
    (fun ω => by
      beta_reduce
      unfold joinO
      rw [map_root_mkKs]
      rfl) fun c => ?_
  -- the slot's leaf of the request tree
  rw [plainOf_rleafT_bind, getD_length_append]
  refine Tie.query (fun ω d =>
    (joinO3 t cms x cap a A w W embS embP i m k
      (coOf ll (vs.getD salt []) cd pre
        (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω))) (show Dig lam from c)
      (mkKs ll (pre i true (vs.getD salt [])) i true
        (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω)) 0 TJ)
      (mkKs ll (pre i false (vs.getD salt [])) i false (patchTs ll i false 0 T0 vs₂ ω) 0 T0)
      (show Dig lam from d)).bind
      fun r => .pure (r.map fun z =>
        (z, patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω))))
    (fun _ => rfl) fun d => ?_
  -- the climb
  rw [plainOf_bind]
  refine (Tie.bindW (tie_climb (μ := μ) cd.path cd.slot (vs₂ ++ [List.ofFn (show Dig lam from
      c)]).length
    (vs₂ ++ [List.ofFn (show Dig lam from c)] ++ [List.ofFn (show Dig lam from d)]) d (by simp)
    (getD_length_append _ _ []))
    (f' := fun ω rq =>
      (joinO4 t cms x cap a A w W embS embP i m k
        (coOf ll (vs.getD salt []) cd pre
          (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω))) (show Dig lam from c)
        (mkKs ll (pre i true (vs.getD salt [])) i true
          (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω)) 0 TJ)
        (mkKs ll (pre i false (vs.getD salt [])) i false (patchTs ll i false 0 T0 vs₂ ω) 0 T0)
        rq).bind
        fun r => .pure (r.map fun z =>
          (z, patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω))))
    fun p5 hp5 => ?_).congr fun ω => ?_
  swap
  · beta_reduce
    unfold joinO3
    rw [Tie.obind_assoc]
    rfl
  obtain ⟨⟨rqT, rts⟩, vs₅⟩ := p5
  obtain ⟨hp5a, hrq, ⟨dq, hdq⟩, hmem⟩ := hp5
  have h25 : vs₂ <+: vs₅ := by
    refine List.IsPrefix.trans ?_ hp5a
    rw [List.append_assoc]
    exact List.prefix_append _ _
  have hcT : vs₅.getD vs₂.length [] = List.ofFn (show Dig lam from c) := by
    have h3 : vs₂ ++ List.ofFn (show Dig lam from c) :: [List.ofFn (show Dig lam from d)] <+:
        vs₅ := by
      rwa [List.append_assoc] at hp5a
    rw [getD_of_prefix h3 (by simp), getD_length_append]
  have hcL : vs₂.length < vs₅.length := by
    have := hp5a.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  -- the Fiat-Shamir query (F4)
  rw [plainOf_bind]
  refine (Tie.bindW (tie_fs (μ := μ) w.gr0 (cap i) w.chal t i rqT [] (fun _ v => .f4 cms v)
    (fun _ => f4_inj cms) (T0.map TreeT.root) (fun α => embP (.inl (.inl α))) (a.plain m.2).1
    (.f4 cms (List.ofFn (digOf lam (vs₅.getD rqT [])))) vs₅ hrq
    (fun u hu => absurd hu (List.not_mem_nil)) (by
      show Head.f4 cms (vs₅.getD rqT []) = _
      rw [hdq, digOf_ofFn]))
    (f' := fun ω o => (onFs i (fun q =>
        (chainO t cms x (coOf ll (vs.getD salt []) cd pre
          (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω))) cap s A W
          (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
          (.shr (List.ofFn q.2.2) (show Dig lam from c)) (k (w.chal q.2.1))).bind
          fun r => .pure (r.map (consP (w.chal q.2.1)
            ((m.1, a.plain.symm (q.1, (a.plain m.2).2)),
              mkKs ll (pre i false (vs.getD salt [])) i false (patchTs ll i false 0 T0 vs₂ ω) 0 T0,
              mkKs ll (pre i true (vs.getD salt [])) i true
                (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω)) 0 TJ)
            (some (digOf lam (vs₅.getD rqT [])))))) o).bind
        fun r => .pure (r.map fun z =>
          (z, patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω))))
    fun p6 hp6 => ?_).congr fun ω => ?_
  swap
  · beta_reduce
    unfold joinO4
    rw [map_root_mkKs, Tie.obind_assoc]
  obtain ⟨oq, vs₆⟩ := p6
  have hp6' : vs₅ <+: vs₆ := hp6.1
  have h06 : vs <+: vs₆ := (h02.trans h25).trans hp6'
  cases oq with
  | none => exact .done ⟨h06, fun z hz => by cases hz⟩ fun _ => rfl
  | some q =>
    obtain ⟨hq1, d', hq2⟩ := hp6.2 q rfl
    have hsv : vs₆.getD salt [] = vs.getD salt [] := getD_of_prefix h06 hs
    have hc6 : vs₆.getD vs₂.length [] = List.ofFn (show Dig lam from c) := by
      rw [getD_of_prefix hp6' hcL, hcT]
    have IH' := IH (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) (.shr q.tl vs₂.length)
      (k (w.chal q.bl)) vs₆ (Nat.lt_of_lt_of_le hs h06.length_le)
      ⟨hq1, Nat.lt_of_lt_of_le hcL hp6'.length_le, _, hc6⟩ hc.2.2
    have ePh : (PhT.shr q.tl vs₂.length).val lam (fun u => vs₆.getD u []) =
        Phase.shr (List.ofFn d') (show Dig lam from c) := by
      show Phase.shr (vs₆.getD q.tl []) (digOf lam (vs₆.getD vs₂.length [])) = _
      rw [hq2, hc6, digOf_ofFn]
    rw [hsv, ePh] at IH'
    show Tie μ _ _ (plainOf ((chainT t cms x ℓ pre salt cd cap s A W (fun p => embS (.inr p))
      (fun z => embP (.inr z)) (i + 1) (.shr q.tl vs₂.length) (k (w.chal q.bl))).bind fun r =>
      Step.pure (r.map (consT (w.chal q.bl)
        ((m.1, a.plain.symm (q.pl, (a.plain m.2).2)), T0, TJ) (some rqT)
        (vs₂.length :: (vs₂ ++ [List.ofFn (show Dig lam from c)]).length ::
          (rts ++ q.tl :: q.dead))))) vs₆) _
    rw [plainOf_bind]
    refine (IH'.bind (f' := fun r' => .pure (r'.map fun y =>
      (consP (w.chal q.bl) ((m.1, a.plain.symm (q.pl, (a.plain m.2).2)),
        mkKs ll (pre i false (vs.getD salt [])) i false (patchTs ll i false 0 T0 vs₂ y.2) 0 T0,
        mkKs ll (pre i true (vs.getD salt [])) i true
          (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ y.2)) 0 TJ)
        (some (digOf lam (vs₅.getD rqT []))) y.1,
        patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ y.2)))) fun p7 hp7 => ?_).congr
      fun ω => ?_
    swap
    · show ((chainO t cms x (coOf ll (vs.getD salt []) cd pre
          (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω))) cap s
          A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
          (.shr (List.ofFn (digOf lam (vs₆.getD q.tl []))) (show Dig lam from c))
          (k (w.chal q.bl))).bind _).bind _ = _
      rw [hq2, digOf_ofFn, Tie.obind_assoc, Tie.obind_assoc]
      have e1 : chainO t cms x (coOf ll (vs.getD salt []) cd pre
          (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂ ω))) cap
          s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
          (.shr (List.ofFn d') (show Dig lam from c)) (k (w.chal q.bl)) =
          chainO t cms x (coOf ll (vs.getD salt []) cd pre ω) cap s A W (fun p => embS (.inr p))
            (fun z => embP (.inr z)) (i + 1) (.shr (List.ofFn d') (show Dig lam from c))
            (k (w.chal q.bl)) :=
        chainO_congr t cms x _ _ _ _ _ _ _ cap s A W _ _ (i + 1) _ _ fun i' hi =>
          funext fun b => funext fun k' => funext fun j => by
            rw [get_patchTs_ne ll i true vs₁ i' b k' j (fun e => by omega),
              get_patchTs_ne ll i false vs₂ i' b k' j (fun e => by omega)]
      rw [e1]
      refine congrArg _ (funext fun r3 => ?_)
      cases r3 <;> rfl
    · obtain ⟨r7, vs₇⟩ := p7
      have hp7' : vs₆ <+: vs₇ := hp7.1
      cases r7 with
      | noFormat => exact .done ⟨h06.trans hp7', fun z hz => by cases hz⟩ fun _ => rfl
      | ranOut j => exact .done ⟨h06.trans hp7', fun z hz => by cases hz⟩ fun _ => rfl
      | ok z =>
        refine .done ⟨h06.trans hp7', fun z' hz' => ?_⟩ fun ω => ?_
        · cases hz'
          refine ⟨⟨Or.inr (hp2.2.mono ((h25.trans hp6').trans hp7')),
            Or.inr (hp.2.mono (((hp2'.trans h25).trans hp6').trans hp7')), (hp7.2 z rfl).1⟩,
            fun u hu => ?_⟩
          obtain rfl : rqT = u := Option.some.inj hu
          refine List.mem_append_left _ (List.mem_cons_of_mem _ ?_)
          rcases hmem with e | e
          · exact e ▸ List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ e)
        have esJ : ∀ ω', patchTs ll i true 0 TJ vs₇ ω' = patchTs ll i true 0 TJ vs₁ ω' := fun ω' =>
          patchTs_store ll i true (((hp2'.trans h25).trans hp6').trans hp7') TJ 0 ω' hp.2.lt
        have es0 : ∀ ω', patchTs ll i false 0 T0 vs₇ ω' = patchTs ll i false 0 T0 vs₂ ω' :=
          fun ω' => patchTs_store ll i false ((h25.trans hp6').trans hp7') T0 0 ω' hp2.2.lt
        have erq : vs₇.getD rqT [] = vs₅.getD rqT [] := getD_of_prefix (hp6'.trans hp7') hrq
        show OComp.pure (Res.ok _) = OComp.pure (Res.ok
          ((((w.chal q.bl, z.rho),
            (((m.1, a.plain.symm (q.pl, (a.plain m.2).2)),
              mkKs ll (pre i false (vs.getD salt [])) i false
                (patchTs ll i true 0 TJ vs₇ (patchTs ll i false 0 T0 vs₇
                  (actK ll s (i + 1) z.kept vs₇ ω))) 0 T0,
              mkKs ll (pre i true (vs.getD salt [])) i true
                (patchTs ll i true 0 TJ vs₇ (patchTs ll i false 0 T0 vs₇
                  (actK ll s (i + 1) z.kept vs₇ ω))) 0 TJ),
            keptW ll (fun i b => pre i b (vs.getD salt []))
              (patchTs ll i true 0 TJ vs₇ (patchTs ll i false 0 T0 vs₇
                (actK ll s (i + 1) z.kept vs₇ ω))) s (i + 1) z.kept),
            z.ph.val lam (fun u => vs₇.getD u []),
            some (digOf lam (vs₇.getD rqT []))) : OutP lam L (r :: s)),
            patchTs ll i true 0 TJ vs₇ (patchTs ll i false 0 T0 vs₇
              (actK ll s (i + 1) z.kept vs₇ ω))))
        rw [esJ, es0, erq,
          keptW_congr ll _ (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂
            (actK ll s (i + 1) z.kept vs₇ ω)))
            (actK ll s (i + 1) z.kept vs₇ ω) s (i + 1) z.kept fun i' b k' j hi => by
              rw [get_patchTs_ne ll i true vs₁ i' b k' j (fun e => by omega),
                get_patchTs_ne ll i false vs₂ i' b k' j (fun e => by omega)],
          mkKs_congr ll (pre i false (vs.getD salt [])) i false
            (patchTs ll i true 0 TJ vs₁ (patchTs ll i false 0 T0 vs₂
              (actK ll s (i + 1) z.kept vs₇ ω)))
            (patchTs ll i false 0 T0 vs₂ (actK ll s (i + 1) z.kept vs₇ ω)) T0 0 fun k' j _ =>
              get_patchTs_ne ll i true vs₁ i false k' j (fun e => Bool.noConfusion e.2) TJ 0 _]
        rfl

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.tie_climb
#print axioms OnBytes.TokenSide.chain_join
