-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/TieFinish.lean: THE PROOF STRING OF THE TOKEN SIDE IS THE COMPILED PROVER's: the
compiled prover's finish (OnBytes/Prover/Defs.lean) gives one string at what its own chain has
yielded (outW, Johnson/TokenSide/TieChain.lean: trees that hold a salt at every leaf number) and at
what the token side lays before it (outK, Johnson/TokenSide/Finish.lean: trees that hold the
revealed values alone). Definitions, and theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

Why it holds: finish reads of a tree its levels, and the salts of the leaves at which a read
position stands. Such a leaf is a leaf of the tree (the wire's laws), its bits were drawn, so the
coins hold its token's value there (Looks), and its token was revealed.

The revealed values are a letter val here. What is asked of it: it gives the store's value at the
request root's token and at the tokens of the leaves of read positions, in the prover's own trees
and in the external ones. The first salt's value is one letter on both sides. So the file does not
hang on the order, or on the number, of a program's reveals.

Main names (namespace OnBytes.TokenSide).
  Looks, looks_actK   at each kept tree's leaves the coins hold the tokens' values; so it is at the
      coins with all drawn bits laid in.
  get_patchTs_in      the same for the trees of one component.
  rootsK_keptW, trK_keptW, trK_keptK   roots and transcript: read off the token side's trees and
      messages alike.
  opensK_eq, extK_eq  the openings.
  finish_eq           THE STRING.

Limits. One slot. The wire's laws (wq.OKG), ExtTie and Covers are premises; no member is shown here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.SpecSame

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
variable {Ω : Type} {μ : PMF Ω} {ℓ : ℕ} {Z : ℕ → Bool → ℕ → ℕ → Prop}

/-! ## Lists -/

theorem forall₂_get {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ (n : ℕ) (b : β), l₂[n]? = some b → ∃ a, l₁[n]? = some a ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons (a := a) h1 _, 0, b, h => by
    obtain rfl := by simpa using h
    exact ⟨a, rfl, h1⟩
  | _, _, .cons _ h2, n + 1, b, h => by
    obtain ⟨a, ha, hr⟩ := forall₂_get h2 n b (by simpa using h)
    exact ⟨a, by simpa using ha, hr⟩

theorem getElem?_mkKs (ll : LeafLens Ω μ ℓ Z) (st : Bits) (i : ℕ) (b : Bool) (ωa : Ω) :
    ∀ (Ts : List (TreeT lam L)) (k n : ℕ),
      (mkKs ll st i b ωa k Ts)[n]? = (Ts[n]?).map (mkK ll st i b (k + n) ωa)
  | [], _, _ => by simp [mkKs]
  | _ :: _, _, 0 => rfl
  | T :: Ts, k, n + 1 => by
    show (mkKs ll st i b ωa (k + 1) Ts)[n]? = (Ts[n]?).map _
    rw [getElem?_mkKs ll st i b ωa Ts (k + 1) n, show k + 1 + n = k + (n + 1) by omega]

/-! ## What the coins hold at the kept trees' leaves -/

theorem get_patchTs_in (ll : LeafLens Ω μ ℓ Z) (i : ℕ) (b : Bool) (vs : List Bits) :
    ∀ (ds : List ℕ) (Ts : List (TreeT lam L)) (k : ℕ) (ω : Ω), TreesOK ℓ ds vs Ts →
      (∀ n d, ds[n]? = some d → ∀ j, j < 2 ^ d → Z i b (k + n) j) →
      ∀ (n : ℕ) (T : TreeT lam L) (j : ℕ) (a : Tok × Tok), Ts[n]? = some T → T.tok[j]? = some a →
        ll.get (patchTs ll i b k Ts vs ω) i b (k + n) j = vs.getD a.1 []
  | _, _, _, _, .nil, _, _, _, _, _, h, _ => by simp at h
  | d :: _, T0 :: Ts, k, ω, .cons h1 _, hz, 0, T, j, a, hT, ha => by
    obtain rfl : T0 = T := by simpa using hT
    exact get_patchT_in ll i b k d vs _ T0 h1 (fun j' hj' => hz 0 d rfl j' hj') j a ha
  | _ :: ds, T0 :: Ts, k, ω, .cons _ h2, hz, n + 1, T, j, a, hT, ha => by
    show ll.get (patchL ll i b k _ _ vs (patchTs ll i b (k + 1) Ts vs ω)) i b (k + (n + 1)) j = _
    rw [get_patchL_ne ll i b k vs _ i b (k + (n + 1)) j (fun e => by omega),
      show k + (n + 1) = k + 1 + n by omega]
    exact get_patchTs_in ll i b vs ds Ts (k + 1) ω h2 (fun n' d' hn' j' hj' => by
      have := hz (n' + 1) d' (by simpa using hn') j' hj'
      rwa [show k + (n' + 1) = k + 1 + n' by omega] at this) n T j a (by simpa using hT) ha

/-- At each leaf of each kept tree the coins ωa hold the value of the leaf's token. -/
def Looks (ll : LeafLens Ω μ ℓ Z) (ωa : Ω) (vs : List Bits) :
    (s : Shape) → ℕ → KeptT lam L s → Prop
  | [], _, _ => True
  | _ :: s, i, (kp, ks) =>
      (∀ n T j a, kp.2.1[n]? = some T → T.tok[j]? = some a →
        ll.get ωa i false n j = vs.getD a.1 []) ∧
      (∀ n T j a, kp.2.2[n]? = some T → T.tok[j]? = some a →
        ll.get ωa i true n j = vs.getD a.1 []) ∧ Looks ll ωa vs s (i + 1) ks

theorem Looks.congr (ll : LeafLens Ω μ ℓ Z) (ωa ωb : Ω) (vs : List Bits) :
    ∀ (s : Shape) (i : ℕ) (ks : KeptT lam L s),
      (∀ i' b k j, i ≤ i' → ll.get ωa i' b k j = ll.get ωb i' b k j) →
      Looks ll ωb vs s i ks → Looks ll ωa vs s i ks
  | [], _, _, _, _ => trivial
  | _ :: s, i, (_, ks), h, hl =>
    ⟨fun n T j a h1 h2 => by rw [h i false n j (Nat.le_refl i)]; exact hl.1 n T j a h1 h2,
      fun n T j a h1 h2 => by rw [h i true n j (Nat.le_refl i)]; exact hl.2.1 n T j a h1 h2,
      Looks.congr ll ωa ωb vs s (i + 1) ks (fun i' b k j hi => h i' b k j (Nat.le_of_succ_le hi))
        hl.2.2⟩

/-- **So it is at the coins with all drawn bits laid in.** -/
theorem looks_actK (ll : LeafLens Ω μ ℓ Z) (vs : List Bits) (ω : Ω) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ) (ks : KeptT lam L s),
      KeptOK ℓ s A W ks vs → Covers Z s A W i → Looks ll (actK ll s i ks vs ω) vs s i ks
  | [], _, _, _, _, _, _ => trivial
  | _ :: s, (_, A), (w, W), i, (kp, ks), hk, hc => by
    refine ⟨fun n T j a h1 h2 => ?_, fun n T j a h1 h2 => ?_, ?_⟩
    · show ll.get (patchTs ll i true 0 kp.2.2 vs (patchTs ll i false 0 kp.2.1 vs _)) i false n j = _
      rw [get_patchTs_ne ll i true vs i false n j (fun e => Bool.noConfusion e.2)]
      rcases hk.1 with e | e
      · rw [e] at h1
        simp at h1
      · have := get_patchTs_in ll i false vs w.depth0 kp.2.1 0 (actK ll s (i + 1) ks vs ω) e hc.2.1
          n T j a h1 h2
        rwa [Nat.zero_add] at this
    · show ll.get (patchTs ll i true 0 kp.2.2 vs (patchTs ll i false 0 kp.2.1 vs _)) i true n j = _
      rcases hk.2.1 with e | e
      · rw [e] at h1
        simp at h1
      · have := get_patchTs_in ll i true vs w.depthJ kp.2.2 0
          (patchTs ll i false 0 kp.2.1 vs (actK ll s (i + 1) ks vs ω)) e hc.1 n T j a h1 h2
        rwa [Nat.zero_add] at this
    · refine Looks.congr ll _ (actK ll s (i + 1) ks vs ω) vs s (i + 1) ks (fun i' b k j hi => ?_)
        (looks_actK ll vs ω s A W (i + 1) ks hk.2.2 hc.2.2)
      show ll.get (patchTs ll i true 0 kp.2.2 vs (patchTs ll i false 0 kp.2.1 vs _)) i' b k j = _
      rw [get_patchTs_ne ll i true vs i' b k j (fun e => by omega),
        get_patchTs_ne ll i false vs i' b k j (fun e => by omega)]

/-! ## Roots and transcript -/

theorem map_root_toK (val : Tok → Bits) (pre : Bits) (Ts : List (TreeT lam L)) :
    (Ts.map (TreeT.toK val pre)).map TreeK.root = Ts.map TreeT.root := by
  rw [List.map_map]
  rfl

theorem rootsK_keptW (ll : LeafLens Ω μ ℓ Z) (st : ℕ → Bool → Bits) (ωa : Ω) (val : Tok → Bits) :
    ∀ (s : Shape) (i : ℕ) (ks : KeptT lam L s),
      rootsK s (keptW ll st ωa s i ks) = rootsK s (keptK val st s i ks)
  | [], _, _ => rfl
  | _ :: s, i, (kp, ks) => by
    show (mkKs ll (st i true) i true ωa 0 kp.2.2).map TreeK.root ++
        ((mkKs ll (st i false) i false ωa 0 kp.2.1).map TreeK.root ++
          rootsK s (keptW ll st ωa s (i + 1) ks)) =
      (kp.2.2.map (TreeT.toK val (st i true))).map TreeK.root ++
        ((kp.2.1.map (TreeT.toK val (st i false))).map TreeK.root ++
          rootsK s (keptK val st s (i + 1) ks))
    rw [map_root_mkKs, map_root_mkKs, map_root_toK, map_root_toK, rootsK_keptW ll st ωa val s (i +
        1) ks]

theorem trK_keptW (ll : LeafLens Ω μ ℓ Z) (st : ℕ → Bool → Bits) (ωa : Ω) :
    ∀ (s : Shape) (i : ℕ) (ks : KeptT lam L s) (ρ : Rho s),
      trK s (keptW ll st ωa s i ks) ρ = trT s ks ρ
  | [], _, _, _ => rfl
  | _ :: s, i, (kp, ks), (c, ρ) =>
    congrArg (fun τ => (kp.1, c, τ)) (trK_keptW ll st ωa s (i + 1) ks ρ)

theorem trK_keptK (val : Tok → Bits) (st : ℕ → Bool → Bits) :
    ∀ (s : Shape) (i : ℕ) (ks : KeptT lam L s) (ρ : Rho s),
      trK s (keptK val st s i ks) ρ = trT s ks ρ
  | [], _, _, _ => rfl
  | _ :: s, i, (kp, ks), (c, ρ) => congrArg (fun τ => (kp.1, c, τ)) (trK_keptK val st s (i + 1) ks
      ρ)

/-! ## The openings -/

/-- One tree: the opening of a leaf whose token's value the coins hold, and val gives. -/
theorem opening_eq (ll : LeafLens Ω μ ℓ Z) (st : Bits) (i : ℕ) (b : Bool) (n : ℕ) (ωa : Ω)
    (val : Tok → Bits) (vs : List Bits) (T : TreeT lam L) (j : ℕ) (a : Tok × Tok)
    (ha : T.tok[j]? = some a) (hg : ll.get ωa i b n j = vs.getD a.1 [])
    (hv : val a.1 = vs.getD a.1 []) {σ : Type} (y : σ) :
    (mkK ll st i b n ωa T).opening j y = (T.toK val st).opening j y := by
  show (⟨y, st ++ ll.get ωa i b n j, pathOf T.lv j⟩ : Opening lam σ) =
    ⟨y, (match T.tok[j]? with
      | some a => st ++ val a.1
      | none => []), pathOf T.lv j⟩
  rw [ha]
  show (⟨y, st ++ ll.get ωa i b n j, pathOf T.lv j⟩ : Opening lam σ) =
    ⟨y, st ++ val a.1, pathOf T.lv j⟩
  rw [hg, hv]

theorem opensK_eq (ll : LeafLens Ω μ ℓ Z) (st : ℕ → Bool → Bits) (ωa : Ω) (val : Tok → Bits)
    (vs : List Bits) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ) (ks : KeptT lam L s)
      (rd : OPos s → Bool), RoundsQueryLayout.OKG s A W → KeptOK ℓ s A W ks vs → Looks ll ωa vs s i ks →
      (∀ p, rd p = true → ∀ u ∈ openT s A W ks p, val u = vs.getD u []) →
      ∀ p, Prover.opensK s A W (keptW ll st ωa s i ks) rd p = Prover.opensK s A W (keptK val st s i
          ks) rd p
  | [], _, _, _, _, _, _, _, _, _, p => nomatch p
  | r :: s, (a, A), (w, W), i, (kp, ks), rd, hW, hk, hl, hv, .inr q =>
    opensK_eq ll st ωa val vs s A W (i + 1) ks (fun p => rd (.inr p)) hW.2 hk.2.2 hl.2.2
      (fun p hp u hu => hv (.inr p) hp u hu) q
  | r :: s, (a, A), (w, W), i, (kp, ks), rd, hW, hk, hl, hv, .inl p => by
    show (if rd (.inl p) then
        ((if a.own p then mkKs ll (st i true) i true ωa 0 kp.2.2
          else mkKs ll (st i false) i false ωa 0 kp.2.1)[w.tree p]?).map fun T =>
          T.opening (w.place p) (r.rd kp.1.1 p)
      else none) =
      (if rd (.inl p) then
        ((if a.own p then kp.2.2.map (TreeT.toK val (st i true))
          else kp.2.1.map (TreeT.toK val (st i false)))[w.tree p]?).map fun T =>
          T.opening (w.place p) (r.rd kp.1.1 p)
      else none)
    by_cases hr : rd (.inl p) = true
    swap
    · rw [if_neg hr, if_neg hr]
    rw [if_pos hr, if_pos hr]
    have hv' := hv (.inl p) hr
    cases hb : a.own p with
    | true =>
      simp only [if_true]
      rw [getElem?_mkKs, List.getElem?_map]
      cases hT : kp.2.2[w.tree p]? with
      | none => rfl
      | some T =>
        have hts : TreesOK ℓ w.depthJ vs kp.2.2 := by
          rcases hk.2.1 with e | e
          · rw [e] at hT
            simp at hT
          · exact e
        obtain ⟨d, hd, hok⟩ := forall₂_get hts _ _ hT
        obtain ⟨d', hd', hlt⟩ := hW.1.place_ltJ p hb
        obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
        have hj : w.place p < T.tok.length := by rw [hok.1]; exact hlt
        have ha : T.tok[w.place p]? = some T.tok[w.place p] := List.getElem?_eq_getElem hj
        refine congrArg some (opening_eq ll (st i true) i true (0 + w.tree p) ωa val vs T _ _ ha ?_
            ?_ _)
        · rw [Nat.zero_add]
          exact hl.2.1 _ T _ _ hT ha
        · refine hv' _ ?_
          show _ ∈ (match (if a.own p then kp.2.2 else kp.2.1)[w.tree p]? with
            | some T => T.toksAt (w.place p)
            | none => [])
          rw [hb]
          simp only [if_true, hT, TreeT.toksAt, ha]
          exact List.mem_cons_self ..
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [getElem?_mkKs, List.getElem?_map]
      cases hT : kp.2.1[w.tree p]? with
      | none => rfl
      | some T =>
        have hts : TreesOK ℓ w.depth0 vs kp.2.1 := by
          rcases hk.1 with e | e
          · rw [e] at hT
            simp at hT
          · exact e
        obtain ⟨d, hd, hok⟩ := forall₂_get hts _ _ hT
        obtain ⟨d', hd', hlt⟩ := hW.1.place_lt0 p hb
        obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
        have hj : w.place p < T.tok.length := by rw [hok.1]; exact hlt
        have ha : T.tok[w.place p]? = some T.tok[w.place p] := List.getElem?_eq_getElem hj
        refine congrArg some (opening_eq ll (st i false) i false (0 + w.tree p) ωa val vs T _ _ ha
            ?_ ?_ _)
        · rw [Nat.zero_add]
          exact hl.1 _ T _ _ hT ha
        · refine hv' _ ?_
          show _ ∈ (match (if a.own p then kp.2.2 else kp.2.1)[w.tree p]? with
            | some T => T.toksAt (w.place p)
            | none => [])
          rw [hb]
          simp only [Bool.false_eq_true, if_false, hT, TreeT.toksAt, ha]
          exact List.mem_cons_self ..

theorem extK_eq {E : ExtSpec} (we : WireE E) (y : E.Str) (xtK : ℕ → TreeK lam L)
    (xt : ℕ → TreeT lam L) (preX : Bits) (vs₀ vs : List Bits) (val : Tok → Bits)
    (rd : E.Pos → Bool) (hX : ExtTie we xtK xt preX vs₀) (h0 : vs₀ <+: vs)
    (hv : ∀ p, rd p = true → ∀ u ∈ (xt (we.which p)).toksAt (we.leaf p), val u = vs.getD u []) :
    extK we y xtK rd = extK we y (fun k => (xt k).toK val preX) rd := by
  funext p
  unfold extK
  by_cases hr : rd p = true
  swap
  · rw [if_neg hr, if_neg hr]
  rw [if_pos hr, if_pos hr]
  obtain ⟨hlv, hs, hlt⟩ := hX p
  refine congrArg some ?_
  show (⟨E.rd y p, ((xtK (we.which p)).inp (we.leaf p)).salt,
      pathOf (xtK (we.which p)).lv (we.leaf p)⟩ : Opening lam E.Sym) =
    ⟨E.rd y p, (match (xt (we.which p)).tok[we.leaf p]? with
      | some a => preX ++ val a.1
      | none => []), pathOf (xt (we.which p)).lv (we.leaf p)⟩
  rw [hs, hlv]
  show (⟨E.rd y p, (match (xt (we.which p)).tok[we.leaf p]? with
      | some a => preX ++ vs₀.getD a.1 []
      | none => []), pathOf (xt (we.which p)).lv (we.leaf p)⟩ : Opening lam E.Sym) = _
  cases ha : (xt (we.which p)).tok[we.leaf p]? with
  | none => rfl
  | some a =>
    show (⟨E.rd y p, preX ++ vs₀.getD a.1 [], pathOf (xt (we.which p)).lv (we.leaf p)⟩ :
      Opening lam E.Sym) = ⟨E.rd y p, preX ++ val a.1, pathOf (xt (we.which p)).lv (we.leaf p)⟩
    rw [hv p hr a.1 (by simp only [TreeT.toksAt, ha]; exact List.mem_cons_self ..),
      getD_of_prefix h0 (hlt a ha)]

theorem isSome_slotVal_val (f g : Tok → Bits) (ph : PhT) :
    (ph.val lam f).slotVal.isSome = (ph.val lam g).slotVal.isSome := by
  cases ph <;> rfl

/-! ## The string -/

/-- **The compiled prover's finish gives one string** at what its own chain has yielded and at what
the token side lays before it. -/
theorem finish_eq (ll : LeafLens Ω μ ℓ Z) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (x : Y) (y : E.Str) (xtK : ℕ → TreeK lam L) (xt : ℕ → TreeT lam L)
    (preX : Bits) (cd : CoinsD lam L) (st : ℕ → Bool → Bits) (sv : Bits)
    (z : OutT lam L Q.loc.shape) (vs₀ vs : List Bits) (ω : Ω) (val : Tok → Bits) (hW : wq.OKG)
    (hK : KeptOK ℓ Q.loc.shape Q.ann wq.sh z.kept vs) (hC : Covers Z Q.loc.shape Q.ann wq.sh 0)
    (hX : ExtTie wq.ext xtK xt preX vs₀) (h0 : vs₀ <+: vs)
    (hrq : ∀ u, z.rq = some u → val u = vs.getD u [])
    (hop : ∀ p ∈ Q.loc.reads x z.rho (trT Q.loc.shape z.kept z.rho).plains,
      ∀ u ∈ openT Q.loc.shape Q.ann wq.sh z.kept p, val u = vs.getD u [])
    (hex : ∀ p ∈ Q.loc.extReads x z.rho,
      ∀ u ∈ (xt (wq.ext.which p)).toksAt (wq.ext.leaf p), val u = vs.getD u []) :
    finish Q wq x y xtK (coinsK sv cd) (outW ll st vs 0 z ω).1 =
      finish Q wq x y (fun k => (xt k).toK val preX) (coinsK sv cd) (outK val st z) := by
  have e1 := trK_keptW ll st (actK ll Q.loc.shape 0 z.kept vs ω) Q.loc.shape 0 z.kept z.rho
  have e2 := trK_keptK val st Q.loc.shape 0 z.kept z.rho
  have e3 := rootsK_keptW ll st (actK ll Q.loc.shape 0 z.kept vs ω) val Q.loc.shape 0 z.kept
  have e4 : (z.rq.map fun u => digOf lam (vs.getD u [])) = z.rq.map fun u => digOf lam (val u) := by
    cases hq : z.rq with
    | none => rfl
    | some u => exact congrArg (fun v => some (digOf lam v)) (hrq u hq).symm
  have e5 := isSome_slotVal_val (lam := lam) (fun t => vs.getD t []) val z.ph
  letI := wq.decO
  letI := wq.ext.dec
  have e6 := funext (opensK_eq ll st (actK ll Q.loc.shape 0 z.kept vs ω) val vs Q.loc.shape Q.ann
    wq.sh 0 z.kept (fun p => decide (p ∈ Q.loc.reads x z.rho (trT Q.loc.shape z.kept z.rho).plains))
    hW.sh hK (looks_actK ll vs ω Q.loc.shape Q.ann wq.sh 0 z.kept hK hC)
    fun p hp => hop p (of_decide_eq_true hp))
  have e7 := extK_eq wq.ext y xtK xt preX vs₀ vs val (fun p => decide (p ∈ Q.loc.extReads x z.rho))
    hX h0 fun p hp => hex p (of_decide_eq_true hp)
  simp only [finish, outW, outK, coinsK, e1, e2, e3, e4, e5]
  exact congrArg₂ (fun o e => (⟨sv, rootsK Q.loc.shape (keptK val st Q.loc.shape 0 z.kept),
    (trT Q.loc.shape z.kept z.rho).plains, o, e,
    (Option.map (fun u => digOf lam (val u)) z.rq).getD fun _ => false, cd.slot,
    if (PhT.val lam val z.ph).slotVal.isSome = true then cd.path else [],
    if (PhT.val lam val z.ph).slotVal.isSome = true then cd.rsalt else []⟩ : OneProtocolProof lam Q)) e6 e7

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.looks_actK
#print axioms OnBytes.TokenSide.opensK_eq
#print axioms OnBytes.TokenSide.extK_eq
#print axioms OnBytes.TokenSide.finish_eq
