-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide/Hand.lean: ALL HASHING OF A COMPILED RUN, WITH ALL THAT IS READ OF ITS OUTCOME WHEN
A STRING IS HANDED OUT: the token side (hashT, Johnson/TokenSide/Finish.lean) does what the compiled
prover's chain does. Definitions, one statement (Spec.sameHand) and its proof.

Lemmas of one step of a proof. This file states no goal of the release.
The definitions of this file are a device of one step of a proof of index privacy. They stand in no
statement on the scheme.

What is handed out of a run, and what is then written into the table (handOut,
Johnson/WholeKey/Sim.lean), reads of the chain's outcome and of the coins just three things:

  handData    the verifier messages; the proof string; the entries of the run's own leaves at the
              positions that are read (laidK).
  handOut_eq  handOut in terms of handData.
  handDataT   the same three, read off the token side's outcome and the store, in the terms in which
              the rule of release speaks (Spec.release, Johnson/TokenRules/ReleaseSpec.lean): the
              string at the values that the reveals return, the leaves' entries at the store.
  tie_mapOut  a function applied to the outputs of both sides of a tie (Tie,
              Johnson/TokenSide/Tie.lean).
  laidTree_eq, laidTrees_eq, laidK_eq   the leaves' entries are the same whether the salts are read
              at the coins with all drawn bits laid in or at the store: they are read at leaves that
              the trees have.
  Spec.sameHand, sameHand   THE TIE: from hash_tie (Johnson/TokenSide/TieHash.lean), finish_eq
              (Johnson/TokenSide/TieFinish.lean) and laidK_eq.
The part on the string follows the proof of sameRun (Johnson/TokenSide/TieRun.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.TieRun
import Johnson.WholeKey.Sim

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- A function applied to the outputs of both sides of a tie. -/
theorem tie_mapOut {S : OSpec} {Ω α β β' : Type} {μ : PMF Ω} {φ : α → Ω → β} {Q : α → Prop}
    (F : β → β') {c : OComp S α} {g : Ω → OComp S β} (h : Tie μ φ Q c g) :
    Tie μ (fun a ω => F (φ a ω)) Q c fun ω => (g ω).bind fun b => .pure (F b) := by
  induction h with
  | done hq e => exact .done hq fun ω => by rw [e ω]; rfl
  | query k' e _ ih =>
    exact .query (fun ω r => (k' ω r).bind fun b => .pure (F b)) (fun ω => by rw [e ω]; rfl) ih
  | draw k' e _ ih =>
    exact .draw (fun ω r => (k' ω r).bind fun b => .pure (F b)) (fun ω => by rw [e ω]; rfl) ih
  | coin e upd he hs _ ih => exact .coin e upd he hs ih

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## What is read when a string is handed out -/

section Data
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (x : Y) (y : E.Str)

/-- The verifier messages, the proof string, the entries of the run's own leaves at the positions
that are read: out of the chain's outcome and the coins. -/
def handData (xt : ℕ → TreeK lam L) (co : Coins lam L) (r : Res (OutP lam L Q.loc.shape)) :
    Res (Rho Q.loc.shape × OneProtocolProof lam Q × Trace (typedOracleFamily lam K L)) :=
  r.map fun z => (z.1, finish Q wq x y xt co z,
    laidK Q.loc.shape Q.ann wq.sh z.2.1 fun p =>
      haveI := wq.decO
      decide (p ∈ Q.loc.reads x z.1 (trK Q.loc.shape z.2.1 z.1).plains))

/-- handOut reads of the outcome and the coins what handData holds. -/
theorem handOut_eq (xt : ℕ → TreeK lam L) (go : Bool) (co : Coins lam L)
    (o : Res (OutP lam L Q.loc.shape) × RSt (typedOracleFamily lam K L) (Table (typedOracleFamily lam K L))) :
    handOut Q wq x y xt go co o =
      match go, handData Q wq x y xt co o.1 with
      | true, .ok d =>
          (some d.2.1, ((o.2.base.lay (o.2.log.filter notLeaf)).lay d.2.2).lay
            (extLaid Q wq x xt d.1))
      | _, _ => (none, o.2.base) := by
  obtain ⟨r, st⟩ := o
  cases go <;> cases r <;> rfl

/-- The same three, read off the token side's outcome a and the store vs. -/
def handDataT (xt : ℕ → TreeT lam L) (preX : Bits) (pre : ℕ → Bool → Bits → Bits)
    (a : Tok × CoinsD lam L × Res (OutT lam L Q.loc.shape)) (vs : List Bits) :
    Res (Rho Q.loc.shape × OneProtocolProof lam Q × Trace (typedOracleFamily lam K L)) :=
  a.2.2.map fun z => (z.rho,
    finish Q wq x y
      (fun k => (xt k).toK (valOf (showC Q wq x xt a.1 z)
        ((showC Q wq x xt a.1 z).map fun u => vs.getD u [])) preX)
      (coinsK (valOf (showC Q wq x xt a.1 z)
        ((showC Q wq x xt a.1 z).map fun u => vs.getD u []) a.1) a.2.1)
      (outK (valOf (showC Q wq x xt a.1 z) ((showC Q wq x xt a.1 z).map fun u => vs.getD u []))
        (fun i b => pre i b (valOf (showC Q wq x xt a.1 z)
          ((showC Q wq x xt a.1 z).map fun u => vs.getD u []) a.1)) z),
    laidK Q.loc.shape Q.ann wq.sh
      (keptK (fun u => vs.getD u []) (fun i b => pre i b (vs.getD a.1 [])) Q.loc.shape 0 z.kept)
      fun p =>
        haveI := wq.decO
        decide (p ∈ Q.loc.reads x z.rho (trT Q.loc.shape z.kept z.rho).plains))

end Data

/-! ## The leaves' entries -/

section Laid
variable {Ω : Type} {μ : PMF Ω} {ℓ : ℕ} {Z : ℕ → Bool → ℕ → ℕ → Prop} (ll : LeafLens Ω μ ℓ Z)

theorem laidTree_eq (st : Bits) (i : ℕ) (b : Bool) (k : ℕ) (ωa : Ω) (vs : List Bits)
    (T : TreeT lam L) {r : Round} (posAt : ℕ → Option r.Pos) (rd : r.Pos → Bool)
    (hlen : T.tok.length = (T.lv.headD []).length)
    (hl : ∀ j a, T.tok[j]? = some a → ll.get ωa i b k j = vs.getD a.1 []) :
    laidTree (K := K) posAt rd (mkK ll st i b k ωa T) =
      laidTree posAt rd (T.toK (fun u => vs.getD u []) st) := by
  unfold laidTree
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < T.tok.length := by
    rw [hlen]
    exact List.mem_range.mp (List.mem_filter.mp hj).1
  have ha : T.tok[j]? = some T.tok[j] := List.getElem?_eq_getElem hj'
  have e : (T.toK (fun u => vs.getD u []) st).inp j = (mkK ll st i b k ωa T).inp j := by
    simp only [TreeT.toK, mkK, ha, hl j _ ha]
  rw [e]
  rfl

theorem laidTrees_eq (st : Bits) (i : ℕ) (b : Bool) (ωa : Ω) (vs : List Bits) {r : Round}
    (posAt : ℕ → ℕ → Option r.Pos) (rd : r.Pos → Bool) :
    ∀ (Ts : List (TreeT lam L)) (k : ℕ), (∀ T ∈ Ts, T.tok.length = (T.lv.headD []).length) →
      (∀ n T j a, Ts[n]? = some T → T.tok[j]? = some a →
        ll.get ωa i b (k + n) j = vs.getD a.1 []) →
      laidTrees (K := K) posAt rd k (mkKs ll st i b ωa k Ts) =
        laidTrees posAt rd k (Ts.map (TreeT.toK (fun u => vs.getD u []) st))
  | [], _, _, _ => rfl
  | T :: Ts, k, h1, h2 => by
    show laidTree (posAt k) rd (mkK ll st i b k ωa T) ++
        laidTrees posAt rd (k + 1) (mkKs ll st i b ωa (k + 1) Ts) =
      laidTree (posAt k) rd (T.toK (fun u => vs.getD u []) st) ++
        laidTrees posAt rd (k + 1) (Ts.map (TreeT.toK (fun u => vs.getD u []) st))
    rw [laidTree_eq ll st i b k ωa vs T (posAt k) rd (h1 T List.mem_cons_self)
        (fun j a ha => h2 0 T j a rfl ha),
      laidTrees_eq st i b ωa vs posAt rd Ts (k + 1)
        (fun T' hT' => h1 T' (List.mem_cons_of_mem _ hT'))
        (fun n T' j a hn ha => by
          have := h2 (n + 1) T' j a (by simpa using hn) ha
          rwa [show k + (n + 1) = k + 1 + n by omega] at this)]

theorem lens_of_treesOK {ds : List ℕ} {vs : List Bits} {Ts : List (TreeT lam L)}
    (h : Ts = [] ∨ TreesOK ℓ ds vs Ts) : ∀ T ∈ Ts, T.tok.length = (T.lv.headD []).length := by
  rcases h with rfl | h
  · exact fun T hT => absurd hT List.not_mem_nil
  · induction h with
    | nil => exact fun T hT => absurd hT List.not_mem_nil
    | cons h1 _ ih =>
      intro T hT
      rcases List.mem_cons.mp hT with rfl | hT
      · exact h1.1.trans h1.2.2.symm
      · exact ih T hT

/-- **The entries of a run's own leaves** are the same whether the salts are read at coins that hold
the tokens' values or at the store. -/
theorem laidK_eq (st : ℕ → Bool → Bits) (ωa : Ω) (vs : List Bits) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ) (ks : KeptT lam L s)
      (rd : OPos s → Bool), KeptOK ℓ s A W ks vs → Looks ll ωa vs s i ks →
      laidK s A W (keptW ll st ωa s i ks) rd =
        laidK s A W (keptK (fun u => vs.getD u []) st s i ks) rd
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), i, (kp, ks), rd, hk, hl => by
    show laidTrees w.posAtJ (fun p => rd (.inl p)) 0 (mkKs ll (st i true) i true ωa 0 kp.2.2) ++
        (laidTrees w.posAt0 (fun p => rd (.inl p)) 0 (mkKs ll (st i false) i false ωa 0 kp.2.1) ++
          laidK s A W (keptW ll st ωa s (i + 1) ks) fun p => rd (.inr p)) =
      laidTrees w.posAtJ (fun p => rd (.inl p)) 0
          (kp.2.2.map (TreeT.toK (fun u => vs.getD u []) (st i true))) ++
        (laidTrees w.posAt0 (fun p => rd (.inl p)) 0
            (kp.2.1.map (TreeT.toK (fun u => vs.getD u []) (st i false))) ++
          laidK s A W (keptK (fun u => vs.getD u []) st s (i + 1) ks) fun p => rd (.inr p))
    rw [laidTrees_eq ll (st i true) i true ωa vs w.posAtJ _ kp.2.2 0 (lens_of_treesOK hk.2.1)
        (fun n T j a hn ha => by rw [Nat.zero_add]; exact hl.2.1 n T j a hn ha),
      laidTrees_eq ll (st i false) i false ωa vs w.posAt0 _ kp.2.1 0 (lens_of_treesOK hk.1)
        (fun n T j a hn ha => by rw [Nat.zero_add]; exact hl.1 n T j a hn ha),
      laidK_eq st ωa vs s A W (i + 1) ks _ hk.2.2 hl.2.2]

end Laid

/-! ## The tie -/

/-- **All hashing of a compiled run, with all that is read of its outcome when a string is handed
out.** -/
def Spec.sameHand : Prop :=
  ∀ {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xtK : ℕ → TreeK lam L) (xt : ℕ → TreeT lam L)
    (preX : Bits) (σ : Strat Q.loc.shape Unit) (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits)
    (cap : ℕ → ℕ) {Ω : Type} {μ : PMF Ω} {Z : RunCo → Prop} (rl : RunLens Ω μ ln Z)
    (vs : List Bits),
    wq.OKG → CoversRun Z ln Q.loc.shape Q.ann wq.sh → ExtTie wq.ext xtK xt preX vs →
    Tie μ
      (fun (p : (Tok × CoinsD lam L × Res (OutT lam L Q.loc.shape)) × List Bits) _ =>
        handDataT Q wq x y xt preX pre p.1 p.2)
      (fun p => vs <+: p.2)
      (plainOf (hashT t Q wq embS embP xin cms x σ ln pre cap) vs)
      (fun ω => (chainX t Q wq embS embP xin cms x cap σ (coRun rl pre ω)).bind fun r =>
        .pure (handData Q wq x y xtK (coRun rl pre ω) r))

theorem sameHand : Spec.sameHand := by
  intro I X lam K L t Y E Q wq embS embP xin cms x y xtK xt preX σ ln pre cap Ω μ Z rl vs hW hC hX
  have h0 := tie_mapOut
    (fun b : Res (OutP lam L Q.loc.shape) × Coins lam L => handData Q wq x y xtK b.2 b.1)
    (hash_tie t Q wq embS embP xin cms x σ pre cap rl vs hC)
  refine ((h0.out ?_).mono fun _ hp => hp.1).congr fun ω => ?_
  swap
  · rw [Tie.obind_assoc]
    refine congrArg _ (funext fun r => ?_)
    cases r <;> rfl
  rintro ⟨⟨salt, cd, r⟩, vs'⟩ ⟨hp1, hp2, hp3⟩ ω
  cases r with
  | noFormat => rfl
  | ranOut j => rfl
  | ok z =>
    obtain ⟨hK, hrq⟩ := hp3 z rfl
    have hval : ∀ u ∈ showC Q wq x xt salt z, valOf (showC Q wq x xt salt z)
        ((showC Q wq x xt salt z).map fun u => vs'.getD u []) u = vs'.getD u [] :=
      fun u hu => valOf_map (fun u => vs'.getD u []) _ u hu
    have hmem : ∀ c ∈ chunksT Q wq x xt salt z, ∀ u ∈ c, u ∈ showC Q wq x xt salt z :=
      fun c hc u hu => List.mem_flatten.mpr ⟨c, hc, hu⟩
    have hsalt : salt ∈ showC Q wq x xt salt z :=
      hmem _ (List.mem_cons_self ..) salt (List.mem_cons_self ..)
    have eS : finish Q wq x y xtK (coinsK (vs'.getD salt []) cd)
        (outW rl.leaf (fun i b => pre i b (vs'.getD salt [])) vs' 0 z ω).1 =
        finish Q wq x y
          (fun k => (xt k).toK (valOf (showC Q wq x xt salt z)
            ((showC Q wq x xt salt z).map fun u => vs'.getD u [])) preX)
          (coinsK (vs'.getD salt []) cd)
          (outK (valOf (showC Q wq x xt salt z)
            ((showC Q wq x xt salt z).map fun u => vs'.getD u []))
            (fun i b => pre i b (vs'.getD salt [])) z) := by
      refine finish_eq rl.leaf Q wq x y xtK xt preX cd _ _ z vs vs' ω _ hW hK hC.2.2.2 hX hp1
        (fun u hu => hval u (hmem _ (List.mem_cons_self ..) u (List.mem_cons_of_mem _ (hrq u hu))))
        (fun p hp u hu => ?_) (fun p hp u hu => ?_)
      · obtain ⟨c, hc, huc⟩ := mem_shownK vs' Q.loc.shape Q.ann wq.sh z.kept (fun p =>
            haveI := wq.decO
            decide (p ∈ Q.loc.reads x z.rho (trT Q.loc.shape z.kept z.rho).plains)) hW.sh hK p
          (by
            letI := wq.decO
            exact decide_eq_true hp) u hu
        exact hval u (hmem c (List.mem_cons_of_mem _ (List.mem_append_left _ hc)) u huc)
      · refine hval u (hmem _ (List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hW.ext.complete p, by
            letI := wq.ext.dec
            exact decide_eq_true hp⟩, rfl⟩))) u hu)
    have eT := trK_keptW rl.leaf (fun i b => pre i b (vs'.getD salt []))
      (actK rl.leaf Q.loc.shape 0 z.kept vs' ω) Q.loc.shape 0 z.kept z.rho
    have eL := fun rd => laidK_eq rl.leaf (fun i b => pre i b (vs'.getD salt []))
      (actK rl.leaf Q.loc.shape 0 z.kept vs' ω) vs' Q.loc.shape Q.ann wq.sh 0 z.kept rd hK
      (looks_actK rl.leaf vs' ω Q.loc.shape Q.ann wq.sh 0 z.kept hK hC.2.2.2)
    show Res.ok (z.rho, finish Q wq x y xtK (coinsK (vs'.getD salt []) cd)
        (outW rl.leaf (fun i b => pre i b (vs'.getD salt [])) vs' 0 z ω).1,
      laidK Q.loc.shape Q.ann wq.sh
        (keptW rl.leaf (fun i b => pre i b (vs'.getD salt []))
          (actK rl.leaf Q.loc.shape 0 z.kept vs' ω) Q.loc.shape 0 z.kept) fun p =>
          haveI := wq.decO
          decide (p ∈ Q.loc.reads x z.rho (trK Q.loc.shape
            (keptW rl.leaf (fun i b => pre i b (vs'.getD salt []))
              (actK rl.leaf Q.loc.shape 0 z.kept vs' ω) Q.loc.shape 0 z.kept) z.rho).plains)) =
      handDataT Q wq x y xt preX pre (salt, cd, Res.ok z) vs'
    rw [eS, eT, eL]
    simp only [handDataT, Res.map, hval salt hsalt]

end OnBytes.LateSide

#print axioms OnBytes.LateSide.laidK_eq
#print axioms OnBytes.LateSide.sameHand
