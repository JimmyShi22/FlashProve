-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Work.lean: HOW MANY TYPED QUERIES the committer and the prover of the scheme with
the whole key published ask (commitW, proveW, Johnson/WholeKey/Defs.lean), AT WRITTEN COUNTS; and
THAT THEY ASK NO POINT OF THE SPARE ORACLE.

General theorems with their proofs. This file states no goal of the release.

Why the counts. Caps of the searches and numbers of test bits are free letters of the scheme. A
prover that never reads the index and finds an accepted string by a long search is shut out by no
bound on the three errors alone. What shuts it out is a bound on the honest side's work, beside
which the error of index binding AT THAT MANY QUERIES can be held.
Why the spare oracle. By the library's account (the head of Johnson/Prover/All/NoOther.lean, which
names layoutsByPublicReading_spare, Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean; not shown again here), where a description's
public readings are answers of the hash function, their strings code points of the spare oracle
("other"). The statement of index privacy is for letters
that are fixed before the oracles are drawn. A step that reads the letters off the hash function
wants that the honest side asks none of these points.

  PathsFit W h   the coins that are listed for a compiled run hold as many sibling digests as its
                 request tree is deep.
  commitN W h    (M + 2) tables, each 2 · 2^depth queries for its tree and 2 for its seed; the
                 compiled run on the first table; M + 1 link runs. A run by chainN
                 (Johnson/Prover/Law/Count.lean): trees, Fiat-Shamir queries WITH EVERY TRY UP TO
                 ITS CAP, the joining round's queries.
  proveN W h     one session's run.
  queryBound_commitW, queryBound_proveW   on every path at most so many typed queries.
  no_commitW, no_proveW   no point of the spare oracle.

Limits. Typed queries, not calls of one hash function. Upper bounds on every path, with chainN's
looseness. Of the simulator nothing is shown here. No number is evaluated.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Defs
import Johnson.Prover.All.Count
import Johnson.Prover.All.NoOther
import OnBytes.K.Arm.TreeCommitCount

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Compile.GenPub (AllOut)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)

/-- The coins that are listed for a compiled run hold as many sibling digests as its request tree is
deep. -/
structure PathsFit : Prop where
  T : ∀ n, (h.coT.e n).path.length = W.depthReqT
  Lk : ∀ n, (h.coL.e n).path.length = W.depthReqL
  B : ∀ n, (h.coB.e n).path.length = W.depthReq

/-- The typed queries of one table: its tree, its seed. -/
def tabN : ℕ := 2 * 2 ^ W.depth + (2 + 0)

/-- The typed queries of one link run. -/
def linkN : ℕ := chainN L.link.shape aL (wLC W).sh h.capL 0 W.depthReqL + 0

/-- **The committer's count.** -/
def commitN : ℕ :=
  tabN W + ((h.M + 1) * tabN W +
    (chainN L.offline.shape aT (wTC W).sh h.capT 0 W.depthReqT + ((h.M + 1) * linkN W h + 0)))

/-- **The prover's count.** -/
def proveN : ℕ := chainN L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh h.capB 0 W.depthReq + 0

/-! ## The counts -/

theorem queryBound_tabO (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) :
    (tabO W S b₀ i r s).QueryBound (tabN W) :=
  (queryBound_committerTreeKeptByProver W b₀ _ _).bind fun _ => (queryBound_seedsO W S _).bind fun _ => trivial

theorem queryBound_tabsO (i : I) : ∀ ds : List (DrawCopy lam L Bd aT aL h.KL),
    (tabsO W S h i ds).QueryBound (ds.length * tabN W)
  | [] => trivial
  | d :: ds => by
    have e : (d :: ds).length * tabN W = tabN W + (ds.length * tabN W + 0) := by
      rw [List.length_cons, Nat.succ_mul]
      omega
    rw [e]
    exact (queryBound_tabO W S h.b₀ i d.r _).bind fun _ =>
      (queryBound_tabsO i ds).bind fun _ => trivial

theorem queryBound_linkO (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (d : DrawCopy lam L Bd aT aL h.KL)
    (hd : d.co.path.length = W.depthReqL) :
    (linkO W cA h i t₁ t₂ d).QueryBound (linkN W h) := by
  have q := queryBound_proveX Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
    (cmsLA cA t₁.tree.root t₂.tree.root (L.recOf i t₁.r t₁.seed).2 (L.recOf i t₂.r t₂.seed).2)
    (L.recOf i t₁.r t₁.seed, L.recOf i t₂.r t₂.seed) (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r)
    (fun k => if k = 0 then t₁.tree else t₂.tree)
    (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) d.κ) (h.dressL (h.rvL d.κ) d.co) h.capL
  have e : (h.dressL (h.rvL d.κ) d.co).path.length = W.depthReqL := hd
  rw [e] at q
  exact q.bind fun _ => trivial

theorem queryBound_linksO (i : I) (t₁ : TabK lam L Bd aT aL) :
    ∀ l : List (DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL),
      (∀ a ∈ l, a.1.co.path.length = W.depthReqL) →
      (linksO W cA h i t₁ l).QueryBound (l.length * linkN W h)
  | [], _ => trivial
  | a :: l, hl => by
    have e : (a :: l).length * linkN W h = linkN W h + (l.length * linkN W h + 0) := by
      rw [List.length_cons, Nat.succ_mul]
      omega
    rw [e]
    exact (queryBound_linkO W cA h i t₁ a.2 a.1 (hl a (List.mem_cons_self ..))).bind fun _ =>
      (queryBound_linksO i t₁ l fun b hb => hl b (List.mem_cons_of_mem _ hb)).bind fun _ => trivial

/-- What the committer's coins are like. -/
def FitC (d : DrawC lam L Bd aT aL h.KT h.KL) : Prop :=
  d.co.path.length = W.depthReqT ∧ d.copies.length = h.M + 1 ∧
    ∀ e ∈ d.copies, e.co.path.length = W.depthReqL

theorem queryBound_commitAt (i : I) (d : DrawC lam L Bd aT aL h.KT h.KL) (hd : FitC W h d) :
    (commitAt W S cA h i d).QueryBound (commitN W h) := by
  refine (queryBound_tabO W S h.b₀ i d.r _).bind fun t₁ => ?_
  have q2 := queryBound_tabsO W S h i d.copies
  rw [hd.2.1] at q2
  refine q2.bind fun ts => ?_
  have q3 := queryBound_proveX Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
    (cmsTA cA t₁.tree.root (L.recOf i t₁.r t₁.seed).2) (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
    (fun _ => t₁.tree) (h.st.T i t₁.r t₁.seed d.κ) (h.dressT (h.rvT d.κ) d.co) h.capT
  have e3 : (h.dressT (h.rvT d.κ) d.co).path.length = W.depthReqT := hd.1
  rw [e3] at q3
  refine q3.bind fun a => ?_
  have q4 := queryBound_linksO W cA h i t₁ (d.copies.zip ts) fun b hb =>
    hd.2.2 b.1 (List.of_mem_zip (a := b.1) (b := b.2) hb).1
  have hlen : (d.copies.zip ts).length * linkN W h ≤ (h.M + 1) * linkN W h := by
    refine Nat.mul_le_mul_right _ ?_
    rw [List.length_zip, hd.2.1]
    exact Nat.min_le_left _ _
  exact (q4.mono hlen).bind fun _ => trivial

theorem allOut_coinsCopy (hp : PathsFit W h) :
    AllOut (fun d : DrawCopy lam L Bd aT aL h.KL => d.co.path.length = W.depthReqL)
      (coinsCopy W h) :=
  fun _ _ _ e => hp.Lk e

theorem allOut_coinsCopies (hp : PathsFit W h) : ∀ n : ℕ,
    AllOut (fun ds : List (DrawCopy lam L Bd aT aL h.KL) =>
      ds.length = n ∧ ∀ e ∈ ds, e.co.path.length = W.depthReqL) (coinsCopies W h n)
  | 0 => ⟨rfl, fun _ he => by cases he⟩
  | n + 1 =>
    AllOut.bind (allOut_coinsCopy W h hp) fun d hd =>
      AllOut.bind (allOut_coinsCopies hp n) fun ds hds =>
        ⟨by simp [hds.1], fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hd
          · exact hds.2 x hx⟩

theorem allOut_coinsC (hp : PathsFit W h) : AllOut (FitC W h) (coinsC W h) :=
  fun _ _ _ e => AllOut.bind (allOut_coinsCopies W h hp (h.M + 1)) fun _ hds =>
    ⟨hp.T e, hds.1, hds.2⟩

theorem queryBound_coinsCopies : ∀ n : ℕ, (coinsCopies W h n).QueryBound 0
  | 0 => trivial
  | n + 1 =>
    OComp.QueryBound.bind (s := 0) (t := 0) (c := coinsCopy W h) (fun _ _ _ _ => trivial) fun _ =>
      OComp.QueryBound.bind (s := 0) (t := 0) (queryBound_coinsCopies n) fun _ => trivial

theorem queryBound_coinsC : (coinsC W h).QueryBound 0 :=
  fun _ _ _ _ =>
    OComp.QueryBound.bind (s := 0) (t := 0) (queryBound_coinsCopies W h _) fun _ => trivial

/-- **The committer asks at most commitN typed queries, on every path.** -/
theorem queryBound_commitW (hp : PathsFit W h) (i : I) :
    (commitW W S cA h i).QueryBound (commitN W h) := by
  have q := OComp.QueryBound.bindOut (queryBound_coinsC W h) (allOut_coinsC W h hp)
    fun d hd => queryBound_commitAt W S cA h i d hd
  rwa [Nat.zero_add] at q

theorem queryBound_proveAt (isk : Isk lam L Bd aT aL) (x : X) (d : DrawP lam L Bd aT aL h.KB)
    (hd : d.co.path.length = W.depthReq) :
    (proveAt W cA r₀ h isk x d).QueryBound (proveN W h) := by
  unfold proveAt
  cases isk.copies[d.j]? with
  | none => trivial
  | some t =>
    have q := queryBound_proveX Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀)
      (cmsBA cA t.tree.root (L.recOf isk.i t.r t.seed).2) (x, L.recOf isk.i t.r t.seed)
      (L.encodeIndex isk.i t.r) (fun _ => t.tree) (h.st.B isk.i t.r t.seed x (h.nm d.j) d.κ)
      (h.dressB (h.rvB d.κ) d.co) h.capB
    have e : (h.dressB (h.rvB d.κ) d.co).path.length = W.depthReq := hd
    rw [e] at q
    exact q.bind fun _ => trivial

/-- **The prover asks at most proveN typed queries, on every path.** -/
theorem queryBound_proveW (hp : PathsFit W h) (isk : Isk lam L Bd aT aL) :
    ∀ b : List (X × Unit), (proveW W cA r₀ h isk b).QueryBound (proveN W h)
  | [] => trivial
  | [(x, _)] => by
    have q := OComp.QueryBound.bindOut (s := 0) (c := coinsP W h)
      (P := fun d : DrawP lam L Bd aT aL h.KB => d.co.path.length = W.depthReq)
      (g := fun d => (proveAt W cA r₀ h isk x d).bind fun π =>
        (OComp.pure ⟨[π], rfl⟩ :
          TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (ZKCP.Gen.Slots (RequestProof lam L) [(x, ())])))
      (t := proveN W h + 0) (fun _ _ _ => trivial) (fun _ _ e => hp.B e) fun d hd =>
        (queryBound_proveAt W cA r₀ h isk x d hd).bind fun _ => trivial
    exact q.mono (by omega)
  | _ :: _ :: _ => trivial

/-! ## No point of the spare oracle -/

theorem no_tabO (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) :
    (tabO W S b₀ i r s).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) :=
  asksIn_bind (no_committerTreeKeptByProver W b₀ _ _) fun _ => asksIn_bind (no_seedsO W S _) fun _ => trivial

theorem no_tabsO (i : I) : ∀ ds : List (DrawCopy lam L Bd aT aL h.KL),
    (tabsO W S h i ds).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL))
  | [] => trivial
  | d :: ds => asksIn_bind (no_tabO W S h.b₀ i d.r _) fun _ =>
      asksIn_bind (no_tabsO i ds) fun _ => trivial

theorem no_linksO (i : I) (t₁ : TabK lam L Bd aT aL) :
    ∀ l : List (DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL),
      (linksO W cA h i t₁ l).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL))
  | [] => trivial
  | _ :: l => asksIn_bind (asksIn_bind (no_proveX _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => trivial)
      fun _ => asksIn_bind (no_linksO i t₁ l) fun _ => trivial

theorem no_coinsCopies : ∀ n : ℕ,
    (coinsCopies W h n).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL))
  | 0 => trivial
  | n + 1 =>
    asksIn_bind (c := coinsCopy W h) (fun _ _ _ _ => trivial) fun _ =>
      asksIn_bind (no_coinsCopies n) fun _ => trivial

/-- **The committer asks no point of the spare oracle.** -/
theorem no_commitW (i : I) :
    (commitW W S cA h i).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) :=
  asksIn_bind (fun _ _ _ _ => asksIn_bind (no_coinsCopies W h _) fun _ => trivial) fun d =>
    asksIn_bind (no_tabO W S h.b₀ i d.r _) fun t₁ =>
      asksIn_bind (no_tabsO W S h i d.copies) fun _ =>
        asksIn_bind (no_proveX _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ =>
          asksIn_bind (no_linksO W cA h i t₁ _) fun _ => trivial

theorem no_proveAt (isk : Isk lam L Bd aT aL) (x : X) (d : DrawP lam L Bd aT aL h.KB) :
    (proveAt W cA r₀ h isk x d).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) := by
  unfold proveAt
  cases isk.copies[d.j]? with
  | none => trivial
  | some t => exact asksIn_bind (no_proveX _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => trivial

/-- **The prover asks no point of the spare oracle.** -/
theorem no_proveW (isk : Isk lam L Bd aT aL) :
    ∀ b : List (X × Unit),
      (proveW W cA r₀ h isk b).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL))
  | [] => trivial
  | [(x, _)] =>
    asksIn_bind (c := coinsP W h) (fun _ _ _ => trivial) fun d =>
      asksIn_bind (no_proveAt W cA r₀ h isk x d) fun _ => trivial
  | _ :: _ :: _ => trivial

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.queryBound_commitW
#print axioms OnBytes.WholeKey.queryBound_proveW
#print axioms OnBytes.WholeKey.no_commitW
#print axioms OnBytes.WholeKey.no_proveW
