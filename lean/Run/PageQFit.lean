-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQFit.lean: on the generic construction, under the hypotheses below, the strings of the
encoding of the queries are the strings of the functions "typed query ↦ call of the format's hash"
(Run/CodingFn.lean; the hash: `Fmt.formatHash`, Fmt/Rules23.lean, this library's rendering of the format
page's, not the edition that ships), for every description and all queries that the format writes.

The compiled verifier asks typed oracles (`OracleName`, Compile/Batch/Oracles.lean), among them those for
chain queries and for the leaves and nodes of hash trees. To run it over one hash function, every
typed query, with the number of a block of its answer, is written as a bit string by a one-to-one
encoding with a parser (a coding: `Rom.OracleCoding`, Rom/Family.lean). Run/CodingPage.lean builds such an
encoding from a record of data, `PageC`.
Theorems. The generic construction (Run/PlanQS.lean) makes from a description a protocol, its
wiring and run functions. Run/PageQ.lean makes the encoding's data from a chain's description
(`pageQ`); Run/PlanQS.lean the spellings for the functions of Run/CodingFn.lean (`PDS`). These are
two separate definitions. Here they are tied:

Main names:
  `pVec_fit`, `leaf1_fit`, `leafCL_fit`, `leafQ_fit`: what the leaves' code writes is the bits of
    the label (leaves' number: `t164`, Run/CodingTag.lean; `PDS`'s tree and index) and then of
    `PDS`'s column with its fill.
  `firstQ_fit`: what the first query's code writes is the string of the call that Run/CodingFn.lean
    makes of a query of round 0 at the block of the chain value.
  `pageQ_fit`: 0 < K → `PageFit (pageQ S C dec K h) (PDS S C dec)` (Run/CodingAgree.lean), for
    `h : OKQ S = true`.

Limits: nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Run.PageQ
import Run.ToyFit

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch
open _root_.Fmt (Item)

theorem pDig_put (r : Dig 256) (u : List Bool) (h : pDig.put r = some u) :
    u = bytesToBits (digToBytes r) := by
  obtain ⟨l, hl, hp⟩ := PCode.pull_put _ _ _ _ _ r u h
  have hl' : l = List.ofFn r := (Option.some.inj hl).symm
  subst hl'
  have h0 : (if (List.ofFn r).length = 256 then some (List.ofFn r) else none) = some u := hp
  rw [if_pos (List.length_ofFn)] at h0
  rw [bits_digToBytes]
  exact (Option.some.inj h0).symm

/-- The message. b: the root's bytes, if the message has a root; any string else. -/
theorem pMsg_fit :
    ∀ (l : List Item) (rt : Option (Dig 256)) (y : RootOf l), toRoots l rt = some y →
      ∀ (x : PlainOf l) (s : List Bool), (pMsg l).1.put (y, x) = some s →
        ∀ b : ByteArray,
          (∀ r, rt = some r → b = digToBytes r) → s = bytesToBits (PlainOf.bytes b l x)
  | [], _, _, _, _, s, h, _, _ => by
      rw [← Option.some.inj h]
      rfl
  | .root :: l, some r, y, hy, x, s, h, b, hb => by
      have h0 : (toRoots l none).map (fun y => ((r, y) : Dig 256 × RootOf l)) = some y := hy
      cases hy' : toRoots l none with
      | none => rw [hy'] at h0; cases h0
      | some y' =>
          rw [hy'] at h0
          have ey : y = ((r, y') : Dig 256 × RootOf l) := (Option.some.inj h0).symm
          subst ey
          obtain ⟨u, v, hu, hv, rfl⟩ :=
            PCode.cons_put pDig 256 pDig_len (fun _ => (pMsg l).1) (r, (y', x)) s h
          rw [pDig_put r u hu, pMsg_fit l none y' hy' x v hv b (fun _ h => by cases h), ← hb r rfl]
          exact (bytesToBits_append _ _).symm
  | .root :: _, none, _, hy, _, _, _, _, _ => by cases hy
  | .f :: l, rt, y, hy, (x : UInt64 × PlainOf l), s, h, b, hb => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put pU64 64 pU64_len (fun _ => (pMsg l).1) (x.1, (y, x.2)) s h
      rw [pU64_put] at hu
      rw [← Option.some.inj hu, pMsg_fit l rt y hy x.2 v hv b hb]
      exact (bytesToBits_append _ _).symm
  | .word :: l, rt, y, hy, (x : UInt64 × PlainOf l), s, h, b, hb => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put pU64 64 pU64_len (fun _ => (pMsg l).1) (x.1, (y, x.2)) s h
      rw [pU64_put] at hu
      rw [← Option.some.inj hu, pMsg_fit l rt y hy x.2 v hv b hb]
      exact (bytesToBits_append _ _).symm
  | .e :: l, rt, y, hy, (x : _root_.Fmt.Ext × PlainOf l), s, h, b, hb => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put pE3 192 pE3_len (fun _ => (pMsg l).1) (x.1, (y, x.2)) s h
      rw [Toy1.pE3_put] at hu
      rw [← Option.some.inj hu, pMsg_fit l rt y hy x.2 v hv b hb]
      exact (bytesToBits_append _ _).symm
  | .answer :: l, rt, y, hy, (x : _root_.Fmt.Ext × PlainOf l), s, h, b, hb => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put pE3 192 pE3_len (fun _ => (pMsg l).1) (x.1, (y, x.2)) s h
      rw [Toy1.pE3_put] at hu
      rw [← Option.some.inj hu, pMsg_fit l rt y hy x.2 v hv b hb]
      exact (bytesToBits_append _ _).symm

theorem pMsgO_fit (l : List Item) (rt : Option (Dig 256)) (x : PlainOf l)
    (s : List Bool) (h : (pMsgO l).put (rt, x) = some s) :
    s = bytesToBits (PlainOf.bytes ((rt.map digToBytes).getD ByteArray.empty) l x) := by
  obtain ⟨a, ha, hs⟩ := PCode.pull_put _ _ _ _ _ (rt, x) s h
  have ha' : (toRoots l rt).map (fun y => (y, x)) = some a := ha
  cases hy : toRoots l rt with
  | none => rw [hy] at ha'; cases ha'
  | some y =>
      rw [hy] at ha'
      rw [← Option.some.inj ha'] at hs
      exact pMsg_fit l rt y hy x s hs _ (fun r hr => by rw [hr]; rfl)

/-- The message and the nonce's word. -/
theorem pRound_fit :
    ∀ (w : ℕ) (l : List Item) (rt : Option (Dig 256)) (p : GPlain ℕ w (PlainOf l)) (s : List Bool),
      (pRound w l).put (rt, p) = some s →
      s = bytesToBits
            (PlainOf.bytes ((rt.map digToBytes).getD ByteArray.empty) l (GPlain.old (b := w) p)) ++
          bytesToBits (_root_.Fmt.u64n (GPlain.nonce (b := w) p))
  | 0, l, rt, p, s, h => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put (pMsgO l) (msgBits l) (pMsgO_len l) (fun _ => pUnit word0) ((rt, p), ()) s h
      rw [pMsgO_fit l rt p u hu, ← Option.some.inj hv]
      rfl
  | w + 1, l, rt, (p : PlainOf l × ℕ), s, h => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put (pMsgO l) (msgBits l) (pMsgO_len l) (fun _ => pWord) ((rt, p.1), p.2) s h
      have hv' : v = bytesToBits (_root_.Fmt.u64n p.2) := by
        have h0 : (if p.2 < 2 ^ 64 then some (bytesToBits (_root_.Fmt.u64n p.2)) else none) =
            some v := hv
        by_cases hn : p.2 < 2 ^ 64
        · rw [if_pos hn] at h0
          exact (Option.some.inj h0).symm
        · rw [if_neg hn] at h0
          cases h0
      rw [pMsgO_fit l rt p.1 u hu, hv']
      rfl

/-! ### The chain -/

theorem inL_put' {R A B : Type} (p : PCode (R × A)) (r : R) (z : A ⊕ B)
    (s : List Bool) (h : (inL p).put (r, z) = some s) :
    ∃ a, z = .inl a ∧ p.put (r, a) = some s := by
  obtain ⟨y, hy, hs⟩ := PCode.via_put' _ _ _ _ _ (r, z) s h
  have := mk_selInl (r, z) y hy
  exact ⟨y.2, (congrArg Prod.snd this).symm, by
    have e : y.1 = r := congrArg Prod.fst this
    rw [← e]
    exact hs⟩

theorem inR_put' {R A B : Type} (p : PCode (R × B)) (r : R) (z : A ⊕ B)
    (s : List Bool) (h : (inR p).put (r, z) = some s) :
    ∃ b, z = .inr b ∧ p.put (r, b) = some s := by
  obtain ⟨y, hy, hs⟩ := PCode.via_put' _ _ _ _ _ (r, z) s h
  have := mk_selInr (r, z) y hy
  exact ⟨y.2, (congrArg Prod.snd this).symm, by
    have e : y.1 = r := congrArg Prod.fst this
    rw [← e]
    exact hs⟩

theorem rcL_fit (C : CK) :
    ∀ (ds : List RD) (i : ℕ) (rt : Option (Dig 256)) (q : PBL C ds) (s : List Bool),
      (rcL C ds i).put (rt, q) = some s →
      s = bytesToBits (msgSL C ((rt.map digToBytes).getD ByteArray.empty) ds q) ++
          bytesToBits (_root_.Fmt.u64n (nonceSL C ds q))
  | [], _, _, _, _, h => by cases h
  | d :: _, 0, rt, q, s, h => by
      obtain ⟨a, rfl, h1⟩ := inL_put' _ rt q s h
      obtain ⟨p, rfl, h2⟩ := inR_put' _ rt a s h1
      exact pRound_fit d.entry.work d.items rt p s h2
  | _ :: ds, i + 1, rt, q, s, h => by
      obtain ⟨b, rfl, h1⟩ := inR_put' _ rt q s h
      exact rcL_fit C ds i rt b s h1

variable (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)

/-- The chain's data fit the spellings. -/
theorem chainQ_fit : ChainFit (chainQ S C dec) (PDS S C dec) where
  label := rfl
  kind := fun _ => rfl
  work := fun _ => rfl
  rc := fun i rt pl s h => by
    match i, h with
    | 0, h => cases h
    | i + 1, h =>
        obtain ⟨b, rfl, h1⟩ := inR_put' _ rt pl s h
        exact rcL_fit C (rds S) i rt b s h1

/-! ### Leaves -/

theorem pVec_fit :
    ∀ (W : ℕ) (col : Fin W → UInt64) (s : List Bool),
      (pVec W).1.put col = some s → s = bytesToBits (_root_.Fmt.colBytes (List.ofFn col))
  | 0, _, s, h => by
      rw [← Option.some.inj h]
      rfl
  | W + 1, col, s, h => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put pU64 64 pU64_len (fun _ => (pVec W).1)
          ((Fin.consEquiv fun _ : Fin (W + 1) => UInt64).symm col) s h
      rw [pU64_put] at hu
      rw [← Option.some.inj hu, pVec_fit W _ v hv]
      show _ = bytesToBits (_root_.Fmt.cat ((List.ofFn col).map _root_.Fmt.u64))
      rw [List.ofFn_succ, List.map_cons, _root_.Fmt.cat_cons, bytesToBits_append]
      rfl

theorem leaf1_fit (t : Option _root_.Fmt.Shape) (salt : ℕ) (x : Fin (posN t))
    (col : Fin (colW t) → UInt64) (m : List Bool) (h : (leaf1 t salt).put (x, col) = some m) :
    m = bytesToBits
          (_root_.Fmt.label 164 (_root_.Fmt.leafPlace (trNo t) (colW t) (salt / 8))
            (posN t + x.val)) ++
        bytesToBits
          (_root_.Fmt.colBytes (List.ofFn col) ++
            _root_.Fmt.zeroBytes (_root_.Fmt.fillLen (colW t) salt)) := by
  obtain ⟨u, hu, rfl⟩ := PCode.pre_put' _ _ _ m h
  obtain ⟨u1, v1, hu1, hv1, rfl⟩ := PCode.cons_put _ _ _ _ (x, (col, ())) u hu
  obtain ⟨u2, v2, hu2, hv2, rfl⟩ := PCode.cons_put _ _ _ _ (col, ()) v1 hv1
  have hx : u1 = bytesToBits (_root_.Fmt.u64n (posN t + x.val)) := by
    obtain ⟨n, hn, hp⟩ := PCode.pull_put _ _ _ _ _ x u1 hu1
    have hn' : n = posN t + x.val := (Option.some.inj hn).symm
    subst hn'
    have h0 : (if posN t + x.val < 2 ^ 64 then some (bytesToBits (_root_.Fmt.u64n (posN t + x.val)))
          else none) = some u1 := hp
    by_cases hb : posN t + x.val < 2 ^ 64
    · rw [if_pos hb] at h0
      exact (Option.some.inj h0).symm
    · rw [if_neg hb] at h0
      cases h0
  rw [hx, pVec_fit _ col u2 hu2, ← Option.some.inj hv2]
  unfold _root_.Fmt.label leafWord fillBits
  simp only [bytesToBits_append, List.append_assoc]

theorem leafCL_fit (salt : ℕ) :
    ∀ (ds : List RD) (y : SymAny (uL C ds)) (m : List Bool), (leafCL C salt ds).put y = some m →
      m = bytesToBits (_root_.Fmt.label 164 (leafSL C salt ds y).1 (leafSL C salt ds y).2.1) ++
          bytesToBits (leafSL C salt ds y).2.2
  | [], _, _, h => by cases h
  | d :: ds, ⟨.inl x, col⟩, m, h => leaf1_fit d.tree salt x col m h
  | d :: ds, ⟨.inr q, col⟩, m, h => leafCL_fit salt ds ⟨q, col⟩ m (PCode.sumF_inr _ _ _ m h)

theorem leafQ_fit (y : SymAny (Compile.Batch.shapeOf (LfQ S C dec ()) .onl))
    (m : List Bool) (h : (leafQ S C dec).put y = some m) :
    m = bytesToBits (_root_.Fmt.label 164 ((PDS S C dec).leaf y).1 ((PDS S C dec).leaf y).2.1) ++
        bytesToBits ((PDS S C dec).leaf y).2.2 := by
  obtain ⟨p, col⟩ := y
  rcases p with p | q
  · exact p.elim
  · exact leafCL_fit C S.plan.salt (rds S) ⟨q, col⟩ m (PCode.sumF_inr _ _ _ m h)

/-! ### The first query, and the whole -/

theorem firstQ_fit (K : ℕ) (q : FbIn 256 (LfQ S C dec ()) .onl)
    (s : List Bool) (h : (firstQ S C dec).put q = some s) :
    q.round = 0 ∧
    ∃ c, fbCall (PDS S C dec) K q (Fin.last K) = some c ∧ s = bytesToBits (strOf c) := by
  obtain ⟨a, ha, hs⟩ := PCode.via_put'
    (pFirst0 S.label (stmQ S) (unstmQ S) (unstm_stmQ S) (stm_unstmQ S))
    (fbSel0 (L := LfQ S C dec ()) (isP0Q S C dec)) (fbMk0 (p0Q S C dec))
    (fbSel0_mk (p0Q S C dec) (isP0Q S C dec) (isP0Q_iff S C dec))
    (fbMk0_sel (p0Q S C dec) (isP0Q S C dec) (isP0Q_iff S C dec)) q s h
  have hq := fbMk0_sel (p0Q S C dec) (isP0Q S C dec) (isP0Q_iff S C dec) q a ha
  subst hq
  refine ⟨rfl,
    ⟨0, 160, 0, S.label, _root_.Fmt.zero32, Run.firstBytes (digToBytes a.1) S.statement a.2.2⟩,
    if_pos rfl, ?_⟩
  have h0 : (stmQ S a.2.1).bind (fun st =>
        if st.size < 2 ^ 64 ∧ (a.2.2 = [] ∨ a.2.2.length = 256) then
          some (hdr160 S.label ++
              bytesToBits (_root_.Fmt.firstBytes (digToBytes a.1) st ByteArray.empty (runOf a.2.2)))
        else none) = some s := hs
  cases hst : stmQ S a.2.1 with
  | none => rw [hst] at h0; cases h0
  | some st =>
      rw [hst] at h0
      have est : st = S.statement := by
        cases hx : a.2.1 with
        | none => rw [hx] at hst; cases hst
        | some _ => rw [hx] at hst; exact (Option.some.inj hst).symm
      have h1 : (if st.size < 2 ^ 64 ∧ (a.2.2 = [] ∨ a.2.2.length = 256) then
              some (hdr160 S.label ++
                  bytesToBits
                    (_root_.Fmt.firstBytes (digToBytes a.1) st ByteArray.empty (runOf a.2.2)))
            else none) = some s := h0
      by_cases hc : st.size < 2 ^ 64 ∧ (a.2.2 = [] ∨ a.2.2.length = 256)
      · rw [if_pos hc] at h1
        rw [← Option.some.inj h1, Toy1.bits_first, est]
        exact (oStr_bits 0 160 0 S.label _root_.Fmt.zero32 _).symm
      · rw [if_neg hc] at h1
        cases h1

/-- What the coding's four partial codes write are the bits of the functions' strings, for every
description that passes the test `OKQ`, if 0 < K. -/
theorem pageQ_fit (K : ℕ) (hK : 0 < K) (h : OKQ S = true) :
    PageFit (pageQ S C dec K h) (PDS S C dec) :=
  PageFit.of (pageQ S C dec K h) (PDS S C dec) hK (chainQ_fit S C dec) rfl S.plan.salt rfl
    (leafQ_fit S C dec) (firstQ_fit S C dec K)

end Run.PQ
