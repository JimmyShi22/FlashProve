-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/HonestCanon.lean: THE COMPILED PROVER's PROOF STRING OF A WHOLE FILE IS Canon
(OnBytes/Prover/Print/Canon.lean): what the reader of bytes asks of it beside Printable: as far as
that hangs on the prover: NONCES, THE LENGTHS OF SALTS AND PATHS, THE COLUMNS' WIDTHS. The words are
premises.

Main names.
  depth_le_of_treeOf, lens_opensK   an opening that the prover lays has a salt of sMT bits and a
    path no longer than the wire record's greatest depth.
  prop_L, prop_R       what holds of all openings' salts and paths holds of a cut's.
  PutIn, putIn_of_putsLe, putIn_L, putIn_R   of plain parts: in a round with a test the hashed
    component is some plain part with a number of at most cap i written in; the transcript as it was
    hashed is so (PutsLe, OnBytes/Prover/Nonces.lean); a cut of such plain parts is so.
  nonce_of, nonces_lo, nonces_sh   so at a written stretch each round's nonce is below B.
  length_colOfSym      a symbol's list of words has the width of one of the data's trees.
  canonP_of            words and nonces together: CanonP.
  canon_of_prove       THE END.

What the end asks. The prover has returned (π, τ); the byte coins' lengths, with at most 64 bytes of
a leaf's own salt; FewJ, Few0 and the wire record's laws (three premises of the prover's own theorem
yes_of_prove); every cap is below 2^64; public: the greatest depth and all widths are below 2^64.
AND THE WORDS, WHICH THE PROVER DOES NOT MAKE: the front's answers and the copy's number; the words
of each round's plain part (WordsP); the words of each opened column; at the outer places read: the
stored column's words and length, the kept leaf's salt's length, the kept tree's path's length.

Does not show: that a strategy's words are below the prime, nor a committer's. Nothing on
acceptance, soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.Honest
import OnBytes.Prover.Print.Canon
import OnBytes.Prover.Nonces
import OnBytes.Maker.WireLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open _root_.Run _root_.Run.PQ Compile.Joined Rom
open _root_.Compile (Tag Opening pathOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃ opensL opensR FewJ Few0 WireSB.app treeOf treeAt_eq_some)
open OnBytes.Maker OnBytes.Maker.Carrier
open OnBytes.Prover

/-! ## Salts' and paths' lengths -/

section Lens
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem depth_le_of_treeOf (m : ℕ) : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (R : RootsOfChain lam s) (p : OPos s) (d : ℕ) (c : Dig lam), RoundsQueryLayout.DepthLe m s A W →
    treeOf s A W R p = some (d, c) → d ≤ m
  | _ :: _, (a, _), (w, _), (rt, _), .inl p, d, c, h, e => by
    have e' : (if a.own p then TypedOracleCompiler.Joined.treeAt w.depthJ (rt.2.getD []) (w.tree p)
        else TypedOracleCompiler.Joined.treeAt w.depth0 (rt.1.getD []) (w.tree p)) = some (d, c) := e
    split at e'
    · exact h.1.2 d (List.mem_of_getElem? (treeAt_eq_some e').1)
    · exact h.1.1 d (List.mem_of_getElem? (treeAt_eq_some e').1)
  | _ :: s, (_, A), (_, W), (_, R), .inr p, d, c, h, e => depth_le_of_treeOf m s A W R p d c h.2 e

theorem lens_opensK (g : Fam (typedOracleFamily lam K L)) (sMT m : ℕ) (s : Shape) (A : RoundSplits s)
    (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L) (kp : Kept lam L s)
    (R : RootsOfChain lam s) (rd : OPos s → Bool) (hR : RoundsAt g sMT s A W embS kp R)
    (hW : RoundsQueryLayout.OKG s A W) (hD : RoundsQueryLayout.DepthLe m s A W) (p : OPos s)
    (op : Opening lam (OSym s p)) (e : opensK s A W kp rd p = some op) :
    op.salt.length = sMT ∧ op.path.length ≤ m := by
  obtain ⟨T, d, ht, hA, -, ho, -, hs⟩ :=
    look s A W embS kp R rd hR hW p (opensK_some s A W kp rd p op e)
  rw [ho] at e
  obtain rfl := Option.some.inj e
  refine ⟨hs, ?_⟩
  show (pathOf T.lv _).length ≤ m
  rw [hA.length_path]
  exact depth_le_of_treeOf m s A W R p d _ hD ht

theorem prop_L {P : Bits → List (Dig lam) → Prop} : ∀ {s u : Shape}
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))),
    (∀ p op, f p = some op → P op.salt op.path) →
    ∀ (p : OPos s) (op : Opening lam (OSym s p)), opensL f p = some op → P op.salt op.path
  | _ :: _, _, _, h, .inl p, op, e => h (.inl p) op e
  | _ :: _, _, f, h, .inr p, op, e =>
    prop_L (fun q => f (.inr q)) (fun q op e => h (.inr q) op e) p op e

theorem prop_R {P : Bits → List (Dig lam) → Prop} : ∀ {s u : Shape}
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))),
    (∀ p op, f p = some op → P op.salt op.path) →
    ∀ (p : OPos u) (op : Opening lam (OSym u p)), opensR (s := s) f p = some op →
      P op.salt op.path
  | [], _, _, h, p, op, e => h p op e
  | _ :: s, _, f, h, p, op, e =>
    prop_R (s := s) (fun q => f (.inr q)) (fun q op e => h (.inr q) op e) p op e

/-! ## Nonces -/

/-- In a round with a test the hashed component is a plain part with a number of at most cap i
written in. i: the first round's number. -/
def PutIn (cap : ℕ → ℕ) : ℕ → (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Plains s → Prop
  | _, [], _, _, _ => True
  | i, _ :: s, (a, A), (w, W), (pl, pls) =>
    (match a.kind with
      | .lo => w.grJ = none ∨ ∃ g n α, n ≤ cap i ∧ w.grJ = some g ∧ (a.plain pl).2 = g.put n α
      | .sh => w.gr0 = none ∨ ∃ g n α, n ≤ cap i ∧ w.gr0 = some g ∧ (a.plain pl).1 = g.put n α) ∧
      PutIn cap (i + 1) s A W pls

theorem putIn_of_putsLe (cap : ℕ → ℕ) : ∀ (i : ℕ) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (τ τ' : Tr s), PutsLe cap i s A W τ τ' → PutIn cap i s A W τ'.plains
  | _, [], _, _, _, _, _ => trivial
  | i, _ :: s, (a, A), (w, W), (m, c, τ), (m', c', τ'), h => by
    refine ⟨?_, putIn_of_putsLe cap (i + 1) s A W τ τ' h.2.2.2⟩
    have h3 := h.2.2.1
    show (match a.kind with
      | .lo => w.grJ = none ∨ ∃ g n α, n ≤ cap i ∧ w.grJ = some g ∧ (a.plain m'.2).2 = g.put n α
      | .sh => w.gr0 = none ∨ ∃ g n α, n ≤ cap i ∧ w.gr0 = some g ∧ (a.plain m'.2).1 = g.put n α)
    generalize a.kind = k at h3 ⊢
    cases k with
    | lo =>
      rcases h3 with ⟨e, -⟩ | ⟨g, n, hn, e, hm⟩
      · exact Or.inl e
      · exact Or.inr ⟨g, n, _, hn, e, by rw [hm, Equiv.apply_symm_apply]⟩
    | sh =>
      rcases h3 with ⟨e, -⟩ | ⟨g, n, hn, e, hm⟩
      · exact Or.inl e
      · exact Or.inr ⟨g, n, _, hn, e, by rw [hm, Equiv.apply_symm_apply]⟩

theorem putIn_L (cap : ℕ → ℕ) : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B) (i : ℕ) (pl : Plains (s ++ u)),
    PutIn cap i (s ++ u) (RoundSplits.app A B) (WireSB.app W V) pl → PutIn cap i s A W (Plains.fst pl)
  | [], _, _, _, _, _, _, _, _ => trivial
  | _ :: _, _, (_, _), _, (_, W), V, i, (_, pls), h => ⟨h.1, putIn_L cap W V (i + 1) pls h.2⟩

theorem putIn_R (cap : ℕ → ℕ) : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B) (i : ℕ) (pl : Plains (s ++ u)),
    PutIn cap i (s ++ u) (RoundSplits.app A B) (WireSB.app W V) pl →
    PutIn cap (i + s.length) u B V (Plains.snd (s := s) pl)
  | [], _, _, _, _, _, _, _, h => h
  | _ :: s, _, (_, _), _, (_, W), V, i, (_, pls), h => by
    have := putIn_R cap W V (i + 1) pls h.2
    rw [List.length_cons, show i + (s.length + 1) = i + 1 + s.length by omega]
    exact this

end Lens

/-- At the written rounds' record of a test: the nonce is the number written in; without a test it
is 0. -/
theorem nonce_of {Cc P : Type} (c B : ℕ) (hc : c < B) : ∀ (b : ℕ) (pl : GPlain ℕ b P),
    ((_root_.Iop.grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr = none ∨
      ∃ g n α, n ≤ c ∧ (_root_.Iop.grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr = some g ∧
        pl = g.put n α) → GPlain.nonce pl < B
  | 0, _, _ => Nat.lt_of_le_of_lt (Nat.zero_le c) hc
  | _ + 1, _, h => by
    rcases h with e | ⟨g, n, α, hn, e, rfl⟩
    · cases e
    · obtain rfl := Option.some.inj e
      exact Nat.lt_of_le_of_lt hn hc

/-- Each round's nonce is below B. -/
def NonceLt (C : CK) (B : ℕ) : (ds : List RDT) → Plains (uLT C ds) → Prop
  | [], _ => True
  | d :: ds, (pl, r) =>
    GPlain.nonce (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl < B ∧ NonceLt C B ds r

/-- Each round's words are below the prime. -/
def WordsP (C : CK) : (ds : List RDT) → Plains (uLT C ds) → Prop
  | [], _ => True
  | d :: ds, (pl, r) =>
    CanonI d.items (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl) ∧
      WordsP C ds r

theorem canonP_of (C : CK) : ∀ (ds : List RDT) (pl : Plains (uLT C ds)), WordsP C ds pl →
    NonceLt C (2 ^ 64) ds pl → CanonP C ds pl
  | [], _, _, _ => trivial
  | _ :: ds, (_, r), hw, hn => ⟨hw.1, hn.1, canonP_of C ds r hw.2 hn.2⟩

section Wire
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (cap : ℕ → ℕ) (B : ℕ)
  (hcap : ∀ i, cap i < B)
include hcap

theorem nonces_lo : ∀ (ds : List RDT) (i : ℕ) (pl : Plains (uLT C ds)),
    PutIn cap i (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) pl → NonceLt C B ds pl
  | [], _, _, _ => trivial
  | d :: ds, i, (pl, r), h =>
    ⟨nonce_of (cap i) B (hcap i) d.entry.work pl h.1, nonces_lo ds (i + 1) r h.2⟩

theorem nonces_sh : ∀ (ds : List RDT) (i : ℕ) (pl : Plains (uLT C ds)),
    PutIn cap i (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) pl →
    NonceLt C B ds pl
  | [], _, _, _ => trivial
  | d :: ds, i, (pl, r), h =>
    ⟨nonce_of (cap i) B (hcap i) d.entry.work pl h.1, nonces_sh ds (i + 1) r h.2⟩

end Wire

/-- A symbol's list of words has the width of one of the data's trees. -/
theorem length_colT : ∀ (ts : List Fmt.Shape) (p : PosT ts) (a : SymT ts p),
    ∃ t ∈ ts, (colT ts p a).length = t.W
  | t :: _, .inl _, _ => ⟨t, List.mem_cons_self, List.length_ofFn⟩
  | _ :: ts, .inr p, a => by
    obtain ⟨t, ht, e⟩ := length_colT ts p a
    exact ⟨t, List.mem_cons_of_mem _ ht, e⟩

theorem length_colOfSym (C : CK) : ∀ (ds : List RDT) (q : OPos (uLT C ds)) (a : OSym (uLT C ds) q),
    ∃ d ∈ ds, ∃ t ∈ d.trees, (colOfSym C ds q a).length = t.W
  | d :: _, .inl p, a => by
    obtain ⟨t, ht, e⟩ := length_colT d.trees p a
    exact ⟨d, List.mem_cons_self, t, ht, e⟩
  | _ :: ds, .inr q, a => by
    obtain ⟨d, hd, t, ht, e⟩ := length_colOfSym C ds q a
    exact ⟨d, List.mem_cons_of_mem _ hd, t, ht, e⟩

/-! ## The end -/

section End
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (run : Xi → View → View → View → Bool)
  {I X : Type} (L : BatchProtocolWithLeafBody I X) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (t : Tag)
  (embS : (p : OPos (wholeDesc C D tF tJ t3 silent run).batch.loc.shape) →
    OSym (wholeDesc C D tF tJ t3 silent run).batch.loc.shape p → Body L)
  (embP : PlainPart (wholeDesc C D tF tJ t3 silent run).batch.loc.shape
    (wholeDesc C D tF tJ t3 silent run).batch.ann → PlainPart (shapeOf L t) (annOf L t))
  (xin : Xi → Option X) (cms : List (Dig 256)) (x : Xi)
  (y : (oneExternalString (2 ^ D.a) SgX).Str) (xt : ℕ → TreeK 256 L)
  (σ : Strat (wholeDesc C D tF tJ t3 silent run).batch.loc.shape Unit) (bc : ByteCoins L)
  (cap : ℕ → ℕ) (g : Fam (typedOracleFamily 256 (K + 1) L)) (salt : ℕ)
  (s : Params.LinBindingShape) (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
  (τ : Tr (wholeDesc C D tF tJ t3 silent run).batch.loc.shape)

/-- **THE COMPILED PROVER's STRING IS Canon, THE WORDS GIVEN.** -/
theorem canon_of_prove
    (hp : (proveX t (wholeDesc C D tF tJ t3 silent run).batch
      (wqWhole C K chal D tF tJ t3 silent run) embS embP xin cms x y xt σ
      (coinsOf (chainsOf C D tF tJ t3).nJ (chainsOf C D tF tJ t3).n3 s.logLeaves bc) cap).det g =
        .ok (π, τ))
    (hfit : bc.Fit salt s) (hsalt : salt ≤ 64)
    (hJ : FewJ (wholeDesc C D tF tJ t3 silent run).batch.loc.shape
      (wholeDesc C D tF tJ t3 silent run).batch.ann (wqWhole C K chal D tF tJ t3 silent run).sh)
    (h0 : Few0 (wholeDesc C D tF tJ t3 silent run).batch.loc.shape
      (wholeDesc C D tF tJ t3 silent run).batch.ann (wqWhole C K chal D tF tJ t3 silent run).sh)
    (hw : (wqWhole C K chal D tF tJ t3 silent run).OKG)
    (hcap : ∀ i, cap i < 2 ^ 64) (hdep : maxDepthW D < 2 ^ 64)
    (hwid : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), ∀ u ∈ d.trees, u.W < 2 ^ 64)
    (hA : ∀ e ∈ (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers, Carrier.okE e.triple)
    (hn : (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers.length < 2 ^ 64)
    (hc : (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.copy < 2 ^ 64)
    (hW₁ : WordsP C D.ds₁ (pls₁ (wholeDesc C D tF tJ t3 silent run) π).2)
    (hW₂ : WordsP C D.ds₂ (pls₂ (wholeDesc C D tF tJ t3 silent run) π).2)
    (hW₃ : WordsP C D.ds₃ (pls₃ (wholeDesc C D tF tJ t3 silent run) π).2)
    (hO₁ : ∀ q op, op₁ C D tF tJ t3 silent run π q = some op →
      ∀ w ∈ colOfSym C D.ds₁ q op.sym, Carrier.okF w)
    (hO₂ : ∀ q op, op₂ C D tF tJ t3 silent run π q = some op →
      ∀ w ∈ colOfSym C D.ds₂ q op.sym, Carrier.okF w)
    (hO₃ : ∀ q op, op₃ C D tF tJ t3 silent run π q = some op →
      ∀ w ∈ colOfSym C D.ds₃ q op.sym, Carrier.okF w)
    (hX : ∀ p ∈ (wholeDesc C D tF tJ t3 silent run).batch.loc.extReads x τ.rho,
      CanonO (y p).2 ((xt ((weOne D.a).which p)).inp ((weOne D.a).leaf p)).salt
        (pathOf (xt ((weOne D.a).which p)).lv ((weOne D.a).leaf p))) :
    Canon C D tF tJ t3 silent run π := by
  have hPL := proveX_putsLe t _ _ embS embP xin cms x y xt σ _ cap g π τ hp
  obtain ⟨z, hz, rfl, rfl⟩ := (proveX_ok_iff t _ _ embS embP xin cms x y xt σ _ cap g π τ).1 hp
  have hco := fit_coinsOf bc (chainsOf C D tF tJ t3).nJ (chainsOf C D tF tJ t3).n3 salt s hfit
  have hL := chainsOf_laws C D tF tJ t3
  obtain ⟨R, hch⟩ := chain_at g (256 + 8 * salt) t cms (xin x) _ cap hco.leaf _ _ _ embS embP 0
    .first σ z hz ((chainsOf C D tF tJ t3).ann_fmt hL) hJ h0 (z.2.2.2.getD fun _ => false)
    (fun r hr => by rw [hr]; rfl)
  have hP := putIn_of_putsLe cap 0 _ _ _ _ _ hPL
  have hP1 := hP.2
  have hPJ := (putIn_R cap (wiresLo C K chal D.ds₁) (wiresOf C K chal D tF tJ t3).shJ 1 _ hP1).2
  have hP3 := (putIn_R cap (wiresSh C K chal D.ds₂) (wiresOf C K chal D tF tJ t3).sh₃ _ _ hPJ).2
  have hLen := lens_opensK g (256 + 8 * salt) (maxDepthW D) _ _
    (wqWhole C K chal D tF tJ t3 silent run).sh embS z.2.1 R
    (haveI := (wqWhole C K chal D tF tJ t3 silent run).decO
     fun p => decide (p ∈ (wholeDesc C D tF tJ t3 silent run).batch.loc.reads x z.1
      (trK _ z.2.1 z.1).plains)) hch.rounds hw.sh hw.depth
  have hO : ∀ (col : List UInt64) (sl : Bits) (pa : List (Dig 256)), (∀ w ∈ col, Carrier.okF w) →
      col.length < 2 ^ 64 → (sl.length = 256 + 8 * salt ∧ pa.length ≤ maxDepthW D) →
      CanonO col sl pa := fun col sl pa h1 h2 h3 =>
    ⟨h1, h2, by rw [h3.1]; omega, Nat.lt_of_le_of_lt h3.2 hdep⟩
  rw [rho_trK] at hX
  exact
    { answers := hA
      count := hn
      copy := hc
      plain₁ := canonP_of C _ _ hW₁ (nonces_lo C K chal cap _ hcap D.ds₁ 1 _
        (putIn_L cap (wiresLo C K chal D.ds₁) (wiresOf C K chal D tF tJ t3).shJ 1 _ hP1))
      plain₂ := canonP_of C _ _ hW₂ (nonces_sh C K chal cap _ hcap D.ds₂ _ _
        (putIn_L cap (wiresSh C K chal D.ds₂) (wiresOf C K chal D tF tJ t3).sh₃ _ _ hPJ))
      plain₃ := canonP_of C _ _ hW₃ (nonces_lo C K chal cap _ hcap D.ds₃ _ _ hP3)
      own₁ := fun q op e => by
        obtain ⟨d, hd, u, hu, el⟩ := length_colOfSym C D.ds₁ q op.sym
        exact hO _ _ _ (hO₁ q op e)
          (by rw [el]; exact hwid d (List.mem_append_left _ hd) u hu)
          (prop_L (P := fun sl pa => sl.length = 256 + 8 * salt ∧ pa.length ≤ maxDepthW D)
            (s := (chainsOf C D tF tJ t3).c₁)
            (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) _ hLen (.inr q) op e)
      own₂ := fun q op e => by
        obtain ⟨d, hd, u, hu, el⟩ := length_colOfSym C D.ds₂ q op.sym
        exact hO _ _ _ (hO₂ q op e)
          (by rw [el]
              exact hwid d (List.mem_append_right _ (List.mem_append_left _ hd)) u hu)
          (prop_L (P := fun sl pa => sl.length = 256 + 8 * salt ∧ pa.length ≤ maxDepthW D)
            (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃) _
            (prop_R (P := fun sl pa => sl.length = 256 + 8 * salt ∧ pa.length ≤ maxDepthW D)
              (s := (chainsOf C D tF tJ t3).c₁)
              (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) _ hLen) (.inr q) op e)
      own₃ := fun q op e => by
        obtain ⟨d, hd, u, hu, el⟩ := length_colOfSym C D.ds₃ q op.sym
        exact hO _ _ _ (hO₃ q op e)
          (by rw [el]
              exact hwid d (List.mem_append_right _ (List.mem_append_right _ hd)) u hu)
          (prop_R (P := fun sl pa => sl.length = 256 + 8 * salt ∧ pa.length ≤ maxDepthW D)
            (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃) _
            (prop_R (P := fun sl pa => sl.length = 256 + 8 * salt ∧ pa.length ≤ maxDepthW D)
              (s := (chainsOf C D tF tJ t3).c₁)
              (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) _ hLen) (.inr q) op e)
      ext := fun p op e => by
        have e' : (if decide (p ∈ (wholeDesc C D tF tJ t3 silent run).batch.loc.extReads x z.1) =
            true then
            some ((xt ((weOne D.a).which p)).opening ((weOne D.a).leaf p) (y p)) else none) =
            some op := e
        split at e'
        · rename_i hd
          obtain rfl := Option.some.inj e'
          exact hX p (of_decide_eq_true hd)
        · cases e' }

end End

end OnBytes.Prover.Print

#print axioms OnBytes.Prover.Print.depth_le_of_treeOf
#print axioms OnBytes.Prover.Print.lens_opensK
#print axioms OnBytes.Prover.Print.prop_L
#print axioms OnBytes.Prover.Print.prop_R
#print axioms OnBytes.Prover.Print.PutIn
#print axioms OnBytes.Prover.Print.putIn_of_putsLe
#print axioms OnBytes.Prover.Print.putIn_L
#print axioms OnBytes.Prover.Print.putIn_R
#print axioms OnBytes.Prover.Print.nonce_of
#print axioms OnBytes.Prover.Print.NonceLt
#print axioms OnBytes.Prover.Print.WordsP
#print axioms OnBytes.Prover.Print.canonP_of
#print axioms OnBytes.Prover.Print.nonces_lo
#print axioms OnBytes.Prover.Print.nonces_sh
#print axioms OnBytes.Prover.Print.length_colT
#print axioms OnBytes.Prover.Print.length_colOfSym
#print axioms OnBytes.Prover.Print.canon_of_prove
