-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/StratLaw.lean: StratOwes (Johnson/Prover/Print/OwesOf.lean), WHICH SPEAKS OF
THE COMPILED PROVER's STRING UNDER ONE FAMILY OF ORACLE FUNCTIONS, FROM A LAW ON THE STRATEGY's OWN
RUN AT EVERY VERIFIER's RANDOMNESS. For all data of a whole file.

Main names.
  StratLaw σ run2 run3   at every ρ, of the transcript (σ.run ρ).1: the joining round's plain part
    holds run2, the seam's is run3; the words of each written round's plain part are below the
    prime; the words of EVERY symbol of every oracle are below the prime.
  opensK_sym, reads_L, reads_R   an opening that the prover lays holds the kept oracle's symbol; so
    do the openings of a cut.
  putsLe_L, putsLe_R     a cut of two transcripts that differ by nonces alone differs so.
  old_put, stretch_lo, stretch_sh   at a written stretch: the same oracles; the same plain parts
    but for the nonces: so the words' condition goes over.
  law_cuts               the three stretches and the two silent rounds of a whole file.
  stratOwes_of_law       THE END: the prover has returned (π, τ) · StratLaw σ bc.run2 bc.run3: THEN
    StratOwes bc π. No other premise.

By: proveX_ok_iff (OnBytes/Prover/Main.lean) · proveX_putsLe (OnBytes/Prover/Nonces.lean).

Does not show: that a strategy meets StratLaw. The law asks the words of ALL symbols, read or not:
more than StratOwes spends. Nothing on acceptance, soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.OwesOf
import OnBytes.Prover.Nonces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open Rom
open _root_.Run.PQ (View SgX CK PlainOf Dn)
open Compile.Joined (JoinMsg Chains)
open _root_.Compile (Tag Opening)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃ opensL opensR WireSB.app)
open OnBytes.Maker
open OnBytes.Prover OnBytes.Prover.Print

section Gen
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem opensK_sym : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (kp : Kept lam L s)
    (rd : OPos s → Bool) (p : OPos s) (op : Opening lam (OSym s p)),
    opensK s A W kp rd p = some op → op.sym = symK s kp p
  | [], _, _, _, _, p, _, _ => nomatch p
  | r :: s, (a, A), (w, W), (kp, ks), rd, .inl p, op, h => by
    have hp : rd (.inl p) = true := opensK_some (r :: s) (a, A) (w, W) (kp, ks) rd (.inl p) op h
    simp only [opensK, hp, if_true] at h
    obtain ⟨T, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  | _ :: s, (_, A), (_, W), (_, ks), rd, .inr q, op, h =>
    opensK_sym s A W ks (fun p => rd (.inr p)) q op h

theorem reads_L : ∀ {s u : Shape}
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))) (τ : Tr (s ++ u)),
    (∀ p op, f p = some op → op.sym = τ.read p) →
    ∀ (p : OPos s) (op : Opening lam (OSym s p)), opensL f p = some op →
      op.sym = (Tr.fst τ).read p
  | _ :: _, _, _, (_, _, _), h, .inl p, op, e => h (.inl p) op e
  | _ :: _, _, f, (_, _, τ), h, .inr p, op, e =>
    reads_L (fun q => f (.inr q)) τ (fun q op e => h (.inr q) op e) p op e

theorem reads_R : ∀ {s u : Shape}
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))) (τ : Tr (s ++ u)),
    (∀ p op, f p = some op → op.sym = τ.read p) →
    ∀ (p : OPos u) (op : Opening lam (OSym u p)), opensR (s := s) f p = some op →
      op.sym = (Tr.snd (s := s) τ).read p
  | [], _, _, _, h, p, op, e => h p op e
  | _ :: s, _, f, (_, _, τ), h, p, op, e =>
    reads_R (s := s) (fun q => f (.inr q)) τ (fun q op e => h (.inr q) op e) p op e

theorem putsLe_L (cap : ℕ → ℕ) : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K s A) (V : RoundsQueryLayout lam K u B) (i : ℕ) (τ τ' : Tr (s ++ u)),
    PutsLe cap i (s ++ u) (RoundSplits.app A B) (WireSB.app W V) τ τ' →
    PutsLe cap i s A W (Tr.fst τ) (Tr.fst τ')
  | [], _, _, _, _, _, _, _, _, _ => trivial
  | _ :: _, _, (_, _), _, (_, W), V, i, (_, _, τ), (_, _, τ'), h =>
    ⟨h.1, h.2.1, h.2.2.1, putsLe_L cap W V (i + 1) τ τ' h.2.2.2⟩

theorem putsLe_R (cap : ℕ → ℕ) : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K s A) (V : RoundsQueryLayout lam K u B) (i : ℕ) (τ τ' : Tr (s ++ u)),
    PutsLe cap i (s ++ u) (RoundSplits.app A B) (WireSB.app W V) τ τ' →
    PutsLe cap (i + s.length) u B V (Tr.snd (s := s) τ) (Tr.snd (s := s) τ')
  | [], _, _, _, _, _, _, _, _, h => h
  | _ :: s, _, (_, _), _, (_, W), V, i, (_, _, τ), (_, _, τ'), h => by
    have := putsLe_R cap W V (i + 1) τ τ' h.2.2.2
    rw [List.length_cons, show i + (s.length + 1) = i + 1 + s.length by omega]
    exact this

end Gen

/-- Writing a number in leaves the plain part behind the nonce as it was. -/
theorem old_put {Cc P : Type} : ∀ (b : ℕ) (pl pl' : GPlain ℕ b P),
    (((_root_.Iop.grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr = none ∧ pl' = pl) ∨
      ∃ g n, (_root_.Iop.grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr = some g ∧
        pl' = g.put n pl) → GPlain.old pl' = GPlain.old pl
  | 0, _, _, h => by
    rcases h with ⟨-, rfl⟩ | ⟨g, n, e, -⟩
    · rfl
    · cases e
  | _ + 1, _, _, h => by
    rcases h with ⟨e, -⟩ | ⟨g, n, e, rfl⟩
    · cases e
    · obtain rfl := Option.some.inj e
      rfl

section Wire
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (cap : ℕ → ℕ)

theorem stretch_lo : ∀ (ds : List RDT) (i : ℕ) (τ τ' : Tr (uLT C ds)),
    PutsLe cap i (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) τ τ' →
    (WordsP C ds τ.plains → WordsP C ds τ'.plains) ∧ ∀ q, τ'.read q = τ.read q
  | [], _, _, _, _ => ⟨fun _ => trivial, fun q => nomatch q⟩
  | d :: ds, i, (m, _, τ), (m', _, τ'), h => by
    obtain ⟨ih1, ih2⟩ := stretch_lo ds (i + 1) τ τ' h.2.2.2
    have ho : GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) m'.2 =
        GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) m.2 :=
      old_put (Cc := C.Ch d.entry d.kind) d.entry.work m.2 m'.2 (by
        rcases h.2.2.1 with ⟨e, e'⟩ | ⟨g, n, -, e, e'⟩
        · exact Or.inl ⟨e, e'⟩
        · exact Or.inr ⟨g, n, e, e'⟩)
    refine ⟨fun hw => ⟨?_, ih1 hw.2⟩, fun q => ?_⟩
    · show CanonI d.items (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) m'.2)
      rw [ho]
      exact hw.1
    · cases q with
      | inl p =>
        show Round.rd _ m'.1 p = Round.rd _ m.1 p
        rw [h.1]
      | inr q => exact ih2 q

theorem stretch_sh : ∀ (ds : List RDT) (i : ℕ) (τ τ' : Tr (uLT C ds)),
    PutsLe cap i (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) τ τ' →
    (WordsP C ds τ.plains → WordsP C ds τ'.plains) ∧ ∀ q, τ'.read q = τ.read q
  | [], _, _, _, _ => ⟨fun _ => trivial, fun q => nomatch q⟩
  | d :: ds, i, (m, _, τ), (m', _, τ'), h => by
    obtain ⟨ih1, ih2⟩ := stretch_sh ds (i + 1) τ τ' h.2.2.2
    have ho : GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) m'.2 =
        GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) m.2 :=
      old_put (Cc := C.Ch d.entry d.kind) d.entry.work m.2 m'.2 (by
        rcases h.2.2.1 with ⟨e, e'⟩ | ⟨g, n, -, e, e'⟩
        · exact Or.inl ⟨e, e'⟩
        · exact Or.inr ⟨g, n, e, e'⟩)
    refine ⟨fun hw => ⟨?_, ih1 hw.2⟩, fun q => ?_⟩
    · show CanonI d.items (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) m'.2)
      rw [ho]
      exact hw.1
    · cases q with
      | inl p =>
        show Round.rd _ m'.1 p = Round.rd _ m.1 p
        rw [h.1]
      | inr q => exact ih2 q

variable (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- The three stretches and the two silent rounds behind the front. -/
theorem law_cuts (τ τ' : Tr (chainsOf C D tF tJ t3).sh)
    (h : PutsLe cap 0 (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wiresOf C K chal D tF tJ t3).sh τ τ') :
    ((chainsOf C D tF tJ t3).msgJ τ').2 = ((chainsOf C D tF tJ t3).msgJ τ).2 ∧
      ((chainsOf C D tF tJ t3).msg3 τ').2 = ((chainsOf C D tF tJ t3).msg3 τ).2 ∧
      (∃ i, PutsLe cap i (uLT C D.ds₁) (RoundSplits.allLocal _) (wiresLo C K chal D.ds₁)
        ((chainsOf C D tF tJ t3).tr₁ τ) ((chainsOf C D tF tJ t3).tr₁ τ')) ∧
      (∃ i, PutsLe cap i (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) _)
        (wiresSh C K chal D.ds₂) ((chainsOf C D tF tJ t3).tr₂ τ)
        ((chainsOf C D tF tJ t3).tr₂ τ')) ∧
      ∃ i, PutsLe cap i (uLT C D.ds₃) (RoundSplits.allLocal _) (wiresLo C K chal D.ds₃)
        ((chainsOf C D tF tJ t3).tr₃ τ) ((chainsOf C D tF tJ t3).tr₃ τ') := by
  have h1 := h.2.2.2
  have hJ := putsLe_R cap (wiresLo C K chal D.ds₁) (wiresOf C K chal D tF tJ t3).shJ 1 _ _ h1
  have h3 := putsLe_R cap (wiresSh C K chal D.ds₂) (wiresOf C K chal D tF tJ t3).sh₃ _ _ _
    hJ.2.2.2
  refine ⟨?_, ?_, ⟨_, putsLe_L cap (wiresLo C K chal D.ds₁) (wiresOf C K chal D tF tJ t3).shJ 1 _ _
    h1⟩, ⟨_, putsLe_L cap (wiresSh C K chal D.ds₂) (wiresOf C K chal D tF tJ t3).sh₃ _ _ _
    hJ.2.2.2⟩, ⟨_, h3.2.2.2⟩⟩
  · rcases hJ.2.2.1 with ⟨-, e⟩ | ⟨g, n, -, e, -⟩
    · exact e
    · cases e
  · rcases h3.2.2.1 with ⟨-, e⟩ | ⟨g, n, -, e, -⟩
    · exact e
    · cases e

end Wire

/-! ## The end -/

section End
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (run : Xi → View → View → View → Bool)

/-- **The law on the strategy's own run**, at every verifier's randomness. -/
structure StratLaw (σ : Strat (chainsOf C D tF tJ t3).sh Unit) (run2 run3 : ByteArray) : Prop where
  run2 : ∀ ρ, ((chainsOf C D tF tJ t3).msgJ (σ.run ρ).1).2.run = run2
  run3 : ∀ ρ, ((chainsOf C D tF tJ t3).msg3 (σ.run ρ).1).2 = run3
  words₁ : ∀ ρ, WordsP C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ (σ.run ρ).1).plains
  words₂ : ∀ ρ, WordsP C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ (σ.run ρ).1).plains
  words₃ : ∀ ρ, WordsP C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ (σ.run ρ).1).plains
  cols₁ : ∀ ρ q, ∀ w ∈ colOfSym C D.ds₁ q (((chainsOf C D tF tJ t3).tr₁ (σ.run ρ).1).read q),
    Carrier.okF w
  cols₂ : ∀ ρ q, ∀ w ∈ colOfSym C D.ds₂ q (((chainsOf C D tF tJ t3).tr₂ (σ.run ρ).1).read q),
    Carrier.okF w
  cols₃ : ∀ ρ q, ∀ w ∈ colOfSym C D.ds₃ q (((chainsOf C D tF tJ t3).tr₃ (σ.run ρ).1).read q),
    Carrier.okF w

/-- the three stretches' plain parts of a string are the transcript's, if the string's are -/
theorem stretches_of_plains (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (τ : Tr (chainsOf C D tF tJ t3).sh) (h : π.plains = τ.plains) :
    (pls₁ (wholeDesc C D tF tJ t3 silent run) π).2 = ((chainsOf C D tF tJ t3).tr₁ τ).plains ∧
      (pls₂ (wholeDesc C D tF tJ t3 silent run) π).2 = ((chainsOf C D tF tJ t3).tr₂ τ).plains ∧
      (pls₃ (wholeDesc C D tF tJ t3 silent run) π).2 = ((chainsOf C D tF tJ t3).tr₃ τ).plains := by
  unfold pls₁ pls₂ pls₃
  rw [h]
  refine ⟨?_, ?_, ?_⟩
  · show Plains.fst (s := (chainsOf C D tF tJ t3).s₁) (Tr.plains τ.2.2) = _
    rw [← Tr.plains_fst]
    rfl
  · show Plains.fst (s := (chainsOf C D tF tJ t3).s₂)
      (Plains.snd (s := (chainsOf C D tF tJ t3).s₁) (Tr.plains τ.2.2)).2 = _
    rw [← Tr.plains_snd]
    show Plains.fst (s := (chainsOf C D tF tJ t3).s₂)
      (Tr.plains ((chainsOf C D tF tJ t3).trJ τ).2.2) = _
    rw [← Tr.plains_fst]
    rfl
  · show (Plains.snd (s := (chainsOf C D tF tJ t3).s₂)
      (Plains.snd (s := (chainsOf C D tF tJ t3).s₁) (Tr.plains τ.2.2)).2).2 = _
    rw [← Tr.plains_snd]
    show (Plains.snd (s := (chainsOf C D tF tJ t3).s₂)
      (Tr.plains ((chainsOf C D tF tJ t3).trJ τ).2.2)).2 = _
    rw [← Tr.plains_snd]
    rfl

variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (t : Tag)
  (embS : (p : OPos (wholeDesc C D tF tJ t3 silent run).batch.loc.shape) →
    OSym (wholeDesc C D tF tJ t3 silent run).batch.loc.shape p → Body L)
  (embP : PlainPart (wholeDesc C D tF tJ t3 silent run).batch.loc.shape
    (wholeDesc C D tF tJ t3 silent run).batch.ann → PlainPart (shapeOf L t) (annOf L t))
  (xin : Xi → Option X) (cms : List (Dig 256)) (x : Xi)
  (y : (oneExternalString (2 ^ D.a) SgX).Str) (xt : ℕ → TreeK 256 L)
  (σ : Strat (wholeDesc C D tF tJ t3 silent run).batch.loc.shape Unit) (co : Coins 256 L)
  (bc : ByteCoins L) (cap : ℕ → ℕ) (g : Fam (typedOracleFamily 256 (K + 1) L))
  (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
  (τ : Tr (wholeDesc C D tF tJ t3 silent run).batch.loc.shape)

/-- **FROM THE LAW ON THE STRATEGY TO StratOwes AT THE PROVER's STRING.** At any coins. -/
theorem stratOwes_of_law
    (hp : (proveX t (wholeDesc C D tF tJ t3 silent run).batch
      (wqWhole C K chal D tF tJ t3 silent run) embS embP xin cms x y xt σ co cap).det g =
        .ok (π, τ))
    (h : StratLaw C D tF tJ t3 σ bc.run2 bc.run3) :
    StratOwes C D tF tJ t3 silent run bc π := by
  have hPL := proveX_putsLe t _ _ embS embP xin cms x y xt σ co cap g π τ hp
  obtain ⟨eJ, e3, ⟨i₁, p₁⟩, ⟨i₂, p₂⟩, ⟨i₃, p₃⟩⟩ := law_cuts C K chal cap D tF tJ t3 _ _ hPL
  obtain ⟨w₁, r₁⟩ := stretch_lo C K chal cap D.ds₁ i₁ _ _ p₁
  obtain ⟨w₂, r₂⟩ := stretch_sh C K chal cap D.ds₂ i₂ _ _ p₂
  obtain ⟨w₃, r₃⟩ := stretch_lo C K chal cap D.ds₃ i₃ _ _ p₃
  obtain ⟨z, -, rfl, rfl⟩ := (proveX_ok_iff t _ _ embS embP xin cms x y xt σ co cap g π τ).1 hp
  obtain ⟨-, sJ, s3⟩ := silents_of_plains C D tF tJ t3 silent run
    (finish (wholeDesc C D tF tJ t3 silent run).batch (wqWhole C K chal D tF tJ t3 silent run) x y
      xt co z) (trK _ z.2.1 z.1) rfl
  obtain ⟨q₁, q₂, q₃⟩ := stretches_of_plains C D tF tJ t3 silent run
    (finish (wholeDesc C D tF tJ t3 silent run).batch (wqWhole C K chal D tF tJ t3 silent run) x y
      xt co z) (trK _ z.2.1 z.1) rfl
  have hsym : ∀ p op, (finish (wholeDesc C D tF tJ t3 silent run).batch
      (wqWhole C K chal D tF tJ t3 silent run) x y xt co z).opens p = some op →
      op.sym = (trK _ z.2.1 z.1).read p := fun p op e =>
    (opensK_sym _ _ _ _ _ p op e).trans (read_trK _ z.2.1 z.1 p).symm
  exact
    { run2 := by rw [sJ, eJ]; exact h.run2 _
      run3 := by rw [s3, e3]; exact h.run3 _
      words₁ := by rw [q₁]; exact w₁ (h.words₁ _)
      words₂ := by rw [q₂]; exact w₂ (h.words₂ _)
      words₃ := by rw [q₃]; exact w₃ (h.words₃ _)
      cols₁ := fun q op e => by
        have := reads_L (s := (chainsOf C D tF tJ t3).c₁)
          (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) _ _ hsym (.inr q) op e
        rw [this]
        show ∀ w ∈ colOfSym C D.ds₁ q
          (((chainsOf C D tF tJ t3).tr₁ (trK _ z.2.1 z.1)).read q), Carrier.okF w
        rw [r₁ q]
        exact h.cols₁ _ q
      cols₂ := fun q op e => by
        have := reads_L (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃) _ _
          (reads_R (s := (chainsOf C D tF tJ t3).c₁)
            (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) _ _ hsym) (.inr q) op e
        rw [this]
        show ∀ w ∈ colOfSym C D.ds₂ q
          (((chainsOf C D tF tJ t3).tr₂ (trK _ z.2.1 z.1)).read q), Carrier.okF w
        rw [r₂ q]
        exact h.cols₂ _ q
      cols₃ := fun q op e => by
        have := reads_R (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃) _ _
          (reads_R (s := (chainsOf C D tF tJ t3).c₁)
            (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) _ _ hsym) (.inr q) op e
        rw [this]
        show ∀ w ∈ colOfSym C D.ds₃ q
          (((chainsOf C D tF tJ t3).tr₃ (trK _ z.2.1 z.1)).read q), Carrier.okF w
        rw [r₃ q]
        exact h.cols₃ _ q }

end End

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.opensK_sym
#print axioms Johnson.Prover.Print.reads_L
#print axioms Johnson.Prover.Print.reads_R
#print axioms Johnson.Prover.Print.putsLe_L
#print axioms Johnson.Prover.Print.putsLe_R
#print axioms Johnson.Prover.Print.old_put
#print axioms Johnson.Prover.Print.stretch_lo
#print axioms Johnson.Prover.Print.stretch_sh
#print axioms Johnson.Prover.Print.law_cuts
#print axioms Johnson.Prover.Print.StratLaw
#print axioms Johnson.Prover.Print.stretches_of_plains
#print axioms Johnson.Prover.Print.stratOwes_of_law
