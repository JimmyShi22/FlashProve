-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ReadsBlind.lean: which positions the three files' verifiers read does not hang on the
proof-of-work test bits of the verifier's messages, nor on any plain part of a prover's message, so
on no nonce. Definitions, statements and proofs. General in the rounds' data: no size, no public
file, no honest prover occurs here.

The setting. In the compiler's second form a round's wiring data (`WireRB`,
OnBytes/TypedOracleCompiler/Iop/BatchWire.lean) may hold the data of a proof-of-work test (`GrW`): which bits of the
verifier's message are test bits, and where the prover's plain part holds the nonce.
`RoundsQueryLayout.zero s A W ρ` is the verifier randomness ρ with all test bits set to 0. The compiler's first
form asks, for privacy, five clauses of a protocol and its wire (`GrFitP`,
Compile/Batch/SpecFit.lean). Three of them speak of the verifier alone. This file shows these three,
in a form for the second form's wire, of a whole file's protocol and of the copy's file's.

What is shown.
  `BlindToWork Q W`: the three clauses, as a name: `reads` and `extReads` are the same at ρ and at
    ρ with all test bits set to 0; `reads` is the same at all plain parts.
  `old_zero_lo`, `old_zero_sh`: in a written round, local or shared, the verifier's message behind
    the test bits (`GChal.old`) is the same with the test bits set to 0.
  `drawn_zeroSL`, `drawn_zeroLo`, `drawn_zeroSh`: so what a written chain samples (`drawnSL`,
    `drawnT`) is the same.
  `zero_fst`, `zero_snd`; `rho₁_zero`, `rho₂_zero`, `rho₃_zero`: setting the test bits to 0 goes
    through rounds in a row, and through the three chains of a file: for ALL wiring data of a
    file's parts (`Wires`, OnBytes/TypedOracleCompiler/Joined/WireOf.lean).
  **`whole_blind`**: the three clauses for a whole file's protocol under its wiring data
    (`wqWhole`, OnBytes/Maker/Wire.lean), at any data D, any silent test and any decision.
  **`linkW_blind`**: the three clauses for the protocol of a copy's file, under the written wire
    data of its rounds behind ANY data of the round in front.

Limits.
- The third clause is stronger than what the first form asks: there, `reads` is to be the same at
  two plain parts that differ by a nonce written in; here it is the same at all plain parts, since
  these verifiers do not read a plain part to choose a position. It is met by unfolding.
- The two clauses that speak of the honest prover (its abort sets and its messages do not hang on
  the test bits) are not treated: no prover occurs here.
- Nothing is shown on whether a decision hangs on the test bits. By the definitions it does: the
  proof-of-work check (`GChal.pass`, Iop/Grind.lean: every test bit is 0) stands in both decisions
  (`passT`, OnBytes/Maker/Whole.lean; `passSL`, OnBytes/TypedOracleCompiler/Run/PlanQX.lean).
- At data without proof of work the first two clauses say that ρ is ρ.
- No probability, no hash function. Nothing on hiding follows from this file alone.

`BlindToWork` may be read as part of a goal (what a compiler's theorem on privacy asks of a
verifier). It is not among this library's goals, and whoever states that theorem fixes its
own premise.


-/
import OnBytes.Maker.Wire
import OnBytes.Flat.LinkSib
import Iop.GrindProofs

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Reads
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open Compile.Joined (Chains)
open TypedOracleCompiler.Run.PQ (roundS uL wireS wiresSL drawnSL)
open OnBytes.Flat (linkProtocolOfRoundData)

variable {lam K : ℕ}

/-- **The three clauses on the verifier alone.** Which positions a verifier reads, of the committed
tables (`extReads`) and of the prover's oracles (`reads`), is the same with all proof-of-work test
bits of its messages set to 0; and `reads` does not hang on the prover's plain parts. -/
structure BlindToWork {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (W : RoundsQueryLayout lam K Q.loc.shape Q.ann) : Prop where
  reads : ∀ x ρ pl, Q.loc.reads x (RoundsQueryLayout.zero Q.loc.shape Q.ann W ρ) pl = Q.loc.reads x ρ pl
  extReads : ∀ x ρ, Q.loc.extReads x (RoundsQueryLayout.zero Q.loc.shape Q.ann W ρ) = Q.loc.extReads x ρ
  plains : ∀ x ρ pl pl', Q.loc.reads x ρ pl = Q.loc.reads x ρ pl'

/-! ## 1. One round -/

/-- A verifier's message with the test bits of a test's data set to 0; itself where there are none.
-/
def zeroBy {Cc P : Type} : Option (GrW Cc P) → Cc → Cc
  | none, c => c
  | some g, c => g.set (fun _ => false) c

theorem zero_lo_eq {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hk : a.kind = .lo)
    (c : r.Chal) : w.zero c = zeroBy w.grJ c := by
  unfold TypedOracleCompiler.Iop.WireRB.zero
  rw [hk]
  cases w.grJ <;> rfl

theorem zero_sh_eq {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hk : a.kind = .sh)
    (c : r.Chal) : w.zero c = zeroBy w.gr0 c := by
  unfold TypedOracleCompiler.Iop.WireRB.zero
  rw [hk]
  cases w.gr0 <;> rfl

/-- To set the written test's bits to 0 leaves the message behind them as it was. -/
theorem old_zeroBy {Cc P : Type} : ∀ (b : ℕ) (c : GChal b Cc),
    GChal.old (zeroBy ((_root_.Iop.grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr) c) = GChal.old c
  | 0, _ => rfl
  | b + 1, c => GChal.old_mk (b + 1) (GChal.old c) fun _ => false

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- A written round that is local. -/
theorem old_zero_lo (d : TypedOracleCompiler.Run.PQ.RD) (c : (roundS C d).up.Chal) :
    GChal.old (b := d.entry.work) ((wireS C K chal d).zero c) =
      GChal.old (b := d.entry.work) c :=
  (congrArg (GChal.old (b := d.entry.work)) (zero_lo_eq (wireS C K chal d) rfl c)).trans
    (old_zeroBy (Cc := C.Ch d.entry d.kind) (P := PlainOf d.items) d.entry.work c)

/-- A written round that is shared. -/
theorem old_zero_sh (d : TypedOracleCompiler.Run.PQ.RD) (c : (roundS C d).up.Chal) :
    GChal.old (b := d.entry.work) ((TypedOracleCompiler.Slice.wireSh C K chal d).zero c) =
      GChal.old (b := d.entry.work) c :=
  (congrArg (GChal.old (b := d.entry.work))
    (zero_sh_eq (TypedOracleCompiler.Slice.wireSh C K chal d) rfl c)).trans
    (old_zeroBy (Cc := C.Ch d.entry d.kind) (P := PlainOf d.items) d.entry.work c)

/-! ## 2. A chain -/

/-- What the written rounds of a copy's file sample is the same with the test bits set to 0. -/
theorem drawn_zeroSL : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (ρ : Rho (uL C ds)),
    drawnSL C ds (RoundsQueryLayout.zero _ _ (wiresSL C K chal ds) ρ) = drawnSL C ds ρ
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
      show C.dr d.entry d.kind (GChal.old (b := d.entry.work) ((wireS C K chal d).zero c)) ::
          drawnSL C ds (RoundsQueryLayout.zero _ _ (wiresSL C K chal ds) ρ) =
        C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) :: drawnSL C ds ρ
      rw [old_zero_lo C K chal d c, drawn_zeroSL ds ρ]

/-- The same for a file's chain of local rounds. -/
theorem drawn_zeroLo : ∀ (ds : List RDT) (ρ : Rho (uLT C ds)),
    drawnT C ds (RoundsQueryLayout.zero _ _ (wiresLo C K chal ds) ρ) = drawnT C ds ρ
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
      show C.dr d.entry d.kind
            (GChal.old (b := d.entry.work) ((wireS C K chal d.toRD).zero c)) ::
          drawnT C ds (RoundsQueryLayout.zero _ _ (wiresLo C K chal ds) ρ) =
        C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) :: drawnT C ds ρ
      rw [old_zero_lo C K chal d.toRD c, drawn_zeroLo ds ρ]

/-- The same for a file's chain of shared rounds. -/
theorem drawn_zeroSh : ∀ (ds : List RDT) (ρ : Rho (uLT C ds)),
    drawnT C ds (RoundsQueryLayout.zero _ _ (wiresSh C K chal ds) ρ) = drawnT C ds ρ
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
      show C.dr d.entry d.kind (GChal.old (b := d.entry.work)
            ((TypedOracleCompiler.Slice.wireSh C K chal d.toRD).zero c)) ::
          drawnT C ds (RoundsQueryLayout.zero _ _ (wiresSh C K chal ds) ρ) =
        C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) :: drawnT C ds ρ
      rw [old_zero_sh C K chal d.toRD c, drawn_zeroSh ds ρ]

end

/-! ## 3. Rounds in a row, and the three chains of a file -/

theorem zero_fst : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B) (ρ : Rho (s ++ u)),
    Rho.fst (RoundsQueryLayout.zero (s ++ u) (RoundSplits.app A B) (WireSB.app W V) ρ) =
      RoundsQueryLayout.zero s A W (Rho.fst ρ)
  | [], _, _, _, _, _, _ => rfl
  | r :: s, _, (_, A), _, (w, W), V, (c, ρ) => by
      show ((w.zero c, Rho.fst (RoundsQueryLayout.zero _ _ (WireSB.app W V) ρ)) : r.Chal × Rho s) =
        (w.zero c, RoundsQueryLayout.zero s A W (Rho.fst ρ))
      rw [zero_fst W V ρ]

theorem zero_snd : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B) (ρ : Rho (s ++ u)),
    Rho.snd (s := s) (RoundsQueryLayout.zero (s ++ u) (RoundSplits.app A B) (WireSB.app W V) ρ) =
      RoundsQueryLayout.zero u B V (Rho.snd (s := s) ρ)
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, _, (_, _), _, (_, W), V, (_, ρ) => zero_snd W V ρ

section
variable {G : Chains} (V : Wires lam K G)

theorem rho₁_zero (ρ : Rho G.sh) :
    G.rho₁ (RoundsQueryLayout.zero G.sh G.ann V.sh ρ) = RoundsQueryLayout.zero G.s₁ _ V.W₁ (G.rho₁ ρ) :=
  zero_fst V.W₁ V.shJ ρ.2

theorem rhoJ_zero (ρ : Rho G.sh) :
    G.rhoJ (RoundsQueryLayout.zero G.sh G.ann V.sh ρ) = RoundsQueryLayout.zero G.shJ G.annJ V.shJ (G.rhoJ ρ) :=
  zero_snd V.W₁ V.shJ ρ.2

theorem rho₂_zero (ρ : Rho G.sh) :
    G.rho₂ (RoundsQueryLayout.zero G.sh G.ann V.sh ρ) = RoundsQueryLayout.zero G.s₂ _ V.W₂ (G.rho₂ ρ) := by
  unfold Compile.Joined.Chains.rho₂
  rw [rhoJ_zero V ρ]
  exact zero_fst V.W₂ V.sh₃ (G.rhoJ ρ).2

theorem rho₃_zero (ρ : Rho G.sh) :
    G.rho₃ (RoundsQueryLayout.zero G.sh G.ann V.sh ρ) = RoundsQueryLayout.zero G.s₃ _ V.W₃ (G.rho₃ ρ) := by
  unfold Compile.Joined.Chains.rho₃
  rw [rhoJ_zero V ρ]
  exact congrArg Prod.snd (zero_snd V.W₂ V.sh₃ (G.rhoJ ρ).2)

end

/-! ## 4. A whole file -/

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- What the three chains' sampled positions ask for is the same with the test bits set to 0. -/
theorem wants_zero (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    wants₁ C D tF tJ t3 (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ) =
        wants₁ C D tF tJ t3 ρ ∧
      wants₂ C D tF tJ t3 (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ) =
        wants₂ C D tF tJ t3 ρ ∧
      wants₃ C D tF tJ t3 (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ) =
        wants₃ C D tF tJ t3 ρ := by
  refine ⟨?_, ?_, ?_⟩
  · unfold wants₁
    rw [rho₁_zero (wiresOf C K chal D tF tJ t3) ρ]
    exact congrArg (wantsOf D.a D.depth D.ds₁) (drawn_zeroLo C K chal D.ds₁ _)
  · unfold wants₂
    rw [rho₂_zero (wiresOf C K chal D tF tJ t3) ρ]
    exact congrArg (wantsOf D.a D.depth D.ds₂) (drawn_zeroSh C K chal D.ds₂ _)
  · unfold wants₃
    rw [rho₃_zero (wiresOf C K chal D tF tJ t3) ρ]
    exact congrArg (wantsOf D.a D.depth D.ds₃) (drawn_zeroLo C K chal D.ds₃ _)

variable {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The three clauses for a whole file's protocol under its wiring data.** -/
theorem whole_blind :
    BlindToWork (wholeDesc C D tF tJ t3 silent run).batch
      (wqWhole C K chal D tF tJ t3 silent run).sh where
  reads := fun _ ρ _ => by
    obtain ⟨h₁, h₂, h₃⟩ := wants_zero C K chal D tF tJ t3 ρ
    show ((wants₁ C D tF tJ t3 (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ) ++
      (wants₂ C D tF tJ t3 (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ) ++
        wants₃ C D tF tJ t3 (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ))).filterMap
          (ownPosOf C D tF tJ t3)).toFinset = _
    rw [h₁, h₂, h₃]
  extReads := fun _ ρ => by
    obtain ⟨h₁, h₂, h₃⟩ := wants_zero C K chal D tF tJ t3 ρ
    show ((wants₁ C D tF tJ t3 (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ) ++
      (wants₂ C D tF tJ t3 (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ) ++
        wants₃ C D tF tJ t3 (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ))).filterMap
          (extPosOf D)).toFinset = _
    rw [h₁, h₂, h₃]
  plains := fun _ _ _ _ => rfl

end

/-! ## 5. The copy's file -/

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)

/-- **The three clauses for the protocol of a copy's file**, under the written wiring data of its
rounds, behind any data w₀ of the round in front. -/
theorem linkW_blind (w₀ : WireRB 256 (K + 1) (TypedOracleCompiler.Run.PQ.s0 C).up
      (TypedOracleCompiler.Run.PQ.s0 C).lo) :
    BlindToWork (lam := 256) (K := K + 1) (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up
      (w₀, wiresSL C K chal ds) where
  reads := fun _ ρ _ => by
    show (((TypedOracleCompiler.Run.PQ.wanted ds
      (drawnSL C ds (RoundsQueryLayout.zero _ _ (wiresSL C K chal ds) ρ.2))).filterMap _).toFinset) = _
    rw [drawn_zeroSL C K chal ds ρ.2]
  extReads := fun _ ρ => by
    show (((TypedOracleCompiler.Run.PQ.xWanted a ds xs
      (drawnSL C ds (RoundsQueryLayout.zero _ _ (wiresSL C K chal ds) ρ.2))).filterMap _).toFinset) = _
    rw [drawn_zeroSL C K chal ds ρ.2]
  plains := fun _ _ _ _ => rfl

end

end AtPublicFiles.Reads

#print axioms AtPublicFiles.Reads.old_zero_lo
#print axioms AtPublicFiles.Reads.old_zero_sh
#print axioms AtPublicFiles.Reads.drawn_zeroSL
#print axioms AtPublicFiles.Reads.drawn_zeroLo
#print axioms AtPublicFiles.Reads.drawn_zeroSh
#print axioms AtPublicFiles.Reads.zero_fst
#print axioms AtPublicFiles.Reads.zero_snd
#print axioms AtPublicFiles.Reads.rho₁_zero
#print axioms AtPublicFiles.Reads.rho₂_zero
#print axioms AtPublicFiles.Reads.rho₃_zero
#print axioms AtPublicFiles.Reads.wants_zero
#print axioms AtPublicFiles.Reads.whole_blind
#print axioms AtPublicFiles.Reads.linkW_blind
