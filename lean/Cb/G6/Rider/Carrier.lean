-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G6/Rider/Carrier.lean: a block whose output statement holds coordinates that are single
challenges; the general theorem for a rider on such a block.

Definitions, statements and proofs. No protocol of its own.

`Carries R β ε T r` bundles what the rule of Cb/G6/Rider/Both.lean asks of a reduction R beside its
own theorem: a `Binds` β on R's own shape (Blocks/StageBoth.lean: which round draws which
coordinate) with injective readings (`inj`); each coordinate in T is bound (`mem`); the read-off
(`rd`): whatever the verifier outputs, the reader r of the output statement gives back the bound
challenges; the rider's list of counts, 1 in a binding round and 0 elsewhere, lies below ε (`le`).
The rules `seqL`, `seqR`, `post`, `pre`, `mono` carry the bundle along a term's own make, so that a
composed term (a level, a tree, a whole lookup) gets its bundle one rule for each stage.

`goodAt_cubes`, `good_ride`: a block with such a bundle at its own counts carries any family of
riders, each member on its own cube at its own choice of different coordinates; the same term,
honest prover, extractor and numbers.

An empty use: see the warning at the two theorems and in Cb/G6/Rider/Both.lean. A use should prove
the two sentences that stand at `hollow_own` (Cb/G6/Rider/Both.lean).

Nothing here is computed by a verifier: β, T and r serve the analysis alone.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpFormatAsm
import Cb.G6.Rider.Psc

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks

/-! ## 1. Rounds that bind nothing -/

section Idle
variable {κ E : Type}

/-- Rounds that bind nothing. -/
def idle : (s : Shape) → Binds κ E s
  | [] => ()
  | _ :: s => (none, idle s)

theorem idle_vars : ∀ s : Shape, (idle s : Binds κ E s).vars = []
  | [] => rfl
  | _ :: s => idle_vars s

theorem idle_inj : ∀ s : Shape, (idle s : Binds κ E s).Inj
  | [] => trivial
  | _ :: s => idle_inj s

theorem idle_pt [DecidableEq κ] : ∀ (s : Shape) (ρ : Rho s) (z : κ → E),
    (idle s : Binds κ E s).pt ρ z = z
  | [], _, _ => rfl
  | _ :: s, (_, ρ), z => idle_pt s ρ z

theorem idle_err_le (d : κ → ℕ) : ∀ (s : Shape) (ε : Err s),
    Err.le ((idle s : Binds κ E s).err d) ε
  | [], _ => trivial
  | _ :: s, (_, ε) => ⟨Nat.zero_le _, idle_err_le d s ε⟩

/-- Two lists of rounds in a row: the rider's lists lie below the blocks' own. -/
theorem err_app_le (d : κ → ℕ) {s t : Shape} (a : Binds κ E s) (b : Binds κ E t)
    {ε : Err s} {ε' : Err t} (ha : Err.le (a.err d) ε) (hb : Err.le (b.err d) ε') :
    Err.le ((Binds.app a b).err d) (Err.app ε ε') := by
  rw [Binds.err_app]
  exact Blocks.Err.le_app ha hb

end Idle

/-! ## 2. The output statement holds coordinates that are single challenges -/

/-- The output statement of R holds coordinates each of which is a single challenge of a single
round. β says which round of R draws which coordinate; T says of which coordinates the statement
speaks; r reads the coordinates off the explicit part of the output statement; ε is the list of
counts below which the rider's list must lie. -/
structure Carries {E X₁ X₂ : Type} {E₁ E₂ : ExtSpec} (R : IOR X₁ E₁ X₂ E₂) (β : Binds ℕ E R.shape)
    (ε : Err R.shape) (T : ℕ → Prop) (r : X₂ → ℕ → E) : Prop where
  inj : β.Inj
  mem : ∀ k, T k → k ∈ β.vars
  /-- The read-off: whatever the verifier outputs, coordinate k of the reader is the challenge that
  β binds to k. -/
  rd  : ∀ x y τ x' (z : ℕ → E), R.out x y τ = some x' → ∀ k, T k → β.pt τ.rho z k = r x' k
  le  : Err.le (β.err fun _ => 1) ε

namespace Carries
variable {E X₀ X₁ X₂ X₃ : Type} {E₀ E₁ E₂ E₃ : ExtSpec} {T : ℕ → Prop}

/-- Before a block that hands the reader on. -/
theorem seqL {R₁ : IOR X₁ E₁ X₂ E₂} {β : Binds ℕ E R₁.shape} {ε₁ : Err R₁.shape} {r₂ : X₂ → ℕ → E}
    (C : Carries R₁ β ε₁ T r₂) (R₂ : IOR X₂ E₂ X₃ E₃) (ε₂ : Err R₂.shape) {r₃ : X₃ → ℕ → E}
    (hp : R₂.Passes r₂ r₃) :
    Carries (R₁.seq R₂) (Binds.app (s := R₁.shape) (t := R₂.shape) β (idle R₂.shape))
      (Err.app ε₁ ε₂) T r₃ where
  inj := Binds.Inj.app (s := R₁.shape) (t := R₂.shape) C.inj (idle_inj _)
  mem := fun k hk => by
    show k ∈ Binds.vars (s := R₁.shape ++ R₂.shape) (Binds.app β (idle R₂.shape))
    rw [Binds.vars_app]
    exact List.mem_append_left _ (C.mem k hk)
  rd := fun x y τ x' z h k hk => by
    obtain ⟨x₂, hx, hx'⟩ := Option.bind_eq_some_iff.1 ((IOR.seq_out R₁ R₂ x y τ).symm.trans h)
    show Binds.pt (s := R₁.shape ++ R₂.shape) (Binds.app β (idle R₂.shape))
      (Tr.rho (s := R₁.shape ++ R₂.shape) τ) z k = r₃ x' k
    rw [Binds.pt_app, idle_pt, ← Tr.rho_fst, C.rd x y _ x₂ z hx k hk, hp _ _ _ _ hx']
  le := err_app_le _ (s := R₁.shape) (t := R₂.shape) _ _ C.le (idle_err_le _ _ _)

/-- Behind any block. -/
theorem seqR (R₁ : IOR X₁ E₁ X₂ E₂) (ε₁ : Err R₁.shape) {R₂ : IOR X₂ E₂ X₃ E₃}
    {β : Binds ℕ E R₂.shape} {ε₂ : Err R₂.shape} {r₃ : X₃ → ℕ → E} (C : Carries R₂ β ε₂ T r₃) :
    Carries (R₁.seq R₂) (Binds.app (s := R₁.shape) (t := R₂.shape) (idle R₁.shape) β)
      (Err.app ε₁ ε₂) T r₃ where
  inj := Binds.Inj.app (s := R₁.shape) (t := R₂.shape) (idle_inj _) C.inj
  mem := fun k hk => by
    show k ∈ Binds.vars (s := R₁.shape ++ R₂.shape) (Binds.app (idle R₁.shape) β)
    rw [Binds.vars_app]
    exact List.mem_append_right _ (C.mem k hk)
  rd := fun x y τ x' z h k hk => by
    obtain ⟨x₂, _, hx'⟩ := Option.bind_eq_some_iff.1 ((IOR.seq_out R₁ R₂ x y τ).symm.trans h)
    show Binds.pt (s := R₁.shape ++ R₂.shape) (Binds.app (idle R₁.shape) β)
      (Tr.rho (s := R₁.shape ++ R₂.shape) τ) z k = r₃ x' k
    rw [Binds.pt_app, idle_pt, ← Tr.rho_snd]
    exact C.rd x₂ _ _ x' z hx' k hk
  le := err_app_le _ (s := R₁.shape) (t := R₂.shape) _ _ (idle_err_le _ _ _) C.le

/-- A map on the output statement, which may refuse. -/
theorem post {R : IOR X₁ E₁ X₂ E₂} {β : Binds ℕ E R.shape} {ε : Err R.shape} {r : X₂ → ℕ → E}
    (C : Carries R β ε T r) (φ : X₂ → Option X₃) (g : ExtMap E₂ E₃) {r₃ : X₃ → ℕ → E}
    (h : ∀ x x', φ x = some x' → ∀ k, T k → r₃ x' k = r x k) :
    Carries (R.post φ g) (β : Binds ℕ E R.shape) ε T r₃ where
  inj := C.inj
  mem := C.mem
  rd := fun x y τ x' z hx k hk => by
    obtain ⟨x₂, h1, h2⟩ := Option.bind_eq_some_iff.1 (show (R.out x y τ).bind φ = some x' from hx)
    rw [h _ _ h2 k hk]
    exact C.rd x y τ x₂ z h1 k hk
  le := C.le

/-- A map on the input statement, which may refuse. -/
theorem pre {R : IOR X₁ E₁ X₂ E₂} {β : Binds ℕ E R.shape} {ε : Err R.shape} {r : X₂ → ℕ → E}
    (C : Carries R β ε T r) (φ : X₀ → Option X₁) (g : ExtMap E₀ E₁) :
    Carries (R.pre φ g) (β : Binds ℕ E R.shape) ε T r where
  inj := C.inj
  mem := C.mem
  rd := fun x y τ x' z hx k hk => by
    obtain ⟨x₂, _, h2⟩ := Option.bind_eq_some_iff.1
      (show (φ x).bind (fun x₁ => R.out x₁ (g.map y) τ) = some x' from hx)
    exact C.rd x₂ (g.map y) τ x' z h2 k hk
  le := C.le

/-- Fewer coordinates. -/
theorem mono {R : IOR X₁ E₁ X₂ E₂} {β : Binds ℕ E R.shape} {ε : Err R.shape} {r : X₂ → ℕ → E}
    (C : Carries R β ε T r) {T' : ℕ → Prop} (h : ∀ k, T' k → T k) : Carries R β ε T' r :=
  ⟨C.inj, fun k hk => C.mem k (h k hk), fun x y τ x' z hx k hk => C.rd x y τ x' z hx k (h k hk),
      C.le⟩

end Carries

/-! ## 3. The general theorem -/

section General
variable {E : Type} [Field E] [Fintype E]

/-- The source: each member i of the family is 0 at every vertex of its own cube, of dimension g i.
-/
def OnCubes {St M ι : Type} (g : ι → ℕ) (f : ι → St → M → ℕ → E) (st : St) (m : M) : Prop :=
  ∀ i, ∀ X < 2 ^ g i, f i st m X = 0

/-- The target: the multilinear extension of each member i is 0 at its own choice sel i 0, .., sel i
(g i - 1) of coordinates of the point pt. -/
def AtCoords {St M ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ) (f : ι → St → M → ℕ → E) (st : St)
    (pt : ℕ → E) (m : M) : Prop :=
  ∀ i, ext (g i) (f i st m) (fun t => pt (sel i t)) = 0

/-- The choices: different coordinates for each member, all among those of which T speaks. -/
def SelOK {ι : Type} (T : ℕ → Prop) (g : ι → ℕ) (sel : ι → ℕ → ℕ) : Prop :=
  ∀ i, (∀ t < g i, ∀ t' < g i, sel i t = sel i t' → t = t') ∧ ∀ t < g i, T (sel i t)

theorem red_out {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} {a : Xi × Ei.Str}
    {τ : Tr R.shape} {b : Xo × Eo.Str} (h : R.red.out a τ = some b) : R.out a.1 a.2 τ = some
        b.1 := by
  obtain ⟨xo, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  exact hx

variable {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- The general theorem. A block that is `GoodAt`, and whose output statement holds coordinates that
are single challenges (`Carries`, at the block's own counts), is `GoodAt` as the same term with the
same numbers from (A and the source) to (B and the target). The arrays are read off the input
statement (fi) and off the output statement (fo), which must agree wherever the verifier outputs
(hf). Cube and choice are per member; one list of counts serves the whole family: a statement
outside the source names one member that fails, before the first challenge. Warning: A and B are
free. Wherever the input joint's `relR` without the rider (a relation that rides along, or the
block's own claim) or the output joint's `relR` already gives the source, this says nothing
(`hollow_own`, `hollow_out`, Cb/G6/Rider/Both.lean; the test of a use stands at `hollow_own`). -/
theorem goodAt_cubes {ι : Type} {R : IOR Xi Ei Xo Eo} {H : R.Honest (M × Wi) (M × Wo)}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext' : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (h : GoodAt R H A B ext' P)
    {β : Binds ℕ E R.shape} {T : ℕ → Prop} {r : Xo → ℕ → E} (C : Carries R β P.err T r)
    (g : ι → ℕ) (sel : ι → ℕ → ℕ) (hsel : SelOK T g sel)
    (fi : ι → M → Xi × Ei.Str → ℕ → E) (fo : ι → M → Xo × Eo.Str → ℕ → E)
    (hf : ∀ i m a τ b, R.red.out a τ = some b → ∀ X < 2 ^ g i, fo i m b X = fi i m a X) :
    GoodAt R H (withRider A fun m a => ∀ i, ∀ X < 2 ^ g i, fi i m a X = 0)
      (withRider B fun m b => ∀ i, ext (g i) (fo i m b) (fun t => r b.1 (sel i t)) = 0) ext' P := by
  have G := goodAt_rider h β C.inj (d := fun _ => 1)
    (fun i m a (z : ℕ → E) => ext (g i) (fi i m a) fun t => z (sel i t))
    (fun i m a => degLE_ext_comp (g i) (fi i m a) (sel i) (hsel i).1) (fun _ _ _ => 0)
    (fun m b => ∀ i, ext (g i) (fo i m b) (fun t => r b.1 (sel i t)) = 0)
    (fun m a τ b hb => forall_congr' fun i => by
      rw [ext_congr (hf i m a τ b hb)]
      rw [ext_congr_point (fun t ht =>
        (C.rd a.1 a.2 τ b.1 (fun _ => 0) (red_out hb) (sel i t) ((hsel i).2 t ht)).symm)
            (fi i m a)])
  rw [numsMax_eq P C.le] at G
  exact goodAt_congr_rider
    (fun m a => forall_congr' fun i =>
      ⟨fun hv => vanishes_ext (hsel i).1 (fun t ht => C.mem _ ((hsel i).2 t ht)) hv,
        fun hz => vanishes_ext_of_zero (sel i) _ _ hz⟩)
    (fun _ _ => Iff.rfl) G

/-- The same for a block at the base (`BkA`), the arrays read off a state that the block hands on.
Warning: A and B are free. Wherever the input joint's `relR` without the rider (a relation that
rides along, or the block's own claim) or the output joint's `relR` already gives the source, this
says nothing (`hollow_own`, `hollow_out`, Cb/G6/Rider/Both.lean; the test of a use stands at
`hollow_own`). -/
theorem good_ride {X₁ X₂ St ι : Type} {Ex : ExtSpec} {Wp : Type} {b : BkA K M X₁ X₂ Ex Wp}
    {A : IOR.Rels K X₁ Ex (M × Wp)} {B : IOR.Rels K X₂ Ex (M × Wp)} (h : b.Good A B)
    {β : Binds ℕ E b.R.shape} {T : ℕ → Prop} {r : X₂ → ℕ → E} (C : Carries b.R β b.P.err T r)
    (s₁ : X₁ → St) (s₂ : X₂ → St) (hs : b.R.Passes s₁ s₂) (g : ι → ℕ) (sel : ι → ℕ → ℕ)
    (hsel : SelOK T g sel) (f : ι → St → M → ℕ → E) :
    b.Good (withRider A fun m a => OnCubes g f (s₁ a.1) m)
      (withRider B fun m o => AtCoords g sel f (s₂ o.1) (r o.1) m) :=
  goodAt_cubes h C g sel hsel (fun i m a => f i (s₁ a.1) m) (fun i m o => f i (s₂ o.1) m)
    fun i m a τ o ho X _ => by
      show f i (s₂ o.1) m X = f i (s₁ a.1) m X
      rw [hs _ _ _ _ (red_out ho)]

end General

end Cb.Rider

#print axioms Cb.Rider.Carries.seqL
#print axioms Cb.Rider.Carries.seqR
#print axioms Cb.Rider.Carries.post
#print axioms Cb.Rider.Carries.pre
#print axioms Cb.Rider.goodAt_cubes
#print axioms Cb.Rider.good_ride
