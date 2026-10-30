-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageCount.lean: numbers of rounds of stages and chains, and sums over all vectors that are
sent. (Words of this library: lean/GLOSSARY.md.)

A long protocol has hundreds of rounds, so these numbers are not found by evaluating the list of
rounds. Here they are sums over the stages.
 * `EncData.sum f`: the sum of f (code, rows, row variables, role, positions read) over all vectors
   of all rounds; `EncData.sum_eq` (it is the sum over the index type of the vectors);
   `Core.Track.sum`.
 * Stages of Blocks/StageLib.lean and the masked sumcheck: the theorems whose names begin with
   rounds_ and sum_track.
-/
import Blocks.StageSide
import Blocks.Opens

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop Prob

/-! ## Rounds -/

section Rounds

variable {P E : Type} {a b c : Sorts}

/-- The number of rounds of a stage. -/
def Stage.rounds (S : Stage P E a b) : ℕ := S.B.shape.length

theorem Stage.rounds_seq (S₁ : Stage P E a b) (S₂ : Stage P E b c) :
    (S₁.seq S₂).rounds = S₁.rounds + S₂.rounds :=
  List.length_append

theorem Stage.rounds_id (a : Sorts) : (Stage.id (P := P) (E := E) a).rounds = 0 := rfl

/-- The number of rounds of a chain: the sum over its stages. -/
def Chain.rounds : {a b : Sorts} → Chain P E a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons S t => S.rounds + t.rounds

theorem Chain.rounds_stage : ∀ {a b : Sorts} (t : Chain P E a b), t.stage.rounds = t.rounds
  | _, _, .nil _ => rfl
  | _, _, .cons S t => by
      show (S.seq t.stage).rounds = S.rounds + t.rounds
      rw [Stage.rounds_seq, Chain.rounds_stage t]

end Rounds

section Enc

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem length_encShape : ∀ (s : Shape) (d : EncData F E s), (encShape s d).length = s.length
  | [], _ => rfl
  | _ :: s, (_, d) => congrArg (· + 1) (length_encShape s d)

/-! ## Sums over all vectors -/

/-- The sum of f (code, rows, row variables, role, positions read) over all vectors of all
rounds. -/
def EncData.sum (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ) : (s : Shape) → EncData F E s → ℕ
  | [], _ => 0
  | _ :: s, (e, d) =>
    (∑ a, f (e.code a) (e.rows a) (e.mrow a) (e.role a) (e.q a)) + EncData.sum f s d

variable (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ)

theorem EncData.sum_app :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t),
      EncData.sum f (s ++ t) (d.app d') = EncData.sum f s d + EncData.sum f t d'
  | [], _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (_, d), d' => by
      show _ + EncData.sum f _ (d.app d') = _ + EncData.sum f _ d + _
      rw [EncData.sum_app d d', Nat.add_assoc]

/-- It is the sum over the index type of the vectors. -/
theorem EncData.sum_eq :
    ∀ (s : Shape) (d : EncData F E s), ∑ v : VIdx s d,
        f (vcode s d v) (vrows s d v) (vmrow s d v) (vrole s d v) (vq s d v) =
      EncData.sum f s d
  | [], _ => rfl
  | _ :: s, (e, d) => by
      show ∑ v : e.A ⊕ VIdx s d, _ = _
      rw [Fintype.sum_sum_type]
      show (∑ a, f (e.code a) (e.rows a) (e.mrow a) (e.role a) (e.q a)) +
          ∑ v : VIdx s d, f (vcode s d v) (vrows s d v) (vmrow s d v) (vrole s d v) (vq s d v) = _
      rw [EncData.sum_eq s d]
      rfl

end Enc

section Track

variable {F P E : Type} [Field F] [Field E] [Algebra F E]
  {a b c : Sorts} (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ)

/-- The sum of f over the vectors that the protocol sends. -/
def Core.Track.sum {S : Core P E a b} {ra : Reads F E a} {rb : Reads F E b} (t : S.Track ra rb) :
    ℕ :=
  EncData.sum f S.B.shape t.d

theorem Core.Track.sum_seq {S₁ : Core P E a b} {S₂ : Core P E b c} {ra : Reads F E a}
    {rb : Reads F E b} {rc : Reads F E c} (t₁ : S₁.Track ra rb) (t₂ : S₂.Track rb rc) :
    (t₁.seq t₂).sum f = t₁.sum f + t₂.sum f :=
  EncData.sum_app f t₁.d t₂.d

theorem Core.Track.sum_id (ra : Reads F E a) : (Core.Track.id (P := P) ra).sum f = 0 := rfl

end Track

/-! ## Blocks/StageLib.lean; the masked sumcheck -/

section Lib

open scoped ENNReal

variable {F P E : Type} [Field F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E] [Fintype P]
  [DecidableEq P] {a b a' b' : Sorts} (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ)

theorem Stage.rounds_nameScalars
    {K : Type} [Fintype K] [DecidableEq K] (idx : K → P) (val : a.I → K → E) :
    (Stage.nameScalars (E := E) a idx val).rounds = 1 := rfl

theorem Stage.rounds_sample {I' C : Type} [Fintype C] [Nonempty C] (ok : C → Bool)
    (nx : a.I → C → I') (e : ℕ) (pBad : ℝ≥0∞) :
    (Stage.sample (P := P) (E := E) a I' C ok nx e pBad).rounds = 1 := rfl

theorem Stage.rounds_pure (g₁ : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I) :
    (Stage.pure (P := P) (E := E) g₁ g nx).rounds = 0 := rfl

theorem Stage.rounds_send {X' Z : Type} (r : Round) (p₀ : r.Plain) (msg : a.I → (P → E) → r.Orc)
    (φ : r.Orc → Z) (fx : a.X → X') :
    (Stage.send a X' Z r p₀ msg φ fx).rounds = 1 := rfl

theorem Stage.rounds_on (S : Stage P E a b) (gx : a'.X → a.X) (px : a'.X → b.X → b'.X)
    (gy : a'.Y → a.Y) (py : a'.Y → b.Y → b'.Y) (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) :
    (S.on gx px gy py ga pa).rounds = S.rounds := rfl

theorem SC.length_shape_sc {Y Ξ ι : Type} [DecidableEq E] [DecidableEq ι] (S : SC E Y P Ξ ι) :
    ∀ l : List ι, (S.sc l).shape.length = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (SC.length_shape_sc S l)

/-- The masked sumcheck has one round for each variable. -/
theorem SC.Prover.rounds_stage {Y Ξ ι A : Type} [DecidableEq E] [DecidableEq ι] {S : SC E Y P Ξ ι}
    (H : S.Prover A) (l : List ι) : (H.stage l).rounds = l.length :=
  SC.length_shape_sc S l

theorem Stage.sum_trackNameScalars
    {K : Type} [Fintype K] [DecidableEq K] (idx : K → P) (val : a.I → K → E) (ra : Reads F E a) :
    (Stage.trackNameScalars idx val ra).sum f = 0 := rfl

theorem Core.sum_trackSample
    {I' C : Type} [Fintype C] [Nonempty C] (ok : C → Bool) (nx : a.I → C → I') (ra : Reads F E a) :
    (Core.trackSample (P := P) ok nx ra).sum f = 0 := rfl

theorem Stage.sum_trackPure (g₁ : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I)
    (ra : Reads F E a) (rb : Reads F E b) (σ : rb.N → ra.N) :
    (Stage.trackPure (P := P) g₁ g nx ra rb σ).sum f = 0 := rfl

theorem Stage.sum_trackSend {X' Z : Type} {r : Round} (e : REnc F E r) (p₀ : r.Plain)
    (msg : a.I → (P → E) → r.Orc) (φ : r.Orc → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (e.A × ℕ × ℕ)) :
    (Stage.trackSend (P := P) e p₀ msg φ fx ra rb src).sum f =
      ∑ v, f (e.code v) (e.rows v) (e.mrow v) (e.role v) (e.q v) := Nat.add_zero _

theorem Core.Track.sum_on {S : Core P E a b} {ra : Reads F E a} {rb : Reads F E b}
    (t : S.Track ra rb) (gx : a'.X → a.X) (px : a'.X → b.X → b'.X) (gy : a'.Y → a.Y)
    (py : a'.Y → b.Y → b'.Y) (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) (ra' : Reads F E a')
    (rb' : Reads F E b') (κ : ra.N → ra'.N) (σ : rb'.N → ra'.N ⊕ rb.N) :
    (t.on gx px gy py ga pa ra' rb' κ σ).sum f = t.sum f := rfl

theorem SC.sum_encSc {Y Ξ ι : Type} [DecidableEq E] [DecidableEq ι] (S : SC E Y P Ξ ι) :
    ∀ l : List ι, EncData.sum f (S.sc l).shape (SC.encSc S F l) = 0
  | [] => rfl
  | _ :: l => by
      show (∑ a : Empty, _) + EncData.sum f (S.sc l).shape (SC.encSc S F l) = 0
      rw [SC.sum_encSc S l]
      rfl

theorem SC.Prover.sum_track {Y Ξ ι A : Type} [DecidableEq E] [DecidableEq ι] {S : SC E Y P Ξ ι}
    (H : S.Prover A) (l : List ι) (ra : Reads F E ⟨S.X, Y, A × (ι → E)⟩) :
    (H.track l ra).sum f = 0 :=
  SC.sum_encSc f S l

end Lib

end Blocks
