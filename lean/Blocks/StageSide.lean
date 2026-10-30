-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageSide.lean: side conditions of a protocol built from stages: conditions on the vectors
that are sent, and on the use of the pads. (Words of this library: lean/GLOSSARY.md.)

A condition on a protocol's parameters (codes, numbers of rows, roles, numbers of positions read) is
a statement on all vectors of all rounds. A long protocol has hundreds of rounds, most of them
without vectors, so one would not prove such a statement by cases on the rounds. Here:
 * `EncData.All Q`: every vector that is sent has the property Q (of its code, number of rows,
   number of row variables, role, number of positions read). It is closed under concatenation
   (`EncData.All.app`); `Core.Track.All` carries it through stages.
 * `Stage.all_trackNameScalars`, `Core.all_trackSample`, `Stage.all_trackPure`,
   `Stage.all_trackSend`, `SC.Prover.all_track`: for stages of Blocks/StageLib.lean and the masked
   sumcheck.
 * `Chain.Within`, `Chain.padsOK_of_regions`: if `Stage.U` and `Stage.D` of each stage of a chain
   are within its region, and the regions are disjoint, the pads are used as masked form asks
   (`Chain.PadsOK`).
-/
import Blocks.SumCheckStage

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop Prob
open scoped ENNReal

/-! ## A condition on every vector -/

section All

variable {F E : Type}

/-- Every vector of every round has the property Q of its code, number of rows, number of row
variables, role and number of positions read. -/
def EncData.All (Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop) : (s : Shape) → EncData F E s → Prop
  | [], _ => True
  | _ :: s, (e, d) =>
    (∀ a, Q (e.code a) (e.rows a) (e.mrow a) (e.role a) (e.q a)) ∧ EncData.All Q s d

variable {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop}

theorem EncData.All.app :
    ∀ {s t : Shape} {d : EncData F E s} {d' : EncData F E t},
      EncData.All Q s d → EncData.All Q t d' → EncData.All Q (s ++ t) (d.app d')
  | [], _, _, _, _, h' => h'
  | _ :: _, _, (_, _), _, h, h' => ⟨h.1, EncData.All.app h.2 h'⟩

/-- `All Q`, vector by vector. -/
theorem EncData.All.apply :
    ∀ {s : Shape} {d : EncData F E s}, EncData.All Q s d →
      ∀ v : VIdx s d, Q (vcode s d v) (vrows s d v) (vmrow s d v) (vrole s d v) (vq s d v)
  | _ :: _, (_, _), h, .inl a => h.1 a
  | _ :: _, (_, _), h, .inr v => EncData.All.apply h.2 v

end All

section Track

variable {F P E : Type} [Field F] [Field E] [Algebra F E] {a b c : Sorts}
  (Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop)

/-- Every vector that the protocol sends has the property Q. -/
def Core.Track.All {S : Core P E a b} {ra : Reads F E a} {rb : Reads F E b} (t : S.Track ra rb) :
    Prop :=
  EncData.All Q S.B.shape t.d

variable {Q}

theorem Core.Track.All.seq {S₁ : Core P E a b} {S₂ : Core P E b c} {ra : Reads F E a}
    {rb : Reads F E b} {rc : Reads F E c} {t₁ : S₁.Track ra rb} {t₂ : S₂.Track rb rc}
    (h₁ : t₁.All Q) (h₂ : t₂.All Q) : (t₁.seq t₂).All Q :=
  EncData.All.app h₁ h₂

theorem Core.Track.all_id (ra : Reads F E a) : (Core.Track.id (P := P) ra).All Q := trivial

end Track

/-! ## Blocks/StageLib.lean; the masked sumcheck -/

section Lib

variable {F P E : Type} [Field F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E] [Fintype P]
  [DecidableEq P] {a b a' b' : Sorts} {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop}

/-- Masked scalars, a challenge, a stage without rounds: no vector is sent. -/
theorem Stage.all_trackNameScalars
    {K : Type} [Fintype K] [DecidableEq K] (idx : K → P) (val : a.I → K → E) (ra : Reads F E a) :
    (Stage.trackNameScalars idx val ra).All Q :=
  ⟨fun e => e.elim, trivial⟩

theorem Core.all_trackSample
    {I' C : Type} [Fintype C] [Nonempty C] (ok : C → Bool) (nx : a.I → C → I') (ra : Reads F E a) :
    (Core.trackSample (P := P) ok nx ra).All Q :=
  ⟨fun e => e.elim, trivial⟩

theorem Stage.all_trackPure (f : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I)
    (ra : Reads F E a) (rb : Reads F E b) (σ : rb.N → ra.N) :
    (Stage.trackPure (P := P) f g nx ra rb σ).All Q := trivial

/-- One prover message of vectors: the condition on these vectors. -/
theorem Stage.all_trackSend {X' Z : Type} {r : Round} (e : REnc F E r) (p₀ : r.Plain)
    (msg : a.I → (P → E) → r.Orc) (φ : r.Orc → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (e.A × ℕ × ℕ))
    (h : ∀ v, Q (e.code v) (e.rows v) (e.mrow v) (e.role v) (e.q v)) :
    (Stage.trackSend (P := P) e p₀ msg φ fx ra rb src).All Q := ⟨h, trivial⟩

/-- A stage on a part of a larger statement sends the same vectors. -/
theorem Core.Track.All.on {S : Core P E a b} {ra : Reads F E a} {rb : Reads F E b}
    {t : S.Track ra rb} (h : t.All Q) (gx : a'.X → a.X) (px : a'.X → b.X → b'.X) (gy : a'.Y → a.Y)
    (py : a'.Y → b.Y → b'.Y) (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) (ra' : Reads F E a')
    (rb' : Reads F E b') (κ : ra.N → ra'.N) (σ : rb'.N → ra'.N ⊕ rb.N) :
    (t.on gx px gy py ga pa ra' rb' κ σ).All Q := h

/-- The masked sumcheck sends no vector. -/
theorem SC.all_encSc {Y Ξ ι : Type} [DecidableEq E] [DecidableEq ι] (S : SC E Y P Ξ ι) :
    ∀ l : List ι, EncData.All Q (S.sc l).shape (SC.encSc S F l)
  | [] => trivial
  | _ :: l => ⟨fun e => e.elim, SC.all_encSc S l⟩

theorem SC.Prover.all_track {Y Ξ ι A : Type} [DecidableEq E] [DecidableEq ι] {S : SC E Y P Ξ ι}
    (H : S.Prover A) (l : List ι) (ra : Reads F E ⟨S.X, Y, A × (ι → E)⟩) : (H.track l ra).All Q :=
  SC.all_encSc S l

end Lib

/-! ## The use of the pads -/

section Pads

variable {P E : Type}

/-- `Stage.U` and `Stage.D` of each stage of the chain are within its region; the list gives the
regions, in the order of the stages. -/
def Chain.Within : {a b : Sorts} → Chain P E a b → List (Set P) → Prop
  | _, _, .nil _, _ => True
  | _, _, .cons _ _, [] => False
  | _, _, .cons S t, B :: A => S.U ⊆ B ∧ S.D ⊆ B ∧ t.Within A

theorem Chain.Within.mem_U :
    ∀ {a b : Sorts} {t : Chain P E a b} {A : List (Set P)},
      t.Within A → ∀ q ∈ t.stage.U, ∃ B ∈ A, q ∈ B
  | _, _, .nil _, _, _, _, hq => hq.elim
  | _, _, .cons _ _, _ :: _, h, q, hq => by
      rcases hq with hq | hq
      · exact ⟨_, List.mem_cons_self, h.1 hq⟩
      · obtain ⟨B, hB, hqB⟩ := Chain.Within.mem_U h.2.2 q hq
        exact ⟨B, List.mem_cons_of_mem _ hB, hqB⟩

/-- Under `Within` and pairwise disjoint regions: `Chain.PadsOK` (no two stages mask with the same
pad; no stage's plain parts depend on a pad with which a later one masks). -/
theorem Chain.padsOK_of_regions :
    ∀ {a b : Sorts} {t : Chain P E a b} {A : List (Set P)},
      t.Within A → A.Pairwise Disjoint → t.PadsOK
  | _, _, .nil _, _, _, _ => trivial
  | _, _, .cons _ _, _ :: _, h, hA => by
      have hd := List.pairwise_cons.1 hA
      refine ⟨Set.disjoint_left.2 fun q hq hq' => ?_,
        Set.disjoint_left.2 fun q hq hq' => ?_,
        Chain.padsOK_of_regions h.2.2 hd.2⟩
      · obtain ⟨B, hB, hqB⟩ := Chain.Within.mem_U h.2.2 q hq'
        exact Set.disjoint_left.1 (hd.1 B hB) (h.1 hq) hqB
      · obtain ⟨B, hB, hqB⟩ := Chain.Within.mem_U h.2.2 q hq'
        exact Set.disjoint_left.1 (hd.1 B hB) (h.2.1 hq) hqB

end Pads

end Blocks
