-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ScriptAt.lean: the four ties of Law/Script.lean, each AT ONE
STAND: the tie's sentence at one run's coins k, one state s of the verifier and one stand m of the
prover's run, without the thread's sentence in front of it; and one of them at more fields.
Definitions of hypotheses, and statements by unfolding.

Not shown here. THAT A TIE HOLDS ANYWHERE. Nothing on soundness, on completeness or on any other
property.

Why. A tie of Law/Script.lean asks its sentence wherever the thread's sentence `Thr T b` holds in
front of the member. A statement that speaks at one stand, or at the stands that a parameter At
names (`ShareAt`, Law/Table.lean), wants the tie there alone: that is the lesser hypothesis, and
whoever proves a tie at reached states alone can prove it in this form.

  `K4MaskTieAt`, `K4CellsTieAt`, `K4LookTieAt`, `K4TokensTieAt`   the four sentences at (k, s, m).
  `K4LookWideAt`   the tie on what the lookup has sampled AT SIX FIELDS: the three that K4's parts
      read (zx, zk, e) and the three that the reads' tables on the lookup's planes are made of
      (shape, zb0, zb1): the verifier makes its list of tables at what the state holds, the honest
      side its reads at what `look` makes: a statement that holds the two lists together wants all
      six. `lookWide_tie`: it gives `K4LookTieAt`.
  `k4MaskTie_iff_at`, `k4CellsTie_iff_at`, `k4LookTie_iff_at`, `k4TokensTie_iff_at`: a tie of
      Law/Script.lean is its sentence at every stand at which `Thr T b` holds: by unfolding.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Script

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Claim First.S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgQ dataQ matsOfData)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)

/-- **The mask row's entry under a slot of the member is the coin that the book lent**, at one
stand: at all coins that the row spends but the last (j + 1 below their number): the last is spent
on another message's entry. The parameters: as in `K4MaskTie`. This defines a hypothesis; the
definition claims nothing. -/
def K4MaskTieAt (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub)
    (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ) (k : Coins Bk) (s : First.S)
    (m : Mid (Local W₀ Rc Xi Tr) X) : Prop :=
  ∀ a c, segAt? s = some a →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c →
    ∀ ds j, j + 1 < (spentOf _ c).length →
      (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ ds)))).mask (a.F.next + j) =
        Reading.gl.val ((spentOf _ c).getD j zeroE)

/-- **The witness's cell is the trace's**, at one stand. The parameters: as in `K4CellsTie`. This
defines a hypothesis; the definition claims nothing. -/
def K4CellsTieAt (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub)
    (tl : OnBytes.Model.HTailF2) (names : Array (Nat × String)) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) (k : Coins Bk) (s : First.S)
    (m : Mid (Local W₀ Rc Xi Tr) X) : Prop :=
  ∀ a, segAt? s = some a → ∀ ds i r c,
    i < tl.NM → i ≠ (OnBytes.Model.Layer.matIx Q.P.y).iB →
    r < (tl.mats.getD i {}).m → c < (tl.mats.getD i {}).k →
      Reading.gl.val
          (OnBytes.ofF ((k4Wit Q cells weights tokens (look Q) m.st.input).cell i r c)) =
        matsOfData tl names (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ ds)))) i r c

/-- **What the lookup has sampled, as the state holds it, is what `look` makes**, at one stand. This
defines a hypothesis; the definition claims nothing. -/
def K4LookTieAt (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub)
    (s : First.S) (m : Mid (Local W₀ Rc Xi Tr) X) : Prop :=
  ∃ g, s.lookHeard? = some g ∧ OnBytes.Desc.First.K4.seatS.look s = some g ∧
    (look Q m.st.heard).zx = g.zx ∧ (look Q m.st.heard).zk = g.zk ∧ (look Q m.st.heard).e = g.e

/-- **The same at six fields**: with the lookup's shape and its two points on the planes. This
defines a hypothesis; the definition claims nothing. -/
def K4LookWideAt (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub)
    (s : First.S) (m : Mid (Local W₀ Rc Xi Tr) X) : Prop :=
  ∃ g, s.lookHeard? = some g ∧ OnBytes.Desc.First.K4.seatS.look s = some g ∧
    (look Q m.st.heard).zx = g.zx ∧ (look Q m.st.heard).zk = g.zk ∧ (look Q m.st.heard).e = g.e ∧
    (look Q m.st.heard).shape = g.shape ∧ (look Q m.st.heard).zb0 = g.zb0 ∧
    (look Q m.st.heard).zb1 = g.zb1

/-- The six give the three. -/
theorem lookWide_tie {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub}
    {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} (h : K4LookWideAt look Q s m) :
    K4LookTieAt look Q s m := by
  obtain ⟨g, h1, h2, h3, h4, h5, _⟩ := h
  exact ⟨g, h1, h2, h3, h4, h5⟩

/-- **The tokens that the state holds are the instance's**, at one stand. This defines a hypothesis;
the definition claims nothing. -/
def K4TokensTieAt (tokens : Xi → Array Nat) (s : First.S) (m : Mid (Local W₀ Rc Xi Tr) X) : Prop :=
  s.tokv = tokens m.st.input.x

/-- `K4MaskTie` is its sentence at every stand at which the thread's sentence holds. -/
theorem k4MaskTie_iff_at (b : Nat) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (Q : K4Pub) (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ) :
    K4MaskTie T b cells weights tokens look Q own rdOf ↔
      ∀ k s m E, Thr T b k s m E → K4MaskTieAt T cells weights tokens look Q own rdOf k s m :=
  Iff.rfl

/-- `K4CellsTie` likewise. -/
theorem k4CellsTie_iff_at (b : Nat) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (Q : K4Pub) (tl : OnBytes.Model.HTailF2) (names : Array (Nat × String))
    (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ) :
    K4CellsTie T b cells weights tokens look Q tl names own rdOf ↔
      ∀ k s m E, Thr T b k s m E →
        K4CellsTieAt T cells weights tokens look Q tl names own rdOf k s m :=
  Iff.rfl

/-- `K4LookTie` likewise. -/
theorem k4LookTie_iff_at (b : Nat) (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (Q : K4Pub) :
    K4LookTie T b look Q ↔ ∀ k s m E, Thr T b k s m E → K4LookTieAt (Rc := Rc) look Q s m :=
  Iff.rfl

/-- `K4TokensTie` likewise. -/
theorem k4TokensTie_iff_at (b : Nat) (tokens : Xi → Array Nat) :
    K4TokensTie T b tokens ↔
      ∀ k s m E, Thr T b k s m E → K4TokensTieAt (W₀ := W₀) (Rc := Rc) (Tr := Tr) tokens s m :=
  Iff.rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.lookWide_tie
#print axioms ProofFile.Honest.K4.k4MaskTie_iff_at
#print axioms ProofFile.Honest.K4.k4CellsTie_iff_at
#print axioms ProofFile.Honest.K4.k4LookTie_iff_at
#print axioms ProofFile.Honest.K4.k4TokensTie_iff_at
