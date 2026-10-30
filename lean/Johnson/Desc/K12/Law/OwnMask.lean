-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OwnMask.lean: the library's law on a chain of a proximity test (the kind K12),
with the word of fresh mask rows a function of the chain's first message.

Statements and proofs. The library's law (`chain_many`, `chain_many_acc`, `chain_many_list`,
OnBytes/Slice/ManySem.lean and ManyCloses.lean) takes the word z as a letter outside the game. At a
place whose first fold sends its own mask, z is read off the chain's own first message: another
transcript has another z, so «a yes gives c.Acc q y z g b for one z at every b» could not be paid
there. No law of the library is proved again. «The prover has lost» (`Iop.Doomed`) begins with
«whatever first message the prover sends», so it is enough to show, for each first message m₀, that
the prover has lost towards «bad, or the first message is not m₀» (`doomed_by_first`); and there the
library's own law serves at z := fz m₀.
Main names:
  `doomed_by_first`, `Msg1`, `msg1`: the device, and the chain's first message.
  `chain_many_own`, `chain_many_acc_own`, `chain_many_list_own`: the three laws in that form, for
    every chain; at a chain that is a base case alone z is not read.
  `K12Condition.gives_own`: `K12Condition.gives` in that form; at a constant fz it is `gives`.
Limits: That the law of the kind gives `c.Acc` at z := fz (the first message) for a named fz, the
standard reading of the own mask's tree off the fold's first message, is not shown here. The letters
q, y and g stand outside the game. All limits of Johnson/Desc/K12/Law/ChainHolds.lean but its
(6) stand. This is a statement on the library's chain; that a yes of the block gives the chain's yes
is the law of the kind, under its own premises.

-/
import Johnson.Desc.K12.Law.ChainHolds

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open scoped ENNReal

/-- If, for every first message m₀, the prover has lost towards «bad, or the first message is not
m₀», it has lost towards bad: it must send some first message. -/
theorem doomed_by_first {r : Round} {s : Shape} (e : ℕ) (ε : Err s) (bad : Tr (r :: s) → Prop)
    (h : ∀ m₀ : r.Msg, Doomed (r :: s) (e, ε) fun τ => τ.1 = m₀ → bad τ) :
    Doomed (r :: s) (e, ε) bad := by
  intro m
  have hm := h m m
  refine le_trans (cnt_mono ?_) hm
  intro c hc hd
  exact hc (Doomed.mono s ε (fun τ hτ => hτ rfl) hd)

/-- The type of the chain's first message. -/
def Msg1 : {s : Sg} → Chain s → Type
  | _, .last _ _ dL _ _ _ _ => (wRound dL).Msg
  | _, .step _ _ _ _ _ dE _ _ _ _ _ _ _ _ _ => (wRound dE).Msg

/-- The chain's first message, off the blocks' transcripts. -/
def msg1 : {s : Sg} → (c : Chain s) → c.Bl → Msg1 c
  | _, .last _ _ _ _ _ _ _ => fun τ => τ.1
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fun b => b.1.1

/-- The library's chain_many with the word of fresh mask rows a function of the chain's first
message. -/
theorem chain_many_own {s : Sg} (c : Chain s) (h : c.Holds) (q : GE × (s.cIn.J → GE))
    (y : s.cIn.Word) (fz : Msg1 c → s.cFr.Word) (g : s.cIn.Word)
    (hno : ∀ w, ¬ s.RIn c.rad (q, y) w) (bad : Tr c.sh → Prop)
    (hp : ∀ b, c.pass b = false → bad (c.tr b))
    (H : ∀ b, ¬ c.Acc q y (fz (msg1 c b)) g b → bad (c.tr b)) : Doomed c.sh c.err bad := by
  cases c with
  | last s e dL dB fu fs εb =>
    exact chain_many _ h q y (fun _ _ => 0) g hno bad hp H
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    refine doomed_by_first _ _ bad fun m₀ => ?_
    refine chain_many (.step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next) h q y (fz m₀) g hno _
      (fun b hb _ => hp b hb) fun b hA hm => H b ?_
    have hm' : b.1.1 = m₀ := hm
    show ¬ (Chain.step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next).Acc q y (fz b.1.1) g b
    rw [hm']
    exact hA

/-- The same for a verdict (the library's chain_many_acc). -/
theorem chain_many_acc_own {s : Sg} (c : Chain s) (h : c.Holds) (q : GE × (s.cIn.J → GE))
    (y : s.cIn.Word) (fz : Msg1 c → s.cFr.Word) (g : s.cIn.Word)
    (hno : ∀ w, ¬ s.RIn c.rad (q, y) w) (acc : Tr c.sh → Bool)
    (hacc : ∀ b, acc (c.tr b) = true → c.pass b = true ∧ c.Acc q y (fz (msg1 c b)) g b) :
    Doomed c.sh c.err fun τ => acc τ = false := by
  refine chain_many_own c h q y fz g hno _ ?_ ?_
  · intro b hp
    refine Bool.eq_false_iff.2 fun ha => ?_
    rw [(hacc b ha).1] at hp
    cases hp
  · intro b hs
    exact Bool.eq_false_iff.2 fun ha => hs (hacc b ha).2

/-- The same over the list of rounds (the library's chain_many_list). -/
theorem chain_many_list_own {s : Sg} (c : Chain s) (h : c.Holds) (q : GE × (s.cIn.J → GE))
    (y : s.cIn.Word) (fz : Msg1 c → s.cFr.Word) (g : s.cIn.Word)
    (hno : ∀ w, ¬ s.RIn c.rad (q, y) w) (acc : Tr (PQ.uL (ckP .two) c.rds) → Bool)
    (hacc : ∀ b, acc (c.trL b) = true → c.Acc q y (fz (msg1 c b)) g b ∧
      PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds (c.trL b)) = true) :
    Doomed (PQ.uL (ckP .two) c.rds) c.errL fun τ => acc τ = false := by
  refine doomed_cast c.uL_rds _ _ ?_
  refine chain_many_acc_own c h q y fz g hno
    (fun τ => acc (cast (congrArg Iop.Tr c.uL_rds.symm) τ)) fun b hb => ?_
  beta_reduce at hb
  rw [c.tr_cast] at hb
  exact ⟨(c.pass_trL b).symm.trans (hacc b hb).2, (hacc b hb).1⟩

/-- What the condition of the kind K12 buys, also where the first fold sends its own mask: as
K12Condition.gives, with the word of fresh mask rows a function of the chain's first message. (A
constant function gives K12Condition.gives itself.) -/
theorem K12Condition.gives_own {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ}
    {p : VerifiableInference.Desc.K12.P12}
    {K : Codes} {εs : ℝ≥0∞} (h : K12Condition L mC mS mW rad p K εs) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      chainFrom (.at L mC mS mW rad) rest a l = some c ∧ c.rds = l.map WR.rd ∧
      H2K.JointK.stagesOf c = p.nums.stages ∧ c.rad = rad (sgOf a) ∧ c.Holds ∧ Err.Below c.err εs ∧
      ∀ (q : GE × ((sgOf a).cIn.J → GE)) (y : (sgOf a).cIn.Word) (fz : Msg1 c → (sgOf a).cFr.Word)
        (g : (sgOf a).cIn.Word), (∀ w, ¬ (sgOf a).RIn c.rad (q, y) w) →
        ∀ acc : Tr (PQ.uL (ckP .two) c.rds) → Bool,
          (∀ b, acc (c.trL b) = true → c.Acc q y (fz (msg1 c b)) g b ∧
            PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds (c.trL b)) = true) →
          Doomed (PQ.uL (ckP .two) c.rds) c.errL fun τ => acc τ = false := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6, hH, e8, _⟩ := h.gives
  exact ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6, hH, e8,
    fun q y fz g hno acc hacc => chain_many_list_own c hH q y fz g hno acc hacc⟩

end H2K.Pub
