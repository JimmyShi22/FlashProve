-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AllRows.lean: THE END OF K10's LAW, SAID OF THE PROGRAM's ROWS: at the
decoded messages EVERY row that the batching took in holds, as a vector on the arranged message.
Statements and proofs.

  `dec_ans`: what a word decodes to with a sample has the sample's answers (by the decoder's make).
  `front_all`: under `FrontAt` (Front.lean, beside this file), at whatever family m is the
    decodings: ALL typed rows that a test on the group takes in hold of the group's messages in m:
    the rows of the claim, and every member's sample rows (the library's `ldBat_rows_iff`).
  `front_program`: so, under `OrderedV` (BatTie.lean) and the arrangement's laws: for every row w of
    the program's list, by its number: `rowVec` of w, on the arranged messages of m (with any
    randomness), gives the reading of w's target (`OrderedV.holds_iff`, RowsHold.lean).
Limits. Those of Front.lean and RowsHold.lean: typed decoding; the program's row stands as the
vector `rowVec`; `OrderedV` is a premise. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.Front
import Johnson.Desc.First.Close.Law.RowsHold
import Cb.Ld.LdBatSigProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Iop IOR KObj Cb Cb.Pv Johnson.Top.H

/-- What a word decodes to with a sample has the sample's answers. -/
theorem dec_ans {K : Type} [Field K] (o : OMsg K) (f : o.Str) (σ : o.Smp) (m : o.Msg)
    (h : o.dec f σ = some m) : o.Z.val σ.1 m = σ.2 := by
  unfold OMsg.dec Ood.decMin at h
  split at h
  · next hx =>
    obtain rfl := Option.some.inj h
    exact hx.choose_spec.1.1
  · cases h

section Front
variable {K : Type} [Field K] [Fintype K] (s : Cb.Pv.Bat.Size K) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)) (F : ExtSpec)

/-- At the decoded messages all typed rows hold: the claim's and the samples'. -/
theorem front_all
    (x : ((((s.B → K) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × ((E₀.prod s.S.ext).prod F).Str)
    (h : FrontAt s A₀ F x) (m : s.S.Msg) (hm : ∀ i, s.S.decs x.1.2 x.2.1.2 i = some (m i)) :
    Slf.All (s.G.rows s.sl) (s.G.claims x.1.1.1 x.1.2) (s.G.msg m) :=
  (ldBat_rows_iff K s.B s.S s.G s.Sb s.sl x.1.1.1 x.1.2 (s.G.msg m)).2
    ⟨(h.2 m hm).1, fun a => dec_ans (s.S.om a.1) _ _ _ (hm a.1)⟩

end Front

section Program
variable {S : Sig GE} (R : RowsK S) (keep : S.O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (F : ExtSpec)

/-- **At the decoded messages every row that the batching took in holds**, as a vector on the
arranged message. -/
theorem front_program (hL : R.Sh.rho.Laws)
    (x : ((((B → GE) × (∀ b, Sb b)) × St₀) × S.Smp) × ((E₀.prod S.ext).prod F).Str)
    (h : FrontAt (R.sizeB keep Sb sl Z) A₀ F x) (m : S.Msg)
    (hm : ∀ i, S.decs x.1.2 x.2.1.2 i = some (m i))
    {N : SlotNames R} {fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J} {z : Z.D} {e : E}
    {T : Statement} {L : GroupLayout} {rows : List OnBytes.Row}
    (hO : OrderedV R Sb sl Z N fr x.1.1.1 x.1.2 z e T L rows) (r : R.G.C.Q → GE)
    (i : ℕ) (hi : i < rows.length) :
    ∑ j, rowVec N T L rows[i] j * (R.Sh.rho.up (R.G.msg m, r)).1 j = readE rows[i].target := by
  obtain ⟨ord, -, -, hl, o⟩ := OrderedV.holds_iff R Sb sl Z hL hO
  exact (o i (hl ▸ hi) (R.G.msg m, r)).1
    (front_all (R.sizeB keep Sb sl Z) A₀ F x h m hm (ord[i]'(hl ▸ hi)))

end Program

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.dec_ans
#print axioms VerifiableInference.Desc.First.Close.front_all
#print axioms VerifiableInference.Desc.First.Close.front_program
