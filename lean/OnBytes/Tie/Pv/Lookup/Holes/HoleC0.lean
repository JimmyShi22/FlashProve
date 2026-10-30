-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Holes/HoleC0.lean.
The knowledge soundness of a sub-proof's lookup, stated at the named short sumcheck blocks.

`HC` (OnBytes/Tie/Pv/Lookup/Holes/HoleC.lean) is stated for every pair of short sumcheck blocks `V`,
`VC`. The records of such blocks hold a proof of their own knowledge soundness as a field, so
whoever uses `HC` has to hand in a pair. Here the pair is the named one, `V₀` and `V₀C`
(Cb/G6/Pick.lean: the short block that leaves out the constant coefficient of each round
polynomial), which are defined for every sumcheck and rest on no hypothesis. So no letter whose
record holds a proof is left.
The named blocks complete each round polynomial by its constant coefficient. At each sumcheck of
this lookup every variable's weights sum to 1 (`asmK_eq0`, Cb/Pv/Lookup/Know/AsmKV0.lean). That is
the condition under which a named block refuses nothing (`F₀_ok`, Cb/G6/Pick.lean;
`short_red_out`, `short_red_outC`, Cb/G6/Value.lean). Where a variable's weights do not sum to 1,
these say nothing on what a named block puts out. No statement of this file compares the named
blocks with the program's verifier.
The record `A0` stays a free letter here: no statement of this file says that it is the record that
belongs to the forest `h`. Its fields St, key and tab are not read.

 * `HC₀`: for every finite field E of characteristic p, every caller's state, every record `A0` of
   the one lookup's numbers, places and orders, every forest of calls `h`, all tables `T` and key
   vectors `K`, every joint `R0` and reading `msg`: under the seven conditions on public numbers
   that the head of HoleC.lean lists, `KnowAt` (Cb/G6/Cut.lean) of the block between "each call's
   keys lie in that call's table" and "the claim on the joint keys and all rows hold", with the
   identity as extractor and the block's own errors. The errors as a list of numbers: `hC_eps`
   (OnBytes/Tie/Pv/Lookup/Holes/HoleCMore.lean [not in this library]), where `A0.oE = Fin.revPerm`.
 * `HCsig₀`: the same block over a signature `Sg`, whose messages are then the committed messages,
   with the same errors. Its form is `Know` alone (Ior/Know.lean), not `KnowAt`; all four facts
   over a signature are in OnBytes/Tie/Pv/Lookup/Holes/HoleC0Sig.lean [not in this library].
 * `hC₀ : HC₀` and `hCsig₀ : HCsig₀`: both are proved. `hCsig₀_of`: the first gives the second.

Which signature stands for `Sg` is the caller's to name. It has to hold what must be committed and
sampled before theta is drawn (before the first challenge, if there is one call): the planes of the
counts' bits, whatever the key vectors are read from, and the row of masks.

Not claimed here: what the head of HoleC.lean lists as not claimed, but for its last point (what the
short sumcheck blocks put out); that the whole block's verifier refuses nothing; that the seven
conditions hold at any forest.
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Holes.HoleC
import Cb.G6.Pick

set_option autoImplicit false

namespace Cb.Fo
open Finset Prob Cb.Lkp Cb.LdLkp Cb.LdLkp.Kn Iop IOR TWhole

/-- A sub-proof's lookup at the named short sumcheck blocks. -/
def HC₀ : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (St : Type) (A0 : LkAsmH E)
    (h : OnBytes.Model.Forest.Shape) (T : St → ℕ → ℕ → E) (K : St → (A0.J → E) → ℕ → ℕ → E)
    (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → A0.J → E),
    Port.OK h → h.NC ≤ p → h.v = A0.v' + 1 → h.d = A0.d → A0.H.lkb.Adm p →
    padsOK (A0.v' + 1) A0.d A0.pads = true → A0.n + 1 + 1 = 2 ^ A0.w →
    KnowAt ((Port.Q h T K).allK A0 (Port.several h) V₀ V₀C (Ex := Ex)).R
      (Port.jIn h T K msg R0)
      (cj (ShiftQ.ride R0) msg Prod.fst (((Port.Q h T K).asmH A0).lk.out id id)
        (((Port.Q h T K).asmH A0).lk.out id id))
      (fun _ _ _ wp => wp) ((Port.Q h T K).allK A0 (Port.several h) V₀ V₀C (Ex := Ex)).e

/-- The same over a signature: the committed messages are the signature's. -/
def HCsig₀ : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (St : Type) (A0 : LkAsmH E)
    (h : OnBytes.Model.Forest.Shape) (T : St → ℕ → ℕ → E) (K : St → (A0.J → E) → ℕ → ℕ → E)
    (Sg : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (R0 : Rels Kc St E₀ (Sg.Msg × Wp))
    (msg : Sg.Msg → A0.J → E),
    Port.OK h → h.NC ≤ p → h.v = A0.v' + 1 → h.d = A0.d → A0.H.lkb.Adm p →
    padsOK (A0.v' + 1) A0.d A0.pads = true → A0.n + 1 + 1 = 2 ^ A0.w →
    (((Port.Q h T K).allK A0 (Port.several h) V₀ V₀C (Ex := E₀)).R.keep Sg.Smp Sg.ext).red.Know
      (Sg.over (Port.jIn h T K msg R0)).on
      (Sg.over (Port.jIn h T K msg R0)).relR
      (Sg.over (cj (ShiftQ.ride R0) msg Prod.fst (((Port.Q h T K).asmH A0).lk.out id id)
        (((Port.Q h T K).asmH A0).lk.out id id))).relR
      (fun _ _ w => (w.1, w.2)) ((Port.Q h T K).allK A0 (Port.several h) V₀ V₀C (Ex := E₀)).e

theorem hC₀ : HC₀ := fun E _ _ p _ St A0 h T K Ex Kc M Wp R0 msg =>
  hC E p St A0 h T K V₀ V₀C Ex Kc M Wp R0 msg

theorem hCsig₀ : HCsig₀ := fun E _ _ p _ St A0 h T K Sg E₀ Kc Wp R0 msg =>
  hCsig E p St A0 h T K V₀ V₀C Sg E₀ Kc Wp R0 msg

/-- The form over a signature is the first form at the signature's messages, lifted: one block, one
list of errors. -/
theorem hCsig₀_of (H : HC₀) : HCsig₀ :=
  fun E _ _ p _ St A0 h T K Sg E₀ Kc Wp R0 msg hOK hp hv hd hA hP hF =>
    sigLift_know E Sg Kc _ _ Wp Wp E₀ E₀ ((Port.Q h T K).allK A0 (Port.several h) V₀ V₀C).R _ _
      (fun _ _ _ wp => wp) ((Port.Q h T K).allK A0 (Port.several h) V₀ V₀C).e
      (H E p St A0 h T K E₀ Kc Sg.Msg Wp R0 msg hOK hp hv hd hA hP hF).know

end Cb.Fo
