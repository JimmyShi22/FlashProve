-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/PortS.lean: the seed that the oracle messages of one sending share.

Definitions, statements and proofs. In Johnson/Pack/PortF.lean the way to draw the seeds is a
parameter that is asked to be fair. In the block SEND (OnBytes/Iop/Send.lean) all oracle messages of
one prover's message share the seed: its point has as many coordinates as the largest cube, each
message uses the first coordinates, as many as its own cube has, and there is one factor, other than
0, for all. That is the library's `Seeds.parts` (Cb/Ld/LdSendFam.lean).
Main names:
  `bMax`, `bits_le`: the largest cube's bits among the shapes of a list.
  `splitE`, `splitE_fst`, `partE`: a point of n coordinates is its first b and the rest; the joint
    seed is a member's own seed and the rest.
  `seedsOf`, `seedsOf_sd`, `seedsOf_fair`: the joint seeds of a sending; a member's seed is the
    first coordinates of the joint point and the joint factor; they are fair
    (`ldSendFam_fair_parts`).
  `send_closed`: knowledge soundness of `ldSendFam (sigOf cs l) (seedsOf cs l)` from `MeetsAt` at
    every member.
Limits: the factor is drawn among the elements other than 0, as in `Sample.pad` with factors in the
units; no lemma here ties that to the way the verifier draws it. `bMax` is the largest cube among
the shapes of the list, which is meant to hold the sampled messages; `Send.verify` takes the largest
cube among the messages of the prover's message that have answers; no lemma here ties the two, and
nothing is said of a prover's message that also holds messages without answers. Nothing on the order
or the coding of the draws. One answer a message. Nothing on the honest prover or on hiding.
-/
import Johnson.Pack.PortF
import Cb.Ld.LdSendFamProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Cb.Ood Iop IOR Prob OnBytes.Slice

/-- A point of n coordinates: its first b, and the rest. -/
def splitE (b n : ℕ) (h : b ≤ n) : (Fin n → GE) ≃ (Fin b → GE) × (Fin (n - b) → GE) :=
  (((finCongr (show n = b + (n - b) by omega)).arrowCongr (Equiv.refl GE)).trans
    (finSumFinEquiv.symm.arrowCongr (Equiv.refl GE))).trans
    (Equiv.sumArrowEquivProdArrow (Fin b) (Fin (n - b)) GE)

theorem splitE_fst (b n : ℕ) (h : b ≤ n) (z : Fin n → GE) (t : Fin b) :
    (splitE b n h z).1 t = z (Fin.castLE h t) := rfl

/-- The joint seed: a member's own seed, and the rest. -/
def partE (b n : ℕ) (h : b ≤ n) :
    (Fin n → GE) × GEˣ ≃ ((Fin b → GE) × GEˣ) × (Fin (n - b) → GE) where
  toFun x := (((splitE b n h x.1).1, x.2), (splitE b n h x.1).2)
  invFun y := ((splitE b n h).symm (y.1.1, y.2), y.1.2)
  left_inv x := by simp
  right_inv y := by simp

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))

/-- The largest cube's bits. -/
def bMax : ℕ := (l.map fun x => bitsZ cs x.1).foldr max 0

theorem le_foldr_max : ∀ (L : List ℕ) (x : ℕ), x ∈ L → x ≤ L.foldr max 0
  | _ :: _, _, .head _ => le_max_left _ _
  | _ :: t, x, .tail _ h => le_trans (le_foldr_max t x h) (le_max_right _ _)

theorem bits_le (i : Fin l.length) : bitsZ cs (l.get i).1 ≤ bMax cs l :=
  le_foldr_max _ _ (List.mem_map.2 ⟨l.get i, List.get_mem l i, rfl⟩)

/-- The joint seeds of a sending. -/
noncomputable def seedsOf : (sigOf cs l).Seeds :=
  Sig.Seeds.parts (sigOf cs l) ((Fin (bMax cs l) → GE) × GEˣ)
    (fun i : Fin l.length => Fin (bMax cs l - bitsZ cs (l.get i).1) → GE)
    fun i => partE (bitsZ cs (l.get i).1) (bMax cs l) (bits_le cs l i)

theorem seedsOf_sd (i : Fin l.length) (z : Fin (bMax cs l) → GE) (β : GEˣ) :
    (seedsOf cs l).sd i (z, β) = ((fun t => z (Fin.castLE (bits_le cs l i) t), β) :
      (Fin (bitsZ cs (l.get i).1) → GE) × GEˣ) := rfl

theorem seedsOf_fair : (seedsOf cs l).Fair :=
  (ldSendFam_fair_parts GE (sigOf cs l) _ _ _).1

/-- Knowledge soundness of the sending, from conditions on numbers alone. -/
theorem send_closed (d Ls : Fin l.length → ℕ)
    (g : ∀ i, MeetsAt cs (l.get i).1 (l.get i).2 (d i) (Ls i)) (Kc X W W' : Type) (E₀ : ExtSpec)
    (A : Rels Kc X E₀ W) (back : (sigOf cs l).Msg → W' → W) :
    (ldSendFam (sigOf cs l) (seedsOf cs l) X E₀).red.KnowInto A.on
      ((sigOf cs l).over ((sigOf cs l).pull A back)).on A.relR
      ((sigOf cs l).over ((sigOf cs l).pull A back)).relR
      (fun _ _ w => back ((sigOf cs l).msgs w.1) w.2)
      (Cb.Pack.sendErr (sigOf cs l) (seedsOf cs l) Ls X E₀) :=
  sigOf_send cs l d Ls g (seedsOf cs l) (seedsOf_fair cs l) Kc X W W' E₀ A back

end
end Johnson.Pack

#print axioms Johnson.Pack.splitE_fst
#print axioms Johnson.Pack.seedsOf
#print axioms Johnson.Pack.seedsOf_sd
#print axioms Johnson.Pack.seedsOf_fair
#print axioms Johnson.Pack.send_closed
