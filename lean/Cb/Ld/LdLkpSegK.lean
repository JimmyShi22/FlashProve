-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpSegK.lean: the lookup, the keys' side as one block at the base: from a masked claim on
the product of λ - key to a masked claim on the multilinear extension of the keys.

Definitions, statements (in `Cb.Spec`) and proofs. The block is the product tree of
Cb/Ld/LdLkpTreeP.lean at the instance of Cb/Ld/LdLkpInst.lean, entered by a step without rounds
(Cb/Ld/LdSigStep.lean). Nothing is assumed beyond the hypotheses of the statements and whatever the
arguments hold as proofs.
The masked claim on the keys is an `MCl` (Cb/Ld/LdLkpTree.lean); a block at the base is a `BkA`
(Cb/Ld/LdLkpTreeP.lean); the joints have the form `cj` (Cb/Ld/LdLkpKit.lean).
A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core. At the base means between joints in which the tuple of messages is a part of the witness
(`BkA`, Cb/Ld/LdLkpTreeP.lean), before the lift over a signature (Cb/Ld/LdSigLift.lean).
`BkA.Good` is `GoodAt` (Cb/Ld/LdSigLift.lean) with the identity as extractor: among its fields,
completeness in the sense of `Honest.Acc` (Ior/Honest.lean) and, for each fixed tuple of messages,
round-by-round knowledge soundness (`Know`, Ior/Know.lean).
The other side of the lookup is the table's (`segT`, Cb/Ld/LdLkpSegT.lean); `chainA` in
Cb/Ld/LdLkpAsm.lean and in Cb/Ld/LdLkpAsm2.lean sets this block in a row with the others.

Main names:
  `segK`: the block: v' + 1 levels, for 2^(v'+1) keys.
  `oldK`, `rowsK`: the state with which the side was entered; the rows on the hiding coefficients of
    the levels (`TreeP.rowsAt`, Cb/Ld/LdLkpTreeRows.lean).
  `ldLkpSegK_base`: the public state that a level reads is the state with which the tree was
    entered.
  `ldLkpSegK_good`: `segK` is `BkA.Good`, that is `GoodAt` (for each fixed tuple of messages; the
    identity extracts; perfectly complete together with `plain_segK` (Cb/Ld/LdLkpFormatAsm.lean)),
    from one joint to another, for any joint R0. Both joints have the form `cj`: each is made from
    R0, which rides along, and from two claims on (state, entries), one for the honest relation, one
    for the relaxed relation. Ψ, ΨR are any predicates on (state, entries). The input joint, honest:
    Ψ, and (product of λ - key) + (form `I.fK` at the entries) = target. The output joint, honest: Ψ
    at the state of entry (`oldK`); the rows of the levels (`rowsK`); and the masked claim `topCl`
    on the keys: extension of the keys at the end point, minus the incoming form, is λ minus the
    target. The relaxed relations have ΨR in place of Ψ.
  `ldLkpSegK_rounds`: the number of rounds of `segK` is the sum over l ≤ v' of (l + 3) + 1 each.

Notation:
  `Ex`: an `ExtSpec` (Iop/InteractiveOracleProof.lean): external oracles: strings that are fixed before the protocol
    starts.
  `Kc`: a type: that of the cores.
  `M`: a type: that of the tuples of messages.
  `Wp`: a type: that of the further witness; a witness is of the type `M × Wp`.
  `St`: a type: that of the caller's states.
  `msg : M → I.J → E`: the entries are m = msg (tuple of messages) (Cb/Ld/LdLkpKit.lean).
  `pr : I.X → St`: reads the caller's state (Cb/Ld/LdLkpKit.lean).

Limits: this file says nothing on zero knowledge (the item "masked messages" of the chain). One key
(v = 0) needs no tree and is not covered. This file does not list the block's errors: `ll_segK`
(Cb/Ld/LdLkpAsmErrProofs.lean) does.
-/
import Cb.Ld.LdLkpInstProofs
import Cb.Ld.LdLkpKit
import Cb.Ld.LdSigStep

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section
variable {E : Type} [Field E] [Fintype E]

/-- the same data with 2^v keys -/
def LkInst.setV (I : LkInst E) (v : ℕ) : LkInst E := { I with v := v }

/-- The step into level 0 of the keys' tree. -/
def enterK (I : LkInst E) (tK : I.X → E) : I.X → E × (I.DK.lv 0).T.St := fun x =>
  (tK x, (x, fun _ => 0))

section
variable (I : LkInst E) (v' : ℕ) (tK : I.X → E)

/-- The keys' side. -/
def segK (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → I.J → E) :
    BkA Kc M I.X (E × ((I.setV (v' + 1)).DK.lv (v' + 1)).T.St) Ex Wp :=
  ⟨((I.setV (v' + 1)).DK.treeA Ex Wp Kc msg v').R.pre
      (fun x => some (enterK (I.setV (v' + 1)) tK x)) (ExtMap.id Ex),
    ((I.setV (v' + 1)).DK.treeA Ex Wp Kc msg v').H.pre
      (fun x => some (enterK (I.setV (v' + 1)) tK x)) (ExtMap.id Ex)
      fun o => (enterK (I.setV (v' + 1)) tK o.1, o.2),
    ((I.setV (v' + 1)).DK.treeA Ex Wp Kc msg v').P.pre
      (fun x => some (enterK (I.setV (v' + 1)) tK x)) (ExtMap.id Ex)⟩

/-- the state with which the side was entered; the rows of the levels (`rowsK`) -/
def oldK (x : E × ((I.setV (v' + 1)).DK.lv (v' + 1)).T.St) : I.X :=
  ((I.setV (v' + 1)).DK.root (v' + 1) x.2).1
def rowsK (x : E × ((I.setV (v' + 1)).DK.lv (v' + 1)).T.St) : List (Row E I.J) :=
  (I.setV (v' + 1)).DK.rowsAt (v' + 1) x.2

end
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

def ldLkpSegK_base : Prop :=
  ∀ (D : TreeP E) (l : ℕ) (s : (D.lv l).T.St), (D.lv l).base s = (D.root l s).1

/-- The keys' side. -/
def ldLkpSegK_good : Prop :=
  ∀ (I : LkInst E) (v' : ℕ) (tK : I.X → E) (Ex : ExtSpec)
      (Kc St M Wp : Type) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → I.J → E)
      (pr : I.X → St) (Ψ ΨR : I.X → (I.J → E) → Prop),
    (segK I v' tK Ex M Wp Kc msg).Good
      (cj R0 msg pr
        (fun x m =>
          Ψ x m ∧ keyProd (v' + 1) (I.key (I.st x) m) (I.lam x) + ∑ j, I.fK x j * m j = tK x)
        fun x m =>
          ΨR x m ∧ keyProd (v' + 1) (I.key (I.st x) m) (I.lam x) + ∑ j, I.fK x j * m j = tK x)
      (cj R0 msg (fun x => pr (oldK I v' x))
        (fun x m =>
          (Ψ (oldK I v' x) m ∧ RowsHold (rowsK I v' x) m) ∧
          ((I.setV (v' + 1)).topCl x).Holds (v' + 1) (I.key (I.st (oldK I v' x)) m) m) fun x m =>
            (ΨR (oldK I v' x) m ∧ RowsHold (rowsK I v' x) m) ∧
            ((I.setV (v' + 1)).topCl x).Holds (v' + 1) (I.key (I.st (oldK I v' x)) m) m)

def ldLkpSegK_rounds : Prop :=
  ∀ (I : LkInst E) (v' : ℕ) (tK : I.X → E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → I.J → E),
    (segK I v' tK Ex M Wp Kc msg).R.shape.length = ∑ l ∈ Finset.range (v' + 1), (0 + l + 3 + 1)

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpSegK_base : Spec.ldLkpSegK_base E := by
  intro D l
  induction l with
  | zero => exact fun _ => rfl
  | succ l ih => exact fun s => ih s.1.st

theorem ldLkpSegK_good : Spec.ldLkpSegK_good E := by
  intro I v' tK Ex Kc St M Wp R0 msg pr Ψ ΨR
  have g := ldLkpP_tree E (I.setV (v' + 1)).DK Ex M Wp Kc msg
    (cj R0 msg (fun s => pr s.1) (fun s m => Ψ s.1 m) fun s m => ΨR s.1 m)
    v' (ldLkpInst_stepK E (I.setV (v' + 1)))
  unfold BkA.Good at g ⊢
  have htop : ∀ (x : E × ((I.setV (v' + 1)).DK.lv (v' + 1)).T.St) (m : I.J → E),
      ((I.setV (v' + 1)).DK.lv (v' + 1)).T.SumHolds
        x (fun j => m (((I.setV (v' + 1)).DK.lv (v' + 1)).toJ j)) ↔
      ((I.setV (v' + 1)).topCl x).Holds (v' + 1) (I.key (I.st (oldK I v' x)) m) m := fun x m => by
    have h := ldLkpInst_topK E (I.setV (v' + 1)) x m
    have hb : ((I.setV (v' + 1)).DK.lv (v' + 1)).base x.2 = oldK I v' x :=
      ldLkpSegK_base E (I.setV (v' + 1)).DK (v' + 1) x.2
    have h' : ((I.setV (v' + 1)).DK.lv (v' + 1)).T.SumHolds
          x (fun j => m (((I.setV (v' + 1)).DK.lv (v' + 1)).toJ j)) ↔
        ((I.setV (v' + 1)).topCl x).Holds
          (v' + 1) (I.key (I.st (((I.setV (v' + 1)).DK.lv (v' + 1)).base x.2)) m) m := h
    rw [hb] at h'
    exact h'
  have e0 := ldLkpK_tree E (I.setV (v' + 1)).DK Ex Kc St M Wp R0 msg (fun s => pr s.1)
    (fun s m => Ψ s.1 m) (fun s m => ΨR s.1 m) 0
  have e1 : (I.setV (v' + 1)).DK.jtAt
        msg (cj R0 msg (fun s => pr s.1) (fun s m => Ψ s.1 m) fun s m => ΨR s.1 m) (v' + 1) =
      cj R0 msg (fun x => pr (oldK I v' x))
        (fun x m =>
          (Ψ (oldK I v' x) m ∧ RowsHold (rowsK I v' x) m) ∧
          ((I.setV (v' + 1)).topCl x).Holds (v' + 1) (I.key (I.st (oldK I v' x)) m) m)
        (fun x m =>
          (ΨR (oldK I v' x) m ∧ RowsHold (rowsK I v' x) m) ∧
          ((I.setV (v' + 1)).topCl x).Holds (v' + 1) (I.key (I.st (oldK I v' x)) m) m) :=
    (ldLkpK_tree E (I.setV (v' + 1)).DK Ex Kc St M Wp R0 msg (fun s => pr s.1) (fun s m => Ψ s.1 m)
        (fun s m => ΨR s.1 m) (v' + 1)).trans
      (ldLkpK_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun x m => and_congr_right fun _ => htop x m)
        (fun x m => and_congr_right fun _ => htop x m))
  rw [e0, e1] at g
  have hsum : ∀ (x : I.X) (m : I.J → E),
      ((I.setV (v' + 1)).DK.lv 0).T.SumHolds
        (enterK (I.setV (v' + 1)) tK x) (fun j => m (((I.setV (v' + 1)).DK.lv 0).toJ j)) ↔
      keyProd (v' + 1) (I.key (I.st x) m) (I.lam x) + ∑ j, I.fK x j * m j = tK x := fun x m => by
    rw [ldLkpP_sum E (I.setV (v' + 1)).DK (ldLkpInst_stepK E (I.setV (v' + 1))) 0
        (enterK (I.setV (v' + 1)) tK x) m]
    have hu : (I.setV (v' + 1)).DK.U
          (((I.setV (v' + 1)).DK.lv 0).base (enterK (I.setV (v' + 1)) tK x).2) m 0 =
        fun _ => keyProd (v' + 1) (I.key (I.st x) m) (I.lam x) :=
      funext fun θ => ldLkpInst_rootK E (I.setV (v' + 1)) x m θ
    rw [hu, Alg.mle_const]
    exact Iff.rfl
  refine goodAt_preMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _
    (enterK (I.setV (v' + 1)) tK) ?_ ?_ ?_ ?_ g
  · exact fun x y w h =>
      ⟨h.1, ⟨h.2.1, fun r hr => absurd hr List.not_mem_nil⟩, (hsum x _).mpr h.2.2⟩
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · exact fun x y w _ h => ⟨h.1, h.2.1.1, (hsum x _).mp h.2.2⟩

theorem ldLkpSegK_rounds : Spec.ldLkpSegK_rounds E := by
  intro I v' tK Ex M Wp Kc msg
  exact ldLkpP_rounds E (I.setV (v' + 1)).DK Ex M Wp Kc msg v'

end
end Cb
