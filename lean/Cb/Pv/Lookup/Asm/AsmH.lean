-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Asm/AsmH.lean.
A lookup with padding, assembled from these blocks in this order: the draw of the point λ, the tie
with its first step of three values, the planes' point, the keys' tree, the table's tree, the
closing with its degrees, the test that the counts' bits are bits, the read-out.
A plane is one bit position of the counts: there are 2^w, of which the first n + 2 count (`LkB`,
Cb/Ld/LdLkp.lean, where n + 2 is W).

States: the record LkAsmH: sizes, keys, table, padding, the places of the masks, and four orders in
which sumchecks bind their variables (oK, oT for the levels of the two trees, oE for the closing, oB
for the bits). None has a default.
  the states between the blocks and the lemmas on the joints (junction1, junction2, enter_iff,
    roots_iff, rowsB_iff, out_iff);
  baseA: the assembled block. The tie's sumcheck is a letter (S : PscBk,
    Cb/Pv/Lookup/Blocks/TieF.lean); every other sumcheck is the library's (Cb/Ld/LdPsc.lean).
  asmH_base: baseA has the library's property of a good block (`BkA.Good`, Cb/Ld/LdLkpTreeP.lean)
    from "every key is a row of the table" (`Lk.inR`) to "the masked claim on the keys and all
    linear rows of the read-out hold" (`Lk.out`).
  asmH_ok: over a signature it meets `SubR.OK` (Cb/Ld/LdLkp.lean). asmH_rounds: its number of
    rounds, at the library's sumcheck.
Premises: p is the characteristic of E; the library's conditions on the sizes (Adm p); padsOK; all
planes count (n + 2 = 2^w); and for the honest side MuOnF Mu (Cb/Pv/Lookup/Blocks/HeadF.lean): where
the claim and Mu hold, the claim after λ holds at every λ.
Limits: no statement of this file compares the block with a program. Outside the tie a round of its
sumchecks sends all coefficients of the round polynomial; the lookup over a sumcheck that sends one
coefficient less is in Cb/Pv/Lookup/Know/AsmKV.lean, with knowledge soundness alone.
Terms: lean/GLOSSARY.md.

-/
import Cb.Pv.Lookup.Blocks.HeadF
import Cb.Pv.Lookup.Blocks.EndM
import Cb.Pv.Lookup.Blocks.E3Bit
import Cb.Ld.LdLkpInst2
import Cb.Ld.LdLkpSegK
import Cb.Ld.LdLkpRoot
import Cb.Ld.LdLkpFormat
import Cb.Ld.LdLkpAsmProofs
import Cb.Ld.LdLkpEndUProofs

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp Finset

noncomputable section

/-- The data of the assembled lookup. -/
structure LkAsmH (E : Type) [Field E] [Fintype E] where
  St : Type
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  v' : ℕ
  d : ℕ
  w : ℕ
  n : ℕ
  key : St → (J → E) → ℕ → E
  tab : St → ℕ → E
  bAt : ℕ → ℕ → J
  /-- the public padding; the tie's places -/
  pads : List (ℕ × ℕ)
  wAt : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → J
  cZ  : J
  cAt : ℕ → Bool → J
  wK : (l : ℕ) → PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) → J
  cK : ℕ → Bool → J
  wT : (l : ℕ) → PIdx (List.replicate (w + l) (pfCube E 2) ++ [pDummy E 2]) → J
  cT : ℕ → Bool → J
  /-- the order in which the closing binds its variables; wE: its places, for a list of variables
  with a degree each (`dgEnd`, Cb/Pv/Lookup/Blocks/EndM.lean) -/
  oE : Equiv.Perm (Fin (w + d))
  wE : PIdx (pfMix E (w + d) (dgEnd w d oE)) → J
  /-- the order in which the bits' sumcheck binds its variables -/
  oB : Equiv.Perm (Fin (w + d))
  wB : PIdx (List.replicate (w + d) (pfCube E 2) ++ [pDummy E 2]) → J
  cB : J
  /-- the orders of the levels of the two trees -/
  oK : (l : ℕ) → Equiv.Perm (Fin (0 + l))
  oT : (l : ℕ) → Equiv.Perm (Fin (w + l))

attribute [instance] LkAsmH.finJ LkAsmH.decJ

namespace LkAsmH
variable {E : Type} [Field E] [Fintype E] (A : LkAsmH E)

/-- the head's data -/
def H : LkHeadF E :=
  { St := A.St, J := A.J, v := A.v' + 1, d := A.d, w := A.w, n := A.n, key := A.key, tab := A.tab,
    bAt := A.bAt, pads := A.pads, wAt := A.wAt, cZ := A.cZ, cAt := A.cAt }

/-- the explicit part after the head; (state, λ) read off it -/
abbrev X2 : Type := E × (A.H.tie.lv (A.n + 1)).T.St
def b2 (x : A.X2) : A.St × E := (A.H.tie.lv (A.n + 1)).base x.2

/-- form and target of the masked claim on the product of the keys -/
def fK (x : A.X2) : A.J → E := fun j => if j = A.cZ then (A.H.tie.bK A.n x.2).1 else 0
def tK (x : A.X2) : E := (A.H.tie.bK A.n x.2).2

/-- Forms and targets of the claims on the products of the table: at or below n (made by the
tie's steps), at n + 1 (the tie's open claim), above (no form, target 1) -/
def formT (x : A.X2) (θ : Fin (A.w + 0) → Bool) : A.J → E :=
  if numLE θ < A.n + 1 then
    fun j => if j = A.cAt (numLE θ) true then (A.H.tie.bT A.n x.2 (numLE θ)).1 else 0
  else if numLE θ = A.n + 1 then fun j => if j = A.cAt A.n false then A.H.tie.be A.n x.2 else 0
  else 0
def tgtT (x : A.X2) (θ : Fin (A.w + 0) → Bool) : E :=
  if numLE θ < A.n + 1 then (A.H.tie.bT A.n x.2 (numLE θ)).2
  else if numLE θ = A.n + 1 then x.1 else 1

/-- the table's data over the state after the head: for the point -/
def I1 : LkInst E :=
  { X := A.X2, St := A.St, st := fun x => (A.b2 x).1, lam := fun x => (A.b2 x).2, J := A.J,
    v := A.v' + 1, d := A.d, w := A.w, key := A.key, tab := A.tab, bAt := A.bAt, fK := A.fK,
    formT := A.formT, wK := A.wK, cK := A.cK, wT := A.wT, cT := A.cT, oK := A.oK, oT := A.oT }

/-- the point for the table's products -/
def R : RootP E := ⟨A.I1.DT2 (A.n + 1), A.formT, A.tgtT⟩

/-- the explicit part after the point: (target, (state after the head, point)) -/
abbrev XR : Type := E × ((A.I1.DT2 (A.n + 1)).lv 0).T.St
def oR (x : A.XR) : A.X2 := x.2.1

/-- the keys' side, over the state after the point -/
def IK : LkInst E :=
  { X := A.XR, St := A.St, st := fun x => (A.b2 (A.oR x)).1,
    lam := fun x => (A.b2 (A.oR x)).2, J := A.J, v := A.v' + 1, d := A.d, w := A.w,
    key := A.key, tab := A.tab, bAt := A.bAt, fK := fun x => A.fK (A.oR x),
    formT := fun _ _ _ => 0, wK := A.wK, cK := A.cK, wT := A.wT, cT := A.cT, oK := A.oK, oT := A.oT
        }

/-- the explicit part after the keys' side; the explicit part after the point read off it -/
abbrev X4 : Type := E × ((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).T.St
def o4 (x : A.X4) : A.XR := oldK A.IK A.v' x

/-- the table's forest, over the state after the keys' side -/
def IT : LkInst E :=
  { X := A.X4, St := A.St, st := fun x => (A.b2 (A.oR (A.o4 x))).1,
    lam := fun x => (A.b2 (A.oR (A.o4 x))).2, J := A.J, v := A.v' + 1, d := A.d, w := A.w,
    key := A.key, tab := A.tab, bAt := A.bAt, fK := fun _ _ => 0,
    formT := fun x => A.formT (A.oR (A.o4 x)), wK := A.wK, cK := A.cK, wT := A.wT, cT := A.cT,
    oK := A.oK, oT := A.oT }

abbrev D : TreeP E := A.IT.DT2 (A.n + 1)

/-- the step without rounds into level 0 of the forest: target and point as they were left by the
point's round -/
def enterT (x : A.X4) : E × (A.D.lv 0).T.St := ((A.o4 x).1, (x, (A.o4 x).2.2))

instance instDecIT : DecidableEq A.IT.J := A.decJ

/-- the closing, where no map is revealed (`PscPar.core`, Cb/Ld/LdPsc.lean); the bit test (its
states: the closing's end claims) -/
def En : LkEndM E := A.IT.endM (A.n + 1) A.oE A.wE
def Bt : LkBitP E := A.IT.bitBP A.En.par.Mid A.oB A.wB A.cB

abbrev XE : Type := A.En.par.Mid
abbrev XB : Type := A.Bt.zc.next.par.Out

/-- the closing's end claim, and the state after the keys' side, read off the last explicit part -/
def outE (o : A.XB) : A.XE := o.st.1
def oldT (o : A.XB) : A.X4 := (A.D.root A.d (A.outE o).st).1

/-- The pin: the multiplicities sum to the number of keys that are not padding, as a row. -/
def numRow : Row E A.J := A.H.numRowF

/-- the rows of the tie, of the keys' side, of the table's side -/
def rows2 (x : A.X2) : List (Row E A.J) := A.H.tie.rowsAt (A.n + 1) x.2
def rows4 (x : A.X4) : List (Row E A.J) := rowsK A.IK A.v' x
def rowsB (o : A.XB) : List (Row E A.J) :=
  A.D.rowsAt A.d (A.outE o).st ++
  [⟨A.En.par.slU A.En.rowB (A.En.outOf (A.outE o)), A.En.par.tU (A.En.outOf (A.outE o))⟩,
    ⟨A.Bt.zc.next.par.slU (fun _ b => b.elim) o, A.Bt.zc.next.par.tU o⟩,
    ⟨A.Bt.zc.next.par.slE A.Bt.rowA () o, o.vals ()⟩]

/-- the masked claim on the keys -/
def clK (x : A.X4) : MCl E A.J := (A.IK.setV (A.v' + 1)).topCl x

/-- The read-out. -/
def rd (o : A.XB) : TX A.St E A.J :=
  ((A.b2 (A.oR (A.o4 (A.oldT o)))).1,
    A.clK (A.oldT o),
    A.rows2 (A.oR (A.o4 (A.oldT o))) ++ (A.rows4 (A.oldT o) ++ (A.rowsB o ++ [A.numRow])))

/-- the lookup claim, on entries -/
def lk : Lk E A.St (A.J → E) := ⟨A.v' + 1, A.d, A.key, A.tab, fun _ _ => True⟩

section
variable (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) (S : PscBk E Ex M Wp Kc)

/-- the keys' side, then the step into the forest; the levels below l -/
def forest : (l : ℕ) → BkA Kc M A.XR (E × (A.D.lv l).T.St) Ex Wp
  | 0 => (segK A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc msg).postM A.enterT
  | l + 1 => (forest l).seq (A.D.levA Ex Wp Kc msg l)

/-- the closing; the bit test -/
def endA : BkA Kc M (E × (A.D.lv A.d).T.St) A.XE Ex Wp :=
  ⟨A.En.par.core Ex, A.En.par.honC Ex fun w => msg w.1, A.En.par.numsC Ex Kc⟩
def bitA : BkA Kc M A.XE A.XB Ex Wp :=
  ⟨A.Bt.zc.toIn.chainAt Ex, A.Bt.zc.toIn.chainAtH Ex M Wp msg, A.Bt.zc.toIn.chainAtN Ex Kc⟩

/-- the chain before the read-out -/
def chainA : BkA Kc M A.St A.XB Ex Wp :=
  ((((A.H.headA msg S).seq (A.R.rootA Ex M Wp Kc)).seq (A.forest Ex M Wp Kc msg A.d)).seq
      (A.endA Ex M Wp Kc msg)).seq
    (A.bitA Ex M Wp Kc msg)

/-- The lookup at the base. -/
def baseA : BkA Kc M A.St (TX A.St E A.J) Ex Wp := (A.chainA Ex M Wp Kc msg S).postM A.rd

end

/-- The lookup over a signature. -/
def sub (Sg : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : Sg.Msg → A.J → E)
    (S : PscBk E E₀ Sg.Msg Wp Kc) : SubR Sg E₀ Kc A.St A.J Wp :=
  ⟨(A.baseA E₀ Sg.Msg Wp Kc msg S).R.keep Sg.Smp Sg.ext,
    Sg.liftH (A.baseA E₀ Sg.Msg Wp Kc msg S).H,
    fun _ _ w => w,
    (A.baseA E₀ Sg.Msg Wp Kc msg S).P.keep Sg.Smp Sg.ext⟩

end LkAsmH
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The assembled lookup, at the base. -/
def asmH_base : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsmH E) (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec)
      (Kc M Wp : Type) (S : PscBk E Ex M Wp Kc) (R0 : Rels Kc A.St Ex (M × Wp))
      (msg : M → A.J → E),
    A.H.lkb.Adm p → padsOK (A.v' + 1) A.d A.pads = true → A.n + 1 + 1 = 2 ^ A.w → A.H.MuOnF Mu →
    (A.baseA Ex M Wp Kc msg S).Good
      (cj R0 msg id (A.lk.inP Mu) A.lk.inR) (cj R0 msg Prod.fst (A.lk.out id id) (A.lk.out id id))

/-- States, under the hypotheses of its statement: the assembled lookup meets the interface of the
sub-protocol. -/
def asmH_ok : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsmH E) (Mu : A.St → (A.J → E) → Prop) (Sg : Sig E) (E₀ : ExtSpec)
      (Kc Wp : Type) (S : PscBk E E₀ Sg.Msg Wp Kc) (R0 : Rels Kc A.St E₀ (Sg.Msg × Wp))
      (msg : Sg.Msg → A.J → E),
    A.H.lkb.Adm p → padsOK (A.v' + 1) A.d A.pads = true → A.n + 1 + 1 = 2 ^ A.w → A.H.MuOnF Mu →
    (A.sub Sg E₀ Kc Wp msg S).OK
      ⟨A.v' + 1, A.d, fun st ym => A.key st (msg ym.2), A.tab, fun _ _ => True⟩
      (fun st ym => Mu st (msg ym.2)) R0 fun ym => msg ym.2

def asmH_rounds : Prop :=
  ∀ (A : LkAsmH E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseA Ex M Wp Kc msg (PscBk.lib E Ex M Wp Kc)).R.shape.length =
      (1 + 3 * (A.n + 1)) + 1 +
        ((∑ l ∈ Finset.range (A.v' + 1), (0 + l + 3 + 1)) +
          ∑ l ∈ Finset.range A.d, (A.w + l + 3 + 1)) +
        (A.w + A.d + 1) + (1 + (A.w + A.d + 3))

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Finset

section
variable {E : Type} [Field E] [Fintype E]

namespace LdLkp
namespace LkAsmH
variable (A : LkAsmH E)

/-- the claims that wait after the head, by name -/
def PKc (x : A.X2) (m : A.J → E) : Prop :=
  keyProd (A.v' + 1) (A.key (A.b2 x).1 m) (A.b2 x).2 + m A.cZ * (A.H.tie.bK A.n x.2).1 =
    (A.H.tie.bK A.n x.2).2
def PTc (x : A.X2) (m : A.J → E) : Prop :=
  ∀ j < A.n + 1,
    A.H.PT (A.b2 x) m j + m (A.cAt j true) * (A.H.tie.bT A.n x.2 j).1 = (A.H.tie.bT A.n x.2 j).2
def Opn (x : A.X2) (m : A.J → E) : Prop := A.H.tie.claim (A.n + 1) x m
def Num (m : A.J → E) : Prop := NumKeysP (A.v' + 1) A.d (A.n + 2) (padNum A.pads) (A.H.bit m)
def Bts (m : A.J → E) : Prop := Bits A.d A.w (A.H.bit m)

/-- the claim at the point -/
def S1 (x : A.XR) (m : A.J → E) : Prop :=
  ((A.I1.DT2 (A.n + 1)).lv 0).T.SumHolds x fun j => m (((A.I1.DT2 (A.n + 1)).lv 0).toJ j)

/-- `Φ1`, `ΨK`, `ΨT`: what rides past the point; past the keys' side; past the table's side.
P: what the honest side knows more -/
def Φ1 (P : A.St → (A.J → E) → Prop) (x : A.X2) (m : A.J → E) : Prop :=
  ((A.H.RestF (A.b2 x) m ∧ P (A.b2 x).1 m) ∧ RowsHold (A.rows2 x) m) ∧ A.PKc x m
def ΨK (P : A.St → (A.J → E) → Prop) (x : A.XR) (m : A.J → E) : Prop :=
  ((A.H.RestF (A.b2 (A.oR x)) m ∧ P (A.b2 (A.oR x)).1 m) ∧ RowsHold (A.rows2 (A.oR x)) m) ∧
  A.S1 x m
def ΨT (P : A.St → (A.J → E) → Prop) (x : A.X4) (m : A.J → E) : Prop :=
  ((A.Num m ∧ P (A.b2 (A.oR (A.o4 x))).1 m) ∧ RowsHold (A.rows2 (A.oR (A.o4 x))) m) ∧
  RowsHold (A.rows4 x) m ∧
  (A.clK x).Holds (A.v' + 1) (A.key (A.b2 (A.oR (A.o4 x))).1 m) m

theorem num_iff (m : A.J → E) : A.numRow.Holds m ↔ A.Num m := headF_num E A.H m

omit [Fintype E] in
/-- `sum_one` (Cb/Ld/LdLkpAsmProofs.lean) for a decidable equality that is given -/
theorem sum_oneD {N : Type} [Fintype N] [DecidableEq N] (c : N) (β : E) (μ : N → E) :
    ∑ j, (if j = c then β else 0) * μ j = μ c * β := by
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_comm _ _

/-- If n + 2 ≤ 2^w: the claims on the products of the table at the counting positions are the
claims that the point takes; at the idle positions nothing is claimed. -/
theorem roots_iff (hW : A.n + 2 ≤ 2 ^ A.w) (x : A.X2) (m : A.J → E) :
    (A.PTc x m ∧ A.Opn x m) ↔ A.R.Holds x m := by
  have hU : ∀ θ : Fin (A.w + 0) → Bool,
      numLE θ < A.n + 2 → A.R.D.U x m 0 θ = A.H.PT (A.b2 x) m (numLE θ) := fun θ hθ =>
    (ldLkpInst2_root E A.I1 (A.n + 1) x m θ).trans (ldLkpInst2_count E A.I1 (A.n + 1) _ m _ _ hθ)
  have hI : ∀ θ : Fin (A.w + 0) → Bool, A.n + 2 ≤ numLE θ → A.R.D.U x m 0 θ = 1 := fun θ hθ =>
    (ldLkpInst2_root E A.I1 (A.n + 1) x m θ).trans (ldLkpInst2_idle E A.I1 (A.n + 1) _ m _ _ hθ)
  have hO : A.Opn x m ↔
      A.H.PT (A.b2 x) m (A.n + 1) + m (A.cAt A.n false) * A.H.tie.be A.n x.2 = x.1 := by
    have hq : A.H.tie.Q (A.b2 x) m (A.n + 1) = A.H.PT (A.b2 x) m (A.n + 1) :=
      headF_open E A.H (A.b2 x) m
    rw [← hq]
    exact tieFR_open E A.H.tie A.n x m
  constructor
  · rintro ⟨hT, hOp⟩ (θ : Fin (A.w + 0) → Bool)
    show A.R.D.U x m 0 θ + ∑ j, A.formT x θ j * m j = A.tgtT x θ
    by_cases h1 : numLE θ < A.n + 1
    · have ef : A.formT x θ =
        fun j =>
          if j = A.cAt (numLE θ) true then (A.H.tie.bT A.n x.2 (numLE θ)).1 else 0 := if_pos h1
      have et : A.tgtT x θ = (A.H.tie.bT A.n x.2 (numLE θ)).2 := if_pos h1
      rw [hU θ (by omega), ef, et, sum_oneD]
      exact hT _ h1
    · by_cases h2 : numLE θ = A.n + 1
      · have ef : A.formT x θ =
            fun j => if j = A.cAt A.n false then A.H.tie.be A.n x.2 else 0 :=
          (if_neg h1).trans (if_pos h2)
        have et : A.tgtT x θ = x.1 := (if_neg h1).trans (if_pos h2)
        rw [hU θ (by omega), ef, et, h2, sum_oneD]
        exact hO.mp hOp
      · have ef : A.formT x θ = 0 := (if_neg h1).trans (if_neg h2)
        have et : A.tgtT x θ = 1 := (if_neg h1).trans (if_neg h2)
        rw [hI θ (by omega), ef, et]
        simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  · intro h
    have h' : ∀ θ : Fin (A.w + 0) → Bool, A.R.D.U x m 0 θ + ∑ j, A.formT x θ j * m j = A.tgtT x θ :=
      h
    refine ⟨fun j hj => ?_, hO.mpr ?_⟩
    · obtain ⟨θ, rfl⟩ := numLE_surj (k := A.w + 0) (c := j) (by show j < 2 ^ A.w; omega)
      have ef : A.formT x θ =
        fun j =>
          if j = A.cAt (numLE θ) true then (A.H.tie.bT A.n x.2 (numLE θ)).1 else 0 := if_pos hj
      have et : A.tgtT x θ = (A.H.tie.bT A.n x.2 (numLE θ)).2 := if_pos hj
      have := h' θ
      rw [hU θ (by omega), ef, et, sum_oneD] at this
      exact this
    · obtain ⟨θ, hθ⟩ := numLE_surj (k := A.w + 0) (c := A.n + 1) (by show A.n + 1 < 2 ^ A.w; omega)
      have h1 : ¬ numLE θ < A.n + 1 := by omega
      have ef : A.formT x θ = fun j => if j = A.cAt A.n false then A.H.tie.be A.n x.2 else 0 :=
        (if_neg h1).trans (if_pos hθ)
      have et : A.tgtT x θ = x.1 := (if_neg h1).trans (if_pos hθ)
      have := h' θ
      rw [hU θ (by omega), ef, et, hθ, sum_oneD] at this
      exact this

/-- junction 1: if n + 2 ≤ 2^w, what the head leaves is what the point takes -/
theorem junction1 (hW : A.n + 2 ≤ 2 ^ A.w) (P : A.St → (A.J → E) → Prop) (x : A.X2) (m : A.J → E) :
    (((A.H.RestF (A.b2 x) m ∧ P (A.b2 x).1 m) ∧ A.H.tie.Done A.n x.2 m) ∧
      A.H.tie.claim (A.n + 1) x m) ↔
    (A.Φ1 P x m ∧ A.R.Holds x m) := by
  rw [← A.roots_iff hW x m]
  constructor
  · rintro ⟨⟨hRP, hr, hk, ht⟩, ho⟩
    exact ⟨⟨⟨hRP, hr⟩, hk⟩, ht, ho⟩
  · rintro ⟨⟨⟨hRP, hr⟩, hk⟩, ht, ho⟩
    exact ⟨⟨hRP, hr, hk, ht⟩, ho⟩

/-- junction 2: what the point leaves is what the keys' side takes -/
theorem junction2 (P : A.St → (A.J → E) → Prop) (x : A.XR) (m : A.J → E) :
    ((A.Φ1 P ((A.I1.DT2 (A.n + 1)).root 0 x.2).1 m ∧ RowsHold ((A.I1.DT2 (A.n + 1)).rowsAt 0 x.2) m)
        ∧
      ((A.I1.DT2 (A.n + 1)).lv 0).T.SumHolds x fun j => m (((A.I1.DT2 (A.n + 1)).lv 0).toJ j)) ↔
    (A.ΨK P x m ∧
      keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
        A.tK (A.oR x)) := by
  have hs : ∑ j, A.IK.fK x j * m j = m A.cZ * (A.H.tie.bK A.n (A.oR x).2).1 :=
    sum_oneD (N := A.J) A.cZ _ m
  rw [hs]
  constructor
  · rintro ⟨⟨⟨hRr, hk⟩, _⟩, h1⟩
    exact ⟨⟨hRr, h1⟩, hk⟩
  · rintro ⟨⟨hRr, h1⟩, hk⟩
    exact ⟨⟨⟨hRr, hk⟩, fun r hr => absurd hr List.not_mem_nil⟩, h1⟩

/-- the claim at the point, read again after the keys' side, is the forest's claim at level 0 -/
theorem enter_iff (x : A.X4) (m : A.J → E) :
    (A.D.lv 0).T.SumHolds (A.enterT x) (fun j => m ((A.D.lv 0).toJ j)) ↔ A.S1 (A.o4 x) m :=
  (ldLkpP_sum E A.D (ldLkpInst2_step E A.IT (A.n + 1)) 0 (A.enterT x) m).trans
    (ldLkpP_sum E (A.I1.DT2 (A.n + 1)) (ldLkpInst2_step E A.I1 (A.n + 1)) 0 (A.o4 x) m).symm

/-- the rows of the table's side say: the bit test's output rows, the closing's end claim, the rows
of the forest -/
theorem rowsB_iff (o : A.XB) (m : A.J → E) :
    RowsHold (A.rowsB o) m ↔
    A.Bt.zc.next.par.OutHolds o m ∧
    A.En.par.MidHolds (A.outE o) m ∧
    RowsHold (A.D.rowsAt A.d (A.outE o).st) m := by
  rw [ldLkpBitP_rows E A.Bt o m, endM_row E A.En (A.outE o) m]
  refine (rowsHold_append (A.D.rowsAt A.d (A.outE o).st) _ m).trans ?_
  constructor
  · rintro ⟨h1, h2⟩
    have hE := h2
      ⟨A.En.par.slU A.En.rowB (A.En.outOf (A.outE o)), A.En.par.tU (A.En.outOf (A.outE o))⟩
      List.mem_cons_self
    have hU := h2 ⟨A.Bt.zc.next.par.slU (fun _ b => b.elim) o, A.Bt.zc.next.par.tU o⟩
      (List.mem_cons_of_mem _ List.mem_cons_self)
    have hV := h2 ⟨A.Bt.zc.next.par.slE A.Bt.rowA () o, o.vals ()⟩
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    exact ⟨⟨hU, hV⟩, hE, h1⟩
  · rintro ⟨⟨hU, hV⟩, hE, h1⟩
    refine ⟨h1, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hE
    · exact hU
    · exact hV

/-- the read-out -/
theorem out_iff (o : A.XB) (m : A.J → E) :
    A.lk.out id id (A.rd o) m ↔ (A.ΨT (fun _ _ => True) (A.oldT o) m ∧ RowsHold (A.rowsB o) m) := by
  have e : RowsHold (A.rd o).2.2 m ↔
      A.Num m ∧
      RowsHold (A.rows2 (A.oR (A.o4 (A.oldT o)))) m ∧
      RowsHold (A.rows4 (A.oldT o)) m ∧
      RowsHold (A.rowsB o) m := by
    show RowsHold
        (A.rows2 (A.oR (A.o4 (A.oldT o))) ++ (A.rows4 (A.oldT o) ++ (A.rowsB o ++ [A.numRow]))) m ↔
      _
    rw [rowsHold_append, rowsHold_append, rowsHold_append, rowsHold_cons, A.num_iff]
    exact ⟨fun h => ⟨h.2.2.2.1, h.1, h.2.1, h.2.2.1⟩,
      fun h => ⟨h.2.1, h.2.2.1, h.2.2.2, h.1, fun r hr => absurd hr List.not_mem_nil⟩⟩
  constructor
  · rintro ⟨hc, hr, _⟩
    obtain ⟨hn, h2, h4, hB⟩ := e.mp hr
    exact ⟨⟨⟨⟨hn, trivial⟩, h2⟩, h4, hc⟩, hB⟩
  · rintro ⟨⟨⟨⟨hn, _⟩, h2⟩, h4, hc⟩, hB⟩
    exact ⟨hc, e.mpr ⟨hn, h2, h4, hB⟩, trivial⟩

end LkAsmH
end LdLkp
end

section
variable (E : Type) [Field E] [Fintype E]

/-- what rides through the forest: the caller's joint, ΨT, and "all bits are bits" -/
noncomputable def LdLkp.LkAsmH.A0 (A : LkAsmH E) {Ex : ExtSpec} {Kc M Wp : Type}
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop) :
    Rels Kc (A.D.lv 0).T.St Ex (M × Wp) :=
  cj R0 msg (fun s => (A.b2 (A.oR (A.o4 s.1))).1) (fun s m => A.ΨT Mu s.1 m ∧ A.Bts m)
    fun s m => A.ΨT (fun _ _ => True) s.1 m ∧ A.Bts m

/-- the keys' side, the step into the forest, the levels below l -/
theorem LdLkp.LkAsmH.forest_good (A : LkAsmH E) (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec)
    (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E) (l : ℕ) :
    (A.forest Ex M Wp Kc msg l).Good
      (cj R0 msg (fun x => (A.b2 (A.oR x)).1)
        (fun x m =>
          A.ΨK Mu x m ∧
          keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
            A.tK (A.oR x)) fun x m =>
              A.ΨK (fun _ _ => True) x m ∧
              keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
                A.tK (A.oR x))
      (A.D.jtAt msg (A.A0 E R0 msg Mu) l) := by
  induction l with
  | zero =>
    have g := ldLkpSegK_good E A.IK A.v' (fun x => A.tK (A.oR x)) Ex Kc A.St M Wp R0 msg
      (fun x => (A.b2 (A.oR x)).1) (A.ΨK Mu) (A.ΨK fun _ _ => True)
    unfold BkA.Good at g ⊢
    rw [show A.D.jtAt msg (A.A0 E R0 msg Mu) 0 = _
        from ldLkpK_tree E A.D Ex Kc A.St M Wp R0 msg (fun s => (A.b2 (A.oR (A.o4 s.1))).1)
          (fun s m => A.ΨT Mu s.1 m ∧ A.Bts m)
          (fun s m => A.ΨT (fun _ _ => True) s.1 m ∧ A.Bts m) 0]
    refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _ A.enterT g ?_ ?_ ?_ ?_
    · intro x y w h
      obtain ⟨hR, ⟨⟨⟨⟨⟨hb, hn⟩, hP⟩, hr2⟩, h1⟩, hr4⟩, hc⟩ := h
      exact ⟨hR,
        ⟨⟨⟨⟨⟨hn, hP⟩, hr2⟩, hr4, hc⟩, hb⟩, fun r hr => absurd hr List.not_mem_nil⟩,
        (A.enter_iff x _).mpr h1⟩
    · exact fun _ _ h => h
    · exact fun _ => rfl
    · intro x y w _ h
      obtain ⟨hR, ⟨⟨⟨⟨⟨hn, hP⟩, hr2⟩, hr4, hc⟩, hb⟩, _⟩, h1⟩ := h
      exact ⟨hR, ⟨⟨⟨⟨⟨hb, hn⟩, hP⟩, hr2⟩, (A.enter_iff x _).mp h1⟩, hr4⟩, hc⟩
  | succ l ih =>
    exact segT_seq ih
      (ldLkpP_level E A.D Ex M Wp Kc msg (A.A0 E R0 msg Mu) l (ldLkpInst2_step E A.IT (A.n + 1)))

/-- the chain before the read-out -/
theorem LdLkp.LkAsmH.chain_good (p : ℕ) [CharP E p] (A : LkAsmH E) (Mu : A.St → (A.J → E) → Prop)
    (Ex : ExtSpec) (Kc M Wp : Type) (S : PscBk E Ex M Wp Kc) (R0 : Rels Kc A.St Ex (M × Wp))
    (msg : M → A.J → E) (hA : A.H.lkb.Adm p) (hP : padsOK (A.v' + 1) A.d A.pads = true)
    (hF : A.n + 1 + 1 = 2 ^ A.w) (hMu : A.H.MuOnF Mu) :
    (A.chainA Ex M Wp Kc msg S).Good (cj R0 msg id (A.lk.inP Mu) A.lk.inR)
      (cj R0 msg (fun o => (A.b2 (A.oR (A.o4 (A.oldT o)))).1)
        (fun o m => A.ΨT Mu (A.oldT o) m ∧ RowsHold (A.rowsB o) m)
        fun o m => A.ΨT (fun _ _ => True) (A.oldT o) m ∧ RowsHold (A.rowsB o) m) := by
  -- the head
  have g1 := headF_good E p A.H Mu Ex Kc M Wp S R0 msg hA hP hMu
  -- the point
  let R1 : Rels Kc A.X2 Ex (M × Wp) :=
    cj R0 msg (fun x => (A.b2 x).1) (A.Φ1 Mu) (A.Φ1 fun _ _ => True)
  have g2 : (A.R.rootA Ex M Wp Kc).Good
      ⟨fun st y w => R1.rel st y w ∧ A.R.Holds st (msg w.1),
        fun a w => R1.relR a w ∧ A.R.Holds a.1 (msg w.1),
        R1.on, R1.core⟩
      ((A.I1.DT2 (A.n + 1)).jtAt msg (A.R.toIn.ride R1) 0) :=
    ldLkpRoot_good E A.R Ex M Wp Kc R1 msg (ldLkpInst2_step E A.I1 (A.n + 1)) fun _ _ _ => rfl
  have e1 : cj R0 msg (fun x : A.X2 => (A.b2 x).1)
        (fun x m =>
          ((A.H.RestF (A.b2 x) m ∧ Mu (A.b2 x).1 m) ∧ A.H.tie.Done A.n x.2 m) ∧
          A.H.tie.claim (A.n + 1) x m)
        (fun x m =>
          (A.H.RestF (A.b2 x) m ∧ A.H.tie.Done A.n x.2 m) ∧ A.H.tie.claim (A.n + 1) x m) =
      (⟨fun st y w => R1.rel st y w ∧ A.R.Holds st (msg w.1),
        fun a w => R1.relR a w ∧ A.R.Holds a.1 (msg w.1),
        R1.on,
        R1.core⟩ : Rels Kc A.X2 Ex (M × Wp)) :=
    (ldLkpK_congr E Kc A.St M Wp A.J A.X2 Ex R0 msg (fun x => (A.b2 x).1) _ _
        (fun x m => A.Φ1 Mu x m ∧ A.R.Holds x m)
        (fun x m => A.Φ1 (fun _ _ => True) x m ∧ A.R.Holds x m) (fun x m => A.junction1 hA.1 Mu x m)
        (fun x m =>
          Iff.trans (by simp only [and_true]) (A.junction1 hA.1 (fun _ _ => True) x m))).trans
      (ldLkpK_and E Kc A.St M Wp A.J A.X2 Ex R0 msg (fun x => (A.b2 x).1) (A.Φ1 Mu)
        (A.Φ1 fun _ _ => True) (fun x m => A.R.Holds x m) fun x m => A.R.Holds x m).symm
  have e2 : (A.I1.DT2 (A.n + 1)).jtAt msg (A.R.toIn.ride R1) 0 =
      cj R0 msg (fun x : A.XR => (A.b2 (A.oR x)).1)
        (fun x m =>
          A.ΨK Mu x m ∧
          keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
            A.tK (A.oR x)) fun x m =>
              A.ΨK (fun _ _ => True) x m ∧
              keyProd (A.v' + 1) (A.IK.key (A.IK.st x) m) (A.IK.lam x) + ∑ j, A.IK.fK x j * m j =
                A.tK (A.oR x) :=
    (ldLkpK_tree E (A.I1.DT2 (A.n + 1)) Ex Kc A.St M Wp R0 msg (fun s => (A.b2 s.1).1)
        (fun s m => A.Φ1 Mu s.1 m) (fun s m => A.Φ1 (fun _ _ => True) s.1 m) 0).trans
      (ldLkpK_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun x m => A.junction2 Mu x m)
        (fun x m => A.junction2 (fun _ _ => True) x m))
  -- the keys' side and the forest
  have g3 := A.forest_good E Mu Ex Kc M Wp R0 msg A.d
  -- the closing
  let A1 : Rels Kc (A.D.lv A.d).T.St Ex (M × Wp) := A.D.ride msg (A.A0 E R0 msg Mu) A.d
  have g4 : (A.endA Ex M Wp Kc msg).Good
      (A.En.relsIn A1 fun w => msg w.1) (A.En.par.baseMid A1 fun w => msg w.1) :=
    endM_goodAt E A.En Ex M Wp Kc A1 msg (instM_ok E A.IT (A.n + 1) A.oE A.wE)
  have e3 : A.D.jtAt msg (A.A0 E R0 msg Mu) A.d = A.En.relsIn A1 fun w => msg w.1 :=
    instM_top E A.IT (A.n + 1) A.oE A.wE hF Ex M Wp Kc msg (A.A0 E R0 msg Mu)
  -- the bit test
  let R2 : Rels Kc A.XE Ex (M × Wp) :=
    cj R0 msg (fun z : A.XE => (A.b2 (A.oR (A.o4 (A.D.root A.d z.st).1))).1)
      (fun z m =>
        (A.ΨT Mu (A.D.root A.d z.st).1 m ∧ RowsHold (A.D.rowsAt A.d z.st) m) ∧
        A.En.par.MidHolds z m) fun z m =>
          (A.ΨT (fun _ _ => True) (A.D.root A.d z.st).1 m ∧ RowsHold (A.D.rowsAt A.d z.st) m) ∧
          A.En.par.MidHolds z m
  have g5 : (A.bitA Ex M Wp Kc msg).Good
      ⟨fun st y w => R2.rel st y w ∧ A.Bt.AllBits (msg w.1),
        fun a w => R2.relR a w ∧ A.Bt.AllBits (msg w.1),
        R2.on, R2.core⟩
      (A.Bt.zc.next.par.baseOut (A.Bt.zc.toIn.ride R2) fun w => msg w.1) :=
    ldLkpBitP_goodAt E A.Bt Ex M Wp Kc R2 msg
  have hb : ∀ m, A.Bt.AllBits m ↔ A.Bts m := fun m => ldLkpInst_bitsP E A.IT _ A.oB A.wB A.cB m
  obtain ⟨r1, r2, r3, r4⟩ := ldLkpP_ride E A.D Ex M Wp Kc msg (A.A0 E R0 msg Mu) A.d
  have e4 : A.En.par.baseMid A1 (fun w => msg w.1) =
      (⟨fun st y w => R2.rel st y w ∧ A.Bt.AllBits (msg w.1),
        fun a w => R2.relR a w ∧ A.Bt.AllBits (msg w.1),
        R2.on,
        R2.core⟩ : Rels Kc A.XE Ex (M × Wp)) := by
    refine LdLkp.rels_ext (funext fun z => funext fun y => funext fun w => propext ?_)
      (funext fun a => funext fun w => propext ?_) (funext fun a => propext (r3 a.1.st a.2)) r4
    · show A1.rel z.st y w ∧ A.En.par.MidHolds z (msg w.1) ↔ _
      rw [r1]
      exact ⟨fun h => ⟨⟨h.1.1.1, ⟨h.1.1.2.1, h.1.2⟩, h.2⟩, (hb _).2 h.1.1.2.2⟩,
        fun h => ⟨⟨⟨h.1.1, h.1.2.1.1, (hb _).1 h.2⟩, h.1.2.1.2⟩, h.1.2.2⟩⟩
    · show A1.relR (a.1.st, a.2) w ∧ A.En.par.MidHolds a.1 (msg w.1) ↔ _
      rw [r2]
      exact ⟨fun h => ⟨⟨h.1.1.1, ⟨h.1.1.2.1, h.1.2⟩, h.2⟩, (hb _).2 h.1.1.2.2⟩,
        fun h => ⟨⟨⟨h.1.1, h.1.2.1.1, (hb _).1 h.2⟩, h.1.2.1.2⟩, h.1.2.2⟩⟩
  have e5 : A.Bt.zc.next.par.baseOut (A.Bt.zc.toIn.ride R2) (fun w => msg w.1) =
      cj R0 msg (fun o => (A.b2 (A.oR (A.o4 (A.oldT o)))).1)
        (fun o m => A.ΨT Mu (A.oldT o) m ∧ RowsHold (A.rowsB o) m)
        fun o m => A.ΨT (fun _ _ => True) (A.oldT o) m ∧ RowsHold (A.rowsB o) m := by
    refine LdLkp.rels_ext (funext fun o => funext fun y => funext fun w => propext ?_)
      (funext fun a => funext fun w => propext ?_) rfl rfl
    · show R2.rel (A.outE o) y w ∧ A.Bt.zc.next.par.OutHolds o (msg w.1) ↔
        R0.rel (A.b2 (A.oR (A.o4 (A.oldT o)))).1 y w ∧
        A.ΨT Mu (A.oldT o) (msg w.1) ∧
        RowsHold (A.rowsB o) (msg w.1)
      rw [A.rowsB_iff]
      exact ⟨fun h => ⟨h.1.1, h.1.2.1.1, h.2, h.1.2.2, h.1.2.1.2⟩,
        fun h => ⟨⟨h.1, ⟨h.2.1, h.2.2.2.2⟩, h.2.2.2.1⟩, h.2.2.1⟩⟩
    · show R2.relR (A.outE a.1, a.2) w ∧ A.Bt.zc.next.par.OutHolds a.1 (msg w.1) ↔
        R0.relR ((A.b2 (A.oR (A.o4 (A.oldT a.1)))).1, a.2) w ∧
        A.ΨT (fun _ _ => True) (A.oldT a.1) (msg w.1) ∧
        RowsHold (A.rowsB a.1) (msg w.1)
      rw [A.rowsB_iff]
      exact ⟨fun h => ⟨h.1.1, h.1.2.1.1, h.2, h.1.2.2, h.1.2.1.2⟩,
        fun h => ⟨⟨h.1, ⟨h.2.1, h.2.2.2.2⟩, h.2.2.2.1⟩, h.2.2.1⟩⟩
  rw [e2] at g2
  rw [e3] at g3
  rw [e4] at g4
  rw [e5] at g5
  exact segT_seq (segT_seq (segT_seq (segT_seq (e1 ▸ g1) g2) g3) g4) g5

theorem asmH_base : Spec.asmH_base E := by
  intro p _ A Mu Ex Kc M Wp S R0 msg hA hP hF hMu
  have g := A.chain_good E p Mu Ex Kc M Wp S R0 msg hA hP hF hMu
  unfold BkA.Good at g ⊢
  refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _ A.rd g ?_ ?_ ?_ ?_
  · intro o y w h
    exact ⟨h.1, (A.out_iff o _).mpr ⟨⟨⟨⟨h.2.1.1.1.1, trivial⟩, h.2.1.1.2⟩, h.2.1.2⟩, h.2.2⟩⟩
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · intro o y w _ h
    exact ⟨h.1, (A.out_iff o _).mp h.2⟩

theorem asmH_ok : Spec.asmH_ok E := by
  intro p _ A Mu Sg E₀ Kc Wp S R0 msg hA hP hF hMu
  exact sigLift_goodB E Sg Kc _ _ Wp Wp E₀ E₀ _ _ _ _ _ _
    (asmH_base E p A Mu E₀ Kc Sg.Msg Wp S R0 msg hA hP hF hMu)

theorem LdLkp.LkAsmH.forest_len
    (A : LkAsmH E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) (l : ℕ) :
    (A.forest Ex M Wp Kc msg l).R.shape.length =
      (∑ i ∈ Finset.range (A.v' + 1), (0 + i + 3 + 1)) +
        ∑ i ∈ Finset.range l, (A.w + i + 3 + 1) := by
  induction l with
  | zero =>
      rw [Finset.sum_range_zero]
      exact ldLkpSegK_rounds E A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc msg
  | succ l ih =>
      have hl : (A.D.levA Ex Wp Kc msg l).R.shape.length = A.w + l + 3 + 1 := by
        have e : (A.D.levA Ex Wp Kc msg l).R.shape =
            ((A.D.lv l).T.par.psc Ex).shape ++ (A.D.lineA Ex M Wp Kc l).R.shape := rfl
        rw [e, List.length_append, psc_our_len E (A.D.lv l).T Ex, A.D.fmt_len l]
        rfl
      have e : (A.forest Ex M Wp Kc msg (l + 1)).R.shape =
          (A.forest Ex M Wp Kc msg l).R.shape ++ (A.D.levA Ex Wp Kc msg l).R.shape := rfl
      rw [e, List.length_append, ih, hl, Finset.sum_range_succ (fun i => A.w + i + 3 + 1) l]
      exact Nat.add_assoc _ _ _

theorem asmH_rounds : Spec.asmH_rounds E := by
  intro A Ex M Wp Kc msg
  have e : (A.baseA Ex M Wp Kc msg (PscBk.lib E Ex M Wp Kc)).R.shape =
      ((((A.H.headA msg (PscBk.lib E Ex M Wp Kc)).R.shape ++ [IOR.drawRound A.R.toIn.ev.D]) ++
            (A.forest Ex M Wp Kc msg A.d).R.shape) ++
          (A.En.par.core Ex).shape) ++
        ([IOR.drawRound A.Bt.zc.toIn.ev.D] ++ (A.Bt.zc.next.par.psc Ex).shape) := rfl
  rw [e, List.length_append, List.length_append, List.length_append, List.length_append,
    List.length_append, headF_rounds E A.H Ex M Wp Kc msg, A.forest_len E Ex M Wp Kc msg A.d,
    endM_len E A.En Ex, psc_our_len E A.Bt.zc.next Ex]
  show _ + (1 + ((List.replicate (A.w + A.d) (pfCube E 2)).length + 3)) = _
  rw [List.length_replicate]
  rfl

end
end Cb
