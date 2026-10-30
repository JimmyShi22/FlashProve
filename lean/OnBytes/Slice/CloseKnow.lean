-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CloseKnow.lean: the blocks of the library's closing of a link, each with its
round-by-round knowledge soundness alone.

The closing of the library's link (Cb/Ld/LdLinkClose.lean) brings all rows that are left into one
row and then runs a proximity test, which it takes as a parameter. The library builds its tests of
three blocks: the folding, the code switch, the base case. It states most blocks as bundles, of
which knowledge soundness is one part. A theorem about a verifier needs that part alone. This file
takes it out of the bundles, in the form in which blocks are taken off a written protocol
(OnBytes/Slice/Peel.lean): on all statements, with no hypothesis on an honest side.

Main theorems: `know_bat`, `know_bat_beside` (several rows into one), `back_bridge`, `know_bridge`
(from decoding with a sample to closeness at one joint radius), `ok_powers_comap` (powers of one
challenge as coefficients).
The three blocks of a test have that form in the library and are not stated again: the
folding (`Cb.ld_sum_know`), the code switch (`Cb.ldSwitch_know`) and the base case
(`Cb.ldBase_know`). For the folding, `codesOK_iff`, `errOK_iff` and `qwDeg_iff` write out what its
three named hypotheses ask. The base case asks the code's laws, a radius below the number d that
its extractor takes, a bound on the exceptional points of a line and a bound on the lists of pairs.
That the closing's rows say what the link's last relation says is the library's
`Cb.ldLkC_rows`.
Not claimed: a bound on any list or on any count of exceptional points. These stay hypotheses.
-/
import Cb.Ld.LdBatProofs
import Cb.Ld.LdBatSigProofs
import Cb.Ld.LdSumKnowProofs
import Cb.Ld.LdSwitchProofs
import Cb.Ld.LdBaseProofs
import Cb.Ld.LdLinProofsChain
import Cb.Gen.BatEvaderProofs

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb

/-! ### Several rows into one -/

section
variable {E P B : Type} [Field E] [Fintype E] [Fintype P] [Fintype B]

/-- The batching: one round, in which the verifier draws the seed of the coefficients. Except for
L * Z.err seeds, a witness for the one combined row is a witness for all rows: the same code word
within e long positions of the given word, the same message. -/
theorem know_bat (C : LdCode E P) (S : B → Type) (sl : ∀ b, Slf E (S b) C.J) (Z : Evader E B)
    (e L : ℕ) (hZ : Z.OK) (hL : C.ListAt e L) :
    (ldBatEx C S Z).red.Know (fun _ => True) (ConL C.N e (Slf.All sl))
      (ConL C.N e (Slf.bat Z.ze sl).Holds) (fun _ _ w => w) ((L * Z.err, ()) : ℕ × Unit) :=
  (ldBat_ex E P B Unit C S sl Z e L (fun _ => ()) (fun _ => True) hZ hL).good.know

/-- The batching beside a part of the statement that is carried along. -/
theorem know_bat_beside {Kc Xc Wc : Type} (C : LdCode E P) (S : B → Type)
    (sl : ∀ b, Slf E (S b) C.J) (Z : Evader E B) (e L : ℕ) (Ec : ExtSpec)
    (Bc : IOR.Rels Kc Xc Ec Wc) (hZ : Z.OK) (hL : C.ListAt e L) :
    (IOR.draw Z.D (fun (x : ((B → E) × (∀ b, S b)) × Xc) ρ => (batNx Z.ze x.1 ρ, x.2))
        (C.ext.prod Ec)).red.Know (fun _ => True)
      (IOR.Rels.beside (C.relsAll sl e fun _ => ()) Bc).cf.relR
      (IOR.Rels.beside (C.rels (Slf.bat Z.ze sl) e fun _ => ()) Bc).cf.relR (fun _ _ w => w)
      ((L * Z.err, ()) : ℕ × Unit) :=
  (ldk_pieceTr_cf
    (ldBat_ex_beside E P B Kc Xc Wc C S sl Z e L Ec Bc (fun _ => True) hZ hL)).good.know

end

/-! ### From decoding with a sample to closeness at one joint radius -/

section
variable {E B Kc St₀ Wp : Type} [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
  (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
  (E₀ : ExtSpec) (A₀ : IOR.Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o)

/-- The step without rounds in front of the batching, backwards. Asked: the joint radius implies
each member's own (G.Fits), the statement has no collision, and the carried part's own condition
holds.
Given: the group's word is within the joint radius of a code word whose message meets all rows, the
sample rows among them, and the relaxed relation of the carried part holds of the kept messages.
Then each member of the group decodes, with its sample, to its share of that message, each kept
message decodes to the carried pair, the rows of the claim hold, and so does the carried part. -/
theorem back_bridge (hF : G.Fits) (x : (((B → E) × (∀ b, Sb b)) × St₀) × S.Smp)
    (y : (E₀.prod S.ext).Str) (w' : LdBrW G kp Wp) (hcf : S.CF x.2 y.2) (hA : A₀.on (x.1.2, y.1))
    (h : (IOR.Rels.beside (G.C.relsAll (G.rows sl) G.e fun _ => ()) ((S.sub kp).over A₀)).relR
      (ldBrF G kp Sb St₀ x, (ldBrG G kp E₀).map y) w') :
    (S.over (claimRels (fun x m => Slf.All sl x (G.msg m))
      (onMsgRels (S.res (T := OMsg.Msg) kp) A₀))).relR (x, y) (ldBrBack G kp Wp hc w') :=
  (ldBat_step E B Kc St₀ Wp S G kp Sb sl E₀ A₀ hc hF).know x y _ w' ⟨hcf, hA⟩ rfl h

/-- That step and the batching together: the library's bridge, one round. -/
theorem know_bridge (Z : Evader E (G.Row B)) (L : ℕ) (hZ : Z.OK) (hL : G.C.ListAt G.e L)
    (hF : G.Fits) :
    (ldBridge G kp Sb Z St₀ E₀).red.Know (fun _ => True)
      (S.over (claimRels (fun x m => Slf.All sl x (G.msg m))
        (onMsgRels (S.res (T := OMsg.Msg) kp) A₀))).cf.relR
      (IOR.Rels.beside (G.C.rels (Slf.bat Z.ze (G.rows sl)) G.e fun _ => ())
        ((S.sub kp).over A₀)).cf.relR
      (fun _ _ w => ldBrBack G kp Wp hc w) ((L * Z.err, ()) : ℕ × Unit) :=
  (ldk_pieceTr_cf (ldBat_bridge E B Kc St₀ Wp S G kp Sb sl Z L E₀ A₀ hc (fun _ => True)
    (fun _ => True) hZ hL hF fun _ _ => trivial)).good.know

end

/-! ### What the folding's named hypotheses ask -/

section
variable {E P : Type} [Field E] [Fintype E] [Fintype P]

omit [Fintype E] in
/-- The three codes of a folding: each is linear and injective and reads what it declares, each has
distance at least d, and the radius is below d. -/
theorem codesOK_iff (C Z Zw : LdCode E P) (d e : ℕ) :
    Spec.CodesOK E P C Z Zw d e ↔
      (C.Laws ∧ Z.Laws ∧ Zw.Laws) ∧ (C.Dist d ∧ Z.Dist d ∧ Zw.Dist d) ∧ e < d :=
  Iff.rfl

/-- The numbers of a folding: a bound on the lists of each stage, and for each of the three tables
a bound on the exceptional points of each halving. -/
theorem errOK_iff (Y : SumPar E P) (e : ℕ) (Lst mC mS mW : ℕ → ℕ) :
    Y.ErrOK e Lst mC mS mW ↔
      (∀ j, j ≤ Y.k → (Y.stage j).ListAt e (Lst j)) ∧
      (∀ j, 1 ≤ j → j ≤ Y.k → (Y.C.il (Fin (Y.k - j) → Bool)).MCAat e (mC j)) ∧
      (∀ j, 1 ≤ j → j ≤ Y.h → (Y.Z.il (Fin (Y.h - j) → Bool)).MCAat e (mS j)) ∧
      (∀ j, 1 ≤ j → j ≤ Y.h → (Y.Zw.il (Fin (Y.h - j) → Bool)).MCAat e (mW j)) :=
  ⟨fun h => ⟨h.list, h.mcaC, h.mcaS, h.mcaW⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

omit [Fintype E] [Fintype P] in
/-- The degrees of the fresh mask's weights. In a variable numbered below h each weight has degree
at most n - 1 (0 if n = 0). In any other variable its degree is at most n. -/
theorem qwDeg_iff (Y : SumPar E P) :
    Y.QwDeg ↔ ∀ j, Alg.DegLE (fun i : Fin Y.k => if i.val < Y.h then Y.n - 1 else Y.n)
      fun z => Y.Qw z j :=
  Iff.rfl

end

/-! ### Coefficients -/

/-- The powers of one challenge as coefficients, at rows that are numbered below n without repeats.
If the rows' values are not all 0, their combination is 0 at no more than n - 1 challenges. -/
theorem ok_powers_comap {E J : Type} [Field E] [Fintype E] [Fintype J] (n : ℕ) (f : J → Fin n)
    (hf : Function.Injective f) : ((Evader.powers E n).comap f).OK :=
  ok_comap E J (Fin n) (Evader.powers E n) f hf (ok_powers E n)

end OnBytes.Slice

#print axioms OnBytes.Slice.know_bat
#print axioms OnBytes.Slice.know_bat_beside
#print axioms OnBytes.Slice.back_bridge
#print axioms OnBytes.Slice.know_bridge
#print axioms OnBytes.Slice.codesOK_iff
#print axioms OnBytes.Slice.errOK_iff
#print axioms OnBytes.Slice.qwDeg_iff
#print axioms OnBytes.Slice.ok_powers_comap
