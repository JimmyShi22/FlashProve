-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ent/CloseKnow.lean: the blocks of the closing of a link, each with its round-by-round knowledge
soundness alone.

The closing of the library's link (Cb/Ld/LdLinkClose.lean) brings all rows that are left into one
row and then runs a proximity test, which it takes as a parameter. The library builds its tests of
three blocks: the folding, the code switch, the base case. It states most blocks as bundles, of
which knowledge soundness is one part. This file states that part by itself: on all statements, with
no hypothesis on an honest side.
Statements. The proofs: Cb/Ent/CloseKnowProofs.lean.

Main names: `Spec.know_bat`, `Spec.know_bat_beside` (several rows into one), `Spec.back_bridge`,
`Spec.know_bridge` (from decoding with a sample to closeness at one joint radius),
`Spec.ok_powers_comap` (powers of one challenge as coefficients).
The three blocks of a test have that form in the library and are not stated again: the
folding (`Cb.ld_sum_know`), the code switch (`Cb.ldSwitch_know`) and the base case
(`Cb.ldBase_know`). For the folding, `Spec.codesOK_iff`, `Spec.errOK_iff` and `Spec.qwDeg_iff` write
out what its three named hypotheses ask. The base case asks the code's laws, a radius below the
number d that its extractor takes, a bound on the exceptional points of a line and a bound on the
lists of pairs.
That the closing's rows say what the link's last relation says is the library's `Cb.ldLkC_rows`.

Limits: no bound on any list or on any count of exceptional points. These stay hypotheses.
Nothing on an honest prover or on zero knowledge.
Terms: lean/GLOSSARY.md.

-/
import Cb.Ld.LdBat
import Cb.Ld.LdBatSig
import Cb.Ld.LdSumKnow
import Cb.Gen.BatEvader

set_option autoImplicit false

namespace Cb
open Iop Prob

namespace Spec

/-! ### Several rows into one -/

section
variable (E P B : Type) [Field E] [Fintype E] [Fintype P] [Fintype B]

/-- The batching: one round, in which the verifier draws the seed of the coefficients. Except for
L * Z.err seeds, a witness for the one combined row is a witness for all rows: the same code word
within e long positions of the given word, the same message. -/
def know_bat : Prop :=
  ∀ (C : LdCode E P) (S : B → Type) (sl : ∀ b, Slf E (S b) C.J) (Z : Evader E B) (e L : ℕ),
    Z.OK → C.ListAt e L →
    (ldBatEx C S Z).red.Know (fun _ => True) (ConL C.N e (Slf.All sl))
      (ConL C.N e (Slf.bat Z.ze sl).Holds) (fun _ _ w => w) ((L * Z.err, ()) : ℕ × Unit)

/-- The batching beside a part of the statement that is carried along. -/
def know_bat_beside : Prop :=
  ∀ (Kc Xc Wc : Type) (C : LdCode E P) (S : B → Type) (sl : ∀ b, Slf E (S b) C.J)
      (Z : Evader E B) (e L : ℕ) (Ec : ExtSpec) (Bc : IOR.Rels Kc Xc Ec Wc),
    Z.OK → C.ListAt e L →
    (IOR.draw Z.D (fun (x : ((B → E) × (∀ b, S b)) × Xc) ρ => (batNx Z.ze x.1 ρ, x.2))
        (C.ext.prod Ec)).red.Know (fun _ => True)
      (IOR.Rels.beside (C.relsAll sl e fun _ => ()) Bc).cf.relR
      (IOR.Rels.beside (C.rels (Slf.bat Z.ze sl) e fun _ => ()) Bc).cf.relR (fun _ _ w => w)
      ((L * Z.err, ()) : ℕ × Unit)

end

/-! ### From decoding with a sample to closeness at one joint radius -/

section
variable (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B]

/-- The step without rounds in front of the batching, backwards. Asked: the joint radius implies
each member's own (G.Fits), the statement has no collision, and the carried part's own condition
holds.
Given: the group's word is within the joint radius of a code word whose message meets all rows, the
sample rows among them, and the relaxed relation of the carried part holds of the kept messages.
Then each member of the group decodes, with its sample, to its share of that message, each kept
message decodes to the carried pair, the rows of the claim hold, and so does the carried part. -/
def back_bridge : Prop :=
  ∀ (S : Sig E) (G : Grp S) (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o),
    G.Fits → ∀ (x : (((B → E) × (∀ b, Sb b)) × St₀) × S.Smp) (y : (E₀.prod S.ext).Str)
      (w' : LdBrW G kp Wp), S.CF x.2 y.2 → A₀.on (x.1.2, y.1) →
    (IOR.Rels.beside (G.C.relsAll (G.rows sl) G.e fun _ => ()) ((S.sub kp).over A₀)).relR
      (ldBrF G kp Sb St₀ x, (ldBrG G kp E₀).map y) w' →
    (S.over (claimRels (fun x m => Slf.All sl x (G.msg m))
      (onMsgRels (S.res (T := OMsg.Msg) kp) A₀))).relR (x, y) (ldBrBack G kp Wp hc w')

/-- That step and the batching together: the library's bridge, one round. -/
def know_bridge : Prop :=
  ∀ (S : Sig E) (G : Grp S) (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o)
      (Z : Evader E (G.Row B)) (L : ℕ),
    Z.OK → G.C.ListAt G.e L → G.Fits →
    (ldBridge G kp Sb Z St₀ E₀).red.Know (fun _ => True)
      (S.over (claimRels (fun x m => Slf.All sl x (G.msg m))
        (onMsgRels (S.res (T := OMsg.Msg) kp) A₀))).cf.relR
      (IOR.Rels.beside (G.C.rels (Slf.bat Z.ze (G.rows sl)) G.e fun _ => ())
        ((S.sub kp).over A₀)).cf.relR
      (fun _ _ w => ldBrBack G kp Wp hc w) ((L * Z.err, ()) : ℕ × Unit)

end

/-! ### What the folding's named hypotheses ask -/

section
variable (E P : Type) [Field E] [Fintype E] [Fintype P]

/-- The three codes of a folding: each is linear and injective and reads what it declares, each has
distance at least d, and the radius is below d. -/
def codesOK_iff : Prop :=
  ∀ (C Z Zw : LdCode E P) (d e : ℕ),
    Spec.CodesOK E P C Z Zw d e ↔
      (C.Laws ∧ Z.Laws ∧ Zw.Laws) ∧ (C.Dist d ∧ Z.Dist d ∧ Zw.Dist d) ∧ e < d

/-- The numbers of a folding: a bound on the lists of each stage, and for each of the three tables
a bound on the exceptional points of each halving. -/
def errOK_iff : Prop :=
  ∀ (Y : SumPar E P) (e : ℕ) (Lst mC mS mW : ℕ → ℕ),
    Y.ErrOK e Lst mC mS mW ↔
      (∀ j, j ≤ Y.k → (Y.stage j).ListAt e (Lst j)) ∧
      (∀ j, 1 ≤ j → j ≤ Y.k → (Y.C.il (Fin (Y.k - j) → Bool)).MCAat e (mC j)) ∧
      (∀ j, 1 ≤ j → j ≤ Y.h → (Y.Z.il (Fin (Y.h - j) → Bool)).MCAat e (mS j)) ∧
      (∀ j, 1 ≤ j → j ≤ Y.h → (Y.Zw.il (Fin (Y.h - j) → Bool)).MCAat e (mW j))

/-- The degrees of the fresh mask's weights. In a variable numbered below h each weight has degree
at most n - 1 (0 if n = 0). In any other variable its degree is at most n. -/
def qwDeg_iff : Prop :=
  ∀ (Y : SumPar E P),
    Y.QwDeg ↔ ∀ j, Alg.DegLE (fun i : Fin Y.k => if i.val < Y.h then Y.n - 1 else Y.n)
      fun z => Y.Qw z j

end

/-! ### Coefficients -/

/-- The powers of one challenge as coefficients, at rows that are numbered below n without repeats.
If the rows' values are not all 0, their combination is 0 at no more than n - 1 challenges. -/
def ok_powers_comap : Prop :=
  ∀ (E J : Type) [Field E] [Fintype E] [Fintype J] (n : ℕ) (f : J → Fin n),
    Function.Injective f → ((Evader.powers E n).comap f).OK

end Spec
end Cb
