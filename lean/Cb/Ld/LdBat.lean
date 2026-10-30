-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBat.lean: a random linear combination that turns many claims on one encoded message into one
claim, at a radius that may be beyond unique decoding: bounds on the number of bad seeds, and the
step as a reduction.

Definitions and statements; the proofs are in Cb/Ld/LdBatProofs.lean. Many statements of this
library are written twice: a definition in the namespace `Spec` states a proposition, and a theorem
of the same name outside that namespace proves it (lean/GLOSSARY.md). The two uses on statements
with samples (many claims into one; the bridge from the relaxation by decoding with a sample to the
existential one) are in Cb/Ld/LdBatSig.lean.

The protocol, in all uses. There are claims named by a finite set B: "the value v_b of the message
is τ_b". The prover sends nothing. The verifier sends a seed ρ of a zero-evader Z with one
coefficient for each b (`Evader`, Cb/Gen/BatEvader.lean: data and a number err; its property
`Evader.OK` is a hypothesis). The new claim is one: "∑_b Z(ρ)_b v_b is ∑_b Z(ρ)_b τ_b". One round,
one verifier message, no query, the verifier never rejects; oracles and witness stay as they are:
this is `IOR.draw` of Ior/Draw.lean.

In standard terms: a zero-evader is a family of coefficient vectors, one for each seed, such that
every fixed vector other than 0 has inner product 0 with at most err of them (`Evader.OK`);
independent coefficients and the powers of one challenge are such families (stated as
`Spec.ok_indep`, `Spec.ok_powers` in Cb/Gen/BatEvader.lean, proved in Cb/Gen/BatEvaderProofs.lean).
The existential relaxation at the radius e accepts every witness whose encoding is within e long
positions of the word and of whose message the claim holds (`ConL`, Cb/Ld/LdRel.lean); it does not
ask that there be only one.
`PieceTr`, a piece of a chain, asks of a reduction between two joints the bundle `IOR.GoodT` and
three further clauses, `noHid`, `noTie` and `bears`, which Cb/Ld/LdTowerKit.lean states (`bears`
through `IOR.Bears`, Ior/Bears.lean); `IOR.Piece` (Ior/Tail.lean) asks the same over `IOR.Good`.
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge. `Spec.ldBat_ex` concludes `PieceTr`.

Main names:
  `Vf E St M`: a value with a state: a function from states and messages to E, not necessarily
    linear in the message. As for the linear forms of Cb/Ld/LdRel.lean (`Slf`), the value is a
    parameter of a relation and the state is in the explicit part: a claim is x = (target, state).
  `Spec.ldBat_cnt_one`, `Spec.ldBat_cnt_list`: the bounds on the number of bad seeds.
  `Spec.ldBat_ex`: from `C.relsAll sl e core` to `C.rels (Slf.bat Z.ze sl) e core`, the same radius:
    a piece of a chain (`IOR.PieceTr` of Cb/Ld/LdTowerKit.lean, so `IOR.GoodT`): strings, local,
    perfectly complete, nothing to simulate, nothing withheld, knowledge sound with the identity as
    extractor and the one error L · err, L a bound for the list of C at e (`C.ListAt e L`,
    Cb/Ld/LdRel.lean: for every native word at most L pairs (message, randomness) have an encoding
    within e long positions of it).
    (not all hypotheses are named here: see its statement)

Why the list size: in the existential relaxation the witness is named after the seed: a prover may
choose, among the codewords near its word, one that the seed favours. So the union over the list is
paid. Where the message is a function of the statement (decoding with a sample), it is not:
`Spec.ldBat_cnt_one`.

Limits: `Evader.OK` with err ≥ the number of seeds holds for free, and an error L · err that reaches
the number of seeds says nothing. No bound on a list is proved here (bounds: `Spec.ld_list_johnson`,
`Spec.ld_list_unique`, Cb/Ld/LdRelJohnson.lean, each under its hypotheses). That a combination of
claims of some kind (sums of a polynomial over a cube, say) is again a claim of that kind is said
for linear forms only. This file says nothing on running times or succinctness.
The batched form and the union over the list follow a definition and a step of a proof of the paper
that this protocol builds on (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRel
import Cb.Gen.OodDec
import Cb.Ld.LdTowerKit
import Ior.Draw

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood

/-! ## Values with a state -/

/-- A value with a state: from states and messages to E. -/
abbrev Vf (E St M : Type) : Type := St → M → E

namespace Vf
variable {E St M B D : Type} {S : B → Type}

/-- The claim, x = (target, state): the value at (state, m) is the target. -/
def Holds (v : Vf E St M) : E × St → M → Prop := fun x m => v x.2 m = x.1

/-- A family of claims, x = (targets, states): all hold. -/
def All (v : ∀ b, Vf E (S b) M) : (B → E) × (∀ b, S b) → M → Prop := fun x m =>
  ∀ b, (v b).Holds (x.1 b, x.2 b) m

/-- The combination of the values v b, with the coefficients that Z makes from a seed. -/
def bat [Field E] [Fintype B] (Z : D → B → E) (v : ∀ b, Vf E (S b) M) : Vf E ((∀ b, S b) × D) M :=
  fun x m => ∑ b, Z x.2 b * v b (x.1 b) m

end Vf

/-- The new claim: the combination of the targets; the seed joins the states. -/
def batNx {E B D : Type} {S : B → Type} [Field E] [Fintype B] (Z : D → B → E) :
    (B → E) × (∀ b, S b) → D → E × ((∀ b, S b) × D) :=
  fun x ρ => (∑ b, Z ρ b * x.1 b, (x.2, ρ))

/-- the value of a linear form -/
def Slf.val {E St J : Type} [Field E] [Fintype J] (sl : Slf E St J) : Vf E St (J → E) := fun st m =>
  ∑ j, sl st j * m j

/-- Several rows: a family of linear claims, x = (targets, states). -/
def Slf.All {E J B : Type} {S : B → Type} [Field E] [Fintype J] (sl : ∀ b, Slf E (S b) J) :
    (B → E) × (∀ b, S b) → (J → E) → Prop :=
  fun x m => ∀ b, (sl b).Holds (x.1 b, x.2 b) m

/-- The coefficients (1 - ρ, ρ) for two claims. -/
@[reducible] def Evader.line (E : Type) [Field E] [Fintype E] : Evader E Bool :=
  { D := E, ze := fun ρ b => if b then ρ else 1 - ρ, err := 1 }

/-! ## Inside the existential relaxation -/

/-- For any code C read under a transformation (`LdCode`): the main relation of Cb/Ld/LdRel.lean
with several rows: x = (targets, states); the relaxation: the witness's encoding is within e long
positions of the word, and all rows hold of its message. -/
def LdCode.relsAll {E P : Type} [Field E] [Fintype E] [Finite P] {Kc B : Type} {S : B → Type}
    (C : LdCode E P) (sl : ∀ b, Slf E (S b) C.J) (e : ℕ) (core : C.N.Wit → Kc) :
    IOR.Rels Kc ((B → E) × (∀ b, S b)) C.ext C.N.Wit where
  rel  := Con C.N (Slf.All sl)
  relR := ConL C.N e (Slf.All sl)
  on   := fun _ => True
  core := core

section
variable {E P B : Type} [Field E] [Fintype E] [Fintype B] (C : LdCode E P)
  (S : B → Type) (Z : Evader E B)

/-- The batching: the verifier draws the seed. -/
abbrev ldBatEx : IOR ((B → E) × (∀ b, S b)) C.ext (E × ((∀ b, S b) × Z.D)) C.ext :=
  IOR.draw Z.D (batNx Z.ze) C.ext

/-- its honest side: nothing is sent, the witness stays -/
abbrev ldBatExH : (ldBatEx C S Z).Honest C.N.Wit C.N.Wit :=
  IOR.Honest.draw Z.D (batNx Z.ze) C.ext C.N.Wit

/-- its numbers: one error; nothing is withheld; every budget -/
abbrev ldBatExN (Kc : Type) (err : ℕ) : IOR.Nums Kc (ldBatEx C S Z) :=
  IOR.Nums.draw Kc Z.D (batNx Z.ze) C.ext err

end

/-! ## The statements -/

namespace Spec
open IOR

/-- All claims hold: then the new claim holds, at every seed. -/
def ldBat_fwd : Prop :=
  ∀ (E M B D : Type) [Field E] [Fintype B] (S : B → Type) (Z : D → B → E) (v : ∀ b, Vf E (S b) M)
      (x : (B → E) × (∀ b, S b)) (m : M) (ρ : D),
    Vf.All v x m → (Vf.bat Z v).Holds (batNx Z x ρ) m

/-- States: if `Z.OK`, for at most one candidate m, fixed before the seed, there are at most err
seeds at which the new claim holds of it though not all old claims do. No list size. -/
def ldBat_cnt_one : Prop :=
  ∀ (E M B : Type) [Field E] [Fintype B] (S : B → Type) (Z : Evader E B) (v : ∀ b, Vf E (S b) M)
      (x : (B → E) × (∀ b, S b)) (Q : M → Prop),
    Z.OK → (∀ m m', Q m → Q m' → m = m') →
    cnt (fun ρ : Z.D => ∃ m, Q m ∧ (Vf.bat Z.ze v).Holds (batNx Z.ze x ρ) m ∧ ¬ Vf.All v x m) ≤
      Z.err

/-- States: if `Z.OK`, for a finite type M of messages (`[Finite M]`) and a list of at most L
candidates, fixed before the seed, there are at most L · err seeds at which the new claim holds of
some member of which not all old claims hold: the union over the list. -/
def ldBat_cnt_list : Prop :=
  ∀ (E M B : Type) [Field E] [Fintype B] [Finite M] (S : B → Type) (Z : Evader E B)
      (v : ∀ b, Vf E (S b) M) (x : (B → E) × (∀ b, S b)) (Lst : M → Prop) (L : ℕ),
    Z.OK → ListLE Lst L →
    cnt (fun ρ : Z.D => ∃ m, Lst m ∧ (Vf.bat Z.ze v).Holds (batNx Z.ze x ρ) m ∧ ¬ Vf.All v x m) ≤
      L * Z.err

/-- For linear forms: the combination of the values is the value of the combined form. -/
def ldBat_slf : Prop :=
  ∀ (E J B D : Type) [Field E] [Fintype J] [Fintype B] (S : B → Type)
      (Z : D → B → E) (sl : ∀ b, Slf E (S b) J),
    (Slf.bat Z sl).val = Vf.bat Z fun b => (sl b).val

/-- The coefficients (1 - ρ, ρ) are a zero-evader with at most one bad value. -/
def ldBat_ok_line : Prop := ∀ (E : Type) [Field E] [Fintype E], (Evader.line E).OK

/-- The batching inside the existential relaxation. States, if `Z.OK` and `C.ListAt e L`: several
rows into one, at the same radius; the identity extracts; the error is L, a bound for the list of C
at e, times the evader's number. -/
def ldBat_ex : Prop :=
  ∀ (E P B Kc : Type) [Field E] [Fintype E] [Fintype P] [Fintype B] (C : LdCode E P)
      (S : B → Type) (sl : ∀ b, Slf E (S b) C.J) (Z : Evader E B) (e L : ℕ)
      (core : C.N.Wit → Kc) (q : Finset C.ext.Pos → Prop),
    Z.OK → C.ListAt e L →
    PieceTr (ldBatEx C S Z) (ldBatExH C S Z) (C.relsAll sl e core) (C.rels (Slf.bat Z.ze sl) e core)
      (fun _ _ w => w) (ldBatExN C S Z Kc (L * Z.err)) q q

end Spec
end Cb
