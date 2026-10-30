-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Know/TwOne.lean.
The assembled lookup as one reduction whose out-statement is a list of linear forms on the caller's
entries, and its knowledge soundness with the five arguments of `Iop.Reduction.Know` (Ior/Know.lean)
written out.

Definitions, statements and proofs. It stands on Cb/Pv/Lookup/Know/AsmKV.lean (the chain and its
knowledge soundness), OnBytes/Tie/Pv/Lookup/Value/TwForms.lean (the last step),
OnBytes/Tie/Pv/Lookup/Port/TwTies.lean and OnBytes/Tie/Pv/Lookup/Value/TwTeeth.lean (the small
lookup's numbers and its two relations) and Cb/Pv/Lookup/Know/TwSig.lean (`jn`, `Sig3`).
Main names, general in `A : LkAsmH E`:
  `oneK A kAt V VC Ex := (A.baseK V VC).postM (outA A kAt)`: the chain, then the last step. The
    out-statement is a list of rows (coefficients and a target): public data alone.
  `RBof l μ := ∀ r ∈ l, r.Holds μ`: the forms that the verifier puts out meet their targets. It
    reads the out-statement and the entries, and nothing else.
  `one_knowAt`: `KnowAt` between the base joints `jn Ex msg A.lk.inR` and `jn Ex msg RBof` (their
    condition is `fun _ => True`); the identity extracts; for every V, VC, Ex, M, msg.
At the small lookup `o65A` (OnBytes/Tie/Pv/Lookup/Value/TwO65.lean: one part, no shift, all planes
counting, the range table of two rows; 15 keys, 16 plane entries, 104 mask entries; 65 rounds:
`o65R_len`, OnBytes/Tie/Pv/Lookup/Know/TwOneR.lean):
  `o65R V VC Ex`, `o65Eps V VC Ex`: the reduction and its errors, applied to the two records.
  `o65_know_vec`: knowledge soundness for every vector of entries. The vector is fixed before the
    run; the further witness is Unit and the identity extracts.
  `o65_know`: the same for every signature S with `Sig3 S (Fin 15) (Fin 16) (Fin 104)` and every
    `m : S.Msg`, between base joints over `S.Msg × Unit`. The in-relation is `o65RA`: every key that
    is not padding is a row of the table (`∀ b : Fin 15, ∃ u < 2, μ (.inl b) = u`).
  `o65_know_sig`: over every such signature, by `sigLift_know` (through `sig3_know`).
  `o65_sig_source`, `o65_sig_holds`, `o65_sig_fails`: over the plain signature the in-relation of
    `o65_know_sig` holds at some collision-free statement and fails at another.
Premises: at the small lookup none but the two records V, VC (and Ex, S, `h : Sig3 ..`, data on the
shape of S). `ShortK`, `ShortKC` (Cb/G6/Letter.lean) are records of a sumcheck's verifier with, as
a field, a proof of its knowledge soundness; `V₀`, `V₀C` (Cb/G6/Pick.lean) fill the two types. In
general form: `A.H.lkb.Adm p`, `CharP E p`, `padsOK .. = true`,
`A.n + 1 + 1 = 2 ^ A.w`, `KeyRd A kAt`. None reads a message, a witness or a transcript.
Limits: for the interactive form. The end claims are handed on, not tested: no opening, proximity
test or commitment stands in these reductions. `ShortK` lays no law on what its verifier accepts,
so a statement for every V, VC says nothing on what is accepted or handed on. `o65_know_sig` speaks
of collision-free statements alone; nothing here shows that a statement over a given S is
collision-free, but for the plain signature `S65` (the word is the message; radius 0; no sample).
This file says nothing on an honest prover.

-/
import Cb.Pv.Lookup.Know.AsmKV
import OnBytes.Tie.Pv.Lookup.Value.TwTeeth
import Cb.Pv.Lookup.Know.TwSig

set_option autoImplicit false

namespace Cb.Tw
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole

/-- The forms of the out-statement meet their targets at the entries μ. -/
def RBof {E J : Type} [Field E] [Fintype J] (l : List (Row E J)) (μ : J → E) : Prop := ∀ r ∈ l,
    r.Holds μ

section General
variable {E : Type} [Field E] [Fintype E]

/-- General in A: the chain, then the last step onto linear forms on the caller's entries. -/
noncomputable def oneK (A : LkAsmH E) (kAt : ℕ → A.J ⊕ E) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
    (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) (Ex : ExtSpec) : BkK A.St (List (Row E A.J)) Ex :=
  (A.baseK V VC (Ex := Ex)).postM (outA A kAt)

/-- Knowledge soundness of the whole lookup, between the base joints of
Cb/Pv/Lookup/Know/TwSig.lean. -/
theorem one_knowAt (p : ℕ) [CharP E p] (A : LkAsmH E) (kAt : ℕ → A.J ⊕ E) (hk : KeyRd A kAt)
    (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) (Ex : ExtSpec)
        (M : Type)
    (msg : M → A.J → E) (hA : A.H.lkb.Adm p) (hP : padsOK (A.v' + 1) A.d A.pads = true)
    (hF : A.n + 1 + 1 = 2 ^ A.w) :
    KnowAt (oneK A kAt V VC Ex).R (jn Ex msg A.lk.inR) (jn Ex msg RBof) (fun _ _ _ wp => wp) (oneK A
        kAt V VC Ex).e := by
  have g := asmK_base E p A (fun _ _ => True) Ex Unit M Unit (PscLtK.ofShort V VC Ex)
    (jn Ex msg fun _ _ => True) msg (asmK_shortOK E A V VC Ex M Unit Unit msg) hA hP hF
  have g' : (oneK A kAt V VC Ex).Know
      (cj (jn Ex msg fun _ _ => True) msg id (A.lk.inP fun _ _ => True) A.lk.inR) (jn Ex msg RBof)
          :=
    know_postM (outA A kAt) g (fun _ _ _ => trivial)
      (fun x _ w _ h => ⟨trivial, (out_iff A kAt hk x (msg w.1)).2 h⟩)
  exact knowAt_congr g' rfl
    (funext fun a => funext fun w => propext ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩) rfl rfl

end General

/-! ### At the small lookup -/

/-- the block at the small lookup, applied to the two records -/
noncomputable def o65K (V : ∀ (Y : PscPar K) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar K) Ex, ShortKC Y
    Ex)
    (Ex : ExtSpec) : BkK Unit (List (Row K o65J)) Ex :=
  oneK o65A (kAt K TwNums.o65S) V VC Ex

/-- The reduction: one constant applied to the two records. -/
noncomputable def o65R (V : ∀ (Y : PscPar K) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar K) Ex, ShortKC Y
    Ex)
    (Ex : ExtSpec) : IOR Unit Ex (List (Row K o65J)) Ex := (o65K V VC Ex).R

/-- its errors: one number a round -/
noncomputable def o65Eps (V : ∀ (Y : PscPar K) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar K) Ex, ShortKC Y
    Ex)
    (Ex : ExtSpec) : Err (o65R V VC Ex).shape := (o65K V VC Ex).e

section
variable (V : ∀ (Y : PscPar K) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar K) Ex, ShortKC Y Ex) (Ex :
    ExtSpec)

/-- `KnowAt` at the small lookup, for every reading msg. -/
theorem o65_knowAt (M : Type) (msg : M → o65J → K) :
    KnowAt (o65R V VC Ex) (jn Ex msg fun _ => o65RA) (jn Ex msg RBof) (fun _ _ _ wp => wp) (o65Eps V
        VC Ex) :=
  knowAt_congr
    (one_knowAt Cb.Gl.p o65A (kAt K TwNums.o65S) (keyA_rd _ _) V VC Ex M msg o65_adm o65_padsOK
        o65_full)
    rfl (funext fun _ => funext fun w => propext (o65_RA_iff (msg w.1)).symm) rfl rfl

/-- For every vector of the caller's entries; the five arguments of `Know` written out. -/
theorem o65_know_vec (μ : o65J → K) :
    (o65R V VC Ex).red.Know (fun _ => True) (fun _ (_ : Unit) => o65RA μ) (fun b (_ : Unit) => RBof
        b.1 μ)
      (fun _ _ wp => wp) (o65Eps V VC Ex) :=
  (o65_knowAt V VC Ex (o65J → K) id).know μ

/-- For each tuple of messages. The joints are base joints over S.Msg × Unit; the condition is
`fun _ => True` by rfl; the identity extracts. -/
theorem o65_know (S : Sig K) (h : Sig3 S (Fin 15) (Fin 16) (Fin 104)) (m : S.Msg) :
    (o65R V VC Ex).red.Know (jn Ex h.msg fun _ => o65RA).on
      (fun a wp => (jn Ex h.msg fun (_ : Unit) => o65RA).relR a (m, wp))
      (fun b wp => (jn Ex h.msg RBof).relR b (m, wp)) (fun _ _ wp => wp) (o65Eps V VC Ex) :=
  sig3_at S h (o65R V VC Ex) (fun _ => o65RA) RBof (o65Eps V VC Ex) (o65_know_vec V VC Ex) m

/-- For every `S : Sig Cb.Gl.E` with three messages whose entries are Fin 15, Fin 16, Fin 104. -/
theorem o65_know_sig (S : Sig K) (h : Sig3 S (Fin 15) (Fin 16) (Fin 104)) :
    ((o65R V VC Ex).keep S.Smp S.ext).red.Know (S.over (jn Ex h.msg fun (_ : Unit) => o65RA)).on
      (S.over (jn Ex h.msg fun (_ : Unit) => o65RA)).relR (S.over (jn Ex h.msg RBof)).relR (fun _ _
          w => w)
      (o65Eps V VC Ex) :=
  sig3_know S h (o65R V VC Ex) (fun _ => o65RA) RBof (o65Eps V VC Ex) (o65_know_vec V VC Ex)

/-! The arguments, by rfl. -/
example (S : Sig K) (h : Sig3 S (Fin 15) (Fin 16) (Fin 104)) :
    (jn Ex h.msg fun (_ : Unit) => o65RA).on = fun _ => True := rfl
example (S : Sig K) (h : Sig3 S (Fin 15) (Fin 16) (Fin 104)) (a : Unit × Ex.Str) (m : S.Msg) :
    (jn Ex h.msg fun (_ : Unit) => o65RA).relR a (m, ()) = o65RA (h.msg m) := rfl
example (S : Sig K) (h : Sig3 S (Fin 15) (Fin 16) (Fin 104)) (b : List (Row K o65J) × Ex.Str) (m :
    S.Msg) :
    (jn Ex h.msg RBof).relR b (m, ()) = ∀ r ∈ b.1, r.Holds (h.msg m) := rfl
/-- over a signature the condition is: collision-free, and no more -/
example (S : Sig K) (h : Sig3 S (Fin 15) (Fin 16) (Fin 104)) :
    (S.over (jn Ex h.msg fun (_ : Unit) => o65RA)).on = fun a => S.CF a.1.2 a.2.2 ∧ True := rfl
/-- the verifier is the chain of Cb/Pv/Lookup/Know/AsmKV.lean at `o65A`, then the last step `o65Out`
-/
example : o65R V VC Ex = ((o65A.baseK V VC (Ex := Ex)).postM o65Out).R := rfl
example : o65Eps V VC Ex = (o65A.baseK V VC (Ex := Ex)).e := rfl
/-- `RBof` is `o65RB` (on the chain's read-out) and `o65RBb` (on the out-statement) of
OnBytes/Tie/Pv/Lookup/Value/TwTeeth.lean -/
example (x : TX Unit K o65J) (μ : o65J → K) : o65RB x μ = RBof (o65Out x) μ := rfl
example (b : List (Row K o65J)) (μ : o65J → K) : o65RBb b μ = RBof b μ := rfl

end

/-- the plain signature and its shape -/
abbrev S65 : Sig K := sigId3 K (Fin 15) (Fin 16) (Fin 104)
def h65 : Sig3 S65 (Fin 15) (Fin 16) (Fin 104) := sig3Id K (Fin 15) (Fin 16) (Fin 104)

/-- A signature with the three messages exists, and over it, for every vector of entries, a
collision-free statement and a witness with these entries, at which the in-relation of
`o65_know_sig` holds exactly if `o65RA` holds of the entries. -/
theorem o65_sig_source (Ex : ExtSpec) (y : Ex.Str) (μ : o65J → K) :
    ∃ (a : (Unit × S65.Smp) × (Ex.prod S65.ext).Str) (w : S65.Wit × Unit),
      h65.msg (S65.msgs w.1) = μ ∧ (S65.over (jn Ex h65.msg fun (_ : Unit) => o65RA)).on a ∧
      ((S65.over (jn Ex h65.msg fun (_ : Unit) => o65RA)).relR a w ↔ o65RA μ) := by
  obtain ⟨a, w, _, h2, h3, h4⟩ :=
    sig3Id_source K (Fin 15) (Fin 16) (Fin 104) Ex (fun (_ : Unit) => o65RA) () y μ
  exact ⟨a, w, h2, h3, h4⟩

/-- At the keys `OnBytes.Lkp.o65Keys` there is a collision-free statement and a witness in the
in-relation of `o65_know_sig`. -/
theorem o65_sig_holds (Ex : ExtSpec) (y : Ex.Str) :
    ∃ (a : (Unit × S65.Smp) × (Ex.prod S65.ext).Str) (w : S65.Wit × Unit),
      ClosedKeys (h65.msg (S65.msgs w.1)) ∧ (S65.over (jn Ex h65.msg fun (_ : Unit) => o65RA)).on a
          ∧
      (S65.over (jn Ex h65.msg fun (_ : Unit) => o65RA)).relR a w := by
  obtain ⟨μ, hμ⟩ := closed_exists
  obtain ⟨a, w, h1, h2, h3⟩ := o65_sig_source Ex y μ
  exact ⟨a, w, h1 ▸ hμ, h2, h3.2 (RA_closed μ hμ)⟩

/-- And a collision-free statement and a witness that are not in that in-relation. The statement
does not say why; in the proof every entry of the witness is 5, and key 2 equal to 5 is no row. -/
theorem o65_sig_fails (Ex : ExtSpec) (y : Ex.Str) :
    ∃ (a : (Unit × S65.Smp) × (Ex.prod S65.ext).Str) (w : S65.Wit × Unit),
      (S65.over (jn Ex h65.msg fun (_ : Unit) => o65RA)).on a ∧
      ¬ (S65.over (jn Ex h65.msg fun (_ : Unit) => o65RA)).relR a w := by
  obtain ⟨a, w, _, h2, h3⟩ := o65_sig_source Ex y (fun _ => 5)
  exact ⟨a, w, h2, fun h => RA_false_a (fun _ => 5) rfl (h3.1 h)⟩

end Cb.Tw
#print axioms Cb.Tw.one_knowAt
#print axioms Cb.Tw.o65_knowAt
#print axioms Cb.Tw.o65_know_vec
#print axioms Cb.Tw.o65_know
#print axioms Cb.Tw.o65_know_sig
#print axioms Cb.Tw.o65_sig_source
#print axioms Cb.Tw.o65_sig_holds
#print axioms Cb.Tw.o65_sig_fails
