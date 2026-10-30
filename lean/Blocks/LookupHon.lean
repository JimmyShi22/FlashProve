-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupHon.lean: the lookup argument's honest prover; completeness of every step, masked form
of every step that has a round.

Blocks/LookupBlock.lean defines the argument's steps as blocks, with the relations for soundness.
This file gives each block its honest prover (`Hon`, Blocks/BlockHon.lean) and proves completeness
(`Hon.AccOn`) and masked form (`Hon.Masked`) step by step. (Words of this library:
lean/GLOSSARY.md.)

The state: `LkA`, with the prover's copy `HLed` of the list of deferred claims (`Ledger`,
Blocks/Form.lean). It holds no pad.

Completeness. `Lk.accOn_hAl`, .., `Lk.accOn_hRec`: one theorem for each step, under its hypotheses,
for all pads and at every value ρ of the verifier's randomness outside the public bad set
(`Hon.Bad`, Blocks/BlockHon.lean); together: `Lk.props_stLookup` (Blocks/LookupStage.lean), field
`acc`. That set: a coordinate of ϱ, ϱ3, ϱ5, ϱ' or a challenge of a layer of the two forests is 0; of
the last layer of the key side, whose challenges are the coordinates of the end point z, only one
that `LkPar.zf` selects. The relations: before the argument: `Lk.Lnk0` T U a π led y (y the implicit
part, U a set of pads), which includes `Lk.TF`; after it: `Lk.H10`: the end claim (without its
premise), the two claims on ~B and the degree claim are true.

Notation:
 * D, σ, r, lp, NT: natural numbers, fields of `LkPar`: 2^D keys in a tree, NT trees, tables with
   2^r entries, 2^lp bits for a multiplicity; σ: the number of bits of a tree's index
   (Blocks/LookupRel.lean; σ: the head of Blocks/LookupWhole.lean).
 * gT: `LkPar.gT` = r + σ + lp: the number of variables of the leaves of the table side; Pm:
   `LkPar.Pm` = 2^lp - 1: the number of the highest plane (Blocks/LookupRel.lean).
 * α, ϱ, ϱ3, ϱ5, ϱ': the verifier's messages of the blocks `bAl`, `bZY`, `bT0`, `bB0`, `bUV` (the
   head of Blocks/LookupBlock.lean).
 * `Hon.AccOn` H Hi Ho: pointwise completeness (Blocks/BlockHon.lean).
 * `Hon.Masked` H V U D Sim, with H : Hon B P E Ii Io, V : Ii → Prop, U, D : Set P, Sim : Rho
   B.shape → PMF (Plains B.shape): see its definition, Blocks/BlockHon.lean.
 * `ext` g v pt, written ~v(pt): the multilinear extension of the vector v of length 2^g at the
   point pt (Blocks/Ext.lean).

Two limits. (1) `Lk.Lnk0` asks that the keys and the bits B of the state are those of y as functions
on all natural numbers, also outside the ranges θ < N_T, i < 2^D, ..: so both should be defined by
the same expression, or be cut off in the same way outside the ranges. (2) `Lk.Lnk0` says proj y
(place q) = π q for every pad q in U. If `place` sends two pads of the argument to one entry, no y
satisfies this for all π, and completeness says nothing. `Lk.PadsOK` is about the thirteen maps into
Pd only; that `place` is injective on the places of the argument is left to the containing protocol.

Masked form, under `Lk.PadsOK` and `LkPar.OrdOK`: outside the withheld set (`Hon.withheld`,
Blocks/BlockHon.lean) each step masks with the pads at the places of its group (`Lk.grp`) and reads
no other pad: `masked_hZY`, `masked_hK`, .., `masked_hRs`. `Lk.PadsOK` says that no place is used
twice. π is the family of pads in relations and the number of a bit plane in indices (θ, π); `Lk.hB`
is the honest prover of the bit layer, `Lk.Vecs.B` the true bits.
-/
import Blocks.LookupBlock
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob

/-! ## 1. The honest prover's copy of the list of deferred claims -/

/-- The honest prover's copy of the list of deferred claims, for the closing block
(Blocks/ClosingBlock.lean): the number of LIN, the values of the opened forms, the terms of the REL.
It holds no pad. -/
structure HLed (E : Type) where
  nl : ℕ
  ov : List E
  tm : List (List (E × ℕ × ℕ))

namespace HLed

variable {N E : Type}

def addProd [One E] (h : HLed E) (e0 e1 : E) : HLed E :=
  ⟨h.nl, h.ov ++ [e0, e1], h.tm ++ [[(1, h.ov.length, h.ov.length + 1)]]⟩
def addLin (h : HLed E) : HLed E := ⟨h.nl + 1, h.ov, h.tm⟩
def addRel (h : HLed E) (vs : List E) (ts : List (E × ℕ × ℕ)) : HLed E :=
  ⟨h.nl, h.ov ++ vs, h.tm ++ [ts.map fun t => (t.1, h.ov.length + t.2.1, h.ov.length + t.2.2)]⟩

variable [Fintype N] [CommRing E]

/-- The copy matches the list `led`, at the entries y. -/
def Of (h : HLed E) (led : Ledger N E) (y : N → E) : Prop :=
  led.lin.length = h.nl ∧
  led.opn.map (fun f => Form.val y f) = h.ov ∧
  led.rel.map (fun r => r.2) = h.tm

theorem Of.length {h : HLed E} {led : Ledger N E} {y : N → E} (H : h.Of led y) :
    led.opn.length = h.ov.length := by
  rw [← H.2.1, List.length_map]

theorem Of.addProd {h : HLed E} {led : Ledger N E} {y : N → E} (H : h.Of led y) (f a b : Form N E) :
    (h.addProd (Form.val y a) (Form.val y b)).Of (led.addProd f a b) y := by
  refine ⟨H.1, ?_, ?_⟩
  · simp [Ledger.addProd, HLed.addProd, H.2.1]
  · simp [Ledger.addProd, HLed.addProd, H.2.2, H.length]

theorem Of.addLin {h : HLed E} {led : Ledger N E} {y : N → E} (H : h.Of led y) (f : Form N E) :
    h.addLin.Of (led.addLin f) y := by
  refine ⟨?_, H.2.1, H.2.2⟩
  simp [Ledger.addLin, HLed.addLin, H.1]

theorem Of.addRel {h : HLed E} {led : Ledger N E} {y : N → E} (H : h.Of led y) (f : Form N E)
    (os : List (Form N E)) (ts : List (E × ℕ × ℕ)) :
    (h.addRel (os.map fun g => Form.val y g) ts).Of (led.addRel f os ts) y := by
  refine ⟨H.1, ?_, ?_⟩
  · simp [Ledger.addRel, HLed.addRel, H.2.1]
  · simp [Ledger.addRel, HLed.addRel, H.2.2, H.length]

end HLed

/-! ## 2. The honest state -/

/-- The honest prover's state in a lookup argument. The keys and the bits B; its copy of the list of
deferred claims; the challenges so far. It holds no pad. -/
structure LkA (E : Type) where
  key : ℕ → ℕ → E
  B : ℕ → ℕ → ℕ → E
  hl : HLed E
  al : E
  pt : ℕ → E
  z : ℕ → E
  p4 : ℕ → E
  p5 : ℕ → E
  p6 : ℕ → E
  pr : ℕ → E
  cx : ℕ → E

namespace Lk

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] (L : Lk E Y Pd N) (T : Lk.Vecs E Y)

/-- The honest facts on keys and multiplicities: the B are bits, the degree check holds, and the
identity `LkPar.Ident` holds for the true products at every α (`LkPar.HonB`, Blocks/LookupRel.lean,
gives all three if D < 2^lp). -/
def TF (y : Y) : Prop :=
  L.par.Bits (T.B y) ∧ L.par.DegE (T.B y) ∧
  ∀ al, L.par.Ident al (L.par.Zt (T.key y) al) (L.par.Yt (T.B y) al)

/-- The state matches the implicit part and the list: keys and B are those of y, each pad in U is
the entry of y that `place` names, the list passes `Ledger.wf` and is true, the state has its copy,
and `TF` holds. -/
def Lnk0 (U : Set Pd) (a : LkA E) (π : Pd → E) (led : Ledger N E) (y : Y) : Prop :=
  a.key = T.key y ∧ a.B = T.B y ∧ (∀ p ∈ U, L.proj y (L.place p) = π p) ∧
  led.wf = true ∧ led.True (L.proj y) ∧ a.hl.Of led (L.proj y) ∧ (L.TF T) y

/-- The state holds the challenges that the explicit part of the statement holds. -/
def Pub (a : LkA E) (x : LkX N E) : Prop :=
  a.al = x.al ∧ a.z = x.z ∧ a.p4 = x.p4 ∧ a.p5 = x.p5 ∧ a.p6 = x.p6 ∧ a.pr = x.pr ∧ a.cx = x.cx

/-- `Lnk0` inside the argument: also the challenges are those of the statement. -/
def Lnk (U : Set Pd) (a : LkA E) (π : Pd → E) (x : LkX N E) (y : Y) : Prop :=
  (L.Lnk0 T) U a π x.led y ∧ Pub a x

/-! ## 3. Step 1: α -/

@[reducible] def hAl : Hon L.bAl Pd E (LkA E) (LkA E) :=
  Hon.one (fun _ _ => (fun e => Empty.elim e, fun k => Empty.elim k))
    (fun a al =>
      ⟨a.key, a.B, a.hl, al, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
        fun _ => 0, fun _ => 0⟩)
    ∅ fun _ => ∅

omit [DecidableEq E] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem accOn_hAl (U : Set Pd) : L.hAl.AccOn (L.Lnk0 T U) (L.Lnk T U) :=
  Hon.accOn_one fun _ _ _ _ _ hi _ _ => ⟨_, rfl, hi, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 4. Step 2 and the start of the key side -/

/-- The honest tree products, masked. -/
def msgZY (a : LkA E) (π : Pd → E) : L.KZY → E
  | .inl θ => L.par.Zt a.key a.al θ + π (L.pZ θ)
  | .inr (θ, π') => L.par.Yt a.B a.al θ π' + π (L.pY θ π')

@[reducible] def hZY : Hon L.bZY Pd E (LkA E) (LkA E) :=
  Hon.one (fun a π => (fun e => Empty.elim e, L.msgZY a π)) (fun a ϱ => { a with pt := nat ϱ })
    {ϱ | nzT ϱ = false} fun _ => ∅

/-- The places of the pads of Z and Y. -/
def padsZY : Set Pd :=
  {p | (∃ θ < L.par.NT, p = L.pZ θ) ∨ ∃ θ < L.par.NT, ∃ π < 2 ^ L.par.lp, p = L.pY θ π}

/-- The sent tree products are the true ones. -/
def TZ (x : LkX N E) (y : Y) : Prop :=
  (∀ θ < L.par.NT, L.V y (x.Zf θ) = L.par.Zt (T.key y) x.al θ) ∧ (L.YT T) x y

/-- The running point is that of the state, and none of its first g coordinates is 0. -/
def PT (g : ℕ) (a : LkA E) (x : LkX N E) : Prop := a.pt = x.pt ∧ ∀ t < g, x.pt t ≠ 0

/-- Inside the key side, at level l: the relation for the honest run. -/
def HK (U : Set Pd) (l : ℕ) (a : LkA E) (π : Pd → E) (x : LkX N E) (y : Y) : Prop :=
  (L.Lnk T) U a π x y ∧
  (L.TZ T) x y ∧
  (a.pt = x.pt ∧ ∀ t < l + L.par.σ, L.par.kf l t = true → x.pt t ≠ 0) ∧
  L.V y x.C = ext (l + L.par.σ) (L.par.kLev (T.key y) x.al l) x.pt

omit [NeZero (2 : E)] in
theorem accOn_hZY {U : Set Pd} (hU : L.padsZY ⊆ U) : L.hZY.AccOn (L.Lnk T U) (L.HK T U 0) :=
  Hon.accOn_one fun a π x y ϱ hi hb _ => by
    have hnz : nzT ϱ = true := by
      cases h : nzT ϱ
      · exact absurd h hb
      · rfl
    obtain ⟨⟨hk, hB, hp, hrest⟩, hpub⟩ := hi
    have hal := hpub.1
    have hZ : ∀ θ < L.par.NT, L.V y (L.zForm (L.msgZY a π) θ) = L.par.Zt (T.key y) x.al θ := by
      intro θ hθ
      unfold zForm
      rw [dif_pos hθ]
      change Form.val (L.proj y) _ = _
      rw [Form.val_masked, hp _ (hU (Or.inl ⟨θ, hθ, rfl⟩))]
      show L.par.Zt a.key a.al θ + π (L.pZ θ) - π (L.pZ θ) = _
      rw [add_sub_cancel_right, hk, hal]
    have hY : ∀ θ < L.par.NT,
        ∀ π' < 2 ^ L.par.lp, L.V y (L.yForm (L.msgZY a π) θ π') = L.par.Yt (T.B y) x.al θ π' := by
      intro θ hθ π' hπ'
      unfold yForm
      rw [dif_pos ⟨hθ, hπ'⟩]
      change Form.val (L.proj y) _ = _
      rw [Form.val_masked, hp _ (hU (Or.inr ⟨θ, hθ, π', hπ', rfl⟩))]
      show L.par.Yt a.B a.al θ π' + π (L.pY θ π') - π (L.pY θ π') = _
      rw [add_sub_cancel_right, hB, hal]
    refine ⟨_, if_pos hnz, ⟨⟨hk, hB, hp, hrest⟩, hpub⟩, ⟨hZ, hY⟩,
      ⟨rfl, fun t ht _ => nat_ne_zero_of_nzT hnz t (by omega)⟩, ?_⟩
    show Form.val (L.proj y) (extF L.par.σ (L.par.msk (L.zForm (L.msgZY a π))) (nat ϱ)) =
      ext (0 + L.par.σ) (L.par.kLev (T.key y) x.al 0) (nat ϱ)
    rw [Nat.zero_add, val_extF]
    refine ext_congr (fun θ hθ => ?_) _
    rw [LkPar.val_msk, L.par.kLev_zero _ _ hθ]
    unfold LkPar.msk
    split_ifs with hN
    · exact hZ θ hN
    · rfl

/-! ## 5. The key side -/

/-- What a product layer preserves: the state has the keys, B and the challenges of the statement,
and its copy of the list. -/
def Inv (a : LkA E) (_ : Pd → E) (led : Ledger N E) (ξ : LkX N E) (y : Y) : Prop :=
  a.key = T.key y ∧ a.B = T.B y ∧ a.hl.Of led (L.proj y) ∧ Pub a ξ

/-- After a layer the state stores the next point, and the values of v0 and v1 in its copy of the
list. -/
def setA (a : LkA E) (p : ℕ → E) (e0 e1 : E) : LkA E := { a with pt := p, hl := a.hl.addProd e0 e1 }

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem inv_setA (a : LkA E) (p : ℕ → E) (π : Pd → E) (led : Ledger N E) (ξ : LkX N E) (y : Y)
    (f w0 w1 : Form N E) (h : (L.Inv T) a π led ξ y) :
    (L.Inv T) (setA a p (Form.val (L.proj y) w0) (Form.val (L.proj y) w1)) π
      (led.addProd f w0 w1) ξ y :=
  ⟨h.1, h.2.1, h.2.2.1.addProd f w0 w1, h.2.2.2⟩

@[reducible] def prK (l : ℕ) : (L.plK l).Prover (LkA E) where
  pt a := a.pt
  f0 a X := L.par.kLev a.key a.al (l + 1) X
  f1 a X := L.par.kLev a.key a.al (l + 1) (X + 2 ^ (l + L.par.σ))
  set := setA

@[reducible] def hK (l : ℕ) : Hon (L.bK l) Pd E (LkA E) (LkA E) :=
  (L.prK l).pl.on gxPL pxPL id (fun _ yo => yo) id (fun _ ao => ao)

theorem accOn_hK (ho : L.par.OrdOK) {U : Set Pd} {l : ℕ}
    (hl : l < L.par.D) (hU : (L.plK l).pads ⊆ U) :
    (L.hK l).AccOn (L.HK T U l) ((L.HK T) U (l + 1)) :=
  ((L.prK l).accOn_pl (L.vK T l) (L.Inv T) (ho.kOrd l) (fun _ _ _ _ => rfl) (L.inv_setA T)).on'
      fun a π x y hR => by
    obtain ⟨⟨⟨hk, hB, hp, hwf, htrue, hof, htf⟩, hpu⟩, htz, ⟨hpt, hnz⟩, hC⟩ := hR
    have hal := hpu.1
    refine ⟨⟨⟨hpt.symm, ?_, ?_, fun p hp' => hp p (hU hp'), hwf, htrue, hk, hB, hof, hpu⟩,
        fun t ht => hnz t ht (L.par.kf_of_lt hl t),
        ?_⟩,
      fun ρ xo _ hpub hO => ?_⟩
    · show (fun X => L.par.kLev (T.key y) x.al (l + 1) X) = fun X => L.par.kLev a.key a.al (l + 1) X
      rw [hk, hal]
    · show (fun X => L.par.kLev (T.key y) x.al (l + 1) (X + 2 ^ (l + L.par.σ))) =
        fun X => L.par.kLev a.key a.al (l + 1) (X + 2 ^ (l + L.par.σ))
      rw [hk, hal]
    · show Form.val (L.proj y) x.C =
        ext (l + L.par.σ)
          (fun X =>
            L.par.kLev (T.key y) x.al (l + 1) X *
              L.par.kLev (T.key y) x.al (l + 1) (X + 2 ^ (l + L.par.σ))) x.pt
      rw [← L.par.ext_kLev (T.key y) x.al hl]
      exact hC
    · have e : (L.plK l).pl.imp (id y) ((L.prK l).pl.tr (id a) π ρ) = y := (L.plK l).imp_pl _ _
      rw [e] at hO ⊢
      have hpb : xo.1.pub = x := (L.plK l).pub_of_pl hpub
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hO
      rw [hpb] at h5 h6
      refine ⟨⟨⟨h6.1, h6.2.1, hp, h3, h4.1, h6.2.2.1, htf⟩, h6.2.2.2⟩,
        htz,
        ⟨h1.symm, fun t ht hf => h2 t (by show t < l + L.par.σ + 1; omega) hf⟩,
        ?_⟩
      show Form.val (L.proj y) xo.1.C =
        ext (l + 1 + L.par.σ) (L.par.kLev (T.key y) x.al (l + 1)) xo.1.pt
      rw [show l + 1 + L.par.σ = l + L.par.σ + 1 by omega, ← consPt_eta xo.1.pt, ext_succ_consPt]
      exact h5

/-- The end claim for the honest run: true, without premise (that of `Lk.END`,
Blocks/LookupBlock.lean); and no coordinate of the end point that the verifier checks is 0. -/
def ENDh (x : LkX N E) (y : Y) : Prop :=
  (∀ t < L.par.D + L.par.σ, L.par.zf t = true → x.z t ≠ 0) ∧
  L.V y x.Cend = ext (L.par.D + L.par.σ) (L.par.leafK (T.key y) x.al) x.z

def H3 (U : Set Pd) (a : LkA E) (π : Pd → E) (x : LkX N E) (y : Y) : Prop :=
  (L.Lnk T) U a π x y ∧ (L.TZ T) x y ∧ (L.ENDh T) x y

@[reducible] def hKe : Hon L.bKe Pd E (LkA E) (LkA E) := Hon.pure _ id fun a => { a with z := a.pt }

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem accOn_hKe (U : Set Pd) : L.hKe.AccOn (L.HK T U L.par.D) (L.H3 T U) :=
  Hon.accOn_pure fun a π x y hi => by
    obtain ⟨⟨hl, hpu⟩, htz, ⟨hpt, hnz⟩, hC⟩ := hi
    refine ⟨_, rfl, ⟨hl, hpu.1, hpt, hpu.2.2⟩, htz,
      fun t ht hf => hnz t ht ((L.par.kf_top t).trans hf), ?_⟩
    rw [L.par.kLev_top] at hC
    exact hC

/-! ## 6. The table side -/

def HT (U : Set Pd) (l : ℕ) (a : LkA E) (π : Pd → E) (x : LkX N E) (y : Y) : Prop :=
  (L.Lnk T) U a π x y ∧ (L.TZ T) x y ∧ (L.ENDh T) x y ∧ PT (l + (L.par.σ + L.par.lp)) a x ∧
    L.V y x.C = ext (l + (L.par.σ + L.par.lp)) (L.par.tLev (T.B y) x.al l) x.pt

@[reducible] def hT0 : Hon L.bT0 Pd E (LkA E) (LkA E) :=
  Hon.one (fun _ _ => (fun e => Empty.elim e, fun k => Empty.elim k))
    (fun a ϱ => { a with pt := nat ϱ }) {ϱ | nzT ϱ = false} fun _ => ∅

omit [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem accOn_hT0 (U : Set Pd) (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    L.hT0.AccOn (L.H3 T U) (L.HT T U 0) :=
  Hon.accOn_one fun a π x y ϱ hi hb _ => by
    have hnz : nzT ϱ = true := by
      cases h : nzT ϱ
      · exact absurd h hb
      · rfl
    obtain ⟨hl, htz, hend⟩ := hi
    refine ⟨_, if_pos hnz, hl, htz, hend,
      ⟨rfl, fun t ht => nat_ne_zero_of_nzT hnz t (by omega)⟩, ?_⟩
    show Form.val (L.proj y) (extF (L.par.σ + L.par.lp) (L.yFlat x.Yf) (nat ϱ)) =
      ext (0 + (L.par.σ + L.par.lp)) (L.par.tLev (T.B y) x.al 0) (nat ϱ)
    rw [Nat.zero_add, val_extF]
    have h0 := (L.par.dY_eq_zero_iff hnt (T.B y) x.al fun θ π => L.V y (x.Yf θ π)).mpr htz.2
    refine ext_congr (fun u hu => ?_) _
    have h1 := sub_eq_zero.mp (h0 u hu)
    rw [← h1]
    unfold yFlat
    split_ifs
    · rfl
    · exact map_zero _

@[reducible] def prT (l : ℕ) : (L.plT l).Prover (LkA E) where
  pt a := a.pt
  f0 a X := L.par.tLev a.B a.al (l + 1) X
  f1 a X := L.par.tLev a.B a.al (l + 1) (X + 2 ^ (l + (L.par.σ + L.par.lp)))
  set := setA

@[reducible] def hT (l : ℕ) : Hon (L.bT l) Pd E (LkA E) (LkA E) :=
  (L.prT l).pl.on gxPL pxPL id (fun _ yo => yo) id (fun _ ao => ao)

theorem accOn_hT {U : Set Pd} {l : ℕ} (hl : l < L.par.r) (hU : (L.plT l).pads ⊆ U) :
    (L.hT l).AccOn (L.HT T U l) ((L.HT T) U (l + 1)) :=
  ((L.prT l).accOn_pl (L.vT T l) (L.Inv T) (List.Perm.refl _)
        (fun _ _ _ _ => rfl) (L.inv_setA T)).on'
      fun a π x y hR => by
    obtain ⟨⟨⟨hk, hB, hp, hwf, htrue, hof, htf⟩, hpu⟩, htz, hend, ⟨hpt, hnz⟩, hC⟩ := hR
    have hal := hpu.1
    refine ⟨⟨⟨hpt.symm, ?_, ?_, fun p hp' => hp p (hU hp'), hwf, htrue, hk, hB, hof, hpu⟩, hnz, ?_⟩,
      fun ρ xo _ hpub hO => ?_⟩
    · show (fun X => L.par.tLev (T.B y) x.al (l + 1) X) = fun X => L.par.tLev a.B a.al (l + 1) X
      rw [hB, hal]
    · show (fun X => L.par.tLev (T.B y) x.al (l + 1) (X + 2 ^ (l + (L.par.σ + L.par.lp))))
        = fun X => L.par.tLev a.B a.al (l + 1) (X + 2 ^ (l + (L.par.σ + L.par.lp)))
      rw [hB, hal]
    · show Form.val (L.proj y) x.C =
        ext (l + (L.par.σ + L.par.lp))
          (fun X =>
            L.par.tLev (T.B y) x.al (l + 1) X *
              L.par.tLev (T.B y) x.al (l + 1) (X + 2 ^ (l + (L.par.σ + L.par.lp)))) x.pt
      rw [← L.par.ext_tLev (T.B y) x.al hl]
      exact hC
    · have e : (L.plT l).pl.imp (id y) ((L.prT l).pl.tr (id a) π ρ) = y := (L.plT l).imp_pl _ _
      rw [e] at hO ⊢
      have hpb : xo.1.pub = x := (L.plT l).pub_of_pl hpub
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hO
      rw [hpb] at h5 h6
      refine ⟨⟨⟨h6.1, h6.2.1, hp, h3, h4.1, h6.2.2.1, htf⟩, h6.2.2.2⟩, htz, hend,
        ⟨h1.symm, fun t ht => h2 t (by show t < l + (L.par.σ + L.par.lp) + 1; omega) rfl⟩, ?_⟩
      show Form.val (L.proj y) xo.1.C =
        ext (l + 1 + (L.par.σ + L.par.lp)) (L.par.tLev (T.B y) x.al (l + 1)) xo.1.pt
      rw [show l + 1 + (L.par.σ + L.par.lp) = l + (L.par.σ + L.par.lp) + 1 by omega,
        ← consPt_eta xo.1.pt, ext_succ_consPt]
      exact h5


/-! ### The leaf layer -/

def H5 (U : Set Pd) (a : LkA E) (π : Pd → E) (x : LkX N E) (y : Y) : Prop :=
  (L.Lnk T) U a π x y ∧ (L.TZ T) x y ∧ (L.ENDh T) x y ∧ (L.CB4 T) x y

@[reducible] def prL : L.plL.Prover (LkA E) where
  pt a := a.pt
  f0 a X := L.par.vB a.B X
  f1 a X := L.par.vA a.al X
  set := setA

@[reducible] def hL : Hon L.bL Pd E (LkA E) (LkA E) :=
  L.prL.pl.on L.gxL L.pxL id (fun _ yo => yo) id
    (fun _ ao => { ao with p4 := fun t => ao.pt (t + 1), hl := ao.hl.addLin })

theorem accOn_hL {U : Set Pd} (hU : L.plL.pads ⊆ U) : L.hL.AccOn (L.HT T U L.par.r) (L.H5 T U) :=
  (L.prL.accOn_pl (L.vL T) (L.Inv T) (List.Perm.refl _) (fun _ _ _ _ => rfl) (L.inv_setA T)).on'
      fun a π x y hR => by
    obtain ⟨⟨⟨hk, hB, hp, hwf, htrue, hof, htf⟩, hpu⟩, htz, hend, ⟨hpt, hnz⟩, hC⟩ := hR
    have hal := hpu.1
    refine ⟨⟨⟨hpt.symm, ?_, ?_, fun p hp' => hp p (hU hp'), hwf, htrue, hk, hB, hof, hpu⟩, hnz, ?_⟩,
      fun ρ xo _ hpub hO => ?_⟩
    · show (fun X => L.par.vB (T.B y) X) = fun X => L.par.vB a.B X
      rw [hB]
    · show (fun X => L.par.vA x.al X) = fun X => L.par.vA a.al X
      rw [hal]
    · show Form.val (L.proj y) (x.C - Form.const (ext L.par.gT L.par.vI x.pt)) =
        ext L.par.gT (fun X => L.par.vB (T.B y) X * L.par.vA x.al X) x.pt
      rw [map_sub, Form.val_const, ← L.par.ext_leafT, ← L.par.tLev_top]
      exact congrArg (· - _) hC
    · have e : L.plL.pl.imp (id y) (L.prL.pl.tr (id a) π ρ) = y := L.plL.imp_pl _ _
      rw [e] at hO ⊢
      have hpb : xo.1.pub = x := L.plL.pub_of_pl hpub
      obtain ⟨h1, _, h3, h4, _, h6⟩ := hO
      rw [hpb] at h6
      obtain ⟨h41, h42, h43⟩ := h4
      rw [hpb] at h43
      obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := h6.2.2.2
      refine ⟨⟨⟨h6.1, h6.2.1, hp, h3, (Ledger.true_addLin _ _ _).mpr ⟨h41, ?_⟩,
            h6.2.2.1.addLin _, htf⟩,
          q1, q2, ?_, q4, q5, q6, q7⟩,
        htz, hend, h42⟩
      · rw [map_sub, Form.val_const, sub_eq_zero]
        exact h43
      · show (fun t => (L.prL.pl.next (id a) ρ).pt (t + 1)) = fun t => xo.1.pt (t + 1)
        rw [h1]

/-! ### The bit layer -/

def H6 (U : Set Pd) (a : LkA E) (π : Pd → E) (x : LkX N E) (y : Y) : Prop :=
  (L.Lnk T) U a π x y ∧ (L.TZ T) x y ∧ (L.ENDh T) x y ∧ (L.CB4 T) x y ∧ PT L.par.gT a x ∧
    L.V y x.C = ext L.par.gT (fun X => L.par.vB (T.B y) X * (L.par.vB (T.B y) X - 1)) x.pt

@[reducible] def hB0 : Hon L.bB0 Pd E (LkA E) (LkA E) :=
  Hon.one (fun _ _ => (fun e => Empty.elim e, fun k => Empty.elim k))
    (fun a ϱ => { a with pt := nat ϱ }) {ϱ | nzT ϱ = false} fun _ => ∅

omit [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem accOn_hB0 (U : Set Pd) (hnt : L.par.NT ≤ 2 ^ L.par.σ) : L.hB0.AccOn (L.H5 T U) (L.H6 T U) :=
  Hon.accOn_one fun a π x y ϱ hi hb _ => by
    have hnz : nzT ϱ = true := by
      cases h : nzT ϱ
      · exact absurd h hb
      · rfl
    obtain ⟨hl, htz, hend, hcb⟩ := hi
    refine ⟨_, if_pos hnz, hl, htz, hend, hcb, ⟨rfl, nat_ne_zero_of_nzT hnz⟩, ?_⟩
    show Form.val (L.proj y) 0 = _
    rw [map_zero, ext_zero_of_forall ((L.par.bits_iff hnt (T.B y)).mpr hl.1.2.2.2.2.2.2.1)]

def H7 (U : Set Pd) (a : LkA E) (π : Pd → E) (x : LkX N E) (y : Y) : Prop :=
  (L.Lnk T) U a π x y ∧ (L.TZ T) x y ∧ (L.ENDh T) x y ∧ (L.CB4 T) x y ∧ (L.CB5 T) x y

@[reducible] def prB : L.plB.Prover (LkA E) where
  pt a := a.pt
  f0 a X := L.par.vB a.B X
  f1 a X := L.par.vB a.B X - 1
  set := setA

@[reducible] def hB : Hon L.bB Pd E (LkA E) (LkA E) :=
  L.prB.pl.on gxPL pxB id (fun _ yo => yo) id
    (fun _ ao => { ao with p5 := fun t => ao.pt (t + 1), hl := ao.hl.addLin })

theorem accOn_hB {U : Set Pd} (hU : L.plB.pads ⊆ U) : L.hB.AccOn (L.H6 T U) (L.H7 T U) :=
  (L.prB.accOn_pl (L.vBt T) (L.Inv T) (List.Perm.refl _) (fun _ _ _ _ => rfl) (L.inv_setA T)).on'
      fun a π x y hR => by
    obtain ⟨⟨⟨hk, hB, hp, hwf, htrue, hof, htf⟩, hpu⟩, htz, hend, hcb, ⟨hpt, hnz⟩, hC⟩ := hR
    refine ⟨⟨⟨hpt.symm, ?_, ?_, fun p hp' => hp p (hU hp'), hwf, htrue, hk, hB, hof, hpu⟩, hnz, hC⟩,
      fun ρ xo _ hpub hO => ?_⟩
    · show (fun X => L.par.vB (T.B y) X) = fun X => L.par.vB a.B X
      rw [hB]
    · show (fun X => L.par.vB (T.B y) X - 1) = fun X => L.par.vB a.B X - 1
      rw [hB]
    · have e : L.plB.pl.imp (id y) (L.prB.pl.tr (id a) π ρ) = y := L.plB.imp_pl _ _
      rw [e] at hO ⊢
      have hpb : xo.1.pub = x := L.plB.pub_of_pl hpub
      obtain ⟨h1, _, h3, h4, _, h6⟩ := hO
      rw [hpb] at h6
      obtain ⟨h41, h42, h43⟩ := h4
      obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := h6.2.2.2
      refine ⟨⟨⟨h6.1, h6.2.1, hp, h3, (Ledger.true_addLin _ _ _).mpr ⟨h41, ?_⟩,
            h6.2.2.1.addLin _, htf⟩,
          q1, q2, q3, ?_, q5, q6, q7⟩,
        htz, hend, hcb, h42⟩
      · have h5 : Form.val (L.proj y) xo.2.1 =
            ext L.par.gT (L.par.vB (T.B y)) (fun t => xo.1.pt (t + 1)) := h42
        have h7 : Form.val (L.proj y) xo.2.2 =
            ext L.par.gT (fun X => L.par.vB (T.B y) X - 1) (fun t => xo.1.pt (t + 1)) := h43
        rw [map_add, map_sub, Form.val_const, h5, h7, L.par.ext_vB_sub_one]
        ring
      · show (fun t => (L.prB.pl.next (id a) ρ).pt (t + 1)) = fun t => xo.1.pt (t + 1)
        rw [h1]

/-! ## 7. The degree check -/

def H8 (U : Set Pd) (a : LkA E) (π : Pd → E) (x : LkX N E) (y : Y) : Prop :=
  (L.H7 T) U a π x y ∧ (L.CDEG T) x y

@[reducible] def hDeg : Hon L.bDeg Pd E (LkA E) (LkA E) :=
  Hon.one (fun _ _ => (fun e => Empty.elim e, fun k => Empty.elim k))
    (fun a ϱ => { a with p6 := nat ϱ }) ∅ fun _ => ∅

omit [DecidableEq E] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem accOn_hDeg (U : Set Pd) (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    L.hDeg.AccOn (L.H7 T U) (L.H8 T U) :=
  Hon.accOn_one fun a π x y ϱ hi _ _ => by
    obtain ⟨⟨hl, q1, q2, q3, q4, _, q6, q7⟩, htz, hend, h4, h5⟩ := hi
    exact ⟨_, rfl, ⟨⟨hl, q1, q2, q3, q4, rfl, q6, q7⟩, htz, hend, h4, h5⟩,
      ext_zero_of_forall ((L.par.dDeg_eq_zero_iff hnt (T.B y)).mpr hl.2.2.2.2.2.2.2.1) _⟩

/-! ## 8. The root test -/

section Congr

variable {P : LkPar E} {Zv Zv' : ℕ → E} {Yv Yv' Uv Uv' Vv Vv' : ℕ → ℕ → E}

omit [Field E] [Fintype E] [DecidableEq E] in
private theorem uArr_congr (hY : ∀ θ < P.NT, ∀ π < 2 ^ P.lp, Yv θ π = Yv' θ π)
    (hU : ∀ π < P.Pm, ∀ θ < P.NT, Uv π θ = Uv' π θ) {π θ : ℕ} (hπ : π ≤ P.Pm) (hθ : θ < P.NT) :
    P.uArr Yv Uv π θ = P.uArr Yv' Uv' π θ := by
  unfold LkPar.uArr
  split_ifs with h
  · exact hY θ hθ _ (by have := P.Pm_succ; omega)
  · exact hU π (by omega) θ hθ

omit [Fintype E] [DecidableEq E] in
omit [NeZero (2 : E)] in
private theorem msk_congr {A A' : ℕ → E} (h : ∀ θ < P.NT, A θ = A' θ) : P.msk A = P.msk A' := by
  funext θ
  unfold LkPar.msk
  split_ifs with hθ
  · exact h θ hθ
  · rfl

omit [Fintype E] [DecidableEq E] in
omit [NeZero (2 : E)] in
private theorem dStar_congr (al : E) (hZ : ∀ θ < P.NT, Zv θ = Zv' θ)
    (hY : ∀ θ < P.NT, ∀ π < 2 ^ P.lp, Yv θ π = Yv' θ π)
    (hU : ∀ π < P.Pm, ∀ θ < P.NT, Uv π θ = Uv' π θ) :
    P.dStar al Zv Yv Uv = P.dStar al Zv' Yv' Uv' :=
  msk_congr fun θ hθ => by rw [hZ θ hθ, uArr_congr hY hU (Nat.zero_le _) hθ]

omit [Fintype E] [DecidableEq E] in
omit [NeZero (2 : E)] in
private theorem rootPhi_congr (hY : ∀ θ < P.NT, ∀ π < 2 ^ P.lp, Yv θ π = Yv' θ π)
    (hU : ∀ π < P.Pm, ∀ θ < P.NT, Uv π θ = Uv' π θ)
    (hV : ∀ π < P.Pm, ∀ θ < P.NT, Vv π θ = Vv' π θ) (c w : ℕ → E) :
    P.rootPhi Yv Uv Vv c w = P.rootPhi Yv' Uv' Vv' c w := by
  unfold LkPar.rootPhi LkPar.eV LkPar.eU LkPar.eY
  refine Finset.sum_congr rfl fun π hπ => ?_
  have hπ' := Finset.mem_range.mp hπ
  rw [msk_congr (hV π hπ'),
    msk_congr (A := P.uArr Yv Uv (π + 1)) fun θ hθ => uArr_congr hY hU (by omega) hθ,
    msk_congr (A := P.uArr Yv Uv π) fun θ hθ => uArr_congr hY hU (by omega) hθ,
    msk_congr (A := fun θ => Yv θ π) fun θ hθ => hY θ hθ π (by have := P.Pm_succ; omega)]

end Congr

/-- The tree products of the table side, computed from the state. -/
def Yh (a : LkA E) : ℕ → ℕ → E := L.par.Yt a.B a.al

def msgUV (a : LkA E) (π : Pd → E) : L.KUV → E
  | .inl (π', θ) => L.par.hU (L.Yh a) π' θ + π (L.pU π' θ)
  | .inr (π', θ) => L.par.hV (L.Yh a) π' θ + π (L.pV π' θ)

@[reducible] def hUV : Hon L.bUV Pd E (LkA E) (LkA E) :=
  Hon.one (fun a π => (fun e => Empty.elim e, L.msgUV a π)) (fun a ϱ => { a with pr := nat ϱ })
    {ϱ | nzT ϱ = false} fun _ => ∅

def padsUV : Set Pd := {p | ∃ π < L.par.Pm, ∃ θ < L.par.NT, p = L.pU π θ ∨ p = L.pV π θ}

/-- The sent arrays are the honest ones. -/
def TUV (x : LkX N E) (y : Y) : Prop :=
  (∀ π < L.par.Pm, ∀ θ < L.par.NT, L.Uv x y π θ = L.par.hU (L.par.Yt (T.B y) x.al) π θ) ∧
    ∀ π < L.par.Pm, ∀ θ < L.par.NT, L.Vv x y π θ = L.par.hV (L.par.Yt (T.B y) x.al) π θ

def H9 (U : Set Pd) (a : LkA E) (π : Pd → E) (x : LkX N E) (y : Y) : Prop :=
  (L.H8 T) U a π x y ∧ (L.TUV T) x y ∧ ∀ t < L.par.σ, x.pr t ≠ 0

omit [NeZero (2 : E)] in
theorem accOn_hUV {U : Set Pd} (hU : L.padsUV ⊆ U) : L.hUV.AccOn (L.H8 T U) (L.H9 T U) :=
  Hon.accOn_one fun a π x y ϱ hi hb _ => by
    have hnz : nzT ϱ = true := by
      cases h : nzT ϱ
      · exact absurd h hb
      · rfl
    obtain ⟨⟨⟨hl, q1, q2, q3, q4, q5, _, q7⟩, hrest⟩, hdeg⟩ := hi
    have hB := hl.2.1
    have hp := hl.2.2.1
    refine ⟨_, if_pos hnz,
      ⟨⟨⟨hl, q1, q2, q3, q4, q5, rfl, q7⟩, hrest⟩, hdeg⟩,
      ⟨fun π' hπ' θ hθ => ?_, fun π' hπ' θ hθ => ?_⟩,
      nat_ne_zero_of_nzT hnz⟩
    · show Form.val (L.proj y) (L.uForm (L.msgUV a π) π' θ) = _
      unfold uForm
      rw [dif_pos ⟨hπ', hθ⟩, Form.val_masked, hp _ (hU ⟨π', hπ', θ, hθ, Or.inl rfl⟩)]
      show L.par.hU (L.Yh a) π' θ + π (L.pU π' θ) - π (L.pU π' θ) = _
      rw [add_sub_cancel_right]
      unfold Yh
      rw [hB, q1]
      rfl
    · show Form.val (L.proj y) (L.vForm (L.msgUV a π) π' θ) = _
      unfold vForm
      rw [dif_pos ⟨hπ', hθ⟩, Form.val_masked, hp _ (hU ⟨π', hπ', θ, hθ, Or.inr rfl⟩)]
      show L.par.hV (L.Yh a) π' θ + π (L.pV π' θ) - π (L.pV π' θ) = _
      rw [add_sub_cancel_right]
      unfold Yh
      rw [hB, q1]
      rfl

@[reducible] def hXi : Hon L.bXi Pd E (LkA E) (LkA E) :=
  Hon.one (fun _ _ => (fun e => Empty.elim e, fun k => Empty.elim k))
    (fun a c => { a with cx := nat c }) ∅ fun _ => ∅

omit [DecidableEq E] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem accOn_hXi (U : Set Pd) : L.hXi.AccOn (L.H9 T U) (L.H9 T U) :=
  Hon.accOn_one fun a π x y c hi _ _ => by
    obtain ⟨⟨⟨⟨hl, q1, q2, q3, q4, q5, q6, _⟩, hrest⟩, hdeg⟩, htuv, hpr⟩ := hi
    exact ⟨_, rfl, ⟨⟨⟨hl, q1, q2, q3, q4, q5, q6, rfl⟩, hrest⟩, hdeg⟩, htuv, hpr⟩

/-- The honest prover of the sumcheck of the root test. -/
@[reducible] def prR : L.scR.Prover (LkA E) where
  wt a := Alg.eqW a.pr
  Φ a w := L.par.rootPhi (L.Yh a) (L.par.hU (L.Yh a)) (L.par.hV (L.Yh a)) a.cx w
  deg _ := L.par.degLE_rootPhi _ _ _ _

@[reducible] def hRs : Hon L.bRs Pd E (LkA E) (LkA E) :=
  (L.prR.sc (lkVars L.par.σ) []).on (fun x => ((0 : Form N E), fun _ => 0, x))
    (fun x xo => { x with C := xo.1, pt := xo.2.1 }) id (fun _ yo => yo)
    (fun a => (a, fun _ => 0)) (fun _ ao => { ao.1 with pt := ao.2 })

def H9c (U : Set Pd) (a : LkA E) (π : Pd → E) (x : LkX N E) (y : Y) : Prop :=
  (L.H9 T) U a π x y ∧ a.pt = x.pt ∧ L.REV x y

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
omit [NeZero (2 : E)] in
/-- For a statement that matches the state (`H9`), the polynomial of the statement is the
prover's. -/
theorem rootPhi_of_H9 {U : Set Pd} {a : LkA E} {π : Pd → E} {x : LkX N E} {y : Y}
    (h : (L.H9 T) U a π x y) (w : ℕ → E) :
    L.par.rootPhi (L.Yv x y) (L.Uv x y) (L.Vv x y) x.cx w =
      L.par.rootPhi (L.Yh a) (L.par.hU (L.Yh a)) (L.par.hV (L.Yh a)) a.cx w := by
  obtain ⟨⟨⟨⟨hl, q1, _, _, _, _, _, q7⟩, htz, _⟩, _⟩, htuv, _⟩ := h
  have hY : L.Yh a = L.par.Yt (T.B y) x.al := by
    unfold Yh
    rw [hl.2.1, q1]
  rw [hY, q7]
  exact rootPhi_congr htz.2 htuv.1 htuv.2 _ _

theorem accOn_hRs {U : Set Pd} (hU : L.scR.padsOf (lkVars L.par.σ) ⊆ U) :
    L.hRs.AccOn (L.H9 T U) (L.H9c T U) :=
  (L.prR.accOn_sc (Link := (L.H9 T) U) L.scR_ok.forms (fun _ => Alg.node_injective_one (NeZero.ne 2)) (lkVars L.par.σ) [] fun a π ξ y hL =>
    ⟨by show Alg.eqW ξ.pr = Alg.eqW a.pr; rw [hL.1.1.1.2.2.2.2.2.2.1], fun p hp => by
      show Form.val (L.proj y) (Form.ent (L.place p)) = π p
      rw [Form.val_ent]
      exact hL.1.1.1.1.2.2.1 p (hU hp)⟩).on' fun a π x y hR => by
    refine ⟨⟨hR, rfl, fun v hv => ?_, fun v hv _ => absurd hv (by simp), ?_⟩,
      fun ρ xo _ hpub hO => ?_⟩
    · rw [List.append_nil] at hv
      show (if true = true then a.pr v else 1 - a.pr v) ≠ 0
      rw [if_pos rfl, hR.1.1.1.2.2.2.2.2.2.1]
      exact hR.2.2 v (mem_lkVars.mp hv)
    · show Form.val (L.proj y) (0 : Form N E) = Alg.sumOutL (Alg.eqW a.pr) (lkVars L.par.σ ++ [])
        (L.par.rootPhi (L.Yh a) (L.par.hU (L.Yh a)) (L.par.hV (L.Yh a)) a.cx) (fun _ => 0)
      rw [map_zero, List.append_nil, L.par.sumOutL_rootPhi]
      refine (Finset.sum_eq_zero fun j hj => ?_).symm
      have hid : L.par.Ident a.al (L.par.Zt a.key a.al) (L.Yh a) := by
        have h1 := hR.1.1.1.1.2.2.2.2.2.2.2.2 a.al
        rw [← hR.1.1.1.1.1, ← hR.1.1.1.1.2.1] at h1
        exact h1
      have h2 : ∀ θ,
          L.par.dPair (L.Yh a) (L.par.hU (L.Yh a)) (L.par.hV (L.Yh a)) j θ = 0 := fun θ => by
        have h3 := L.par.dFam_honest hid ⟨j + 1, by have := Finset.mem_range.mp hj; omega⟩ θ
        simpa [LkPar.dFam] using h3
      rw [ext_zero_of_forall fun θ _ => h2 θ, mul_zero]
    · have e : (L.scR.sc (lkVars L.par.σ)).imp
            (id y) ((L.prR.sc (lkVars L.par.σ) []).tr (a, fun _ => 0) π ρ) = y :=
        L.scR.imp_sc _ _ _
      rw [e] at hO ⊢
      have hdata : xo.2.2 = x := L.scR.data_of_pub_sc _ _ _ _ _ hpub
      obtain ⟨h1, h2, _, _, h5⟩ := hO
      rw [hdata] at h1
      refine ⟨h1, h2.symm, ?_⟩
      show Form.val (L.proj y) xo.1 = L.par.rootPhi (L.Yv x y) (L.Uv x y) (L.Vv x y) x.cx xo.2.1
      rw [(L.rootPhi_of_H9 T) h1, h2]
      exact h5

/-! ### The claims that the root test defers -/

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem val_fS (x : LkX N E) (y : Y) :
    L.V y (L.fS x) = ext L.par.σ (L.par.dStar x.al (L.Zv x y) (L.Yv x y) (L.Uv x y)) x.pr := by
  unfold fS LkPar.dStar
  change Form.val (L.proj y) _ = _
  rw [val_extF]
  refine ext_congr (fun θ _ => ?_) _
  rw [LkPar.val_msk]
  unfold LkPar.msk
  split_ifs
  · beta_reduce
    rw [map_sub, map_smul, smul_eq_mul]
    exact congrArg₂ (· - ·) rfl (congrArg _ (L.val_uArr x y 0 θ))
  · rfl

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem val_fR (x : LkX N E) (y : Y) :
    L.V y (L.fR x) =
      L.V y x.C -
        ∑ π ∈ Finset.range L.par.Pm, (x.cx π * L.par.eV (L.Vv x y) π x.pt +
          x.cx (L.par.Pm + π) * L.par.eU (L.Yv x y) (L.Uv x y) π x.pt) := by
  unfold fR
  change Form.val (L.proj y) _ = _
  rw [map_sub, map_sum]
  refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun π _ => ?_)
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  exact congrArg₂ (· + ·) (congrArg _ (L.val_eVf x y π x.pt)) (congrArg _ (L.val_eUf x y π x.pt))

/-- The honest values of the opened forms of the root test, and its terms, from the state. -/
def ovA (a : LkA E) : List E :=
  (List.range (3 * L.par.Pm)).map fun k =>
    if k % 3 = 0 then L.par.eU (L.Yh a) (L.par.hU (L.Yh a)) (k / 3 + 1) a.pt
    else if k % 3 = 1 then L.par.eV (L.par.hV (L.Yh a)) (k / 3) a.pt
    else L.par.eY (L.Yh a) (k / 3) a.pt

def tsA (a : LkA E) : List (E × ℕ × ℕ) :=
  (List.range L.par.Pm).flatMap fun π =>
    [(-a.cx π, 3 * π, 3 * π), (-a.cx (L.par.Pm + π), 3 * π + 1, 3 * π + 2)]

@[reducible] def hRec : Hon L.bRec Pd E (LkA E) (LkA E) :=
  Hon.pure _ id fun a => { a with hl := (a.hl.addRel (L.ovA a) (L.tsA a)).addLin }

/-- After the argument, for the honest run: the statement matches the state, and the claims that are
passed to the containing protocol are true. -/
def H10 (U : Set Pd) (a : LkA E) (π : Pd → E) (x : LkX N E) (y : Y) : Prop :=
  (L.Lnk T) U a π x y ∧ (L.ENDh T) x y ∧ (L.CB4 T) x y ∧ (L.CB5 T) x y ∧ (L.CDEG T) x y

omit [Fintype E] [DecidableEq E] [DecidableEq N] [Fintype N] in
omit [NeZero (2 : E)] in
theorem ts_lt (x : LkX N E) : ∀ t ∈ L.ts x, t.2.1 < (L.os x).length ∧ t.2.2 < (L.os x).length := by
  intro t ht
  have hlen : (L.os x).length = 3 * L.par.Pm := by simp [os]
  rw [hlen]
  obtain ⟨π, hπ, ht'⟩ := List.mem_flatMap.mp ht
  have hπ' := List.mem_range.mp hπ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
  rcases ht' with rfl | rfl
  · exact ⟨by show 3 * π < _; omega, by show 3 * π < _; omega⟩
  · exact ⟨by show 3 * π + 1 < _; omega, by show 3 * π + 2 < _; omega⟩

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem accOn_hRec (U : Set Pd) : L.hRec.AccOn (L.H9c T U) (L.H10 T U) :=
  Hon.accOn_pure fun a π x y hi => by
    obtain ⟨h9, hpt, hrev⟩ := hi
    obtain ⟨⟨⟨⟨hl, hpu⟩, htz, hend, h4, h5⟩, hdeg⟩, htuv, _⟩ := h9
    obtain ⟨hk, hB, hp, hwf, htrue, hof, htf⟩ := hl
    have hY : L.Yh a = L.par.Yt (T.B y) x.al := by
      unfold Yh
      rw [hB, hpu.1]
    have hYv : ∀ θ < L.par.NT, ∀ π < 2 ^ L.par.lp, L.Yv x y θ π = L.par.Yt (T.B y) x.al θ π := htz.2
    have hZv : ∀ θ < L.par.NT, L.Zv x y θ = L.par.Zt (T.key y) x.al θ := htz.1
    -- the values of the opened forms
    have hov : (L.os x).map (fun g => Form.val (L.proj y) g) = L.ovA a := by
      unfold os ovA
      rw [List.map_map]
      refine List.map_congr_left fun k hk' => ?_
      have hk3 := List.mem_range.mp hk'
      have hps := L.par.Pm_succ
      show Form.val (L.proj y) (L.osFn x k) = _
      unfold osFn
      rw [hY, hpt]
      split_ifs
      · refine (L.val_eUf x y _ _).trans ?_
        unfold LkPar.eU
        rw [msk_congr (A := L.par.uArr (L.Yv x y) (L.Uv x y) (k / 3 + 1)) fun θ hθ =>
            uArr_congr hYv htuv.1 (by omega) hθ]
      · refine (L.val_eVf x y _ _).trans ?_
        unfold LkPar.eV
        rw [msk_congr (htuv.2 (k / 3) (by omega))]
      · refine (L.val_eYf x y _ _).trans ?_
        unfold LkPar.eY
        rw [msk_congr (A := fun θ => L.Yv x y θ (k / 3)) fun θ hθ => hYv θ hθ (k / 3) (by omega)]
    have hts : L.ts x = L.tsA a := by
      unfold ts tsA
      rw [hpu.2.2.2.2.2.2]
    have hrel : Form.val (L.proj y) (L.fR x) =
        termSum (fun i => Form.val (L.proj y) ((L.os x).getD i 0)) (L.ts x) := by
      rw [L.termSum_ts]
      exact (L.val_fR x y).trans ((L.par.rootPhi_eq_iff _ _ _ _ _ _).mp hrev)
    have hlin : Form.val (L.proj y) (L.fS x) = 0 := by
      refine (L.val_fS x y).trans ?_
      rw [dStar_congr x.al hZv hYv htuv.1]
      refine ext_zero_of_forall (fun θ _ => ?_) _
      have h3 := L.par.dFam_honest (htf.2.2 x.al) ⟨0, by omega⟩ θ
      simpa [LkPar.dFam] using h3
    refine ⟨_, if_pos hwf, ⟨⟨hk, hB, hp, ?_, ?_, ?_, htf⟩, hpu⟩, hend, h4, h5, hdeg⟩
    · exact Ledger.wf_addRel hwf _ (L.ts_lt x)
    · exact (Ledger.true_addLin _ _ _).mpr
        ⟨(Ledger.true_addRel hwf _ _ _ _).mpr ⟨htrue, hrel⟩, hlin⟩
    · have h6 := (hof.addRel (L.fR x) (L.os x) (L.ts x)).addLin (L.fS x)
      rw [hov] at h6
      rw [← hts]
      exact h6

end Lk

/-! ## 9. Masked form -/

/-- Every pad of a product layer is used for one masked scalar only. -/
def PL.LayerOK {E Y P N Ξ : Type} [Field E] [Fintype N] [DecidableEq N] (Q : PL E Y P N Ξ) : Prop :=
  Q.sc.PlacesOnceOn (PL.vars Q.g) ∧
  Function.Injective Q.pv ∧
  Disjoint (Q.sc.padsOf (PL.vars Q.g)) (Set.range Q.pv)

namespace Lk

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] (L : Lk E Y Pd N) (T : Lk.Vecs E Y)

/-- The pads of the scalars of step 2 and of the arrays of step 6. -/
def idxZY : L.KZY → Pd
  | .inl θ => L.pZ θ
  | .inr (θ, π) => L.pY θ π
def idxUV : L.KUV → Pd
  | .inl (π, θ) => L.pU π θ
  | .inr (π, θ) => L.pV π θ

/-- The groups of masked scalars of the argument. -/
inductive Grp
  | zy | k (l : ℕ) | t (l : ℕ) | lf | bt | uv | rt

/-- The pads of a group. -/
def grp : Grp → Set Pd
  | .zy => Set.range L.idxZY
  | .k l => (L.plK l).pads
  | .t l => (L.plT l).pads
  | .lf => L.plL.pads
  | .bt => L.plB.pads
  | .uv => Set.range L.idxUV
  | .rt => L.scR.padsOf (lkVars L.par.σ)

/-- The groups that occur. -/
def GOK : Grp → Prop
  | .k l => l < L.par.D
  | .t l => l < L.par.r
  | _ => True

/-- Every pad is used for one masked scalar only: inside each group, and different groups have no
pad in common. -/
structure PadsOK : Prop where
  zy : Function.Injective L.idxZY
  uv : Function.Injective L.idxUV
  k : ∀ l < L.par.D, (L.plK l).LayerOK
  t : ∀ l < L.par.r, (L.plT l).LayerOK
  lf : L.plL.LayerOK
  bt : L.plB.LayerOK
  rt : L.scR.PlacesOnceOn (lkVars L.par.σ)
  disj : ∀ g g', L.GOK g → L.GOK g' → g ≠ g' → Disjoint (L.grp g) (L.grp g')

variable [Fintype Pd] [DecidableEq Pd]

/-- The distribution of the plain part of a round in which the prover sends nothing. -/
abbrev simNone (C : Type) [Fintype C] [Nonempty C] :
    Rho [Block.chalRound E C] → PMF (Plains [Block.chalRound E C]) :=
  fun _ => PMF.pure ((fun k => Empty.elim k), ())

omit [DecidableEq E] [Fintype N] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem masked_hAl : L.hAl.Masked (fun _ => True) ∅ ∅ (simNone E) :=
  Hon.masked_one_const _ _ fun _ _ _ => rfl
omit [Fintype N] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem masked_hT0 : L.hT0.Masked (fun _ => True) ∅ ∅ (simNone _) :=
  Hon.masked_one_const _ _ fun _ _ _ => rfl
omit [Fintype N] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem masked_hB0 : L.hB0.Masked (fun _ => True) ∅ ∅ (simNone _) :=
  Hon.masked_one_const _ _ fun _ _ _ => rfl
omit [DecidableEq E] [Fintype N] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem masked_hDeg : L.hDeg.Masked (fun _ => True) ∅ ∅ (simNone _) :=
  Hon.masked_one_const _ _ fun _ _ _ => rfl
omit [DecidableEq E] [Fintype N] [DecidableEq N] in
omit [NeZero (2 : E)] in
theorem masked_hXi : L.hXi.Masked (fun _ => True) ∅ ∅ (simNone _) :=
  Hon.masked_one_const _ _ fun _ _ _ => rfl

omit [NeZero (2 : E)] in
theorem masked_hZY (h : Function.Injective L.idxZY) :
    L.hZY.Masked (fun _ => True) (L.grp .zy) (L.grp .zy)
      (Hon.simOne (r := L.rZY) (K := L.KZY) E id) := by
  have h1 := Hon.masked_one (r := L.rZY) (K := L.KZY)
    (pb := fun x ϱ s => if nzT ϱ then some (L.setZY x ϱ s) else none) (im := fun (y : Y) _ _ => y)
    (msg := fun a π => (fun e => Empty.elim e, L.msgZY a π))
    (nx := fun (a : LkA E) ϱ => { a with pt := nat ϱ }) (Bd := {ϱ | nzT ϱ = false})
    (Wn := fun _ => ∅) id (fun _ => True) L.idxZY h
    (fun a _ k => match k with
      | .inl θ => L.par.Zt a.key a.al θ
      | .inr (θ, π') => L.par.Yt a.B a.al θ π') ∅
    (fun a π _ => funext fun k => by rcases k with θ | ⟨θ, π'⟩ <;> rfl)
    (fun _ _ _ _ _ => rfl) (Set.empty_disjoint _)
  rw [Set.empty_union] at h1
  exact h1

omit [NeZero (2 : E)] in
theorem masked_hUV (h : Function.Injective L.idxUV) :
    L.hUV.Masked (fun _ => True) (L.grp .uv) (L.grp .uv)
      (Hon.simOne (r := L.rUV) (K := L.KUV) E id) := by
  have h1 := Hon.masked_one (r := L.rUV) (K := L.KUV)
    (pb := fun x ϱ s => if nzT ϱ then some (L.setUV x ϱ s) else none) (im := fun (y : Y) _ _ => y)
    (msg := fun a π => (fun e => Empty.elim e, L.msgUV a π))
    (nx := fun (a : LkA E) ϱ => { a with pr := nat ϱ }) (Bd := {ϱ | nzT ϱ = false})
    (Wn := fun _ => ∅) id (fun _ => True) L.idxUV h
    (fun a _ k => match k with
      | .inl (π', θ) => L.par.hU (L.Yh a) π' θ
      | .inr (π', θ) => L.par.hV (L.Yh a) π' θ) ∅
    (fun a π _ => funext fun k => by rcases k with ⟨π', θ⟩ | ⟨π', θ⟩ <;> rfl)
    (fun _ _ _ _ _ => rfl) (Set.empty_disjoint _)
  rw [Set.empty_union] at h1
  exact h1

omit [NeZero (2 : E)] in
theorem masked_hK (ho : L.par.OrdOK) {l : ℕ} (h : (L.plK l).LayerOK) :
    (L.hK l).Masked (fun _ => True) (L.grp (.k l)) (L.grp (.k l)) (PL.Prover.simPl (L.plK l)) :=
  ((L.prK l).masked_pl (ho.kOrd l) (fun _ => True) h.1 h.2.1 h.2.2).on _ _ _ _ _ _

omit [NeZero (2 : E)] in
theorem masked_hT {l : ℕ} (h : (L.plT l).LayerOK) :
    (L.hT l).Masked (fun _ => True) (L.grp (.t l)) (L.grp (.t l)) (PL.Prover.simPl (L.plT l)) :=
  ((L.prT l).masked_pl (List.Perm.refl _) (fun _ => True) h.1 h.2.1 h.2.2).on _ _ _ _ _ _

omit [NeZero (2 : E)] in
theorem masked_hL (h : L.plL.LayerOK) :
    L.hL.Masked (fun _ => True) (L.grp .lf) (L.grp .lf) (PL.Prover.simPl L.plL) :=
  (L.prL.masked_pl (List.Perm.refl _) (fun _ => True) h.1 h.2.1 h.2.2).on _ _ _ _ _ _

omit [NeZero (2 : E)] in
theorem masked_hB (h : L.plB.LayerOK) :
    L.hB.Masked (fun _ => True) (L.grp .bt) (L.grp .bt) (PL.Prover.simPl L.plB) :=
  (L.prB.masked_pl (List.Perm.refl _) (fun _ => True) h.1 h.2.1 h.2.2).on _ _ _ _ _ _

omit [NeZero (2 : E)] in
theorem masked_hRs (h : L.scR.PlacesOnceOn (lkVars L.par.σ)) :
    L.hRs.Masked (fun _ => True) (L.grp .rt) (L.grp .rt) (L.scR.simSc (lkVars L.par.σ)) :=
  (L.prR.masked_sc_on (fun _ => True) (lkVars L.par.σ) [] h
      ((List.nodup_finRange _).map Fin.val_injective)).on
    _ _ _ _ _ _

end Lk

end Blocks
