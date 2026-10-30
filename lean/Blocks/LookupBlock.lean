-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupBlock.lean: the lookup argument step by step, with soundness of every step.

Blocks/LookupRel.lean defines the argument's parameters, trees (batches of keys), key side and table
side. Here are its data, one block for each message or layer, the relations between them, and
soundness of every block. (Words of this library: lean/GLOSSARY.md.)

The data. `Lk` has the public parameters (`LkPar`), how the entries are read off the implicit part y
(`proj`), which entry holds a pad (`place`), and thirteen maps that name the pads of the masked
scalars. Besides `proj`, which only relations use, it holds what the two parties compute with and
nothing else. The true keys and multiplicity bits B are functions of y (`Lk.Vecs`), an argument T of
every relation.

The blocks, in the namespace `Lk` (what the steps of the argument do, in words: the head of
Blocks/LookupStage.lean):
 * `bAl` (α);
 * `bZY` (the tree products, then ϱ);
 * `bK` l (layer l of the key side);
 * `bKe` (C_end and z are stored);
 * `bT0` (ϱ3);
 * `bT` l (layer l of the table side);
 * `bL` (leaf layer);
 * `bB0` (ϱ5);
 * `bB` (bit layer);
 * `bDeg` (ϱ6, for the degree check `LkPar.DegE`);
 * `bUV` (the arrays, then ϱ');
 * `bXi` ((ξ, ξ'));
 * `bRs` (the rounds of the root test);
 * `bRec` (the claims that it defers).
The implicit part is not changed: every prover message consists of masked scalars. The explicit part
is one structure `LkX`, whose fields are filled step by step; the product layers
(Blocks/ProductBlock.lean, also for ζ, v0, v1, ϱ̂) and the sumcheck of the root test
(Blocks/SumCheckBlock.lean) act on parts of it. Blocks/LookupStage.lean composes the steps into
stages: `Lk.st14` (steps 1 to 4), `Lk.st5` (the degree check), `Lk.st6` (the root test) and
`Lk.stLookup`; a containing protocol may put other stages between the three. Blocks/LookupSplit.lean
and Blocks/LookupWhole.lean compose them again, split at the last layer of the key side.

The relations. "The list" is the verifier's list of deferred claims (`Ledger`, Blocks/Form.lean):
LIN(f): the form f has the value 0; REL(f; terms): the value of f is a sum of products of values of
opened forms.
  R0   all claims on the list are true, and every key of every tree is a value of the table of that
       tree (R_lkp)
  R7   after steps 1 to 4: the list; the degree check and the identity `LkPar.Ident` for the sent
       tree products; the end claim END; the claims CB4, CB5 on ~B
  R8   after step 5:  the list; the identity `LkPar.Ident` for the sent tree products; END, CB4, CB5
                      and the degree claim CDEG
  R10  after step 6:  the list; END, CB4, CB5, CDEG

END is val(C_end) = ~LEAF(z). Alone among the four claims that are passed to the containing
protocol, END has a premise: no coordinate of z that the verifier checks (`LkPar.zf`: those by which
later blocks of the containing protocol divide; by default all) is 0 (the verifier has rejected
otherwise). A premise makes the relation after the argument weaker, and so the statement of
soundness stronger. CB4, CB5 and CDEG are about the true B: how B is sent, and so which forms state
these claims, is left to the containing protocol. The argument itself adds to the list: two opened
forms and a REL for each product layer; a LIN of the leaf layer and one of the bit layer; 3 Pm
opened forms, one REL and one LIN of the root test (that they come in this order is not proved in
this library).

Soundness (`Block.Clean`, Blocks/Block.lean), under `LkPar.WF` at the characteristic p of E;
`clean_bK` for l < D, `clean_bT` for l < r. `clean_bAl`, .., `clean_bRec`: one theorem for each
block; together: `Lk.props_stLookup`, field `clean` (which also asks `Lk.PadsOK` and 2 ≠ 0 in E).
R10 after a run without a bad challenge gives R0 before it. Error bounds: `Lk.small_stLookup`
(Blocks/RngSmall.lean). The stage's numbers `pBad`, `pWin`: `Lk.stLookup_pBad`, `Lk.stLookup_pWin`
(Blocks/RngNums.lean).

Choices made here. (1) A point is a single verifier message. (2) All challenges of the layers of the
two forests but those of the last layer of the key side, and the points ϱ, ϱ3, ϱ5, ϱ', are rejected
at 0 (the verifier rejects if the challenge, or a coordinate of the point, is 0): a later layer, or
for ϱ' the sumcheck of the root test, divides by them. The challenges of the last layer of the key
side are the coordinates of the end point z; of these the verifier rejects at 0 those that
`LkPar.zf` selects. Those of the leaf layer, of the bit layer and of the root test's rounds are not
rejected. (2a) The rounds of the last layer of the key side bind its variables in the order
`LkPar.ordK` (by default as all other layers: the top bit first). (3) α, ϱ3, ϱ5, ϱ6 and (ξ, ξ') are
separate rounds, with an empty prover message, though each follows a verifier message directly. (4)
One more check: every product layer and `bRec` reject a list in which a term of a REL names an
opened form that is not there (`Ledger.wf`); otherwise an old term could come to name a form that is
opened later. An honest list passes it.

Notation:
 * D, σ, r, lp, NT: natural numbers, fields of `LkPar`: 2^D keys in a tree, NT trees, tables with
   2^r entries, 2^lp bits for a multiplicity; σ: the number of bits of a tree's index
   (Blocks/LookupRel.lean; σ: the head of Blocks/LookupWhole.lean).
 * gT: `LkPar.gT` = r + σ + lp: the number of variables of the leaves of the table side; Pm:
   `LkPar.Pm` = 2^lp - 1: the number of the highest plane (Blocks/LookupRel.lean).
 * `key` y θ i: key number i of tree θ; `B` y i θ π: bit π of the multiplicity of table entry i
   (`Lk.Vecs`; the head of Blocks/LookupRel.lean).
 * ϱ, ϱ3: the start point of the key side, of the table side (the docstrings of `clean_bZY`,
   `clean_bT0`).
 * α; C_end, z; ϱ6; ϱ', (ξ, ξ'): fields of `LkX`: `al`; the end of the key side (`Cend`, `z`); the
   point of the degree check (`p6`); ϱ' and the coefficients (ξ, ξ') (`pr`, `cx`).
 * ϱ̂, v0, v1, ζ: of a product layer: the end point ϱ̂ of its sumcheck, the two masked scalars v0,
   v1 that the prover sends, the verifier's challenge ζ (the head of Blocks/ProductBlock.lean).
 * `Block.Clean` B Ri Ro ε: a proposition: soundness of a block from Ri to Ro, with errors ε
   (Blocks/Block.lean); ε: `Err`: one number for each round: how many values of the challenge may
   lead from a doomed transcript to one that is not doomed (Iop/Rbr.lean).
-/
import Blocks.ProductBlock
import Blocks.LookupRel
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob

/-! ## 0. Tools -/

/-- `Block.Clean.on'` for a block that leaves the implicit part unchanged. -/
private theorem cleanOnX {Xi Xo X X' Y : Type} {B : Block Xi Y Xo Y} (himp : ∀ y τ, B.imp y τ = y)
    {Ri : Xi → Y → Prop} {Ro : Xo → Y → Prop} {ε : Err B.shape} (h : B.Clean Ri Ro ε) {gx : X → Xi}
    {px : X → Xo → X'} {R : X → Y → Prop} {R' : X' → Y → Prop}
    (hback : ∀ x y xo,
      (∃ ρ p, B.pub (gx x) ρ p = some xo) → R' (px x xo) y → Ro xo y ∧ (Ri (gx x) y → R x y)) :
    (B.on gx px id (fun _ yo => yo)).Clean R R' ε :=
  h.on' fun x y τ xo hxo hR' => by
    have e : B.imp (id y) τ = y := himp y τ
    rw [e] at hR' ⊢
    exact hback x y xo ⟨_, _, hxo⟩ hR'

namespace Ledger

variable {N E : Type}

/-- The list with one more claim LIN(f). -/
def addLin (x : Ledger N E) (f : Form N E) : Ledger N E := ⟨x.lin ++ [f], x.opn, x.rel⟩

theorem wf_addLin (x : Ledger N E) (f : Form N E) : (x.addLin f).wf = x.wf := rfl

theorem true_addLin [Fintype N] [CommRing E] (x : Ledger N E) (f : Form N E) (y : N → E) :
    (x.addLin f).True y ↔ x.True y ∧ Form.val y f = 0 := by
  unfold True addLin opv
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun g hg => h1 g (List.mem_append_left _ hg), h2⟩,
      h1 f (List.mem_append_right _ (List.mem_singleton.mpr rfl))⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun g hg => ?_, h2⟩
    rcases List.mem_append.mp hg with hg | hg
    · exact h1 g hg
    · rw [List.mem_singleton.mp hg]
      exact h3

/-- The list with more opened forms os and one claim REL(f; ts), whose terms name the new opened
forms by their numbers in os. -/
def addRel (x : Ledger N E) (f : Form N E) (os : List (Form N E)) (ts : List (E × ℕ × ℕ)) :
    Ledger N E :=
  ⟨x.lin, x.opn ++ os,
    x.rel ++ [(f, ts.map fun t => (t.1, x.opn.length + t.2.1, x.opn.length + t.2.2))]⟩

theorem wf_addRel {x : Ledger N E} (h : x.wf = true) (f : Form N E) {os : List (Form N E)}
    {ts : List (E × ℕ × ℕ)} (hts : ∀ t ∈ ts, t.2.1 < os.length ∧ t.2.2 < os.length) :
    (x.addRel f os ts).wf = true := by
  rw [wf_iff] at h ⊢
  intro r hr t ht
  have hlen : (x.addRel f os ts).opn.length = x.opn.length + os.length := by simp [addRel]
  rw [hlen]
  rcases List.mem_append.mp hr with hr | hr
  · have := h r hr t ht
    omega
  · obtain rfl := List.mem_singleton.mp hr
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    have := hts t' ht'
    exact ⟨by show x.opn.length + t'.2.1 < _; omega, by show x.opn.length + t'.2.2 < _; omega⟩

/-- If the list passes `wf`, the longer list says what the list said, and val f = ∑ c · val o_i ·
val o_j. -/
theorem true_addRel [Fintype N] [CommRing E] {x : Ledger N E} (h : x.wf = true) (f : Form N E)
    (os : List (Form N E)) (ts : List (E × ℕ × ℕ)) (y : N → E) :
    (x.addRel f os ts).True y ↔
    x.True y ∧ Form.val y f = termSum (fun i => Form.val y (os.getD i 0)) ts := by
  rw [wf_iff] at h
  have hold : ∀ i < x.opn.length, (x.addRel f os ts).opv y i = x.opv y i := fun i hi => by
    unfold opv addRel
    rw [List.getD_append _ _ _ _ hi]
  have hnewi : ∀ i,
      (x.addRel f os ts).opv y (x.opn.length + i) = Form.val y (os.getD i 0) := fun i => by
    unfold opv addRel
    rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  have hts : ∀ r ∈ x.rel,
      termSum ((x.addRel f os ts).opv y) r.2 = termSum (x.opv y) r.2 := fun r hr => by
    unfold termSum
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [hold _ (h r hr t ht).1, hold _ (h r hr t ht).2]
  have hnew : termSum ((x.addRel f os ts).opv y)
        (ts.map fun t => (t.1, x.opn.length + t.2.1, x.opn.length + t.2.2)) =
      termSum (fun i => Form.val y (os.getD i 0)) ts := by
    unfold termSum
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    simp only [Function.comp, hnewi]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, fun r hr => ?_⟩, ?_⟩
    · rw [← hts r hr]
      exact h2 r (List.mem_append_left _ hr)
    · rw [← hnew]
      exact h2 (f, _) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun r hr => ?_⟩
    rcases List.mem_append.mp hr with hr | hr
    · rw [hts r hr]
      exact h2 r hr
    · obtain rfl := List.mem_singleton.mp hr
      exact h3.trans hnew.symm

end Ledger

theorem termSum_append {E : Type} [CommRing E] (o : ℕ → E) (a b : List (E × ℕ × ℕ)) :
    termSum o (a ++ b) = termSum o a + termSum o b := by
  simp [termSum]

theorem termSum_flatMap_range
    {E : Type} [CommRing E] (o : ℕ → E) (f : ℕ → List (E × ℕ × ℕ)) (n : ℕ) :
    termSum o ((List.range n).flatMap f) = ∑ π ∈ Finset.range n, termSum o (f π) := by
  induction n with
  | zero => simp [termSum]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, termSum_append, ih, Finset.sum_range_succ]; simp

/-- A product layer leaves the public data unchanged. -/
theorem PL.pub_of_pl {E Y P N Ξ : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype N]
    [DecidableEq N] (L : PL E Y P N Ξ) {x : PLX N E Ξ} {ρ : Rho L.pl.shape} {p : Plains L.pl.shape}
    {xo : PL.XOut N E Ξ} (h : L.pl.pub x ρ p = some xo) : xo.1.pub = x.pub := by
  obtain ⟨x1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  have h5 := L.sc.data_of_pub_sc _ _ _ _ _ h1
  obtain ⟨_, _, rfl⟩ := L.fin_some h2
  show x1.2.2.2.2 = x.pub
  rw [h5]

theorem PL.imp_pl {E Y P N Ξ : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype N]
    [DecidableEq N] (L : PL E Y P N Ξ) (y : Y) (τ : Tr L.pl.shape) : L.pl.imp y τ = y :=
  L.sc.imp_sc _ _ _

/-! ## 1. The data -/

/-- The data of a lookup argument: the public parameters, how the entries are read off the implicit
part, which entry holds a pad, and the places of the pads of all masked scalars. Pd is the set of
places of pads, N the set of entries. -/
structure Lk (E Y Pd N : Type) where
  par : LkPar E
  proj : Y → N → E
  place : Pd → N
  pZ : ℕ → Pd
  pY : ℕ → ℕ → Pd
  pK : ℕ → ℕ → Fin 2 → Pd
  pKv : ℕ → Bool → Pd
  pT : ℕ → ℕ → Fin 2 → Pd
  pTv : ℕ → Bool → Pd
  pL : ℕ → Fin 2 → Pd
  pLv : Bool → Pd
  pB : ℕ → Fin 2 → Pd
  pBv : Bool → Pd
  pU : ℕ → ℕ → Pd
  pV : ℕ → ℕ → Pd
  pR : ℕ → Fin 2 → Pd

/-- The true vectors of a lookup argument: the keys and the multiplicity bits, as functions of the
implicit part. The relations mention them; no party computes with them, so they are not part of
`Lk`. -/
structure Lk.Vecs (E Y : Type) where
  /-- key y θ i: key number i of tree θ -/
  key : Y → ℕ → ℕ → E
  /-- B y i θ π -/
  B : Y → ℕ → ℕ → ℕ → E

/-- The explicit part of a statement inside a lookup argument: one structure, whose fields are
filled step by step. -/
structure LkX (N E : Type) where
  /-- the list of deferred claims -/
  led : Ledger N E
  al : E
  /-- the value forms of the sent tree products -/
  Zf : ℕ → Form N E
  Yf : ℕ → ℕ → Form N E
  /-- the running form and point -/
  C : Form N E
  pt : ℕ → E
  /-- the end of the key side -/
  Cend : Form N E
  z : ℕ → E
  /-- the two claims on ~B -/
  v4 : Form N E
  p4 : ℕ → E
  v5 : Form N E
  p5 : ℕ → E
  /-- the point of the degree check -/
  p6 : ℕ → E
  /-- the value forms of the arrays of the root test -/
  Uf : ℕ → ℕ → Form N E
  Vf : ℕ → ℕ → Form N E
  /-- ϱ' and the coefficients (ξ, ξ') -/
  pr : ℕ → E
  cx : ℕ → E

/-- The explicit part at the start. -/
def LkX.init {N E : Type} [Zero E] (led : Ledger N E) (al : E) : LkX N E :=
  ⟨led, al, fun _ => 0, fun _ _ => 0, 0, fun _ => 0, 0, fun _ => 0, 0, fun _ => 0, 0, fun _ => 0,
    fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ => 0⟩

/-- The public check of a point: no coordinate is 0. -/
def nzT {E : Type} [Zero E] [DecidableEq E] {n : ℕ} (ϱ : Fin n → E) : Bool := decide (∀ t, ϱ t ≠ 0)

theorem nat_ne_zero_of_nzT {E : Type} [Zero E] [DecidableEq E] {n : ℕ}
    {ϱ : Fin n → E} (h : nzT ϱ = true) : ∀ t < n, nat ϱ t ≠ 0 := by
  intro t ht
  have h1 : ∀ t, ϱ t ≠ 0 := by simpa [nzT] using h
  simpa [nat, ht] using h1 ⟨t, ht⟩

theorem LkPar.val_msk {N E : Type} [Fintype N] [Field E] (P : LkPar E) (y : N → E)
    (F : ℕ → Form N E) (θ : ℕ) :
    Form.val y (P.msk F θ) = P.msk (fun θ => Form.val y (F θ)) θ := by
  unfold LkPar.msk
  split_ifs
  · rfl
  · exact map_zero _

theorem consPt_eta {E : Type} (pt : ℕ → E) : consPt (pt 0) (fun t => pt (t + 1)) = pt := by
  funext t
  cases t <;> rfl

namespace Lk

variable {E Y Pd N : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]
  (L : Lk E Y Pd N) (T : Lk.Vecs E Y)

/-- The value of a form. -/
abbrev V (y : Y) (f : Form N E) : E := Form.val (L.proj y) f

/-! ## 2. The relations between the steps -/

def LED (x : LkX N E) (y : Y) : Prop := x.led.True (L.proj y)
/-- The identity `LkPar.Ident` for the values of the sent tree products. -/
def IDS (x : LkX N E) (y : Y) : Prop :=
  L.par.Ident x.al (fun θ => L.V y (x.Zf θ)) (fun θ π => L.V y (x.Yf θ π))
/-- The sent tree products of the table side are the true ones. -/
def YT (x : LkX N E) (y : Y) : Prop :=
  ∀ θ < L.par.NT, ∀ π < 2 ^ L.par.lp, L.V y (x.Yf θ π) = L.par.Yt (T.B y) x.al θ π
/-- The running claim of the key side at level l. -/
def KL (l : ℕ) (x : LkX N E) (y : Y) : Prop :=
  (∀ t < l + L.par.σ, L.par.kf l t = true → x.pt t ≠ 0) →
  L.V y x.C = ext (l + L.par.σ) (L.par.kLev (T.key y) x.al l) x.pt

/-- R_lkp, with the list. -/
def R0 (led : Ledger N E) (y : Y) : Prop := led.True (L.proj y) ∧ L.par.InTable (T.key y)
/-- After α. -/
def R1 (x : LkX N E) (y : Y) : Prop :=
  L.LED x y ∧ L.par.Bits (T.B y) ∧ L.par.DegE (T.B y) ∧
  L.par.Ident x.al (L.par.Zt (T.key y) x.al) (L.par.Yt (T.B y) x.al)
/-- The claims that stay open through the key side. -/
def FK (x : LkX N E) (y : Y) : Prop :=
  L.par.Bits (T.B y) ∧ L.par.DegE (T.B y) ∧ L.IDS x y ∧ (L.YT T) x y
/-- Inside the key side, at level l. -/
def RK (l : ℕ) (x : LkX N E) (y : Y) : Prop := L.LED x y ∧ (L.FK T) x y ∧ (L.KL T) l x y

/-! ## 3. Step 1: α -/

/-- The verifier sends α. -/
@[reducible] def bAl (_L : Lk E Y Pd N) : Block (Ledger N E) Y (LkX N E) Y :=
  Block.one (Block.chalRound E E) (fun led al _ => some (LkX.init led al)) (fun y _ _ => y)

omit [DecidableEq E] [DecidableEq N] in
/-- Soundness of the block bAl (α), under `LkPar.WF` at the characteristic p of E. -/
theorem clean_bAl {p : ℕ} [CharP E p] (hW : L.par.WF p) :
    L.bAl.Clean (L.R0 T) (L.R1 T) (2 ^ L.par.D - 1, ()) := by
  refine Block.clean_one (r := Block.chalRound E E)
    (pb := fun (led : Ledger N E) al _ => some (LkX.init led al)) (im := fun (y : Y) _ _ => y)
    (fun _ y _ => {al : E | L.par.BadAl (T.key y) (T.B y) al}) (2 ^ L.par.D - 1)
    (fun _ y _ => L.par.cnt_badAl_le (T.key y) (T.B y)) ?_
  intro led y m al xo hc hxo hRo
  obtain rfl := Option.some.inj hxo
  obtain ⟨h1, h2, h3, h4⟩ := hRo
  exact ⟨h1, LkPar.inTable_of_ident hW h2 h3 h4 hc⟩

/-! ## 4. Steps 2 and 3, first half: the tree products, and the start point of the key side -/

/-- The scalars of step 2: Z_θ and Y_(θ,π). -/
abbrev KZY : Type := Fin L.par.NT ⊕ Fin L.par.NT × Fin (2 ^ L.par.lp)

abbrev rZY : Round :=
  vRound E Empty (fun a => Empty.elim a) (fun a => Empty.elim a) L.KZY (Fin L.par.σ → E)

def zForm (s : L.KZY → E) (θ : ℕ) : Form N E :=
  if h : θ < L.par.NT then Form.masked (s (.inl ⟨θ, h⟩)) (L.place (L.pZ θ)) else 0

def yForm (s : L.KZY → E) (θ π : ℕ) : Form N E :=
  if h : θ < L.par.NT ∧ π < 2 ^ L.par.lp then
    Form.masked (s (.inr (⟨θ, h.1⟩, ⟨π, h.2⟩))) (L.place (L.pY θ π))
  else 0

/-- The explicit part after step 2 and the start point of the key side. -/
def setZY (x : LkX N E) (ϱ : Fin L.par.σ → E) (s : L.KZY → E) : LkX N E :=
  { x with
    Zf := L.zForm s
    Yf := L.yForm s
    C := extF L.par.σ (L.par.msk (L.zForm s)) (nat ϱ)
    pt := nat ϱ }

/-- The prover sends the tree products; the verifier sends ϱ, rejects if a coordinate is 0, and
forms ∑_θ eq(ϱ, θ) Z_θ. -/
@[reducible] def bZY : Block (LkX N E) Y (LkX N E) Y :=
  Block.one L.rZY (fun x ϱ s => if nzT ϱ then some (L.setZY x ϱ s) else none) (fun y _ _ => y)

/-- Soundness of the block bZY (ϱ: the start point of the key side), under hnt (NT ≤ 2^σ). -/
theorem clean_bZY (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    L.bZY.Clean (L.R1 T) (L.RK T 0) (L.par.σ * Fintype.card E ^ (L.par.σ - 1), ()) :=
  Block.clean_one (fun x y m =>
    {ϱ | BadPt L.par.σ (L.par.dZ (T.key y) x.al fun θ => L.V y (L.zForm m.2 θ)) ϱ}) _
    (fun x y m => cnt_badPt_le _ _) fun x y m ϱ xo hc hxo hRo => by
      by_cases hnz : nzT ϱ = true
      · rw [if_pos hnz] at hxo
        obtain rfl := Option.some.inj hxo
        obtain ⟨hled, ⟨hb, hd, hids, hyt⟩, hkl⟩ := hRo
        have h1 : L.V y (extF L.par.σ (L.par.msk (L.zForm m.2)) (nat ϱ)) =
            ext (0 + L.par.σ) (L.par.kLev (T.key y) x.al 0) (nat ϱ) :=
          hkl fun t ht _ => nat_ne_zero_of_nzT hnz t (by omega)
        change Form.val (L.proj y) _ = _ at h1
        rw [Nat.zero_add, val_extF] at h1
        have h2 : ext L.par.σ (L.par.dZ (T.key y) x.al fun θ => L.V y (L.zForm m.2 θ)) (nat ϱ) =
            0 := by
          unfold LkPar.dZ
          rw [ext_sub, ← h1]
          simp only [LkPar.val_msk]
          exact sub_self _
        have hzt := (L.par.dZ_eq_zero_iff hnt (T.key y) x.al _).mp (eq_zero_of_not_badPt hc h2)
        refine ⟨hled, hb, hd, fun θ hθ => ?_⟩
        rw [← hzt θ hθ]
        refine (hids θ hθ).trans ?_
        congr 1
        exact Finset.prod_congr rfl fun π hπ =>
          congrArg (· ^ 2 ^ π) (hyt θ hθ π (Finset.mem_range.mp hπ))
      · rw [if_neg hnz] at hxo
        exact absurd hxo (by simp)

/-! ## 5. Step 3: the key side -/

/-- Layer l of the key side: from level l to level l + 1. -/
@[reducible] def plK (l : ℕ) : PL E Y Pd N (LkX N E) where
  g := l + L.par.σ
  ord := L.par.kOrd l
  nz := L.par.kf (l + 1)
  proj := L.proj
  place := L.place
  idx := L.pK l
  pv := L.pKv l

/-- the true vectors of that layer: the two halves of the level l + 1 -/
@[reducible] def vK (l : ℕ) : PL.Vecs E Y (LkX N E) where
  f0 ξ y X := L.par.kLev (T.key y) ξ.al (l + 1) X
  f1 ξ y X := L.par.kLev (T.key y) ξ.al (l + 1) (X + 2 ^ (l + L.par.σ))

/-- A statement of the lookup argument as a statement of a product layer, and back. The whole
explicit part is the public data of the layer. -/
def gxPL (x : LkX N E) : PLX N E (LkX N E) := ⟨x.C, x.pt, x.led, x⟩
def pxPL (x : LkX N E) (xo : PL.XOut N E (LkX N E)) : LkX N E :=
  { x with C := xo.1.C, pt := xo.1.pt, led := xo.1.led }

@[reducible] def bK (l : ℕ) : Block (LkX N E) Y (LkX N E) Y :=
  (L.plK l).pl.on gxPL pxPL id (fun _ yo => yo)

/-- Soundness of one layer of the key side, under ho (`LkPar.OrdOK`), hl (l < D). -/
theorem clean_bK (ho : L.par.OrdOK) {l : ℕ} (hl : l < L.par.D) :
    (L.bK l).Clean (L.RK T l) ((L.RK T) (l + 1)) ((L.plK l).plErr 1) :=
  cleanOnX (L.plK l).imp_pl ((L.plK l).clean_pl_b (L.vK T l) (ho.kOrd l))
      fun x y xo ⟨ρ, p, hpub⟩ h => by
    have hal : xo.1.pub = x := (L.plK l).pub_of_pl hpub
    obtain ⟨hled, hfk, hkl⟩ := h
    refine ⟨⟨hled, fun hpt => ?_⟩, fun hin => ⟨hin.1, hfk, fun hpt => ?_⟩⟩
    · have h1 : L.V y xo.1.C = ext (l + 1 + L.par.σ) (L.par.kLev (T.key y) x.al (l + 1)) xo.1.pt :=
        hkl fun t ht hf => hpt t (by show t < l + L.par.σ + 1; omega) hf
      rw [show l + 1 + L.par.σ = l + L.par.σ + 1 by omega,
        ← consPt_eta xo.1.pt, ext_succ_consPt] at h1
      rw [hal]
      exact h1
    · rw [L.par.ext_kLev (T.key y) x.al hl]
      exact hin.2 fun t ht => hpt t ht (L.par.kf_of_lt hl t)

/-- The end claim: the end form of the key side has the value of the extension of leaf at the end
point. The premise: no coordinate of the end point that the verifier checks (`LkPar.zf`) is 0 (the
verifier has rejected otherwise). -/
def END (x : LkX N E) (y : Y) : Prop :=
  (∀ t < L.par.D + L.par.σ, L.par.zf t = true → x.z t ≠ 0) →
  L.V y x.Cend = ext (L.par.D + L.par.σ) (L.par.leafK (T.key y) x.al) x.z

/-- After the key side. -/
def R3 (x : LkX N E) (y : Y) : Prop := L.LED x y ∧ (L.FK T) x y ∧ (L.END T) x y

/-- The end form and the end point of the key side are stored. -/
@[reducible] def bKe (_L : Lk E Y Pd N) : Block (LkX N E) Y (LkX N E) Y :=
  Block.pure (fun x => some { x with Cend := x.C, z := x.pt }) id

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
theorem clean_bKe : L.bKe.Clean (L.RK T L.par.D) (L.R3 T) () :=
  Block.clean_pure_iff.2 fun x y xo hxo hR => by
    obtain rfl := Option.some.inj hxo
    obtain ⟨h1, h2, h3⟩ := hR
    refine ⟨h1, h2, fun hpt => ?_⟩
    rw [L.par.kLev_top]
    exact h3 fun t ht hf => hpt t ht ((L.par.kf_top t).trans hf)

/-! ## 6. Step 4: the table side -/

/-- The value forms of the Y_(θ,π) at the index (θ|π), 0 for an unused θ. -/
def yFlat (Yf : ℕ → ℕ → Form N E) (u : ℕ) : Form N E :=
  if u / 2 ^ L.par.lp < L.par.NT then Yf (u / 2 ^ L.par.lp) (u % 2 ^ L.par.lp) else 0

/-- The running claim of the table side at level l. -/
def TLc (l : ℕ) (x : LkX N E) (y : Y) : Prop :=
  (∀ t < l + (L.par.σ + L.par.lp), x.pt t ≠ 0) →
  L.V y x.C = ext (l + (L.par.σ + L.par.lp)) (L.par.tLev (T.B y) x.al l) x.pt

/-- The claims that stay open through the table side. -/
def FT (x : LkX N E) (y : Y) : Prop :=
  L.par.Bits (T.B y) ∧ L.par.DegE (T.B y) ∧ L.IDS x y ∧ (L.END T) x y
def RT (l : ℕ) (x : LkX N E) (y : Y) : Prop := L.LED x y ∧ (L.FT T) x y ∧ (L.TLc T) l x y

def setT0 (x : LkX N E) (ϱ : Fin (L.par.σ + L.par.lp) → E) : LkX N E :=
  { x with
    C := extF (L.par.σ + L.par.lp) (L.yFlat x.Yf) (nat ϱ)
    pt := nat ϱ }

/-- The verifier sends ϱ3, rejects if a coordinate is 0, and forms ∑ eq(ϱ3, (θ|π)) Y_(θ,π). -/
@[reducible] def bT0 : Block (LkX N E) Y (LkX N E) Y :=
  Block.one (Block.chalRound E (Fin (L.par.σ + L.par.lp) → E))
    (fun x ϱ _ => if nzT ϱ then some (L.setT0 x ϱ) else none) (fun y _ _ => y)

omit [DecidableEq N] in
/-- Soundness of the block bT0 (ϱ3: the start point of the table side), under hnt (NT ≤ 2^σ). -/
theorem clean_bT0 (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    L.bT0.Clean (L.R3 T) (L.RT T 0)
      ((L.par.σ + L.par.lp) * Fintype.card E ^ (L.par.σ + L.par.lp - 1), ()) := by
  refine Block.clean_one (r := Block.chalRound E (Fin (L.par.σ + L.par.lp) → E))
    (fun x y _ =>
      {ϱ | BadPt (L.par.σ + L.par.lp) (L.par.dY (T.B y) x.al fun θ π => L.V y (x.Yf θ π)) ϱ})
    _ (fun x y m => cnt_badPt_le _ _) fun x y m ϱ xo hc hxo hRo => ?_
  by_cases hnz : nzT ϱ = true
  · rw [if_pos hnz] at hxo
    obtain rfl := Option.some.inj hxo
    obtain ⟨hled, ⟨hb, hd, hids, hend⟩, htl⟩ := hRo
    have h1 : L.V y (extF (L.par.σ + L.par.lp) (L.yFlat x.Yf) (nat ϱ))
        = ext (0 + (L.par.σ + L.par.lp)) (L.par.tLev (T.B y) x.al 0) (nat ϱ) :=
      htl fun t ht => nat_ne_zero_of_nzT hnz t (by omega)
    change Form.val (L.proj y) _ = _ at h1
    rw [Nat.zero_add, val_extF] at h1
    have h2 : ext (L.par.σ + L.par.lp) (L.par.dY (T.B y) x.al fun θ π => L.V y (x.Yf θ π)) (nat ϱ) =
        0 := by
      unfold LkPar.dY
      rw [ext_sub, ← h1]
      refine sub_eq_zero.mpr (ext_congr (fun u _ => ?_) _)
      unfold yFlat
      split_ifs
      · rfl
      · exact (map_zero _).symm
    exact ⟨hled,
      ⟨hb, hd, hids, (L.par.dY_eq_zero_iff hnt (T.B y) x.al _).mp (eq_zero_of_not_badPt hc h2)⟩,
      hend⟩
  · rw [if_neg hnz] at hxo
    exact absurd hxo (by simp)

/-- Layer l of the table side. -/
@[reducible] def plT (l : ℕ) : PL E Y Pd N (LkX N E) where
  g := l + (L.par.σ + L.par.lp)
  nz := fun _ => true
  proj := L.proj
  place := L.place
  idx := L.pT l
  pv := L.pTv l

/-- the true vectors of that layer: the two halves of the level l + 1 -/
@[reducible] def vT (l : ℕ) : PL.Vecs E Y (LkX N E) where
  f0 ξ y X := L.par.tLev (T.B y) ξ.al (l + 1) X
  f1 ξ y X := L.par.tLev (T.B y) ξ.al (l + 1) (X + 2 ^ (l + (L.par.σ + L.par.lp)))

@[reducible] def bT (l : ℕ) : Block (LkX N E) Y (LkX N E) Y :=
  (L.plT l).pl.on gxPL pxPL id (fun _ yo => yo)

theorem clean_bT {l : ℕ} (hl : l < L.par.r) :
    (L.bT l).Clean (L.RT T l) ((L.RT T) (l + 1)) ((L.plT l).plErr 1) :=
  cleanOnX (L.plT l).imp_pl ((L.plT l).clean_pl_b (L.vT T l) (List.Perm.refl _))
      fun x y xo ⟨ρ, p, hpub⟩ h => by
    have hal : xo.1.pub = x := (L.plT l).pub_of_pl hpub
    obtain ⟨hled, hft, htl⟩ := h
    refine ⟨⟨hled, fun hpt => ?_⟩, fun hin => ⟨hin.1, hft, fun hpt => ?_⟩⟩
    · have h1 : L.V y xo.1.C =
          ext (l + 1 + (L.par.σ + L.par.lp)) (L.par.tLev (T.B y) x.al (l + 1)) xo.1.pt :=
        htl fun t ht => hpt t (by show t < l + (L.par.σ + L.par.lp) + 1; omega) rfl
      rw [show l + 1 + (L.par.σ + L.par.lp) = l + (L.par.σ + L.par.lp) + 1 by omega,
        ← consPt_eta xo.1.pt, ext_succ_consPt] at h1
      rw [hal]
      exact h1
    · rw [L.par.ext_tLev (T.B y) x.al hl]
      exact hin.2 hpt


/-! ### The leaf layer -/

/-- The first claim on ~B. -/
def CB4 (x : LkX N E) (y : Y) : Prop := L.V y x.v4 = ext L.par.gT (L.par.vB (T.B y)) x.p4
/-- After the leaf layer. -/
def R5 (x : LkX N E) (y : Y) : Prop := L.LED x y ∧ (L.FT T) x y ∧ (L.CB4 T) x y

@[reducible] def plL : PL E Y Pd N (LkX N E) where
  g := L.par.gT
  nz := fun _ => false
  proj := L.proj
  place := L.place
  idx := L.pL
  pv := L.pLv

/-- the true vectors of the leaf layer -/
@[reducible] def vL : PL.Vecs E Y (LkX N E) where
  f0 _ y X := L.par.vB (T.B y) X
  f1 ξ _ X := L.par.vA ξ.al X

/-- The verifier subtracts the extension of the indicator of θ < NT at the current point. -/
def gxL (x : LkX N E) : PLX N E (LkX N E) :=
  ⟨x.C - Form.const (ext L.par.gT L.par.vI x.pt), x.pt, x.led, x⟩

/-- After the leaf layer: a LIN equates v1 with the public value ~f1(ϱ̂4); v0 and ϱ̂4 are stored for
the first claim on ~B. -/
def pxL (x : LkX N E) (xo : PL.XOut N E (LkX N E)) : LkX N E :=
  { x with
    v4 := xo.2.1
    p4 := fun t => xo.1.pt (t + 1)
    led := xo.1.led.addLin
      (xo.2.2 - Form.const (ext L.par.gT (L.par.vA x.al) fun t => xo.1.pt (t + 1))) }

@[reducible] def bL : Block (LkX N E) Y (LkX N E) Y :=
  L.plL.pl.on L.gxL L.pxL id (fun _ yo => yo)

theorem clean_bL : L.bL.Clean (L.RT T L.par.r) (L.R5 T) (L.plL.plErr 0) :=
  cleanOnX L.plL.imp_pl (L.plL.clean_pl_a (L.vL T) (List.Perm.refl _))
      fun x y xo ⟨ρ, p, hpub⟩ h => by
    have hal : xo.1.pub = x := L.plL.pub_of_pl hpub
    obtain ⟨hled, hft, hcb⟩ := h
    obtain ⟨hl1, hl2⟩ := (Ledger.true_addLin _ _ _).mp hled
    rw [map_sub, Form.val_const, sub_eq_zero] at hl2
    refine ⟨⟨hl1, hcb, ?_⟩, fun hin => ⟨hin.1, hft, fun hpt => ?_⟩⟩
    · rw [hal]
      exact hl2
    · have h1 := hin.2 hpt
      change Form.val (L.proj y) (x.C - Form.const _) =
        ext L.par.gT (fun X => L.par.vB (T.B y) X * L.par.vA x.al X) x.pt at h1
      rw [map_sub, Form.val_const, ← L.par.ext_leafT] at h1
      rw [L.par.tLev_top]
      exact sub_left_injective h1

/-! ### The bit layer -/

/-- The start claim of the bit layer. -/
def BLc (x : LkX N E) (y : Y) : Prop :=
  (∀ t < L.par.gT, x.pt t ≠ 0) →
  L.V y x.C = ext L.par.gT (fun X => L.par.vB (T.B y) X * (L.par.vB (T.B y) X - 1)) x.pt

/-- The claims that stay open through the bit layer. -/
def FB (x : LkX N E) (y : Y) : Prop :=
  L.par.DegE (T.B y) ∧ L.IDS x y ∧ (L.END T) x y ∧ (L.CB4 T) x y
def R6 (x : LkX N E) (y : Y) : Prop := L.LED x y ∧ (L.FB T) x y ∧ (L.BLc T) x y

/-- The verifier sends ϱ5 and rejects if a coordinate is 0; the bit layer starts from the form 0. -/
@[reducible] def bB0 : Block (LkX N E) Y (LkX N E) Y :=
  Block.one (Block.chalRound E (Fin L.par.gT → E))
    (fun x ϱ _ => if nzT ϱ then some { x with C := 0, pt := nat ϱ } else none) (fun y _ _ => y)

omit [DecidableEq N] in
/-- Soundness of the block bB0 (ϱ5), under hnt (NT ≤ 2^σ). -/
theorem clean_bB0 (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    L.bB0.Clean (L.R5 T) (L.R6 T) (L.par.gT * Fintype.card E ^ (L.par.gT - 1), ()) := by
  refine Block.clean_one (r := Block.chalRound E (Fin L.par.gT → E))
    (fun _ y _ => {ϱ | BadPt L.par.gT (fun X => L.par.vB (T.B y) X * (L.par.vB (T.B y) X - 1)) ϱ}) _
    (fun x y m => cnt_badPt_le _ _) fun x y m ϱ xo hc hxo hRo => ?_
  by_cases hnz : nzT ϱ = true
  · rw [if_pos hnz] at hxo
    obtain rfl := Option.some.inj hxo
    obtain ⟨hled, ⟨hd, hids, hend, hcb⟩, hbl⟩ := hRo
    have h1 : L.V y 0 =
        ext L.par.gT (fun X => L.par.vB (T.B y) X * (L.par.vB (T.B y) X - 1)) (nat ϱ) :=
      hbl fun t ht => nat_ne_zero_of_nzT hnz t ht
    change Form.val (L.proj y) 0 = _ at h1
    rw [map_zero] at h1
    exact ⟨hled,
      ⟨(L.par.bits_iff hnt (T.B y)).mp (eq_zero_of_not_badPt hc h1.symm), hd, hids, hend⟩,
      hcb⟩
  · rw [if_neg hnz] at hxo
    exact absurd hxo (by simp)

/-- The second claim on ~B. -/
def CB5 (x : LkX N E) (y : Y) : Prop := L.V y x.v5 = ext L.par.gT (L.par.vB (T.B y)) x.p5
/-- After steps 1 to 4. The open claims: the degree check and the identity `LkPar.Ident` for the
sent products, the end claim, the two claims on ~B; and the list. -/
def R7 (x : LkX N E) (y : Y) : Prop := L.LED x y ∧ (L.FB T) x y ∧ (L.CB5 T) x y

@[reducible] def plB : PL E Y Pd N (LkX N E) where
  g := L.par.gT
  nz := fun _ => false
  proj := L.proj
  place := L.place
  idx := L.pB
  pv := L.pBv

/-- the true vectors of the bit layer -/
@[reducible] def vBt : PL.Vecs E Y (LkX N E) where
  f0 _ y X := L.par.vB (T.B y) X
  f1 _ y X := L.par.vB (T.B y) X - 1

/-- After the bit layer: a LIN states v1 = v0 - 1; v0 and ϱ̂5 are stored for the second claim on
~B. -/
def pxB (x : LkX N E) (xo : PL.XOut N E (LkX N E)) : LkX N E :=
  { x with
    v5 := xo.2.1
    p5 := fun t => xo.1.pt (t + 1)
    led := xo.1.led.addLin (xo.2.2 - xo.2.1 + Form.const 1) }

@[reducible] def bB : Block (LkX N E) Y (LkX N E) Y :=
  L.plB.pl.on gxPL pxB id (fun _ yo => yo)

theorem clean_bB : L.bB.Clean (L.R6 T) (L.R7 T) (L.plB.plErr 0) :=
  cleanOnX L.plB.imp_pl (L.plB.clean_pl_a (L.vBt T) (List.Perm.refl _)) fun x y xo _ h => by
    obtain ⟨hled, hfb, hcb⟩ := h
    obtain ⟨hl1, hl2⟩ := (Ledger.true_addLin _ _ _).mp hled
    rw [map_add, map_sub, Form.val_const] at hl2
    refine ⟨⟨hl1, hcb, ?_⟩, fun hin => ⟨hin.1, hfb, hin.2⟩⟩
    have h5 : Form.val (L.proj y) xo.2.1 =
        ext L.par.gT (L.par.vB (T.B y)) (fun t => xo.1.pt (t + 1)) := hcb
    show Form.val (L.proj y) xo.2.2 =
      ext L.par.gT (fun X => L.par.vB (T.B y) X - 1) (fun t => xo.1.pt (t + 1))
    rw [L.par.ext_vB_sub_one, ← h5]
    linear_combination hl2

/-! ## 7. Step 5: the degree check -/

/-- The degree claim at ϱ6, for the true B. -/
def CDEG (x : LkX N E) (y : Y) : Prop := ext L.par.σ (L.par.dDeg (T.B y)) x.p6 = 0
/-- The claims that stay open from here on: those that the argument passes to the containing
protocol. -/
def OUT5 (x : LkX N E) (y : Y) : Prop :=
  (L.END T) x y ∧ (L.CB4 T) x y ∧ (L.CB5 T) x y ∧ (L.CDEG T) x y
/-- After step 5. -/
def R8 (x : LkX N E) (y : Y) : Prop := L.LED x y ∧ L.IDS x y ∧ (L.OUT5 T) x y

@[reducible] def bDeg : Block (LkX N E) Y (LkX N E) Y :=
  Block.one (Block.chalRound E (Fin L.par.σ → E))
    (fun x ϱ _ => some { x with p6 := nat ϱ }) (fun y _ _ => y)

omit [DecidableEq E] [DecidableEq N] in
/-- Soundness of the block bDeg (ϱ6), under hnt (NT ≤ 2^σ). -/
theorem clean_bDeg (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    L.bDeg.Clean (L.R7 T) (L.R8 T) (L.par.σ * Fintype.card E ^ (L.par.σ - 1), ()) := by
  refine Block.clean_one (r := Block.chalRound E (Fin L.par.σ → E))
    (fun _ y _ => {ϱ | BadPt L.par.σ (L.par.dDeg (T.B y)) ϱ}) _
    (fun x y m => cnt_badPt_le _ _) fun x y m ϱ xo hc hxo hRo => ?_
  obtain rfl := Option.some.inj hxo
  obtain ⟨hled, hids, hend, h4, h5, hdeg⟩ := hRo
  exact ⟨hled,
    ⟨(L.par.dDeg_eq_zero_iff hnt (T.B y)).mp (eq_zero_of_not_badPt hc hdeg), hids, hend, h4⟩,
    h5⟩

/-! ## 8. Step 6: the root test -/

/-- The values of the sent scalars. -/
def Zv (x : LkX N E) (y : Y) (θ : ℕ) : E := L.V y (x.Zf θ)
def Yv (x : LkX N E) (y : Y) (θ π : ℕ) : E := L.V y (x.Yf θ π)
def Uv (x : LkX N E) (y : Y) (π θ : ℕ) : E := L.V y (x.Uf π θ)
def Vv (x : LkX N E) (y : Y) (π θ : ℕ) : E := L.V y (x.Vf π θ)

/-- The scalars of step 6: U_π[θ] and V_π[θ] for π < Pm. -/
abbrev KUV : Type := Fin L.par.Pm × Fin L.par.NT ⊕ Fin L.par.Pm × Fin L.par.NT

abbrev rUV : Round :=
  vRound E Empty (fun a => Empty.elim a) (fun a => Empty.elim a) L.KUV (Fin L.par.σ → E)

def uForm (s : L.KUV → E) (π θ : ℕ) : Form N E :=
  if h : π < L.par.Pm ∧ θ < L.par.NT then
    Form.masked (s (.inl (⟨π, h.1⟩, ⟨θ, h.2⟩))) (L.place (L.pU π θ))
  else 0

def vForm (s : L.KUV → E) (π θ : ℕ) : Form N E :=
  if h : π < L.par.Pm ∧ θ < L.par.NT then
    Form.masked (s (.inr (⟨π, h.1⟩, ⟨θ, h.2⟩))) (L.place (L.pV π θ))
  else 0

def setUV (x : LkX N E) (ϱ : Fin L.par.σ → E) (s : L.KUV → E) : LkX N E :=
  { x with
    Uf := L.uForm s
    Vf := L.vForm s
    pr := nat ϱ }

/-- The prover sends the arrays U, V; then the verifier sends ϱ' and rejects if a coordinate is
0. -/
@[reducible] def bUV : Block (LkX N E) Y (LkX N E) Y :=
  Block.one L.rUV (fun x ϱ s => if nzT ϱ then some (L.setUV x ϱ s) else none) (fun y _ _ => y)

/-- If no coordinate of ϱ' is 0, the extensions of all functions of the family vanish at ϱ'. -/
def FAM (x : LkX N E) (y : Y) : Prop :=
  (∀ t < L.par.σ, x.pr t ≠ 0) →
  ∀ m, ext L.par.σ (L.par.dFam x.al (L.Zv x y) (L.Yv x y) (L.Uv x y) (L.Vv x y) m) x.pr = 0

def R9a (x : LkX N E) (y : Y) : Prop := L.LED x y ∧ (L.OUT5 T) x y ∧ L.FAM x y

/-- Soundness of the block bUV (ϱ'), under hnt (NT ≤ 2^σ). -/
theorem clean_bUV (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    L.bUV.Clean (L.R8 T) (L.R9a T) (L.par.σ * Fintype.card E ^ (L.par.σ - 1), ()) := by
  refine Block.clean_one (r := L.rUV)
    (fun x y m =>
      {ϱ | BadPtFam L.par.σ
        (L.par.dFam x.al (L.Zv x y) (L.Yv x y) (fun π θ => L.V y (L.uForm m.2 π θ))
          (fun π θ => L.V y (L.vForm m.2 π θ))) ϱ})
    _ (fun x y m => cnt_badPtFam_le _ _) fun x y m ϱ xo hc hxo hRo => ?_
  by_cases hnz : nzT ϱ = true
  · rw [if_pos hnz] at hxo
    obtain rfl := Option.some.inj hxo
    obtain ⟨hled, hout, hfam⟩ := hRo
    exact ⟨hled,
      L.par.ident_of_dFam hnt (eq_zero_of_not_badPtFam hc (hfam (nat_ne_zero_of_nzT hnz))),
      hout⟩
  · rw [if_neg hnz] at hxo
    exact absurd hxo (by simp)

/-- ~d⋆(ϱ') = 0. -/
def STAR (x : LkX N E) (y : Y) : Prop :=
  ext L.par.σ (L.par.dStar x.al (L.Zv x y) (L.Yv x y) (L.Uv x y)) x.pr = 0
/-- If no coordinate of ϱ' is 0, the combination of the ~d_π(ϱ'), ~d'_π(ϱ') under the coefficients
vanishes. -/
def SUMc (x : LkX N E) (y : Y) : Prop :=
  (∀ t < L.par.σ, x.pr t ≠ 0) →
  ∑ j ∈ Finset.range (2 * L.par.Pm),
      x.cx j * ext L.par.σ (L.par.dPair (L.Yv x y) (L.Uv x y) (L.Vv x y) j) x.pr = 0

def R9b (x : LkX N E) (y : Y) : Prop := L.LED x y ∧ (L.OUT5 T) x y ∧ L.STAR x y ∧ L.SUMc x y

/-- The verifier sends the coefficients (ξ, ξ'). -/
@[reducible] def bXi : Block (LkX N E) Y (LkX N E) Y :=
  Block.one (Block.chalRound E (Fin (2 * L.par.Pm) → E))
    (fun x c _ => some { x with cx := nat c }) (fun y _ _ => y)

omit [DecidableEq N] in
/-- Soundness of the block bXi ((ξ, ξ')). -/
theorem clean_bXi : L.bXi.Clean (L.R9a T) (L.R9b T) (L.par.eXi (Fintype.card E), ()) := by
  refine Block.clean_one (r := Block.chalRound E (Fin (2 * L.par.Pm) → E))
    (fun x y _ => {c | L.par.BadXi (L.Yv x y) (L.Uv x y) (L.Vv x y) x.pr c}) _
    (fun x y m => L.par.cnt_badXi_le _ _ _ _) fun x y m c xo hc hxo hRo => ?_
  obtain rfl := Option.some.inj hxo
  obtain ⟨hled, hout, hstar, hsum⟩ := hRo
  refine ⟨hled, hout, fun hpt m' => ?_⟩
  have h1 : ∑ j : Fin (2 * L.par.Pm),
        c j * ext L.par.σ (L.par.dPair (L.Yv x y) (L.Uv x y) (L.Vv x y) j) x.pr = 0 := by
    have h2 : ∑ j ∈ Finset.range (2 * L.par.Pm),
          nat c j * ext L.par.σ (L.par.dPair (L.Yv x y) (L.Uv x y) (L.Vv x y) j) x.pr = 0 :=
      hsum hpt
    rw [← Fin.sum_univ_eq_sum_range (fun j =>
        nat c j * ext L.par.σ (L.par.dPair (L.Yv x y) (L.Uv x y) (L.Vv x y) j) x.pr)] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun j _ => by simp [nat, j.2]
  have h3 : (fun j : Fin (2 * L.par.Pm) =>
        ext L.par.σ (L.par.dPair (L.Yv x y) (L.Uv x y) (L.Vv x y) j) x.pr) = 0 := by
    by_contra hne
    exact hc ⟨hne, h1⟩
  unfold LkPar.dFam
  split_ifs with h0
  · exact hstar
  · exact congrFun h3 ⟨m'.val - 1, by have := m'.2; omega⟩

/-- The true polynomial of the sumcheck of the root test. -/
@[reducible] def scRPhi (ξ : LkX N E) (y : Y) (w : ℕ → E) : E :=
  L.par.rootPhi (L.Yv ξ y) (L.Uv ξ y) (L.Vv ξ y) ξ.cx w

/-- The data of the sumcheck of the root test: σ rounds with the equality factor eq(ϱ', ·), of
degree 2. -/
@[reducible] def scR : SC E Y Pd (LkX N E) ℕ where
  forms := Forms.ofForm L.proj L.place
  wt ξ := Alg.eqW ξ.pr
  e _ := 1
  idx := L.pR
  nzv _ := false

omit [Fintype E] [DecidableEq E] in
theorem scR_ok : L.scR.OK L.scRPhi :=
  { forms := Forms.ofForm_ok _ _, deg := fun _ _ => L.par.degLE_rootPhi _ _ _ _ }

@[reducible] def bRs : Block (LkX N E) Y (LkX N E) Y :=
  (L.scR.sc (lkVars L.par.σ)).on (fun x => ((0 : Form N E), fun _ => 0, x))
    (fun x xo => { x with C := xo.1, pt := xo.2.1 }) id (fun _ yo => yo)

/-- The end claim of the sumcheck of the root test. -/
def REV (x : LkX N E) (y : Y) : Prop :=
  L.V y x.C = L.par.rootPhi (L.Yv x y) (L.Uv x y) (L.Vv x y) x.cx x.pt

def R9c (x : LkX N E) (y : Y) : Prop := L.LED x y ∧ (L.OUT5 T) x y ∧ L.STAR x y ∧ L.REV x y

theorem mem_lkVars {g v : ℕ} : v ∈ lkVars g ↔ v < g := by
  unfold lkVars
  rw [List.mem_map]
  exact ⟨fun ⟨t, _, ht⟩ => ht ▸ t.2, fun h => ⟨⟨v, h⟩, List.mem_finRange _, rfl⟩⟩

/-- Soundness of the rounds of the root test. -/
theorem clean_bRs : L.bRs.Clean (L.R9b T) (L.R9c T) (L.scR.scErr (lkVars L.par.σ)) :=
  cleanOnX (L.scR.imp_sc _) (L.scR.clean_sc_eval L.scR_ok (lkVars L.par.σ))
      fun x y xo ⟨ρ, p, hpub⟩ h => by
    have hdata : xo.2.2 = x := L.scR.data_of_pub_sc _ _ _ _ _ hpub
    obtain ⟨hled, hout, hstar, hrev⟩ := h
    refine ⟨fun _ => ?_, fun hin => ⟨hled, hout, hstar, fun hpt => ?_⟩⟩
    · show Form.val (L.proj y) xo.1 =
        L.par.rootPhi (L.Yv xo.2.2 y) (L.Uv xo.2.2 y) (L.Vv xo.2.2 y) xo.2.2.cx xo.2.1
      rw [hdata]
      exact hrev
    · have h1 := hin (fun v hv => hpt v (mem_lkVars.mp hv)) (fun v hv _ => absurd hv (by simp))
      have h2 : Form.val (L.proj y) (0 : Form N E) =
          Alg.sumOutL (Alg.eqW x.pr) (lkVars L.par.σ)
            (L.par.rootPhi (L.Yv x y) (L.Uv x y) (L.Vv x y) x.cx) (fun _ => 0) := h1
      rw [map_zero, L.par.sumOutL_rootPhi] at h2
      exact h2.symm

/-! ### The claims that the root test defers -/

/-- The extensions of the arrays at a point, as forms in the scalars already sent. -/
def eUf (x : LkX N E) (π : ℕ) (w : ℕ → E) : Form N E :=
  extF L.par.σ (L.par.msk (L.par.uArr x.Yf x.Uf π)) w
def eVf (x : LkX N E) (π : ℕ) (w : ℕ → E) : Form N E := extF L.par.σ (L.par.msk (x.Vf π)) w
def eYf (x : LkX N E) (π : ℕ) (w : ℕ → E) : Form N E := extF L.par.σ (L.par.msk fun θ => x.Yf θ π) w

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
theorem val_uArr (x : LkX N E) (y : Y) (π θ : ℕ) :
    L.V y (L.par.uArr x.Yf x.Uf π θ) = L.par.uArr (L.Yv x y) (L.Uv x y) π θ := by
  unfold LkPar.uArr
  split_ifs <;> rfl

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
theorem val_eUf (x : LkX N E) (y : Y) (π : ℕ) (w : ℕ → E) :
    L.V y (L.eUf x π w) = L.par.eU (L.Yv x y) (L.Uv x y) π w := by
  unfold eUf LkPar.eU
  change Form.val (L.proj y) _ = _
  rw [val_extF]
  refine ext_congr (fun θ _ => ?_) w
  rw [LkPar.val_msk]
  unfold LkPar.msk
  split_ifs
  · exact L.val_uArr x y π θ
  · rfl

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
theorem val_eVf (x : LkX N E) (y : Y) (π : ℕ) (w : ℕ → E) :
    L.V y (L.eVf x π w) = L.par.eV (L.Vv x y) π w := by
  unfold eVf LkPar.eV
  change Form.val (L.proj y) _ = _
  rw [val_extF]
  exact ext_congr (fun θ _ => LkPar.val_msk _ _ _ _) w

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
theorem val_eYf (x : LkX N E) (y : Y) (π : ℕ) (w : ℕ → E) :
    L.V y (L.eYf x π w) = L.par.eY (L.Yv x y) π w := by
  unfold eYf LkPar.eY
  change Form.val (L.proj y) _ = _
  rw [val_extF]
  exact ext_congr (fun θ _ => LkPar.val_msk _ _ _ _) w

/-- The opened forms: for each π < Pm the extensions of U_(π+1), V_π, Y_(·,π) at the end point (3 Pm
forms; 93 for lp = 5). -/
def osFn (x : LkX N E) (k : ℕ) : Form N E :=
  if k % 3 = 0 then L.eUf x (k / 3 + 1) x.pt
  else if k % 3 = 1 then L.eVf x (k / 3) x.pt
  else L.eYf x (k / 3) x.pt
def os (x : LkX N E) : List (Form N E) := (List.range (3 * L.par.Pm)).map (L.osFn x)

/-- The terms of the REL: -ξ_π U_(π+1)² and -ξ'_π V_π Y_(·,π). -/
def ts (x : LkX N E) : List (E × ℕ × ℕ) :=
  (List.range L.par.Pm).flatMap fun π =>
    [(-x.cx π, 3 * π, 3 * π), (-x.cx (L.par.Pm + π), 3 * π + 1, 3 * π + 2)]

/-- The end form, less the terms that are linear in V_π and U_π. -/
def fR (x : LkX N E) : Form N E :=
  x.C -
    ∑ π ∈ Finset.range L.par.Pm, (x.cx π • L.eVf x π x.pt + x.cx (L.par.Pm + π) • L.eUf x π x.pt)

/-- The form of the LIN: ∑_θ eq(ϱ', θ) (Z_θ - (α - τ⁰)^ϕ U_0[θ]). -/
def fS (x : LkX N E) : Form N E :=
  extF L.par.σ
    (L.par.msk fun θ =>
      x.Zf θ - ((x.al - L.par.tb θ (L.par.t0 θ)) ^ L.par.φ θ) • L.par.uArr x.Yf x.Uf 0 θ) x.pr

/-- The verifier adds the opened forms, the REL and the LIN of the root test to the list. It rejects
if the list names opened forms that are not there. -/
@[reducible] def bRec : Block (LkX N E) Y (LkX N E) Y :=
  Block.pure (fun x =>
    if x.led.wf then
      some { x with led := (x.led.addRel (L.fR x) (L.os x) (L.ts x)).addLin (L.fS x) }
    else none) id

/-- After the argument: all claims on the list are true, and the claims that are passed to the
containing protocol hold: the end claim, the two claims on ~B and the degree claim. -/
def R10 (x : LkX N E) (y : Y) : Prop := L.LED x y ∧ (L.OUT5 T) x y

omit [Fintype E] [DecidableEq E] [DecidableEq N] [Fintype N] in
theorem os_getD (x : LkX N E) {k : ℕ} (hk : k < 3 * L.par.Pm) : (L.os x).getD k 0 = L.osFn x k := by
  unfold os
  simp [List.getD_eq_getElem?_getD, hk]

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
theorem termSum_ts (x : LkX N E) (y : Y) :
    termSum (fun i => Form.val (L.proj y) ((L.os x).getD i 0)) (L.ts x) =
      ∑ π ∈ Finset.range L.par.Pm, (-x.cx π * L.par.eU (L.Yv x y) (L.Uv x y) (π + 1) x.pt *
          L.par.eU (L.Yv x y) (L.Uv x y) (π + 1) x.pt +
        -x.cx (L.par.Pm + π) * L.par.eV (L.Vv x y) π x.pt * L.par.eY (L.Yv x y) π x.pt) := by
  unfold ts
  rw [termSum_flatMap_range]
  refine Finset.sum_congr rfl fun π hπ => ?_
  have hπ' := Finset.mem_range.mp hπ
  have e0 : (L.os x).getD (3 * π) 0 = L.eUf x (π + 1) x.pt := by
    rw [L.os_getD x (by omega)]
    unfold osFn
    rw [if_pos (by omega), show 3 * π / 3 = π by omega]
  have e1 : (L.os x).getD (3 * π + 1) 0 = L.eVf x π x.pt := by
    rw [L.os_getD x (by omega)]
    unfold osFn
    rw [if_neg (by omega), if_pos (by omega), show (3 * π + 1) / 3 = π by omega]
  have e2 : (L.os x).getD (3 * π + 2) 0 = L.eYf x π x.pt := by
    rw [L.os_getD x (by omega)]
    unfold osFn
    rw [if_neg (by omega), if_neg (by omega), show (3 * π + 2) / 3 = π by omega]
  simp only [termSum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, e0, e1, e2]
  rw [← L.val_eUf, ← L.val_eVf, ← L.val_eYf]

omit [Fintype E] [DecidableEq E] [DecidableEq N] in
theorem clean_bRec : L.bRec.Clean (L.R9c T) (L.R10 T) () :=
  Block.clean_pure_iff.2 fun x y xo hxo hR => by
    by_cases hwf : x.led.wf = true
    · rw [if_pos hwf] at hxo
      obtain rfl := Option.some.inj hxo
      have hR' : (L.R10 T)
          { x with led := (x.led.addRel (L.fR x) (L.os x) (L.ts x)).addLin (L.fS x) } y := hR
      obtain ⟨hled, hout⟩ := hR'
      obtain ⟨h1, hlin⟩ := (Ledger.true_addLin _ _ _).mp hled
      obtain ⟨hled0, hrel⟩ := (Ledger.true_addRel hwf _ _ _ _).mp h1
      refine ⟨hled0, hout, ?_, ?_⟩
      · -- the LIN
        unfold STAR LkPar.dStar
        rw [← hlin]
        unfold fS
        rw [val_extF]
        refine ext_congr (fun θ _ => ?_) _
        rw [LkPar.val_msk]
        unfold LkPar.msk
        split_ifs
        · beta_reduce
          rw [map_sub, map_smul, smul_eq_mul]
          exact congrArg₂ (· - ·) rfl (congrArg _ (L.val_uArr x y 0 θ).symm)
        · rfl
      · -- the REL
        refine (L.par.rootPhi_eq_iff _ _ _ _ _ _).mpr ?_
        rw [← L.termSum_ts, ← hrel]
        unfold fR
        rw [map_sub, map_sum]
        refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun π _ => ?_)
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        exact congrArg₂ (· + ·) (congrArg _ (L.val_eVf x y π x.pt).symm)
          (congrArg _ (L.val_eUf x y π x.pt).symm)
    · rw [if_neg hwf] at hxo
      exact absurd hxo (by simp)

/-! ## 9. The count of a point -/

/-- g |E|^(g-1): the error of a point of g coordinates. -/
def ePt (E : Type) [Fintype E] (g : ℕ) : ℕ := g * Fintype.card E ^ (g - 1)


end Lk

end Blocks
