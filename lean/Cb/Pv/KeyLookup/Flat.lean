-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Flat.lean: typed transcripts and flat ones; the statement "the verifier's output is
a plain function of the flat transcript", and the rules that join such statements.

Definitions, statements and proofs. A transcript of a shape (Iop/Shape.lean) is a nested tuple whose
types hang on the rounds. A flat transcript is a list that has, for each round, the scalars sent and
the elements drawn. This file ties the two, so that what a chain of blocks puts out can be written
once as a function on plain lists and evaluated. The blocks are those without an honest side (BkK,
Cb/Pv/Lookup/Know/KnowAt.lean).

Main names:
  Flat.RV E: a round, flat: (the scalars sent, the elements drawn) : List E × List E.
  Flat.Fm: a round's format: how many scalars are sent, how many elements drawn, whether a drawn
    element must not be 0. Fm.fits, fitsAll: tests with values in Bool. fitsAll_app: a list that
    fits two lists of formats in a row splits into two that fit.
  Flat.RdR E r: how a round r is read flat (sent, drawn) and written from flat (mkM, mkC), with
    three laws: written, then read, is the same on rounds that fit (inv); what is read fits (fit);
    read, then written, is the same (back). So typed rounds and flat rounds that fit are one-to-one.
  Flat.RdS E s: such a record for each round of the shape s, with .fms (the formats), .view (from a
    typed transcript to its flat view), .mk (back), .app; view_mk, mk_view, view_fits, view_app.
  Flat.Runs b fm run: for a block b, a list of formats fm and a plain function
    run : X → List (RV E) → X': records rd for b's shape with the formats fm, and
    out : ∀ x y τ, b.R.out x y τ = some (run x (rd.view τ)): the verifier rejects nothing, and its
    output is run of the view, for all transcripts. The function run stands outside the record, so
    that it can have code where the record has none.
  Runs.seq (run := seqRun n ra rb: the first n rounds go to ra, the others to rb), Runs.postM,
    Runs.preM, Runs.map (a step without rounds), Runs.draw, Runs.fmEq: the rules.
  Runs.ofOut: from out x y τ = some (v x τ): run := v at the typed transcript that the flat one
    spells. Runs.congr: another way to write run; the two need agree on flat lists that fit alone.
  Runs.spells: for every flat list f that fits there is a typed transcript whose view is f, and at
    it the verifier puts out run x f. So a statement Runs is not hollow.
  rd0 (the first round of a sumcheck), FU, fuCube, fuDummy, rdS (a short round of a variable; the
    draw of the further variable is not 0), rdV (the round of shown values, listed by A ≃ Fin n),
    rdD, rdE, rdPt (draws), rdVars, rdFull, rdCore (the shapes shapeS Y and shapeSC Y of the short
    sumcheck, Cb/G6/Letter.lean).

Limits: a decidable equality on E is asked beside Field and Fintype. Nothing on soundness. No honest
side is named.

-/
import Cb.Pv.KeyLookup.Short0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
namespace Flat
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn Johnson.L5.Layers

/-- A round, flat: the scalars sent, the elements drawn. -/
abbrev RV (E : Type) : Type := List E × List E

/-- A round's format. -/
structure Fm where
  sent : ℕ
  drawn : ℕ
  /-- a drawn element must not be 0 -/
  nz : Bool
  deriving DecidableEq, Repr

section
variable {E : Type} [DecidableEq E] [Zero E]

def Fm.fits (f : Fm) (v : RV E) : Bool :=
  v.1.length == f.sent && v.2.length == f.drawn && (!f.nz || v.2.all (· != 0))

def fitsAll : List Fm → List (RV E) → Bool
  | [], [] => true
  | f :: fs, v :: vs => f.fits v && fitsAll fs vs
  | _, _ => false

theorem Fm.fits_iff (f : Fm) (v : RV E) :
    f.fits v = true ↔
      v.1.length = f.sent ∧ v.2.length = f.drawn ∧ (f.nz = true → ∀ e ∈ v.2, e ≠ 0) := by
  unfold Fm.fits
  cases f.nz <;> simp [and_assoc]

theorem fitsAll_app : ∀ (a b : List Fm) (f : List (RV E)), fitsAll (a ++ b) f = true →
    fitsAll a (f.take a.length) = true ∧ fitsAll b (f.drop a.length) = true
  | [], _, _, h => ⟨rfl, h⟩
  | _ :: _, _, [], h => absurd h (by simp [fitsAll])
  | x :: a, b, v :: f, h => by
    have h' : x.fits v = true ∧ fitsAll (a ++ b) f = true := by simpa [fitsAll] using h
    obtain ⟨h1, h2⟩ := fitsAll_app a b f h'.2
    refine ⟨?_, h2⟩
    show (x.fits v && fitsAll a (f.take a.length)) = true
    rw [h'.1, h1]
    rfl

variable (E) in
/-- How one round is read and written. -/
structure RdR (r : Round) where
  fm : Fm
  sent : r.Msg → List E
  drawn : r.Chal → List E
  mkM : List E → r.Msg
  mkC : List E → r.Chal
  /-- written, then read: the same, on a round that fits -/
  inv : ∀ v : RV E, fm.fits v = true → sent (mkM v.1) = v.1 ∧ drawn (mkC v.2) = v.2
  /-- what is read fits -/
  fit : ∀ m c, fm.fits (sent m, drawn c) = true
  /-- read, then written: the same -/
  back : ∀ m c, mkM (sent m) = m ∧ mkC (drawn c) = c

variable (E) in
/-- For each round of a shape, how it is read and written. -/
def RdS : Shape → Type
  | [] => Unit
  | r :: s => RdR E r × RdS s

namespace RdS

def fms : {s : Shape} → RdS E s → List Fm
  | [], _ => []
  | _ :: _, (a, A) => a.fm :: fms A

/-- The view of a typed transcript. -/
def view : {s : Shape} → RdS E s → Tr s → List (RV E)
  | [], _, _ => []
  | _ :: _, (a, A), (m, c, τ) => (a.sent m, a.drawn c) :: view A τ

/-- The typed transcript that a flat one spells. -/
def mk : {s : Shape} → RdS E s → List (RV E) → Tr s
  | [], _, _ => ()
  | _ :: _, (a, A), f => (a.mkM (f.headD ([], [])).1, a.mkC (f.headD ([], [])).2, mk A f.tail)

def app : {s t : Shape} → RdS E s → RdS E t → RdS E (s ++ t)
  | [], _, _, B => B
  | _ :: _, _, (a, A), B => (a, app A B)

theorem fms_app : ∀ {s t : Shape} (A : RdS E s) (B : RdS E t), (A.app B).fms = A.fms ++ B.fms
  | [], _, _, _ => rfl
  | _ :: _, _, (a, A), B => congrArg (List.cons a.fm) (fms_app A B)

theorem view_length : ∀ {s : Shape} (A : RdS E s) (τ : Tr s), (A.view τ).length = A.fms.length
  | [], _, _ => rfl
  | _ :: _, (_, A), (_, _, τ) => congrArg Nat.succ (view_length A τ)

theorem view_app : ∀ {s t : Shape} (A : RdS E s) (B : RdS E t) (τ : Tr (s ++ t)),
    (A.app B).view τ = A.view (Tr.fst τ) ++ B.view (Tr.snd (s := s) τ)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (a, A), B, (m, c, τ) => congrArg (List.cons (a.sent m, a.drawn c)) (view_app A B τ)

theorem view_mk : ∀ {s : Shape} (A : RdS E s) (f : List (RV E)), fitsAll A.fms f = true →
    A.view (A.mk f) = f
  | [], _, [], _ => rfl
  | [], _, _ :: _, h => absurd h (by simp [fms, fitsAll])
  | _ :: _, (_, _), [], h => absurd h (by simp [fms, fitsAll])
  | _ :: _, (a, A), v :: vs, h => by
    have h' : a.fm.fits v = true ∧ fitsAll A.fms vs = true := by
      simpa [fms, fitsAll] using h
    obtain ⟨e1, e2⟩ := a.inv v h'.1
    show (a.sent (a.mkM v.1), a.drawn (a.mkC v.2)) :: A.view (A.mk vs) = v :: vs
    rw [e1, e2, view_mk A vs h'.2]

theorem view_fits : ∀ {s : Shape} (A : RdS E s) (τ : Tr s), fitsAll A.fms (A.view τ) = true
  | [], _, _ => rfl
  | _ :: _, (a, A), (m, c, τ) => by
    show (a.fm.fits (a.sent m, a.drawn c) && fitsAll A.fms (A.view τ)) = true
    rw [a.fit m c, view_fits A τ]
    rfl

theorem mk_view : ∀ {s : Shape} (A : RdS E s) (τ : Tr s), A.mk (A.view τ) = τ
  | [], _, _ => rfl
  | _ :: _, (a, A), (m, c, τ) => by
    show (a.mkM (a.sent m), a.mkC (a.drawn c), A.mk (A.view τ)) = (m, c, τ)
    rw [(a.back m c).1, (a.back m c).2, mk_view A τ]

end RdS

/-- The first n rounds to ra, the others to rb. -/
def seqRun {X X' X'' : Type} (n : ℕ) (ra : X → List (RV E) → X') (rb : X' → List (RV E) → X'') :
    X → List (RV E) → X'' := fun x f => rb (ra x (f.take n)) (f.drop n)

/-- The verifier rejects nothing, and its output is run of the view. -/
structure Runs {X X' : Type} {Ex : ExtSpec} (b : BkK X X' Ex) (fm : List Fm)
    (run : X → List (RV E) → X') where
  rd : RdS E b.R.shape
  fms : rd.fms = fm
  out : ∀ x y τ, b.R.out x y τ = some (run x (rd.view τ))

namespace Runs
variable {X X' X'' : Type} {Ex : ExtSpec}

/-- Not hollow: a flat list that fits is spelled by a typed transcript. -/
theorem spells {b : BkK X X' Ex} {fm : List Fm} {run : X → List (RV E) → X'} (h : Runs b fm run)
    (f : List (RV E)) (hf : fitsAll fm f = true) :
    h.rd.view (h.rd.mk f) = f ∧ ∀ x y, b.R.out x y (h.rd.mk f) = some (run x f) := by
  have e : h.rd.view (h.rd.mk f) = f := h.rd.view_mk f (by rw [h.fms]; exact hf)
  exact ⟨e, fun x y => by rw [h.out, e]⟩

def seq {a : BkK X X' Ex} {b : BkK X' X'' Ex} {fa fb : List Fm} {ra : X → List (RV E) → X'}
    {rb : X' → List (RV E) → X''} (ha : Runs a fa ra) (hb : Runs b fb rb) :
    Runs (a.seq b) (fa ++ fb) (seqRun fa.length ra rb) where
  rd := ha.rd.app hb.rd
  fms := (RdS.fms_app ha.rd hb.rd).trans (by rw [ha.fms, hb.fms])
  out := fun x y τ => by
    have hl : (ha.rd.view (Tr.fst τ)).length = fa.length := by
      rw [RdS.view_length, ha.fms]
    have e : RdS.view (s := a.R.shape ++ b.R.shape) (ha.rd.app hb.rd) τ =
        ha.rd.view (Tr.fst τ) ++ hb.rd.view (Tr.snd (s := a.R.shape) τ) :=
      RdS.view_app ha.rd hb.rd τ
    show (a.R.out x y (Tr.fst τ)).bind (fun x₂ =>
      b.R.out x₂ (a.R.imp y (Tr.fst τ)) (Tr.snd (s := a.R.shape) τ)) =
        some (seqRun fa.length ra rb x
          (RdS.view (s := a.R.shape ++ b.R.shape) (ha.rd.app hb.rd) τ))
    rw [e, ha.out]
    show b.R.out _ _ _ = _
    rw [hb.out]
    unfold seqRun
    rw [List.take_left' hl, List.drop_left' hl]

def postM {b : BkK X X' Ex} {fm : List Fm} {run : X → List (RV E) → X'} (h : Runs b fm run)
    (φ : X' → X'') : Runs (b.postM φ) fm (fun x f => φ (run x f)) where
  rd := h.rd
  fms := h.fms
  out := fun x y τ => by
    show (b.R.out x y τ).bind (fun x => some (φ x)) = _
    rw [h.out]
    rfl

def preM {b : BkK X' X'' Ex} {fm : List Fm} {run : X' → List (RV E) → X''} (h : Runs b fm run)
    (φ : X → X') : Runs (b.preM φ) fm (fun x f => run (φ x) f) where
  rd := h.rd
  fms := h.fms
  out := fun x _ τ => h.out (φ x) _ τ

/-- The same block, another way to write its function: the two need agree on flat lists that fit
alone. -/
def congr {b : BkK X X' Ex} {fm : List Fm} {run run' : X → List (RV E) → X'} (h : Runs b fm run)
    (e : ∀ x f, fitsAll fm f = true → run x f = run' x f) : Runs b fm run' where
  rd := h.rd
  fms := h.fms
  out := fun x y τ => by
    have hv : fitsAll fm (h.rd.view τ) = true :=
      (congrArg (fun l => fitsAll l (h.rd.view τ)) h.fms).symm.trans (h.rd.view_fits τ)
    rw [h.out, e x _ hv]

/-- The same list of formats, written otherwise. -/
def fmEq {b : BkK X X' Ex} {fm fm' : List Fm} {run : X → List (RV E) → X'} (h : Runs b fm run)
    (e : fm = fm') : Runs b fm' run where
  rd := h.rd
  fms := h.fms.trans e
  out := h.out

/-- From a verifier that rejects nothing: its value at the typed transcript that the flat one
spells. -/
def ofOut {b : BkK X X' Ex} (rd : RdS E b.R.shape) (v : X → Tr b.R.shape → X')
    (h : ∀ x y τ, b.R.out x y τ = some (v x τ)) : Runs b rd.fms (fun x f => v x (rd.mk f)) where
  rd := rd
  fms := rfl
  out := fun x y τ => by rw [h, rd.mk_view]

end Runs
end

/-! ### small facts on lists -/
section
variable {E : Type} [Zero E]

theorem one_headD : ∀ l : List E, l.length = 1 → [l.headD 0] = l
  | [_], _ => rfl

omit [Zero E] in
theorem nil_of_length : ∀ l : List E, l.length = 0 → [] = l
  | [], _ => rfl

theorem getD_ofFn {n : ℕ} (g : Fin n → E) (t : Fin n) : (List.ofFn g).getD t.val 0 = g t := by
  simp [List.getD_eq_getElem?_getD]

theorem ofFn_getD (l : List E) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun t : Fin n => l.getD t.val 0) = l := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

end

/-! ### how the rounds of the sumcheck and of a draw are read -/
section
variable {E : Type} [Field E] [Fintype E] [DecidableEq E]

/-- ε's round: one scalar; one element of E. -/
def rd0 : RdR E (pRound0 E) where
  fm := ⟨1, 1, false⟩
  sent := fun m => [m.2]
  drawn := fun c => [c]
  mkM := fun l => ((), l.headD 0)
  mkC := fun l => l.headD 0
  inv := fun v h => by
    obtain ⟨h1, h2, _⟩ := (Fm.fits_iff _ v).1 h
    exact ⟨one_headD v.1 h1, one_headD v.2 h2⟩
  fit := fun _ _ => rfl
  back := fun _ _ => ⟨rfl, rfl⟩

/-- How a variable's draw is written from an element. -/
structure FU (f : PFmt E) where
  un : E → f.Ch
  nz : Bool
  ok : ∀ e, (nz = true → e ≠ 0) → f.val (un e) = e
  ne : nz = true → ∀ c, f.val c ≠ 0
  bk : ∀ c, un (f.val c) = c

def fuCube (n : ℕ) : FU (pfCube E n) :=
  ⟨id, false, fun _ _ => rfl, fun h => absurd h (by decide), fun _ => rfl⟩

def fuDummy (D : ℕ) : FU (pDummy E D) :=
  ⟨fun e => if h : e ≠ 0 then ⟨e, h⟩ else ⟨1, one_ne_zero⟩, true, fun e h => by
    show Subtype.val (if h : e ≠ 0 then (⟨e, h⟩ : {x : E // x ≠ 0}) else ⟨1, one_ne_zero⟩) = e
    rw [dif_pos (h rfl)], fun _ c => c.2, fun c => by
    show (if h : c.1 ≠ 0 then (⟨c.1, h⟩ : {x : E // x ≠ 0}) else ⟨1, one_ne_zero⟩) = c
    rw [dif_pos c.2]
    rfl⟩

/-- A short round of a variable: n coefficients; one element. -/
def rdS {f : PFmt E} (u : FU f) : RdR E (sRound f) where
  fm := ⟨f.n, 1, u.nz⟩
  sent := fun m => List.ofFn m.2
  drawn := fun c => [f.val c]
  mkM := fun l => ((), fun t => l.getD t.val 0)
  mkC := fun l => u.un (l.headD 0)
  inv := fun v h => by
    obtain ⟨h1, h2, h3⟩ := (Fm.fits_iff _ v).1 h
    refine ⟨ofFn_getD v.1 f.n h1, ?_⟩
    have e := one_headD v.2 h2
    show [f.val (u.un (v.2.headD 0))] = v.2
    rw [u.ok _ fun hz => h3 hz _ (by rw [← e]; exact List.mem_singleton.2 rfl)]
    exact e
  fit := fun m c => (Fm.fits_iff _ _).2 ⟨List.length_ofFn, rfl, fun hz e he => by
    rw [List.mem_singleton.1 he]
    exact u.ne hz c⟩
  back := fun m c => ⟨Prod.ext rfl (funext fun t => getD_ofFn m.2 t), u.bk c⟩

/-- The values' round: A listed by a numbering. -/
def rdV {A : Type} {n : ℕ} (e : A ≃ Fin n) : RdR E (pRoundV E A) where
  fm := ⟨n, 0, false⟩
  sent := fun m => List.ofFn fun i => m.2 (e.symm i)
  drawn := fun _ => []
  mkM := fun l => ((), fun a => l.getD (e a).val 0)
  mkC := fun _ => ()
  inv := fun v h => by
    obtain ⟨h1, h2, _⟩ := (Fm.fits_iff _ v).1 h
    refine ⟨?_, nil_of_length v.2 h2⟩
    show List.ofFn (fun i : Fin n => v.1.getD (e (e.symm i)).val 0) = v.1
    simp only [Equiv.apply_symm_apply]
    exact ofFn_getD v.1 n h1
  fit := fun _ _ =>
    (Fm.fits_iff _ _).2 ⟨List.length_ofFn, rfl, fun hz => absurd hz Bool.false_ne_true⟩
  back := fun m _ => ⟨Prod.ext rfl (funext fun a => by
    show (List.ofFn fun i => m.2 (e.symm i)).getD (e a).val 0 = m.2 a
    rw [getD_ofFn (fun i => m.2 (e.symm i)) (e a), Equiv.symm_apply_apply]), rfl⟩

/-- A draw: nothing is sent. -/
def rdD {D : Type} [Fintype D] [Nonempty D] (k : ℕ) (enc : D → List E) (dec : List E → D)
    (h : ∀ l : List E, l.length = k → enc (dec l) = l) (hk : ∀ c, (enc c).length = k)
    (hb : ∀ c, dec (enc c) = c) : RdR E (drawRound D) where
  fm := ⟨0, k, false⟩
  sent := fun _ => []
  drawn := enc
  mkM := fun _ => ((), ())
  mkC := dec
  inv := fun v hv => by
    obtain ⟨h1, h2, _⟩ := (Fm.fits_iff _ v).1 hv
    exact ⟨nil_of_length v.1 h1, h v.2 h2⟩
  fit := fun _ c => (Fm.fits_iff _ _).2 ⟨rfl, hk c, fun hz => absurd hz Bool.false_ne_true⟩
  back := fun _ c => ⟨rfl, hb c⟩

def rdE : RdR E (drawRound E) :=
  rdD 1 (fun c => [c]) (fun l => l.headD 0) one_headD (fun _ => rfl) fun _ => rfl

def rdPt (g : ℕ) : RdR E (drawRound (Fin g → E)) :=
  rdD g (fun p => List.ofFn p) (fun l t => l.getD t.val 0) (fun l h => ofFn_getD l g h)
    (fun _ => List.length_ofFn) fun c => funext fun t => getD_ofFn c t

/-- For each variable of a list how its draw is written. -/
def FUs : List (PFmt E) → Type
  | [] => Unit
  | f :: l => FU f × FUs l

def rdVars : (l : List (PFmt E)) → FUs l → RdS E (sRounds l)
  | [], _ => ()
  | _ :: l, (u, U) => (rdS u, rdVars l U)

/-- The short sumcheck's rounds. -/
def rdFull (Y : PscPar E) (U : FUs Y.fmt) {n : ℕ} (e : Y.A ≃ Fin n) : RdS E (shapeS Y) :=
  (rd0, (rdVars Y.fmt U).app ((rdV e, ()) : RdS E [pRoundV E Y.A]))

def rdCore (Y : PscPar E) (U : FUs Y.fmt) : RdS E (TWhole.shapeSC Y) := (rd0, rdVars Y.fmt U)

variable {X X' : Type} {Ex : ExtSpec}

/-- A step without rounds. -/
def Runs.map (φ : X → X') :
    Runs (E := E) (⟨IOR.pure (fun x => some (φ x)) (ExtMap.id Ex), ()⟩ : BkK X X' Ex) []
      (fun x _ => φ x) where
  rd := ()
  fms := rfl
  out := fun _ _ _ => rfl

/-- A draw. -/
def Runs.draw {D : Type} [Fintype D] [Nonempty D] (nx : X → D → X') (err : ℕ)
    (r : RdR E (drawRound D))
    (dec : List E → D) (hd : ∀ c, dec (r.drawn c) = c) :
    Runs (drawK D nx Ex err) [r.fm] (fun x f => nx x (dec (f.headD ([], [])).2)) where
  rd := (r, ())
  fms := rfl
  out := fun x _ τ => by
    obtain ⟨m, c, u⟩ := τ
    show some (nx x c) = some (nx x (dec (r.drawn c)))
    rw [hd]

end
end Flat
end Lk6

#print axioms Lk6.Flat.RdS.view_mk
#print axioms Lk6.Flat.RdS.view_app
#print axioms Lk6.Flat.Runs.spells
#print axioms Lk6.Flat.Runs.seq
#print axioms Lk6.Flat.Runs.postM
#print axioms Lk6.Flat.Runs.preM
#print axioms Lk6.Flat.Runs.map
#print axioms Lk6.Flat.Runs.draw
#print axioms Lk6.Flat.rdFull
