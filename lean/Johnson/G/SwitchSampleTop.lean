-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchSampleTop.lean: code switching: THE HELD OUT-OF-DOMAIN SAMPLES OF THE TYPED
STATEMENT IN FRONT, MADE AT AN ENTRY r OF THE TABLE AND THE PLAIN LETTERS; and the clause on them
that the law's condition in front asks, FROM THE INVARIANT OF THE VERIFIER's STATE AND FOUR TESTS
WITH CODE.

Why. The sentence "carry" (Johnson/Top/H0/K2Caller/CarryK2.lean) and the law's top leave one letter
that reads the verifier's state: smp, the held samples, by a front and its frame. A typed sample
holds a seed, which is no field of the state: it is read back off the stored sample rows. Here the
letter is `smpMade` (Johnson/Top/H/SwitchInXMade.lean) at r's own data, and what is asked of it
follows from `sample_made_of_goodS` (Johnson/Top/H/SwitchSeedFits.lean).
  `k₀Plain`: the stand-in entry of `plK`. `aOfK`: a held message's member by its place in r.kept.
  `smpTop`: THE LETTER, MADE.
  `keptShapeB r`: a test on r alone: each kept member's shape has one answer and main rows of degree
  3 or 1.
  `keptBitsB r W`: a test on r and a frame, by place: the frame's kept entries have the row bits of
  r's kept members' shapes.
  `storedB r W fx`: a test on r, a frame and a front, by place: at each kept entry's own number the
  front's statement has a message of r's kept member's shape, with a stored sample row.
  `sample_top`: the clause, at `smpTop`, `aOfK`, and answer number 0: from `K2.SampleGoodS fx.st`,
  the front's codes, `SwRow.keptAt` and these three tests.
  `sample_top_loc`: the same in the letters of the law's condition in front, written out.
  `keptShape_full`, `keptShape_small`: the first test says yes at every entry of both tables.
  `bits_at_made`: the second says yes at the made front's frame of every entry of both tables.
WHICH PREMISE IS OF WHICH KIND. Of `sample_made_of_goodS`'s premises: that two kept members with one
number are one: a law (`numAt_inj`); that the frame has the member at its number: from `keptAt`
(closed at a written frame); the row bits: `keptBitsB` (closed at a written frame; NOT a consequence
of `keptAt` and `fitAt`, which tie the entry's row bits to the NEW copy's rows); one answer and the
case of the pad: `keptShapeB` (closed, on r alone); the shapes in the statement and the stored rows:
`storedB`: IT READS THE FRONT's STATEMENT AND MUST RIDE IN THE CONDITION IN FRONT, with the
invariant and the codes.
Limits. W₀ is a letter: nothing says that it is the frame of a place. The two maps of names, the
number t and x₀ are letters that the made samples do not read. No member at a run. Nothing on
soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H.SwitchSeedFits
import Johnson.Top.H0.K2Caller.CarryK2
import Johnson.Top.H0.K2Caller.SlotsOfFrame
import Johnson.G.SwitchFrontTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K2Caller VerifiableInference.Desc.First.K2Hands

/-- The stand-in entry of `plK`. -/
def k₀Plain : KeptPlace := ⟨0, 0, 0, 0, [], 0⟩

/-- **A test on r alone**: each kept member's shape has one answer and main rows of degree 3 or
1. -/
def keptShapeB (r : SwRow) : Bool :=
  r.kept.all fun i => (r.lo[i]?).any fun x =>
    x.1.answers == 1 && (x.1.mainDeg == 3 || x.1.mainDeg == 1)

/-- **A test on r and a frame, by place**: the frame's kept entries have the row bits of r's kept
members' shapes. -/
def keptBitsB (r : SwRow) (W : SwitchFrame) : Bool :=
  decide (W.kept.map (·.rowBits) = r.kept.map fun i => ((r.lo[i]?).map fun x => k1 x.1).getD 0)

/-- **A test on r, a frame and a front, by place**: at each kept entry's own number the front's
statement has a message of r's kept member's shape, with a stored sample row. -/
def storedB (r : SwRow) (W : SwitchFrame) (fx : _root_.Tw.K2.Front) : Bool :=
  (List.range r.kept.length).all fun n =>
    match W.kept[n]?, (r.kept[n]?).bind (r.lo[·]?) with
    | some k, some y =>
      (fx.st.oracles[k.old]?).any fun x => decide (x.shape = y.1) && x.sampleRows.size != 0
    | _, _ => false

set_option maxRecDepth 1000000 in
theorem keptShape_full : (tableFullLit.all keptShapeB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem keptShape_small : (tableSmallLit.all keptShapeB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The second test says yes at the made front's frame, at every entry of both tables. -/
theorem bits_at_made :
    ((tableFullLit ++ tableSmallLit).all fun r => (wAt r).any (keptBitsB r)) = true := by
  decide +kernel

section
variable (r : SwRow) (H : r.OK)

theorem kept_get (a : {a // r.kp a}) : r.kept[numAt r a]? = some a.1.1.val := by
  rw [List.getElem?_eq_getElem (numAt_lt r a)]
  exact congrArg some (List.getElem_idxOf (numAt_lt r a))

theorem lo_get (a : {a // r.kp a}) : r.lo[a.1.1.val]? = some (r.lo.get a.1.1) :=
  List.getElem?_eq_getElem a.1.1.isLt

variable {r}

theorem kept_len {W : SwitchFrame} (h : r.keptAt W = true) : W.kept.length = r.kept.length := by
  have e := congrArg List.length (of_decide_eq_true h)
  simpa using e

/-- The frame has each kept member at its number. -/
theorem hmem_of {W : SwitchFrame} (h : r.keptAt W = true) (a : {a // r.kp a}) :
    W.kept[numAt r a]? = some (W.kept.getD (numAt r a) k₀Plain) := by
  have hl : numAt r a < W.kept.length := by rw [kept_len h]; exact numAt_lt r a
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  rfl

/-- The row bits. -/
theorem hrb_of {W : SwitchFrame} (h : r.keptAt W = true) (hb : keptBitsB r W = true)
    (a : {a // r.kp a}) : (W.kept.getD (numAt r a) k₀Plain).rowBits = k1 (r.lo.get a.1.1).1 := by
  have e := congrArg (fun l : List ℕ => l[numAt r a]?) (of_decide_eq_true hb)
  simp only [List.getElem?_map, kept_get r a, hmem_of h a, Option.map_some, lo_get r a,
    Option.getD_some] at e
  exact Option.some.inj e

/-- One answer, and the degree. -/
theorem shape_of (hs : keptShapeB r = true) (a : {a // r.kp a}) :
    (r.lo.get a.1.1).1.answers = 1 ∧
      ((r.lo.get a.1.1).1.mainDeg = 3 ∨ (r.lo.get a.1.1).1.mainDeg = 1) := by
  have e := List.all_eq_true.1 hs a.1.1.val a.2
  rw [lo_get r a] at e
  simpa using e

/-- The message in the front's statement. -/
theorem hx_of {W : SwitchFrame} {fx : _root_.Tw.K2.Front} (h : r.keptAt W = true)
    (hx : storedB r W fx = true) (a : {a // r.kp a}) :
    ∃ x, fx.st.oracles[(W.kept.getD (numAt r a) k₀Plain).old]? = some x ∧
      x.shape = (r.lo.get a.1.1).1 ∧ x.sampleRows.size ≠ 0 := by
  have e := List.all_eq_true.1 hx (numAt r a) (List.mem_range.2 (numAt_lt r a))
  rw [hmem_of h a, kept_get r a] at e
  simp only [Option.bind_some, lo_get r a] at e
  cases ho : fx.st.oracles[(W.kept.getD (numAt r a) k₀Plain).old]? with
  | none => rw [ho] at e; cases e
  | some x =>
    rw [ho] at e
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at e
    exact ⟨x, rfl, e.1, e.2⟩

variable (r)

/-- A held message's member, by its place in r.kept. -/
def aOfK (k : (vecD (plainD r H)).held.K) : ℕ := r.kept.idxOf k.1.1.val

variable (jN : (plainR r H).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (qN : (plainR r H).Sh.Cf.Q → (sigOf r.cs r.l).Ent) (t : ℕ)

/-- **THE LETTER smp, MADE**: the held samples by a front and its frame. -/
noncomputable def smpTop (x₀ : (vecD (plainD r H)).held.Smp) :
    _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp := fun fx W =>
  smpMade (plainR r H) (heldAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM
      (Letters.plain r H).oZ (Letters.plain r H).kq) (Letters.plain r H).Sb (Letters.plain r H).sl
    (Letters.plain r H).Z (Letters.plain r H).A₀ r.cs r.l jN qN t (Letters.plain r H).w₀ W k₀Plain
    memK rowK (aOfK r H) (fun _ _ => 0) x₀ fx.st

/-- **THE CLAUSE ON THE HELD SAMPLES, AT WHAT IS MADE**: from the invariant of the verifier's state
at the front's statement, the front's codes, and four tests with code. -/
theorem sample_top (x₀ : (vecD (plainD r H)).held.Smp) (W₀ : SwitchFrame)
    (fx : _root_.Tw.K2.Front) (hG : K2.SampleGoodS fx.st) (hcs : fx.st.codes = r.cs)
    (hk : r.keptAt W₀ = true) (hb : keptBitsB r W₀ = true) (hs : keptShapeB r = true)
    (hx : storedB r W₀ fx = true) :
    ∀ ks : Σ k, ((vecD (plainD r H)).held.o k).Z.S, ∃ (k : KeptPlace) (sm : OnBytes.Row),
      W₀.kept[aOfK r H ks.1]? = some k ∧ (samplesOf fx.st k)[0]? = some sm ∧
        (smpTop r H jN qN t x₀ fx W₀ ks.1).2 ks.2 = readE sm.target ∧
        pushTo ((vecD (plainD r H)).held.sJ ks.1)
            (((vecD (plainD r H)).held.o ks.1).Z.mat (smpTop r H jN qN t x₀ fx W₀ ks.1).1 ks.2) =
          slotVec (plainR r H).s (plainR r H).Kp memK rowK (aOfK r H ks.1) k.rowBits (formOn sm) :=
  sample_made_of_goodS r.cs r.lo r.mem (stageOf r.g (Letters.plain r H).t₀) r.rad
    (Letters.plain r H).oM (Letters.plain r H).oZ (H.hM _) (H.hZ _) r.kp (fun a _ => a.2) H.h0
    (Letters.plain r H).kq (numAt r) (Letters.plain r H).Sb (Letters.plain r H).sl
    (Letters.plain r H).Z (Letters.plain r H).A₀ r.cs r.l W₀
    (fun a => W₀.kept.getD (numAt r a) k₀Plain) jN qN t (Letters.plain r H).w₀ k₀Plain x₀ fx hG hcs
    (numAt_inj r) (hmem_of hk) (hrb_of hk hb) (fun a => (shape_of hs a).1)
    (fun a => (shape_of hs a).2.elim (fun h3 => Or.inl (Or.inr h3))
      fun h1 => Or.inr ⟨H.h0 a.1 a.2, h1⟩)
    (hx_of hk hx)

set_option quotPrecheck false in
local notation "locP" => (closeSel (heldAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM
  (Letters.plain r H).oZ (Letters.plain r H).kq) (Letters.plain r H).Sb (Letters.plain r H).sl
  (Letters.plain r H).Z (Letters.plain r H).A₀ r.cs r.l jN qN
  (OnBytes.Params.baseCount r.set .request r.g) (Letters.plain r H).w₀).loc

/-- **The same, in the letters in which the law's condition in front asks it** (`OnTop`,
Johnson/Top/H0/K2Caller/TopAt.lean, which is not imported here): `selLoc` and `selR` at the plain
letters, written out. -/
theorem sample_top_loc (x₀ : (vecD (plainD r H)).held.Smp) (W₀ : SwitchFrame)
    (fx : _root_.Tw.K2.Front) (hG : K2.SampleGoodS fx.st) (hcs : fx.st.codes = r.cs)
    (hk : r.keptAt W₀ = true) (hb : keptBitsB r W₀ = true) (hs : keptShapeB r = true)
    (hx : storedB r W₀ fx = true) :
    ∀ ks : Σ k, ((locP).hd.o k).Z.S, ∃ (k : KeptPlace) (sm : OnBytes.Row),
      W₀.kept[aOfK r H ks.1]? = some k ∧ (samplesOf fx.st k)[0]? = some sm ∧
        (smpTop r H jN qN (OnBytes.Params.baseCount r.set .request r.g) x₀ fx W₀ ks.1).2 ks.2 =
          readE sm.target ∧
        pushTo ((locP).hd.sJ ks.1) (((locP).hd.o ks.1).Z.mat
            (smpTop r H jN qN (OnBytes.Params.baseCount r.set .request r.g) x₀ fx W₀ ks.1).1
            ks.2) =
          slotVec ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM
              (Letters.plain r H).oZ).keep r.kp).s
            ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM
              (Letters.plain r H).oZ).keep r.kp).Kp memK rowK (aOfK r H ks.1) k.rowBits
            (formOn sm) :=
  sample_top r H jN qN _ x₀ W₀ fx hG hcs hk hb hs hx

end

end Johnson.G

#print axioms Johnson.G.keptShape_full
#print axioms Johnson.G.keptShape_small
#print axioms Johnson.G.bits_at_made
#print axioms Johnson.G.kept_get
#print axioms Johnson.G.lo_get
#print axioms Johnson.G.kept_len
#print axioms Johnson.G.hmem_of
#print axioms Johnson.G.hrb_of
#print axioms Johnson.G.shape_of
#print axioms Johnson.G.hx_of
#print axioms Johnson.G.sample_top
#print axioms Johnson.G.sample_top_loc
