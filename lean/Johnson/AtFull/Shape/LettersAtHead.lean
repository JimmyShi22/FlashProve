-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LettersAtHead.lean: UNDER THE HEAD P5J.AtMgA, AT AN OPENING: OF THE 20 LETTERS
THAT THE TABLE's CELLS READ OF Zp AND Bs.G₀ (`lettersOf`, TabLetters.lean) NINE ARE WRITTEN VALUES,
AND THE READER's STRUCTURE's TWO SPELLINGS ARE ONE. So a record L that holds the written values in
these nine, and is alike to the letters in the other eleven, has the table's cells: Tab.g Zp Bs.G₀ n
= (TabL.cells L n).1. A joining of laws; nothing is evaluated.

What it is for. Whoever shows "the run on shapes returns" at given public files by Lean's kernel may
run the second text at a record L of closed terms or literals, and owes: `WrittenHalf L` (nine
closed equations, no Zp in them) and the plans' half's twelve equations at these files (eleven
letters; k2n has two).

Main names.
* `WrittenHalf L`: L.ft = 0; L.k1, L.k1First: K1's makers at the written record
  (K1NumbersAtHead.lean); L.lin; L.k9, L.close: the library's readers on entries at the written
  values (LinkNumbersAtHead.lean); L.wP (TableBackClosed.lean); L.where13 (BackNumbersAtHead.lean);
  L.p12 (TestNumbersAtHead.lean). The functions of a link at l < 25 alone.
* `writtenHalf_at_head`: the letters at Zp and Bs.G₀ themselves meet WrittenHalf.
* **`alike_at_head`**: the head, an opening O, WrittenHalf L, and: Zp.p.X = L.XZ, Zp.p.X = L.XG,
  Zp.p.built.links = L.links, the letters nums, hpL, k8, k2n, look, k11 at Zp and Bs.G₀ are L's (at
  l < 25; hpL and k2n at 0 < l), and k4pubX Zp.p.X g = L.k4pub g, k4ownX Zp.p.X g = L.k4own g at
  every g ⊢ LettersAlike (lettersOf Zp Bs.G₀) L.
* `tab_at_alike`: general: LettersAlike (lettersOf Z G) L gives Tab.g Z G n = (TabL.cells L n).1 and
  Tab.vals Z G n = (TabL.cells L n).2. `bind_alike`: a tool.

Limits. IMPLICATIONS. THE PLANS' HALF IS PAID BY NOBODY HERE: eleven letters, twelve premises. No
record L of closed terms is laid here; the one record that is shown to meet WrittenHalf, and with it
all premises, is the letters at Zp and Bs.G₀ themselves: so the implication is not empty, and no
more is shown. The opening O carries five letters (F, base, c, A, B) that the head already fixes
(h.laid.opened; Open.unique): what it adds is the name Bs, which the table's laws take by hB
instead: the two meet by O.made. The reader's structure has a third spelling in the table, P5J.At.X
Z, which is Z.p.X by definition. That the head has a member is shown in scope, where the reader
returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold
together, at two named sets of public files, in a side library. The written values are closed terms,
not numerals. Nothing on whether a step returns or a test accepts. The full size alone. At the
format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TabLetters
import Johnson.AtFull.Shape.TableBackClosed
import Johnson.AtFull.Shape.LinkNumbersAtHead
import Johnson.AtFull.Shape.K1NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K1 (parLater firstPar qFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.AtFull.Desc.Lots (xsW groupsW k9WhereE k10ParE)
open ProofFile.Honest.K3 (Site)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- The written half of a record of letters holds the written values: the functions of a link at
l < 25 alone. -/
structure WrittenHalf (L : TabLetters) : Prop where
  ft : L.ft = 0
  k1 : ∀ l, l < 25 → ∀ pc m, L.k1 l pc m = parLater qFull gpW l pc m
  k1First : L.k1First = firstPar qFull gpW
  lin : L.lin = proofSizedFull.batch.shape
  k9 : ∀ l, l < 25 → L.k9 l = k9WhereE xsW l
  close : ∀ l, l < 25 → L.close l = (k9WhereE xsW l).bind fun p => k10ParE groupsW xsW p
  wP : ∀ msg, L.wP msg = wParW msg
  where13 : L.where13 = where13W
  p12 : L.p12 = H2K.Member.piLFull

theorem bind_alike {α β : Type} {a a' : Option α} {f f' : α → Option β} (ha : a = a')
    (hf : ∀ y, f y = f' y) : a.bind f = a'.bind f' := by
  rw [ha, funext hf]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Under the head, at an opening, the letters at Zp and Bs.G₀ themselves hold the written values
in their written half.** So WrittenHalf has a member, and alike_at_head's premises can be met. -/
theorem writtenHalf_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base c A B) :
    WrittenHalf (lettersOf Zp Bs.G₀) where
  ft := congrArg (·.firstTree) (par_at_head h.toAtMg)
  k1 := fun l _ pc m => parLater_at_head h.toAtMg O l pc m
  k1First := firstPar_at_head h.toAtMg O
  lin := (first_at_head h.toAtMg).2.1
  k9 := fun l _ => k9At_at_head h.toAtMg l
  close := fun l _ => bind_alike (k9At_at_head h.toAtMg l) (k10_at_head h.toAtMg)
  wP := wPar_at_head h
  where13 := where13_at_head h.toAtMg
  p12 := p12_at_head h.toAtMg

/-- **UNDER THE HEAD, AT AN OPENING: THE LETTERS' WRITTEN HALF IS WRITTEN**: a record L whose
written half holds the written values, and whose plans' half is alike to the letters at Zp and
Bs.G₀, is alike to these letters. -/
theorem alike_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base c A B)
    {L : TabLetters} (W : WrittenHalf L)
    (hXZ : Zp.p.X = L.XZ) (hXG : Zp.p.X = L.XG) (hlinks : Zp.p.built.links = L.links)
    (hnums : ∀ l, l < 25 → (lettersOf Zp Bs.G₀).nums l = L.nums l)
    (hhpL : ∀ l, 0 < l → l < 25 → (lettersOf Zp Bs.G₀).hpL l = L.hpL l)
    (hk8 : ∀ l, l < 25 → (lettersOf Zp Bs.G₀).k8 l = L.k8 l)
    (hk2L : ∀ l, 0 < l → l < 25 → (lettersOf Zp Bs.G₀).k2n (some l) = L.k2n (some l))
    (hk2F : (lettersOf Zp Bs.G₀).k2n none = L.k2n none)
    (hlook : ∀ l, l < 25 → ∀ d, (lettersOf Zp Bs.G₀).look l d = L.look l d)
    (hk4p : ∀ g, k4pubX Zp.p.X g = L.k4pub g) (hk4o : ∀ g, k4ownX Zp.p.X g = L.k4own g)
    (hk11 : (lettersOf Zp Bs.G₀).k11 = L.k11) :
    LettersAlike (lettersOf Zp Bs.G₀) L where
  XZ := hXZ
  XG := O.W.trans hXG
  links := hlinks
  nums := hnums
  hpL := hhpL
  k8 := hk8
  k2nL := hk2L
  k2nF := hk2F
  look := hlook
  k4pub := fun g => (congrArg (fun W => k4pubX W g) O.W).trans (hk4p g)
  k4own := fun g => (congrArg (fun W => k4ownX W g) O.W).trans (hk4o g)
  k11 := hk11
  ft := (congrArg (·.firstTree) (par_at_head h.toAtMg)).trans W.ft.symm
  k1 := fun l hl pc m => (parLater_at_head h.toAtMg O l pc m).trans (W.k1 l hl pc m).symm
  k1First := (firstPar_at_head h.toAtMg O).trans W.k1First.symm
  lin := (first_at_head h.toAtMg).2.1.trans W.lin.symm
  k9 := fun l hl => (k9At_at_head h.toAtMg l).trans (W.k9 l hl).symm
  close := fun l hl =>
    (bind_alike (k9At_at_head h.toAtMg l) (k10_at_head h.toAtMg)).trans (W.close l hl).symm
  wP := fun msg => (wPar_at_head h msg).trans (W.wP msg).symm
  where13 := (where13_at_head h.toAtMg).trans W.where13.symm
  p12 := (p12_at_head h.toAtMg).trans W.p12.symm

/-- **SO THE TABLE's STEPS AND TESTS ARE THE SECOND TEXT's AT L.** General in the public part and
the ground; spent at Zp and Bs.G₀. -/
theorem tab_at_alike {Z₁ : ProofFile.Pub} {G₁ : ProofFile.Ground} {L : TabLetters}
    (hL : LettersAlike (lettersOf Z₁ G₁) L) (n : Nat) :
    Tab.g Z₁ G₁ n = (TabL.cells L n).1 ∧ Tab.vals Z₁ G₁ n = (TabL.cells L n).2 := by
  have e := tab_of_alike hL n
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.bind_alike
#print axioms Johnson.AtFull.Shape.writtenHalf_at_head
#print axioms Johnson.AtFull.Shape.alike_at_head
#print axioms Johnson.AtFull.Shape.tab_at_alike
#print axioms Johnson.AtFull.Shape.WrittenHalf
