-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/CloseShareScope.lean: K10's THIRD OF THE SHARE «close» (CloseShare.lean, beside this file), IN SCOPE, AT THE NUMBERS FILLED OFF WHAT THE SUB-PROTOCOLS OF THE FIRST CHAIN THEMSELVES TELL: ONE PREMISE IS LEFT: «more». Statements and
proofs. (A «block» in the Lean names is a sub-protocol; the «description» is the IOP as written in Lean.)
  toldC c            what the blocks of c's flat list tell, block by block: b.oracles.flatten. (Other files write the same list as toldOf, with flatten or with flatMap id: which form is to rule is not settled here; told_c_id gives the second.)
  told_k10           O : IM.Open o … · HeadIsTwo Z: at every number k at which c.blocksInOrder has a block of the kind K10: (toldC c)[k]? = some []: the seated block's oracles are its lot's block's (IM.alone_oracles), and K10's block tells of no tree
                     (closing_tells_none, CountsAtK10.lean).
  ix_is              ixK10 l (SitsAll.lean) = 14 * l + nA l + 5 at each l < 25: by the kernel.
  told_at_ix         in scope: (toldC c)[14 * l + nA l + 5]? = some [] at each l < 25.
  book_fit_w         bookFit (N.withTold PW told) PW told = true at EVERY told: bookFit_withTold (Johnson/Desc/First/BookFitTold.lean) with flatPlaces_nodup (KindPlaces.lean).
  close_k10_scope    in scope: ∀ l < 25, p, Q, x: (K9.closeOf p Q)[1]? = some x → IM.Hands (N.withTold PW (toldC c)) LW PW E ft (14 * l + nA l + 4 + 1) x.retype: under hE alone.
LIMITS. hE («more»: E (k + 1) s' from XK … k s along a K10Step) is a premise: E is a letter of that
form. In scope, at OnBytes.secondHashFunction, at onlineDescription's return (Open). At the filled numbers the test
bookFit compares a thing with itself (by reading): it carries
nothing there: what it stood for lies in «bookAt» riding, which is paid here for K10. Nothing on soundness.

-/
import Johnson.LPFK10R.CloseShare
import Johnson.LPFK10R.SitsEvery
import Johnson.Desc.First.BookFitTold

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place Oracle KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers bookFit bookFit_withTold)
open VerifiableInference.Desc.First.Close (Par K10Step closing_tells_none)
open ProofFile (Cl)
open IM

/-- What the blocks of a chain's flat list tell, block by block. -/
def toldC (c : Chain S Cl) : List (List Oracle) := c.blocksInOrder.map fun b => b.oracles.flatten

theorem told_c_id (c : Chain S Cl) : toldC c = c.blocksInOrder.map fun b => b.oracles.flatMap id := by
  unfold toldC
  simp only [List.flatMap_id]

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **A block of the kind K10 in the first chain tells nothing.** -/
theorem told_k10 (O : Open o pol lay KL F Z Bs base c A B) (hk2 : HeadIsTwo Z) {k : ℕ}
    {b : Block S Cl} (hb : c.blocksInOrder[k]? = some b) (hK : b.place.kind = KindName.K10) :
    (toldC c)[k]? = some [] := by
  obtain ⟨l, sub, Lk, p, Q, -, -, -, -, -, h5⟩ :=
    k10_sits_every O hk2 b (List.mem_of_getElem? hb) hK
  unfold toldC
  rw [List.getElem?_map, hb, Option.map_some, alone_oracles h5]
  exact congrArg some (closing_tells_none (Cl := Unit) Q)

end

theorem ix_all : (List.range 25).all (fun l => ixK10 l == 14 * l + nA l + 5) = true := by
  decide +kernel

theorem ix_is {l : ℕ} (hl : l < 25) : ixK10 l = 14 * l + nA l + 5 := by
  have h := List.all_eq_true.1 ix_all l (List.mem_range.2 hl)
  simpa using h

theorem book_fit_w (N : Numbers) (told : List (List Oracle)) :
    bookFit (N.withTold PW told) PW told = true :=
  bookFit_withTold N PW told (ProofFile.Law.flatPlaces_nodup LW true)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem told_at_ix (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) :
    (toldC c)[14 * l + nA l + 5]? = some [] := by
  obtain ⟨Lk, p, Q, b, h1, -, -, h4, h5⟩ := k10_sits hS hR O l hl
  have hb := k10_at_flat hS hR O hl h1 h4
  rw [ix_is hl] at hb
  refine told_k10 O (head_is_two hS hR O) hb ?_
  rw [alone_place h5]

/-- **K10's third of the share «close», in scope, at the filled numbers: «more» alone is left.** -/
theorem close_k10_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (N : Numbers)
    (E : Nat → S → Bool) (ft : Nat)
    (hE : ∀ l < 25, ∀ s s', K10Step s s' → s.failed = none →
      IM.XK (N.withTold PW (toldC c)) LW PW E (14 * l + nA l + 5) s = true →
      E (14 * l + nA l + 5 + 1) s' = true) :
    ∀ l < 25, ∀ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (x : Block S Unit),
      (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[1]? = some x →
      IM.Hands (N.withTold PW (toldC c)) LW PW E ft (14 * l + nA l + 4 + 1) x.retype :=
  close_k10_field (N.withTold PW (toldC c)) E ft (toldC c) (book_fit_w N (toldC c))
    (fun _ hl => told_at_ix hS hR O hl) hE

end

end LPFK10

#print axioms LPFK10.told_k10
#print axioms LPFK10.ix_all
#print axioms LPFK10.book_fit_w
#print axioms LPFK10.told_at_ix
#print axioms LPFK10.close_k10_scope
