-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TieThreeSeatsAt.lean: code switching: THE PREMISE hS OF hAt_at_place AND ITS
THREE ARMS (Tw/K2C/TieThreeAt.lean · TieThreeArms.lean), AT seatN := THE SEATS OF A WRITTEN LAYOUT
lay₀ FROM A WRITTEN TREE base ON: fun i => (base + lay₀.tree.getD i 0, lay₀.part.getD i 0). One
theorem with its proof. NO SUB-PROTOCOL IMPORTS THIS FILE.
  hS_at_place   from: lay₀ is the program's layout of written notices under written codes · at the
                front the code switch announces just these notices under these codes (two clauses
                of K2.Fence, Tw/K2C/SendsOn.lean) · p.firstTree + t.roots = base
LEFT, BY NAME: hlay (closed) · hF and hbase, asked at the front, under the table of joints' promise,
Rch and «no mark».
LIMITS. THE SEATS ARE THE LAYOUT's, NOT THE NUMBERS'. ONE seatN MUST SERVE THE LAW AT A PLACE AND
ALL ITS TIES: whoever pays the fourth tie's hN by seatNew_at (K2Caller/SeatsOfN.lean) has N.sent m 0
by place. OWED, CLOSED, BY PLACE, said by nothing here:
  ∀ i, (N.sent m 0).getD i (0, 0) = (base + lay₀.tree.getD i 0, lay₀.part.getD i 0).
What is owed on the numbers (K2.SwitchDebts.sent) says it as a set only, and from the book's count
of trees, not from p.firstTree + t.roots: TieThreeAt.lean's limits have that equation's two halves.
hbase's payer: base_is_roots (Johnson/IMR/BaseIsRoots.lean), where p.firstTree = 0.
No premise is shown met here. No soundness is claimed. On hiding nothing.
-/
import Johnson.Top.H0.Tw.K2C.TieThreeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Hands
open _root_.Tw.K2 (switchNotices)

/-- **hS at a place**, at the seats of a written layout. -/
theorem hS_at_place {F : Frame} {P Cells Tok : Type} {r : SwRow} (p : K2.P2)
    (enter : Rec → Except String Rec)
    (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (z : P) (Rch : ℕ → Rec × F.E.Str → Prop)
    (k base : ℕ) (codes : Codes) (sent : Array OracleNotice) (lay₀ : TreeLay)
    (hlay : layTrees codes sent = some lay₀)
    (hF : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        switchNotices fx.T fx.others = sent ∧ fx.st.codes = codes)
    (hbase : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → p.firstTree + t.roots = base) :
    ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
          ∀ i : Fin r.l.length,
            (fun i : Fin r.l.length =>
                (base + lay₀.tree.getD i.val 0, lay₀.part.getD i.val 0)) i =
              (p.firstTree + (t.roots + lay.tree.getD i.val 0), lay.part.getD i.val 0) := by
  intro a ha hrc hm t et fx hf lay hl i
  obtain ⟨e1, e2⟩ := hF a ha hrc hm t et fx hf
  rw [e1, e2, hlay] at hl
  obtain rfl := Option.some.inj hl
  show (base + lay₀.tree.getD i.val 0, lay₀.part.getD i.val 0) = _
  rw [← hbase a ha hrc hm t et, Nat.add_assoc]

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hS_at_place
